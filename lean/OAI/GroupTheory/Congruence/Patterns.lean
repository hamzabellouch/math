import OAI.Geometry.Coboundary.Flags
import OAI.GroupTheory.Congruence.Basic
import OAI.GroupTheory.Congruence.Elementary

namespace OAI

/-!
Pattern subgroups, matrix opposition, block decompositions, and suffix equivalences.
-/

noncomputable section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Patterns

section
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable {n : ℕ}

def cutRank (cut i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨if i.val < cut.val then i.val + (n + 1) - cut.val else i.val - cut.val, by
    split_ifs <;> omega⟩

theorem cutRank_injective (cut : Fin (n + 1)) : Function.Injective (cutRank cut) := by
  intro i j he
  have he' := congrArg Fin.val he
  simp only [cutRank, Fin.val_mk] at he'
  apply Fin.ext
  split_ifs at he' <;> omega

def cutOrder (cut : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  Equiv.ofBijective (cutRank cut) ⟨cutRank_injective cut, Finite.surjective_of_injective (cutRank_injective cut)⟩

def Arc (a b j : Fin (n + 1)) : Prop :=
  if a.val < b.val then a.val < j.val ∧ j.val ≤ b.val
  else a.val < j.val ∨ j.val ≤ b.val

theorem cutRank_lt_iff (cut a b : Fin (n + 1)) (hab : a ≠ b) :
    cutRank cut a < cutRank cut b ↔ ¬ Arc a b cut := by
  have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
  change (if a.val < cut.val then a.val + (n + 1) - cut.val else a.val - cut.val) <
    (if b.val < cut.val then b.val + (n + 1) - cut.val else b.val - cut.val) ↔ _
  unfold Arc
  split_ifs <;> omega

def reindexSL {A : Type*} [CommRing A] (e : Fin (n + 1) ≃ Fin (n + 1)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) A ≃*
      Matrix.SpecialLinearGroup (Fin (n + 1)) A where
  toFun g := ⟨Matrix.reindex e e g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  invFun g := ⟨Matrix.reindex e.symm e.symm g.val, by rw [Matrix.det_reindex_self]; exact g.property⟩
  left_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  right_inv g := by apply Subtype.ext; ext i j; simp [Matrix.reindex_apply]
  map_mul' g h := by
    apply Subtype.ext
    exact (Matrix.reindexRingEquiv A e).map_mul g.val h.val

@[simp] theorem reindexSL_apply {A : Type*} [CommRing A]
    (e : Fin (n + 1) ≃ Fin (n + 1)) (g : Matrix.SpecialLinearGroup (Fin (n + 1)) A)
    (i j : Fin (n + 1)) : reindexSL e g (e i) (e j) = g i j := by
  change g.val (e.symm (e i)) (e.symm (e j)) = g i j
  simp

@[simp] theorem reindexSL_E {A : Type*} [CommRing A]
    (e : Fin (n + 1) ≃ Fin (n + 1)) {i j : Fin (n + 1)} (h : i ≠ j) (c : A) :
    reindexSL e (E h c) = E (show e i ≠ e j from fun he => h (e.injective he)) c := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    Matrix.one_apply, e.injective.eq_iff]

variable (p : ℕ) [Fact p.Prime]

def upperMonoid (N : ℕ) : Submonoid (Matrix.SpecialLinearGroup (Fin N) (R p)) where
  carrier := {g | Upper g}
  one_mem' := by intro i j h; rfl
  mul_mem' := by
    intro g h hg hh i j hij
    change (g.val * h.val) i j = _
    rw [Matrix.mul_apply]
    by_cases he : i = j
    · subst j
      rw [Finset.sum_eq_single i]
      · rw [hg i i le_rfl, hh i i le_rfl]; simp
      · intro l _ hli
        rcases lt_or_gt_of_ne hli with hl | hl
        · rw [hg i l hl.le]; simp [ne_of_gt hl]
        · rw [hh l i hl.le]; simp [ne_of_gt hl]
      · simp
    · rw [Matrix.one_apply_ne he]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hl : l < i
      · rw [hg i l hl.le]; simp [ne_of_gt hl]
      · have hjl : j < l := lt_of_lt_of_le (lt_of_le_of_ne hij (Ne.symm he)) (le_of_not_gt hl)
        rw [hh l j hjl.le]; simp [ne_of_gt hjl]

theorem upper_prime_power (N : ℕ) (g : Matrix.SpecialLinearGroup (Fin N) (R p))
    (hg : Upper g) : ∃ r : ℕ, g ^ p ^ r = 1 := by
  have hn : IsNilpotent (g.val - 1) := by
    refine ⟨N, strict_upper_pow_zero N _ ?_⟩
    intro i j hij
    rw [Matrix.sub_apply, hg i j hij, sub_self]
  have hc : (p : Matrix (Fin N) (Fin N) (R p)) = 0 := by
    ext i j
    simp [Matrix.natCast_apply]
  obtain ⟨r, hr⟩ := exists_prime_power_unipotent (Fact.out : p.Prime) hc _ hn
  refine ⟨r, Subtype.ext ?_⟩
  simpa only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
    add_sub_cancel] using hr

def upperSubgroup (N : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin N) (R p)) :=
  { upperMonoid p N with
    inv_mem' := by
      intro g hg
      obtain ⟨r, hr⟩ := upper_prime_power p N g hg
      have hp : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos _
      have he : g⁻¹ = g ^ (p ^ r - 1) := by
        apply inv_eq_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hp, hr]
      rw [he]
      exact (upperMonoid p N).pow_mem hg _ }

def cutUpper (cut : Fin (n + 1)) : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  (upperSubgroup p (n + 1)).comap (reindexSL (cutOrder cut)).toMonoidHom

theorem cutUpper_iff (cut : Fin (n + 1)) (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :
    g ∈ cutUpper p cut ↔ ∀ i j, cutRank cut j ≤ cutRank cut i →
      g i j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) (R p)) i j := by
  change Upper (reindexSL (cutOrder cut) g) ↔ _
  constructor
  · intro h i j hij
    have := h (cutOrder cut i) (cutOrder cut j) hij
    simpa only [reindexSL_apply, Matrix.one_apply, (cutOrder cut).injective.eq_iff] using this
  · intro h a b hab
    obtain ⟨i, rfl⟩ := (cutOrder cut).surjective a
    obtain ⟨j, rfl⟩ := (cutOrder cut).surjective b
    simpa only [reindexSL_apply, Matrix.one_apply, (cutOrder cut).injective.eq_iff] using h i j hab

theorem localGroup_le_cutUpper (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    localGroup p n hn cut ≤ cutUpper p cut := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨j, hj, rfl⟩
  change cycleRoot p n hn j ∈ cutUpper p cut
  rw [cutUpper_iff]
  have hlt : cutRank cut (edgeSource n j) < cutRank cut j := by
    rw [cutRank_lt_iff _ _ _ (edgeSource_ne n hn j)]
    by_cases h0 : j = 0
    · subst j
      have hc : 0 < cut.val := by
        have : cut.val ≠ 0 := fun h => hj (Fin.ext h.symm)
        omega
      simp only [edgeSource, dite_eq_left rfl, Arc, Fin.val_last, Fin.val_zero,
        Nat.not_lt_zero, ite_false]
      omega
    · have hj0 : 0 < j.val := by
        have : j.val ≠ 0 := fun h => h0 (Fin.ext h)
        omega
      have hne : j.val ≠ cut.val := fun h => hj (Fin.ext h)
      simp only [edgeSource, dite_eq_right h0, Arc, Fin.val_mk,
        ite_eq_left (show j.val - 1 < j.val by omega)]
      omega
  intro a b hba
  change (Matrix.transvection (edgeSource n j) j _) a b = _
  have hne : ¬ (edgeSource n j = a ∧ j = b) := by
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_ge hba) hlt
  simp [Matrix.transvection, hne]

end

section
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable (p n : ℕ) [Fact p.Prime]

def rootGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  Subgroup.closure {g | ∃ j ∈ J, g = cycleRoot p n hn j}

def intersectionGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :=
  ⨅ cut, ⨅ (_ : cut ∉ J), localGroup p n hn cut

omit [Fact p.Prime] in
theorem mem_intersectionGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p)) :
    g ∈ intersectionGroup p n hn J ↔ ∀ cut ∉ J, g ∈ localGroup p n hn cut := by
  simp [intersectionGroup]

omit [Fact p.Prime] in
theorem rootGroup_le_intersection (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    rootGroup p n hn J ≤ intersectionGroup p n hn J := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨j, hj, rfl⟩
  change cycleRoot p n hn j ∈ intersectionGroup p n hn J
  rw [mem_intersectionGroup]
  intro cut hc
  exact Subgroup.subset_closure ⟨j, by intro he; subst cut; contradiction, rfl⟩

omit [Fact p.Prime] in
theorem root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1))) {j : Fin (n + 1)} (hj : j ∈ J) :
    cycleRoot p n hn j ∈ rootGroup p n hn J := Subgroup.subset_closure ⟨j, hj, rfl⟩

omit [Fact p.Prime] in
theorem upper_adjacent_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a.val + 1 = b.val) (hb : b ∈ J) :
    E (show a ≠ b by intro he; subst b; omega) (1 : R p) ∈ rootGroup p n hn J := by
  have hb0 : b ≠ 0 := by intro he; subst b; simp at hab
  have hs : edgeSource n b = a := by
    apply Fin.ext
    simp only [edgeSource, dite_eq_right hb0, Fin.val_mk]
    omega
  simpa [cycleRoot, hs, hb0] using root_mem p n hn J hb

omit [Fact p.Prime] in
theorem upper_path_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a < b)
    (hpath : ∀ j, a.val < j.val → j.val ≤ b.val → j ∈ J) :
    E hab.ne (1 : R p) ∈ rootGroup p n hn J := by
  generalize hdiff : b.val - a.val = r
  induction r using Nat.strong_induction_on generalizing a b with
  | h r ih =>
    by_cases hadj : a.val + 1 = b.val
    · exact upper_adjacent_mem p n hn J hadj (hpath b hab le_rfl)
    · let c : Fin (n + 1) := ⟨b.val - 1, by omega⟩
      have hac : a < c := by dsimp [c]; change a.val < b.val - 1; omega
      have hcb : c.val + 1 = b.val := by dsimp [c]; omega
      have hcb' : c < b := by change c.val < b.val; omega
      have hc := ih (c.val - a.val) (by omega) hac (fun j hj hj' => hpath j hj (by omega)) rfl
      simpa only [mul_one] using E_path_mem (rootGroup p n hn J) hac.ne hcb'.ne hab.ne hc
        (upper_adjacent_mem p n hn J hcb (hpath b hab le_rfl))

omit [Fact p.Prime] in
theorem lower_path_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hba : b < a)
    (hpath : ∀ j, a.val < j.val ∨ j.val ≤ b.val → j ∈ J) :
    E hba.ne.symm (Polynomial.X : R p) ∈ rootGroup p n hn J := by
  have ha0 : a ≠ 0 := by intro he; subst a; have := hba; change b.val < 0 at this; omega
  have hn0 : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro he; have := congrArg Fin.val he; simp only [Fin.val_last, Fin.val_zero] at this; omega
  have h0 : E hn0 (Polynomial.X : R p) ∈ rootGroup p n hn J := by
    simpa [cycleRoot, edgeSource] using root_mem p n hn J (hpath 0 (Or.inr (Nat.zero_le _)))
  have ha : E ha0 (Polynomial.X : R p) ∈ rootGroup p n hn J := by
    by_cases he : a = Fin.last n
    · subst a; exact h0
    · have hal : a < Fin.last n := by
        have hv : a.val ≠ n := fun h => he (Fin.ext h)
        change a.val < n
        omega
      have hau := upper_path_mem p n hn J hal (fun j hj _ => hpath j (Or.inl hj))
      simpa only [one_mul] using E_path_mem (rootGroup p n hn J) hal.ne hn0 ha0 hau h0
  by_cases hb0 : b = 0
  · subst b; exact ha
  · have h0b : (0 : Fin (n + 1)) < b := by
      have hv : b.val ≠ 0 := fun h => hb0 (Fin.ext h)
      change 0 < b.val
      omega
    have hbu := upper_path_mem p n hn J h0b (fun j _ hj => hpath j (Or.inr hj))
    simpa only [mul_one] using E_path_mem (rootGroup p n hn J) ha0 h0b.ne hba.ne.symm ha hbu

theorem scalar_root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a ≠ b) (f : R p)
    (hf : E hab f ∈ rootGroup p n hn J) (c : ZMod p) :
    E hab (Polynomial.C c * f) ∈ rootGroup p n hn J := by
  have hc : Polynomial.C c = (c.val : R p) := by
    rw [← map_natCast Polynomial.C, ZMod.natCast_zmod_val]
  rw [hc, E_natCast_mul]
  exact (rootGroup p n hn J).pow_mem hf _

def pathCoefficient {a b : Fin (n + 1)} (c : ZMod p) : R p :=
  Polynomial.C c * if a.val < b.val then 1 else Polynomial.X

theorem path_root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    {a b : Fin (n + 1)} (hab : a ≠ b) (hpath : ∀ j, Arc a b j → j ∈ J) (c : ZMod p) :
    E hab (pathCoefficient (p := p) (n := n) (a := a) (b := b) c) ∈ rootGroup p n hn J := by
  unfold pathCoefficient
  by_cases hab' : a < b
  · rw [ite_eq_left (show a.val < b.val from hab')]
    exact scalar_root_mem p n hn J hab _ (upper_path_mem p n hn J hab'
      (fun j hj hj' => hpath j (by simpa [Arc, show a.val < b.val from hab'] using And.intro hj hj'))) c
  · rw [ite_eq_right (show ¬ a.val < b.val from hab')]
    have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab') hab.symm
    exact scalar_root_mem p n hn J hab _ (lower_path_mem p n hn J hba
      (fun j hj => hpath j (by simpa [Arc, show ¬ a.val < b.val from hab'] using hj))) c

end

open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
variable (p n : ℕ) [Fact p.Prime]

theorem entry_nonzero_path (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))
    (hg : g ∈ intersectionGroup p n hn J) {a b : Fin (n + 1)} (hab : a ≠ b)
    (hne : g a b ≠ 0) : ∀ j, Arc a b j → j ∈ J := by
  intro j hj
  by_contra hjJ
  have hg' := (mem_intersectionGroup p n hn J g).mp hg j hjJ
  have hupper := (cutUpper_iff p j g).mp (localGroup_le_cutUpper p hn j hg')
  have hba : cutRank j b ≤ cutRank j a := by
    apply le_of_not_gt
    rwa [cutRank_lt_iff j a b hab, not_not]
  exact hne ((hupper a b hba).trans (Matrix.one_apply_ne hab))

theorem intersection_diagonal (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (cut : Fin (n + 1)) (hcut : cut ∉ J)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))
    (hg : g ∈ intersectionGroup p n hn J) (a : Fin (n + 1)) : g a a = 1 := by
  have hg' := (mem_intersectionGroup p n hn J g).mp hg cut hcut
  have := (cutUpper_iff p cut g).mp (localGroup_le_cutUpper p hn cut hg') a a le_rfl
  simpa using this

theorem local_entry_coefficient (hn : 1 ≤ n) (cut : Fin (n + 1))
    (g : localGroup p n hn cut) {a b : Fin (n + 1)}
    (hlt : cutRank cut a < cutRank cut b) :
    ∃ c : ZMod p, g.val a b = pathCoefficient (p := p) (n := n) (a := a) (b := b) c := by
  obtain ⟨c, hc⟩ := localGroup_entry_equation p n hn cut g a b
  refine ⟨c, ?_⟩
  unfold cutPolynomial at hc
  unfold pathCoefficient
  change (if a.val < cut.val then a.val + (n + 1) - cut.val else a.val - cut.val) <
    (if b.val < cut.val then b.val + (n + 1) - cut.val else b.val - cut.val) at hlt
  by_cases ha : a.val < cut.val <;> by_cases hb : b.val < cut.val
  · rw [ite_eq_left ha, ite_eq_left hb] at hc
    have hab : a.val < b.val := by simp only [ite_eq_left ha, ite_eq_left hb] at hlt; omega
    rw [ite_eq_left hab, mul_one]
    apply mul_left_cancel₀ (Polynomial.X_ne_zero (R := ZMod p))
    simpa only [mul_comm Polynomial.X (Polynomial.C c)] using hc
  · simp only [ite_eq_left ha, ite_eq_right hb] at hlt
    omega
  · rw [ite_eq_right ha, ite_eq_left hb, one_mul] at hc
    rw [ite_eq_right (by omega : ¬ a.val < b.val)]
    exact hc
  · rw [ite_eq_right ha, ite_eq_right hb, one_mul, mul_one] at hc
    have hab : a.val < b.val := by simp only [ite_eq_right ha, ite_eq_right hb] at hlt; omega
    rw [ite_eq_left hab, mul_one]
    exact hc

theorem entry_root_mem (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (cut : Fin (n + 1)) (hcut : cut ∉ J)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))
    (hg : g ∈ intersectionGroup p n hn J) {a b : Fin (n + 1)} (hab : a ≠ b) :
    E hab (g a b) ∈ rootGroup p n hn J := by
  by_cases hz : g a b = 0
  · simp [hz, E]
  · have hpath := entry_nonzero_path p n hn J g hg hab hz
    have hlt : cutRank cut a < cutRank cut b := by
      rw [cutRank_lt_iff cut a b hab]
      exact fun h => hcut (hpath cut h)
    have hg' := (mem_intersectionGroup p n hn J g).mp hg cut hcut
    obtain ⟨c, hc⟩ := local_entry_coefficient p n hn cut ⟨g, hg'⟩ hlt
    change g a b = _ at hc
    rw [hc]
    exact path_root_mem p n hn J hab hpath c

theorem rootGroup_eq_intersection (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (hJ : ∃ cut, cut ∉ J) : rootGroup p n hn J = intersectionGroup p n hn J := by
  apply le_antisymm (rootGroup_le_intersection p n hn J)
  obtain ⟨cut, hcut⟩ := hJ
  let e := reindexSL (A := R p) (cutOrder cut)
  let P := (intersectionGroup p n hn J).map e.toMonoidHom
  let H := (rootGroup p n hn J).map e.toMonoidHom
  have hHP : H ≤ P := Subgroup.map_mono (rootGroup_le_intersection p n hn J)
  have hP : ∀ g ∈ P, Upper g := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' := (mem_intersectionGroup p n hn J g).mp hg cut hcut
    exact localGroup_le_cutUpper p hn cut hg'
  have hE : ∀ g ∈ P, ∀ i j (h : i < j), E h.ne (g i j) ∈ H := by
    rintro _ ⟨g, hg, rfl⟩ i j hij
    obtain ⟨a, rfl⟩ := (cutOrder cut).surjective i
    obtain ⟨b, rfl⟩ := (cutOrder cut).surjective j
    have hab : a ≠ b := fun he => hij.ne (congrArg (cutOrder cut) he)
    refine ⟨E hab (g a b), entry_root_mem p n hn J cut hcut g hg hab, ?_⟩
    change reindexSL (cutOrder cut) _ = _
    rw [reindexSL_E]
    congr 1
    exact (reindexSL_apply (cutOrder cut) g a b).symm
  have hPH := upper_subgroup_le P H hHP hP hE
  intro g hg
  have : e g ∈ H := hPH ⟨g, hg, rfl⟩
  obtain ⟨h, hh, he⟩ := this
  exact e.injective he ▸ hh

theorem rootGroup_inter (hn : 1 ≤ n) (J K : Set (Fin (n + 1)))
    (hJ : ∃ cut, cut ∉ J) (hK : ∃ cut, cut ∉ K) :
    rootGroup p n hn J ⊓ rootGroup p n hn K = rootGroup p n hn (J ∩ K) := by
  have hJK : ∃ cut, cut ∉ J ∩ K := by
    obtain ⟨cut, hc⟩ := hJ
    exact ⟨cut, fun h => hc h.1⟩
  rw [rootGroup_eq_intersection p n hn J hJ, rootGroup_eq_intersection p n hn K hK,
    rootGroup_eq_intersection p n hn (J ∩ K) hJK]
  ext g
  simp only [Subgroup.mem_inf, mem_intersectionGroup, Set.mem_inter_iff]
  constructor
  · rintro ⟨hJ', hK'⟩ cut hc
    by_cases h : cut ∈ J
    · exact hK' cut (fun hk => hc ⟨h, hk⟩)
    · exact hJ' cut h
  · intro h
    exact ⟨fun cut hc => h cut (fun hjk => hc hjk.1),
      fun cut hc => h cut (fun hjk => hc hjk.2)⟩

omit [Fact p.Prime] in
@[simp] theorem rootGroup_empty (hn : 1 ≤ n) : rootGroup p n hn ∅ = ⊥ := by
  simp [rootGroup]

omit [Fact p.Prime] in
@[simp] theorem rootGroup_compl_singleton (hn : 1 ≤ n) (cut : Fin (n + 1)) :
    rootGroup p n hn ({cut}ᶜ) = localGroup p n hn cut := by
  simp [rootGroup, localGroup]

theorem iInf_localGroup_eq_bot (hn : 1 ≤ n) : (⨅ cut, localGroup p n hn cut) = ⊥ := by
  have he := rootGroup_eq_intersection p n hn ∅ ⟨0, by simp⟩
  simpa [intersectionGroup] using he.symm

theorem rootGroup_reduction_injective (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (hJ : ∃ cut, cut ∉ J) {m : ℕ} (hm : 2 ≤ m) :
    Set.InjOn (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)))
      (↑(rootGroup p n hn J) : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) (R p))) := by
  obtain ⟨cut, hc⟩ := hJ
  intro g hg h hh he
  have hg' := (mem_intersectionGroup p n hn J g).mp (rootGroup_le_intersection p n hn J hg) cut hc
  have hh' := (mem_intersectionGroup p n hn J h).mp (rootGroup_le_intersection p n hn J hh) cut hc
  exact localGroups_reduction_injective p n hn hm cut cut ⟨g, hg'⟩ ⟨h, hh'⟩ he

theorem reduction_preserves_rootGroup_intersections (hn : 1 ≤ n)
    (J K : Set (Fin (n + 1))) (hJ : ∃ cut, cut ∉ J) (hK : ∃ cut, cut ∉ K)
    {m : ℕ} (hm : 2 ≤ m) :
    (rootGroup p n hn J).map (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))) ⊓
      (rootGroup p n hn K).map (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))) =
    (rootGroup p n hn (J ∩ K)).map (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))) := by
  rw [← rootGroup_inter p n hn J K hJ hK]
  apply le_antisymm
  · rintro g ⟨⟨a, ha, rfl⟩, b, hb, he⟩
    obtain ⟨ca, hca⟩ := hJ
    obtain ⟨cb, hcb⟩ := hK
    have ha' := (mem_intersectionGroup p n hn J a).mp (rootGroup_le_intersection p n hn J ha) ca hca
    have hb' := (mem_intersectionGroup p n hn K b).mp (rootGroup_le_intersection p n hn K hb) cb hcb
    have hab := localGroups_reduction_injective p n hn hm cb ca ⟨b, hb'⟩ ⟨a, ha'⟩ he
    change b = a at hab
    subst b
    exact ⟨a, ⟨ha, hb⟩, rfl⟩
  · exact Subgroup.map_inf_le _ _ _

def standardLocalGroup (hn : 1 ≤ n) (J : Set (Fin (n + 1))) :
    Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) (ZMod p)) :=
  Subgroup.closure {g | ∃ j ∈ J, g = E (edgeSource_ne n hn j) (1 : ZMod p)}

theorem rootGroup_image_eq_standard (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (cut : Fin (n + 1)) (hc : cut ∉ J) :
    (rootGroup p n hn J).map (cutConjugation p n cut) =
      (standardLocalGroup p n hn J).map (Matrix.SpecialLinearGroup.mapGL (Frac p)) := by
  rw [rootGroup, standardLocalGroup, MonoidHom.map_closure, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨E (edgeSource_ne n hn j) 1, ⟨j, hj, rfl⟩, ?_⟩
    have hjc : j ≠ cut := by intro he; subst cut; contradiction
    rw [cutConjugation_root p n hn cut j hjc]
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    rfl
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨cycleRoot p n hn j, ⟨j, hj, rfl⟩, ?_⟩
    have hjc : j ≠ cut := by intro he; subst cut; contradiction
    rw [cutConjugation_root p n hn cut j hjc]
    apply Matrix.GeneralLinearGroup.ext
    intro a b
    rfl

def localStandardEquiv (hn : 1 ≤ n) (J : Set (Fin (n + 1)))
    (cut : Fin (n + 1)) (hc : cut ∉ J) :
    rootGroup p n hn J ≃* standardLocalGroup p n hn J :=
  ((rootGroup p n hn J).equivMapOfInjective (cutConjugation p n cut)
      (cutConjugation_injective p n cut)).trans
    ((MulEquiv.subgroupCongr (rootGroup_image_eq_standard p n hn J cut hc)).trans
      ((standardLocalGroup p n hn J).equivMapOfInjective
        (Matrix.SpecialLinearGroup.mapGL (Frac p)) Matrix.SpecialLinearGroup.mapGL_injective).symm)

end CoboundaryExpanders.Patterns

namespace CoboundaryExpanders.MatrixOpposition
open Module Submodule SphericalOpposition SphericalOpposition.CompleteFlag Elementary
open scoped Matrix Pointwise
variable {K : Type} [Field K] {N : ℕ}

abbrev stdFlag (K : Type) [Field K] (N : ℕ) : CompleteFlag K (Fin N → K) N :=
  basisFlag (K:=K) (V:=Fin N → K) (Pi.basisFun K (Fin N))
abbrev oppFlag (K : Type) [Field K] (N : ℕ) : CompleteFlag K (Fin N → K) N :=
  oppositeBasisFlag (K:=K) (V:=Fin N → K) (Pi.basisFun K (Fin N))

lemma stdFlags_opposite : (stdFlag K N).Opposite (oppFlag K N) :=
  basisFlags_opposite _

lemma upper_iff_unipotent (g : Matrix.SpecialLinearGroup (Fin N) K) :
    Upper g ↔ Matrix.SpecialLinearGroup.toLin' g ∈ (stdFlag K N).unipotentFlagStabilizer := by
  rw [mem_unipotent_iff_unitriangular _ _ (basisFlag_adapted _)]
  unfold Unitriangular Upper
  simp only [Pi.basisFun_repr, Pi.basisFun_apply, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.one_apply]
  exact ⟨fun h i j hij => h j i hij,fun h i j hij => h j i hij⟩

def upperGroup (K : Type) [Field K] (N : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  (stdFlag K N).unipotentFlagStabilizer.comap Matrix.SpecialLinearGroup.toLin'

@[simp] lemma mem_upperGroup (g : Matrix.SpecialLinearGroup (Fin N) K) :
    g ∈ upperGroup K N ↔ Upper g := (upper_iff_unipotent g).symm

def upperToFlag : upperGroup K N →* (stdFlag K N).unipotentFlagStabilizer :=
  { toFun := fun g => ⟨Matrix.SpecialLinearGroup.toLin' g.val,g.property⟩
    map_one' := by apply Subtype.ext; exact map_one _
    map_mul' := fun g h => by apply Subtype.ext; exact map_mul _ _ _ }

lemma upperToFlag_injective : Function.Injective (upperToFlag (K:=K) (N:=N)) := by
  intro g h he
  apply Subtype.ext
  exact Matrix.SpecialLinearGroup.toLin'_injective (congrArg Subtype.val he)

lemma upperToFlag_surjective : Function.Surjective (upperToFlag (K:=K) (N:=N)) := by
  intro e
  let M := LinearMap.toMatrix' e.val.toLinearMap
  have he : Unitriangular (Pi.basisFun K (Fin N)) e.val :=
    (mem_unipotent_iff_unitriangular _ _ (basisFlag_adapted _) _).mp e.property
  have hM (i j : Fin N) (hji : j ≤ i) : M i j = if i = j then 1 else 0 := by
    simpa only [M, LinearMap.toMatrix'_apply, Pi.basisFun_repr, Pi.basisFun_apply, LinearEquiv.coe_coe] using he j i hji
  have ht : M.IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    rw [hM i j hji.le, ite_eq_right hji.ne.symm]
  have hd : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    apply Finset.prod_eq_one
    intro i hi
    rw [hM i i le_rfl, ite_eq_left rfl]
  let g : Matrix.SpecialLinearGroup (Fin N) K := ⟨M,hd⟩
  have hge : Matrix.SpecialLinearGroup.toLin' g = e.val := by
    apply LinearEquiv.toLinearMap_injective
    change Matrix.toLin' (LinearMap.toMatrix' e.val.toLinearMap) = e.val.toLinearMap
    exact Matrix.toLin'_toMatrix' _
  have hg : g ∈ upperGroup K N := by
    rw [mem_upperGroup]
    intro i j hji
    change M i j = _
    simpa only [Matrix.one_apply] using hM i j hji
  exact ⟨⟨g,hg⟩,Subtype.ext hge⟩

def upperFlagEquiv : upperGroup K N ≃* (stdFlag K N).unipotentFlagStabilizer :=
  MulEquiv.ofBijective upperToFlag ⟨upperToFlag_injective, upperToFlag_surjective⟩

lemma upper_E {i j : Fin N} (hij : i < j) (c : K) : E hij.ne c ∈ upperGroup K N := by
  rw [mem_upperGroup]
  simpa only [mul_one] using upper_E_mul hij c (g:=1) (fun i j _ => rfl)

lemma preserves_suffix_iff (g : upperGroup K N) (k : Fin (N+1)) :
    ((oppFlag K N).space ⟨N-k.val,by omega⟩).map
      (Matrix.SpecialLinearGroup.toLin' g.val).toLinearMap =
      (oppFlag K N).space ⟨N-k.val,by omega⟩ ↔
    ∀ i j : Fin N, i.val < k.val → k.val ≤ j.val → g.val i j = 0 := by
  let e := Matrix.SpecialLinearGroup.toLin' g.val
  have hm := (oppFlag K N).mem_opposite_flag_iff_repr (Pi.basisFun K (Fin N))
    (oppositeBasisFlag_adapted _) k
  simp only [Pi.basisFun_repr] at hm
  constructor
  · intro h i j hi hj
    have hb : Pi.single j (1:K) ∈ (oppFlag K N).space ⟨N-k.val,by omega⟩ := by
      apply (hm _).mpr
      intro a ha
      simp only [Pi.single_apply, ite_eq_right (show a ≠ j by intro he; subst j; omega)]
    have he' : e (Pi.single j 1) ∈ (oppFlag K N).space ⟨N-k.val,by omega⟩ := by
      rw [← h]
      exact ⟨_,hb,rfl⟩
    have hh := (hm _).mp he' i hi
    simpa only [e, Matrix.SpecialLinearGroup.toLin'_apply,Matrix.toLin'_apply,
      Matrix.mulVec_single_one,Matrix.col_apply] using hh
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨v,hv,rfl⟩
      apply (hm _).mpr
      intro i hi
      change (g.val.val *ᵥ v) i = 0
      rw [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hk : k.val ≤ j.val
      · rw [h i j hi hk,zero_mul]
      · rw [(hm v).mp hv j (by omega),mul_zero]
    · exact e.finrank_map_eq _

def suffixStabilizer (K : Type) [Field K] (k : Fin N) :
    Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  (MulAction.stabilizer ((Fin N → K) ≃ₗ[K] (Fin N → K))
    ((oppFlag K N).space ⟨N-k.val,by omega⟩)).comap Matrix.SpecialLinearGroup.toLin'

def patternGroup (K : Type) [Field K] (J : Set (Fin N)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  upperGroup K N ⊓ ⨅ k : Fin N, ⨅ (_ : k ∉ J), suffixStabilizer K k

lemma mem_suffixStabilizer (g : Matrix.SpecialLinearGroup (Fin N) K) (k : Fin N) :
    g ∈ suffixStabilizer K k ↔
    ((oppFlag K N).space ⟨N-k.val,by omega⟩).map
      (Matrix.SpecialLinearGroup.toLin' g).toLinearMap =
        (oppFlag K N).space ⟨N-k.val,by omega⟩ := by
  simp only [suffixStabilizer, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

lemma mem_patternGroup (J : Set (Fin N)) (g : Matrix.SpecialLinearGroup (Fin N) K) :
    g ∈ patternGroup K J ↔ Upper g ∧
      ∀ k : Fin N, k ∉ J → ∀ i j : Fin N,
        i.val < k.val → k.val ≤ j.val → g i j = 0 := by
  simp only [patternGroup,Subgroup.mem_inf,Subgroup.mem_iInf,mem_upperGroup]
  constructor
  · rintro ⟨hg,hs⟩
    refine ⟨hg,fun k hk => ?_⟩
    exact (preserves_suffix_iff ⟨g,(mem_upperGroup g).mpr hg⟩ k.castSucc).mp
      ((mem_suffixStabilizer g k).mp (hs k hk))
  · rintro ⟨hg,hs⟩
    refine ⟨hg,fun k hk => (mem_suffixStabilizer g k).mpr ?_⟩
    exact (preserves_suffix_iff ⟨g,(mem_upperGroup g).mpr hg⟩ k.castSucc).mpr (hs k hk)

def pathGroup (K : Type) [Field K] (J : Set (Fin N)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  Subgroup.closure {g | ∃ i j : Fin N, ∃ h : i.val+1 = j.val,
    j ∈ J ∧ g = E (show i ≠ j by intro he; subst j; omega) (1:K)}

lemma adjacent_mem_pathGroup (J : Set (Fin N)) {i j : Fin N}
    (h : i.val+1 = j.val) (hj : j ∈ J) :
    E (show i ≠ j by intro he; subst j; omega) (1:K) ∈ pathGroup K J :=
  Subgroup.subset_closure ⟨i,j,h,hj,rfl⟩

lemma pathGroup_le_pattern (J : Set (Fin N)) : pathGroup K J ≤ patternGroup K J := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨i,j,h,hj,rfl⟩
  apply (mem_patternGroup J _).mpr
  refine ⟨(mem_upperGroup _).mp (upper_E (show i < j by change i.val < j.val; omega) 1),?_⟩
  intro k hk a b hak hkb
  have hab : a ≠ b := by intro he; subst b; omega
  have hn : ¬ (a = i ∧ b = j) := by
    rintro ⟨hai,hbj⟩
    have ha := congrArg Fin.val hai
    have hb := congrArg Fin.val hbj
    have he : k = j := by apply Fin.ext; omega
    exact hk (he.symm ▸ hj)
  have hn' : ¬ (i = a ∧ j = b) := fun h => hn ⟨h.1.symm,h.2.symm⟩
  change (1 + Matrix.single i j (1:K)) a b = 0
  simp [Matrix.add_apply,hab,hn']

lemma E_path_one_mem (J : Set (Fin N)) {i j : Fin N} (hij : i < j)
    (hpath : ∀ k : Fin N, i.val < k.val → k.val ≤ j.val → k ∈ J) :
    E hij.ne (1:K) ∈ pathGroup K J := by
  generalize hdiff : j.val-i.val = r
  induction r using Nat.strong_induction_on generalizing i j with
  | h r ih =>
    by_cases hadj : i.val+1 = j.val
    · exact adjacent_mem_pathGroup J hadj (hpath j hij le_rfl)
    · let c : Fin N := ⟨j.val-1,by omega⟩
      have hic : i < c := by change i.val < j.val-1; omega
      have hcj : c.val+1 = j.val := by dsimp [c]; omega
      have hcj' : c < j := by change c.val < j.val; omega
      have hc := ih (c.val-i.val) (by omega) hic
        (fun k hi hk => hpath k hi (hk.trans hcj'.le)) rfl
      simpa only [mul_one] using E_path_mem (pathGroup K J) hic.ne hcj'.ne hij.ne hc
        (adjacent_mem_pathGroup J hcj (hpath j hij le_rfl))

variable (p : ℕ) [Fact p.Prime]

lemma E_path_mem_coeff (J : Set (Fin N)) {i j : Fin N} (hij : i < j)
    (hpath : ∀ k : Fin N, i.val < k.val → k.val ≤ j.val → k ∈ J) (c : ZMod p) :
    E hij.ne c ∈ pathGroup (ZMod p) J := by
  have hc : E hij.ne c = E hij.ne (1:ZMod p) ^ c.val := by
    rw [← E_natCast_mul, ZMod.natCast_zmod_val, mul_one]
  rw [hc]
  exact (pathGroup (ZMod p) J).pow_mem (E_path_one_mem J hij hpath) _

theorem pathGroup_eq_pattern (J : Set (Fin N)) :
    pathGroup (ZMod p) J = patternGroup (ZMod p) J := by
  apply le_antisymm (pathGroup_le_pattern J)
  apply upper_subgroup_le _ _ (pathGroup_le_pattern J)
  · intro g hg
    exact ((mem_patternGroup J g).mp hg).1
  · intro g hg i j hij
    by_cases hzero : g i j = 0
    · rw [hzero]
      simpa only [E,Matrix.SpecialLinearGroup.transvection_coeff_zero] using (pathGroup (ZMod p) J).one_mem
    · apply E_path_mem_coeff p J hij
      intro k hik hkj
      by_contra hk
      exact hzero (((mem_patternGroup J g).mp hg).2 k hk i j hik hkj)

lemma full_pathGroup : pathGroup (ZMod p) (Set.univ : Set (Fin N)) = upperGroup (ZMod p) N := by
  rw [pathGroup_eq_pattern]
  ext g
  simp [mem_patternGroup]

lemma pathGroup_inter (J L : Set (Fin N)) :
    pathGroup (ZMod p) J ⊓ pathGroup (ZMod p) L = pathGroup (ZMod p) (J ∩ L) := by
  simp only [pathGroup_eq_pattern]
  ext g
  simp only [Subgroup.mem_inf,mem_patternGroup,Set.mem_inter_iff,not_and_or]
  constructor
  · rintro ⟨⟨hu,hJ⟩,⟨_,hL⟩⟩
    exact ⟨hu,fun k hk => hk.elim (hJ k) (hL k)⟩
  · rintro ⟨hu,h⟩
    exact ⟨⟨hu,fun k hk => h k (Or.inl hk)⟩,⟨hu,fun k hk => h k (Or.inr hk)⟩⟩

lemma pathGroup_delete (k : Fin N) :
    pathGroup (ZMod p) ({k}ᶜ) = upperGroup (ZMod p) N ⊓ suffixStabilizer (ZMod p) k := by
  rw [pathGroup_eq_pattern]
  ext g
  simp [patternGroup]

end CoboundaryExpanders.MatrixOpposition

namespace CoboundaryExpanders.Patterns

section
open Construction Elementary MatrixOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable {n : ℕ}

@[simp] lemma cutOrder_cut (cut : Fin (n+1)) : cutOrder cut cut = 0 := by
  apply Fin.ext
  change (cutRank cut cut).val = 0
  simp [cutRank]

lemma cutOrder_edgeSource (cut j : Fin (n+1)) (hj : j ≠ cut) :
    (cutOrder cut (edgeSource n j)).val + 1 = (cutOrder cut j).val := by
  have hjc : j.val ≠ cut.val := fun h => hj (Fin.ext h)
  by_cases hj0 : j = 0
  · subst j
    have hc : 0 < cut.val := Nat.pos_of_ne_zero (Ne.symm hjc)
    change (cutRank cut (Fin.last n)).val + 1 = (cutRank cut 0).val
    change (if n < cut.val then n+(n+1)-cut.val else n-cut.val)+1 =
      (if 0 < cut.val then 0+(n+1)-cut.val else 0-cut.val)
    rw [ite_eq_right (by omega),ite_eq_left hc]
    omega
  · have hjv : 0 < j.val := by apply Nat.pos_of_ne_zero; intro h; exact hj0 (Fin.ext h)
    change (cutRank cut (edgeSource n j)).val + 1 = (cutRank cut j).val
    simp only [edgeSource,dite_eq_right hj0,cutRank,Fin.val_mk]
    split_ifs <;> omega

variable (p n : ℕ) [Fact p.Prime]

theorem standard_reindex_eq_path (hn : 1 ≤ n) (J : Set (Fin (n+1)))
    (cut : Fin (n+1)) (hc : cut ∉ J) :
    (standardLocalGroup p n hn J).map (reindexSL (cutOrder cut)).toMonoidHom =
      pathGroup (ZMod p) ((cutOrder cut) '' J) := by
  rw [standardLocalGroup,MonoidHom.map_closure,pathGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨_,⟨j,hj,rfl⟩,rfl⟩
    have hjc : j ≠ cut := by intro he; exact hc (he ▸ hj)
    refine ⟨cutOrder cut (edgeSource n j),cutOrder cut j,cutOrder_edgeSource cut j hjc,
      ⟨j,hj,rfl⟩,?_⟩
    exact reindexSL_E _ _ _
  · rintro ⟨i,j,h,hj,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hj
    have hkc : k ≠ cut := by intro he; exact hc (he ▸ hk)
    have hi : i = cutOrder cut (edgeSource n k) := by
      apply Fin.ext
      have := cutOrder_edgeSource cut k hkc
      omega
    refine ⟨E (edgeSource_ne n hn k) 1,⟨k,hk,rfl⟩,?_⟩
    change reindexSL (cutOrder cut) (E (edgeSource_ne n hn k) 1) = _
    subst i
    exact reindexSL_E _ _ _

lemma cutOrder_image_compl (cut : Fin (n+1)) :
    (cutOrder cut) '' ({cut}ᶜ : Set (Fin (n+1))) = ({0}ᶜ : Set (Fin (n+1))) := by
  ext j
  constructor
  · rintro ⟨i,hi,rfl⟩
    simpa only [Set.mem_compl_iff,Set.mem_singleton_iff,← cutOrder_cut cut,
      (cutOrder cut).injective.eq_iff] using hi
  · intro hj
    refine ⟨(cutOrder cut).symm j,?_,(cutOrder cut).apply_symm_apply j⟩
    intro hi
    have hh : j = 0 := by
      have he := congrArg (cutOrder cut) hi
      simpa using he
    exact hj hh

lemma pathGroup_compl_zero :
    pathGroup (ZMod p) ({(0:Fin (n+1))}ᶜ) = upperGroup (ZMod p) (n+1) := by
  rw [pathGroup_eq_pattern]
  ext g
  simp [mem_patternGroup]

theorem standard_max_reindex (hn : 1 ≤ n) (cut : Fin (n+1)) :
    (standardLocalGroup p n hn ({cut}ᶜ)).map (reindexSL (cutOrder cut)).toMonoidHom =
      upperGroup (ZMod p) (n+1) := by
  rw [standard_reindex_eq_path p n hn _ cut (by simp),cutOrder_image_compl,pathGroup_compl_zero]

def standardMaxFlagEquiv (hn : 1 ≤ n) (cut : Fin (n+1)) :
    standardLocalGroup p n hn ({cut}ᶜ) ≃*
      (stdFlag (ZMod p) (n+1)).unipotentFlagStabilizer :=
  ((standardLocalGroup p n hn ({cut}ᶜ)).equivMapOfInjective
    (reindexSL (cutOrder cut)).toMonoidHom (reindexSL (cutOrder cut)).injective).trans
      ((MulEquiv.subgroupCongr (standard_max_reindex p n hn cut)).trans upperFlagEquiv)

def localFlagEquiv (hn : 1 ≤ n) (cut : Fin (n+1)) :
    localGroup p n hn cut ≃* (stdFlag (ZMod p) (n+1)).unipotentFlagStabilizer :=
  (MulEquiv.subgroupCongr (rootGroup_compl_singleton p n hn cut)).symm.trans
    ((localStandardEquiv p n hn ({cut}ᶜ) cut (by simp)).trans
      (standardMaxFlagEquiv p n hn cut))

end

section
open Construction Elementary MatrixOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable (p n : ℕ) [Fact p.Prime]

lemma localStandardEquiv_equation (hn : 1 ≤ n) (J : Set (Fin (n+1)))
    (cut : Fin (n+1)) (hc : cut ∉ J) (g : rootGroup p n hn J) :
    Matrix.SpecialLinearGroup.mapGL (Frac p) (localStandardEquiv p n hn J cut hc g).val =
      cutConjugation p n cut g.val := by
  exact congrArg Subtype.val
    (((standardLocalGroup p n hn J).equivMapOfInjective
      (Matrix.SpecialLinearGroup.mapGL (Frac p)) Matrix.SpecialLinearGroup.mapGL_injective).apply_symm_apply _)

lemma localStandardEquiv_mem_iff (hn : 1 ≤ n) (J L : Set (Fin (n+1)))
    (cut : Fin (n+1)) (hcJ : cut ∉ J) (hcL : cut ∉ L)
    (g : rootGroup p n hn J) :
    (localStandardEquiv p n hn J cut hcJ g).val ∈ standardLocalGroup p n hn L ↔
      g.val ∈ rootGroup p n hn L := by
  have he := localStandardEquiv_equation p n hn J cut hcJ g
  have hm := rootGroup_image_eq_standard p n hn L cut hcL
  constructor
  · intro hg
    have hh : cutConjugation p n cut g.val ∈
        (standardLocalGroup p n hn L).map (Matrix.SpecialLinearGroup.mapGL (Frac p)) := by
      rw [← he]
      exact Subgroup.mem_map_of_mem _ hg
    rw [← hm] at hh
    obtain ⟨x,hx,hxg⟩ := hh
    have hxg' := cutConjugation_injective p n cut hxg
    exact hxg' ▸ hx
  · intro hg
    have hh : Matrix.SpecialLinearGroup.mapGL (Frac p)
        (localStandardEquiv p n hn J cut hcJ g).val ∈
        (rootGroup p n hn L).map (cutConjugation p n cut) := by
      rw [he]
      exact Subgroup.mem_map_of_mem _ hg
    rw [hm] at hh
    obtain ⟨x,hx,hxg⟩ := hh
    have hxg' := Matrix.SpecialLinearGroup.mapGL_injective hxg
    exact hxg' ▸ hx

lemma reindex_mem_iff (hn : 1 ≤ n) (J : Set (Fin (n+1))) (cut : Fin (n+1))
    (hc : cut ∉ J) (g : Matrix.SpecialLinearGroup (Fin (n+1)) (ZMod p)) :
    reindexSL (cutOrder cut) g ∈ pathGroup (ZMod p) ((cutOrder cut) '' J) ↔
      g ∈ standardLocalGroup p n hn J := by
  rw [← standard_reindex_eq_path p n hn J cut hc]
  constructor
  · rintro ⟨x,hx,hxg⟩
    exact ((reindexSL (cutOrder cut)).injective hxg) ▸ hx
  · intro hg
    exact Subgroup.mem_map_of_mem _ hg

lemma two_cuts_image (cut j : Fin (n+1)) :
    cutOrder cut '' (({cut}ᶜ ∩ {j}ᶜ : Set (Fin (n+1)))) =
      ({0}ᶜ ∩ {cutOrder cut j}ᶜ) := by
  rw [Set.image_inter (cutOrder cut).injective,cutOrder_image_compl]
  congr 1
  rw [Set.image_compl_eq (cutOrder cut).bijective,Set.image_singleton]

lemma pathGroup_delete_zero (k : Fin (n+1)) :
    pathGroup (ZMod p) (({0}ᶜ ∩ {k}ᶜ : Set (Fin (n+1)))) =
      upperGroup (ZMod p) (n+1) ⊓ suffixStabilizer (ZMod p) k := by
  rw [← pathGroup_inter,pathGroup_compl_zero,pathGroup_delete,inf_of_le_right inf_le_left]

lemma standardMaxFlagEquiv_value (hn : 1 ≤ n) (cut : Fin (n+1))
    (g : standardLocalGroup p n hn ({cut}ᶜ)) :
    (standardMaxFlagEquiv p n hn cut g).val =
      Matrix.SpecialLinearGroup.toLin' (reindexSL (cutOrder cut) g.val) := rfl

theorem standardMaxFlagEquiv_stabilizer (hn : 1 ≤ n) (cut j : Fin (n+1))
    (g : standardLocalGroup p n hn ({cut}ᶜ)) :
    (standardMaxFlagEquiv p n hn cut g).val ∈
      MulAction.stabilizer ((Fin (n+1) → ZMod p) ≃ₗ[ZMod p] (Fin (n+1) → ZMod p))
        ((oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j).val,by omega⟩) ↔
      g.val ∈ standardLocalGroup p n hn ({cut}ᶜ ∩ {j}ᶜ) := by
  rw [standardMaxFlagEquiv_value]
  change reindexSL (cutOrder cut) g.val ∈ suffixStabilizer (ZMod p) (cutOrder cut j) ↔ _
  have hu : reindexSL (cutOrder cut) g.val ∈ upperGroup (ZMod p) (n+1) := by
    rw [← standard_max_reindex p n hn cut]
    exact Subgroup.mem_map_of_mem _ g.property
  rw [← reindex_mem_iff p n hn _ cut (by simp),two_cuts_image,pathGroup_delete_zero]
  exact (and_iff_right hu).symm

theorem localFlagEquiv_stabilizer (hn : 1 ≤ n) (cut j : Fin (n+1))
    (g : localGroup p n hn cut) :
    (localFlagEquiv p n hn cut g).val ∈
      MulAction.stabilizer ((Fin (n+1) → ZMod p) ≃ₗ[ZMod p] (Fin (n+1) → ZMod p))
        ((oppFlag (ZMod p) (n+1)).space ⟨n+1-(cutOrder cut j).val,by omega⟩) ↔
      g.val ∈ localGroup p n hn j := by
  let gg : rootGroup p n hn ({cut}ᶜ) :=
    (MulEquiv.subgroupCongr (rootGroup_compl_singleton p n hn cut)).symm g
  change (standardMaxFlagEquiv p n hn cut
    (localStandardEquiv p n hn ({cut}ᶜ) cut (by simp) gg)).val ∈ _ ↔ _
  rw [standardMaxFlagEquiv_stabilizer,
    localStandardEquiv_mem_iff p n hn _ _ cut (by simp) (by simp)]
  change g.val ∈ rootGroup p n hn ({cut}ᶜ ∩ {j}ᶜ) ↔ _
  rw [← rootGroup_inter p n hn ({cut}ᶜ) ({j}ᶜ) ⟨cut,by simp⟩ ⟨j,by simp⟩,
    rootGroup_compl_singleton,rootGroup_compl_singleton]
  exact and_iff_right g.property

end

variable {n : ℕ}

lemma cutOrder_pos (cut j : Fin (n+1)) (hj : j ≠ cut) : 0 < (cutOrder cut j).val := by
  by_contra h
  have he : cutOrder cut j = 0 := Fin.ext (Nat.eq_zero_of_not_pos h)
  rw [← cutOrder_cut cut] at he
  exact hj ((cutOrder cut).injective he)

def localTypeIndex (cut : Fin (n+1)) (j : {j : Fin (n+1) // j ≠ cut}) : Fin n :=
  ⟨n-(cutOrder cut j.val).val,by have := cutOrder_pos cut j.val j.property; omega⟩

lemma localTypeIndex_bijective (cut : Fin (n+1)) : Function.Bijective (localTypeIndex cut) := by
  constructor
  · intro i j he
    have h := congrArg Fin.val he
    apply Subtype.ext
    apply (cutOrder cut).injective
    apply Fin.ext
    dsimp [localTypeIndex] at h
    have hi := (cutOrder cut i.val).isLt
    have hj := (cutOrder cut j.val).isLt
    omega
  · intro i
    let k : Fin (n+1) := ⟨n-i.val,by omega⟩
    have hk : k ≠ 0 := by intro he; have h := congrArg Fin.val he; dsimp [k] at h; omega
    let j : Fin (n+1) := (cutOrder cut).symm k
    have hj : j ≠ cut := by
      intro he
      have hh := congrArg (cutOrder cut) he
      have hkj : cutOrder cut j = k := (cutOrder cut).apply_symm_apply k
      rw [hkj,cutOrder_cut] at hh
      exact hk hh
    refine ⟨⟨j,hj⟩,?_⟩
    apply Fin.ext
    change n-(cutOrder cut ((cutOrder cut).symm k)).val = i.val
    rw [(cutOrder cut).apply_symm_apply]
    dsimp [k]
    omega

def localTypeEquiv (cut : Fin (n+1)) : {j : Fin (n+1) // j ≠ cut} ≃ Fin n :=
  Equiv.ofBijective (localTypeIndex cut) (localTypeIndex_bijective cut)

lemma localTypeEquiv_rank (cut : Fin (n+1)) (j : {j : Fin (n+1) // j ≠ cut}) :
    (localTypeEquiv cut j).val+1 = n+1-(cutOrder cut j.val).val := by
  change n-(cutOrder cut j.val).val+1 = _
  have h := (cutOrder cut j.val).isLt
  omega

end CoboundaryExpanders.Patterns

namespace CoboundaryExpanders.MatrixOpposition

section
open Elementary
open scoped Matrix BigOperators
variable {K : Type} [Field K] {a b : ℕ}

def blockMatrix (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    Matrix (Fin (a+b)) (Fin (a+b)) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

@[simp] lemma blockMatrix_ll (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i j : Fin a) : blockMatrix A B (i.castAdd b) (j.castAdd b) = A i j := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  simp
@[simp] lemma blockMatrix_rr (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i j : Fin b) : blockMatrix A B (i.natAdd a) (j.natAdd a) = B i j := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  simp
@[simp] lemma blockMatrix_lr (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i : Fin a) (j : Fin b) : blockMatrix A B (i.castAdd b) (j.natAdd a) = 0 := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr j))) = _
  simp
@[simp] lemma blockMatrix_rl (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K)
    (i : Fin b) (j : Fin a) : blockMatrix A B (i.natAdd a) (j.castAdd b) = 0 := by
  change Matrix.fromBlocks A 0 0 B (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i)))
    (finSumFinEquiv.symm (finSumFinEquiv (Sum.inl j))) = _
  simp

lemma blockMatrix_det (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) :
    (blockMatrix A B).det = A.det * B.det := by
  rw [blockMatrix,Matrix.det_reindex_self,Matrix.det_fromBlocks_zero₂₁]

lemma blockMatrix_mul (A A' : Matrix (Fin a) (Fin a) K) (B B' : Matrix (Fin b) (Fin b) K) :
    blockMatrix (A*A') (B*B') = blockMatrix A B * blockMatrix A' B' := by
  unfold blockMatrix
  change (Matrix.reindexRingEquiv K finSumFinEquiv) _ =
    (Matrix.reindexRingEquiv K finSumFinEquiv) _ * (Matrix.reindexRingEquiv K finSumFinEquiv) _
  rw [← map_mul]
  congr 1
  simp [Matrix.fromBlocks_multiply]

lemma blockMatrix_one : blockMatrix (1 : Matrix (Fin a) (Fin a) K)
    (1 : Matrix (Fin b) (Fin b) K) = 1 := by
  unfold blockMatrix
  rw [Matrix.fromBlocks_one]
  exact (Matrix.reindexRingEquiv K finSumFinEquiv).map_one

lemma blockMatrix_upper (g : upperGroup K a) (h : upperGroup K b) :
    ∀ i j : Fin (a+b), j ≤ i → blockMatrix g.val.val h.val.val i j = (1 : Matrix _ _ K) i j := by
  have hg := (mem_upperGroup _).mp g.property
  have hh := (mem_upperGroup _).mp h.property
  intro i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · intro hji
    simpa [Matrix.one_apply] using hg _ _ (by simpa only [Fin.le_def,Fin.val_castAdd,Fin.val_natAdd,Nat.add_le_add_iff_left] using hji)
  · intro hji
    have hv := Fin.le_iff_val_le_val.mp hji
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · intro _
    rw [blockMatrix_rl,Matrix.one_apply,ite_eq_right]
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · intro hji
    simpa [Matrix.one_apply] using hh _ _ (by simpa only [Fin.le_def,Fin.val_castAdd,Fin.val_natAdd,Nat.add_le_add_iff_left] using hji)

def blockUpper : upperGroup K a × upperGroup K b →* upperGroup K (a+b) where
  toFun gh := ⟨⟨blockMatrix gh.1.val.val gh.2.val.val,by
    rw [blockMatrix_det,gh.1.val.property,gh.2.val.property,mul_one]⟩,
    (mem_upperGroup _).mpr (blockMatrix_upper gh.1 gh.2)⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact blockMatrix_one
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; exact blockMatrix_mul _ _ _ _

lemma blockUpper_injective : Function.Injective (blockUpper (K:=K) (a:=a) (b:=b)) := by
  intro g h he
  have hh := congrArg (fun x : upperGroup K (a+b) => x.val.val) he
  change blockMatrix g.1.val.val g.2.val.val = blockMatrix h.1.val.val h.2.val.val at hh
  apply Prod.ext
  · apply Subtype.ext; apply Subtype.ext
    ext i j
    simpa only [blockMatrix_ll] using congrArg (fun M => M (i.castAdd b) (j.castAdd b)) hh
  · apply Subtype.ext; apply Subtype.ext
    ext i j
    simpa only [blockMatrix_rr] using congrArg (fun M => M (i.natAdd a) (j.natAdd a)) hh

lemma upper_submatrix {c : ℕ} (g : upperGroup K (a+b)) (e : Fin c ↪o Fin (a+b)) :
    ∃ h : upperGroup K c, h.val.val = g.val.val.submatrix e e := by
  let M := g.val.val.submatrix e e
  have hg := (mem_upperGroup _).mp g.property
  have hM (i j : Fin c) (hji : j ≤ i) : M i j = (1 : Matrix _ _ K) i j := by
    simpa [M,Matrix.submatrix_apply,Matrix.one_apply,e.injective.eq_iff] using hg (e i) (e j) (e.monotone hji)
  have ht : M.IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    rw [hM i j hji.le,Matrix.one_apply,ite_eq_right hji.ne.symm]
  have hd : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    apply Finset.prod_eq_one
    intro i _
    rw [hM i i le_rfl,Matrix.one_apply,ite_eq_left rfl]
  exact ⟨⟨⟨M,hd⟩,(mem_upperGroup _).mpr hM⟩,rfl⟩

theorem range_blockUpper (g : upperGroup K (a+b)) :
    g ∈ (blockUpper (K:=K) (a:=a) (b:=b)).range ↔
      ∀ i j : Fin (a+b), i.val < a → a ≤ j.val → g.val i j = 0 := by
  constructor
  · rintro ⟨⟨g,h⟩,rfl⟩ i j hi hj
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · simp only [Fin.val_castAdd] at hj; omega
    · exact blockMatrix_lr _ _ _ _
    · simp only [Fin.val_natAdd] at hi; omega
    · simp only [Fin.val_natAdd] at hi; omega
  · intro hx
    let el : Fin a ↪o Fin (a+b) := ⟨⟨Fin.castAdd b,Fin.castAdd_injective a b⟩,by intro i j; rfl⟩
    let er : Fin b ↪o Fin (a+b) := ⟨⟨Fin.natAdd a,Fin.natAdd_injective b a⟩,by intro i j; simp⟩
    obtain ⟨gl,hgl⟩ := upper_submatrix g el
    obtain ⟨gr,hgr⟩ := upper_submatrix g er
    refine ⟨(gl,gr),?_⟩
    apply Subtype.ext; apply Subtype.ext
    ext i j
    change blockMatrix gl.val.val gr.val.val i j = g.val.val i j
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [blockMatrix_ll,hgl]; rfl
    · rw [blockMatrix_lr,hx _ _ (by simp) (by simp)]
    · rw [blockMatrix_rl,(mem_upperGroup _).mp g.property _ _ (by
        apply Fin.le_iff_val_le_val.mpr; simp only [Fin.val_natAdd,Fin.val_castAdd]; omega)]
      rw [Matrix.one_apply,ite_eq_right]
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    · rw [blockMatrix_rr,hgr]; rfl

def blockRangeEquiv : (upperGroup K a × upperGroup K b) ≃* (blockUpper (K:=K) (a:=a) (b:=b)).range :=
  MonoidHom.ofInjective blockUpper_injective

end

open Elementary SphericalOpposition SphericalOpposition.CompleteFlag
open scoped Matrix Pointwise
variable {K : Type} [Field K] {a b N : ℕ}

def suffixGroup (K : Type) [Field K] (N : ℕ) (cut : Fin (N+1)) : Subgroup (upperGroup K N) :=
  (MulAction.stabilizer ( (Fin N → K) ≃ₗ[K] (Fin N → K))
    ((oppFlag K N).space ⟨N-cut.val,by omega⟩)).comap
      (Matrix.SpecialLinearGroup.toLin'.comp (upperGroup K N).subtype)

@[simp] lemma mem_suffixGroup (g : upperGroup K N) (cut : Fin (N+1)) :
    g ∈ suffixGroup K N cut ↔
      ∀ i j : Fin N, i.val < cut.val → cut.val ≤ j.val → g.val i j = 0 := by
  change Matrix.SpecialLinearGroup.toLin' g.val •
    ((oppFlag K N).space ⟨N-cut.val,by omega⟩) = _ ↔ _
  exact preserves_suffix_iff g cut

lemma range_blockUpper_eq_suffixGroup :
    (blockUpper (K:=K) (a:=a) (b:=b)).range = suffixGroup K (a+b) ⟨a,by omega⟩ := by
  ext g
  rw [range_blockUpper,mem_suffixGroup]

def blockSuffixEquiv : (upperGroup K a × upperGroup K b) ≃*
    suffixGroup K (a+b) ⟨a,by omega⟩ :=
  blockRangeEquiv.trans (MulEquiv.subgroupCongr range_blockUpper_eq_suffixGroup)

@[simp] lemma blockSuffixEquiv_val (g : upperGroup K a × upperGroup K b) :
    (blockSuffixEquiv g).val = blockUpper g := rfl

lemma blockUpper_suffix_left (g : upperGroup K a × upperGroup K b) (cut : Fin (a+1)) :
    blockUpper g ∈ suffixGroup K (a+b) ⟨cut.val,by omega⟩ ↔
      g.1 ∈ suffixGroup K a cut := by
  simp only [mem_suffixGroup]
  constructor
  · intro h i j hi hj
    have he := h (i.castAdd b) (j.castAdd b) hi hj
    change blockMatrix g.1.val.val g.2.val.val (i.castAdd b) (j.castAdd b) = 0 at he
    simpa only [blockMatrix_ll] using he
  · intro h i j hi hj
    change blockMatrix g.1.val.val g.2.val.val i j = 0
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [blockMatrix_ll]
      exact h _ _ hi hj
    · exact blockMatrix_lr _ _ _ _
    · exact blockMatrix_rl _ _ _ _
    · simp only [Fin.val_natAdd] at hi
      omega

lemma blockUpper_suffix_right (g : upperGroup K a × upperGroup K b) (cut : Fin (b+1)) :
    blockUpper g ∈ suffixGroup K (a+b) ⟨a+cut.val,by omega⟩ ↔
      g.2 ∈ suffixGroup K b cut := by
  simp only [mem_suffixGroup]
  constructor
  · intro h i j hi hj
    have he := h (i.natAdd a) (j.natAdd a) (by simpa using hi) (by simpa using hj)
    change blockMatrix g.1.val.val g.2.val.val (i.natAdd a) (j.natAdd a) = 0 at he
    simpa only [blockMatrix_rr] using he
  · intro h i j hi hj
    change blockMatrix g.1.val.val g.2.val.val i j = 0
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · simp only [Fin.val_castAdd] at hj
      omega
    · exact blockMatrix_lr _ _ _ _
    · exact blockMatrix_rl _ _ _ _
    · rw [blockMatrix_rr]
      exact h _ _ (by simpa using hi) (by simpa using hj)

abbrev Cut (N : ℕ) := {c : ℕ // 0 < c ∧ c < N}
def cutGroups (K : Type) [Field K] (N : ℕ) (c : Cut N) : Subgroup (upperGroup K N) :=
  suffixGroup K N ⟨c.val,by have h := c.property; omega⟩

def cutSplitEquiv : (Cut a ⊕ Cut b) ≃ {c : Cut (a+b) // c.val ≠ a} where
  toFun := fun c => match c with
    | Sum.inl c => ⟨⟨c.val,by have h := c.property; omega⟩,by change c.val ≠ a; have h := c.property; omega⟩
    | Sum.inr c => ⟨⟨a+c.val,by have h := c.property; omega⟩,by change a+c.val ≠ a; have h := c.property; omega⟩
  invFun := fun c => if h : c.val.val < a then
    Sum.inl ⟨c.val.val, c.val.property.1,h⟩
    else Sum.inr ⟨c.val.val-a,by have h' := c.val.property; have hn := c.property; omega⟩
  left_inv := by
    intro c
    cases c with
    | inl c =>
      simp only [c.property.2,dite_eq_left]
    | inr c =>
      dsimp only
      rw [dite_eq_right (by omega : ¬ a+c.val < a)]
      congr 1
      apply Subtype.ext
      dsimp
      omega
  right_inv := by
    intro c
    dsimp only
    split_ifs with h
    · rfl
    · apply Subtype.ext; apply Subtype.ext
      have h' := c.val.property
      have hn := c.property
      dsimp
      omega

lemma blockSuffix_system (g : upperGroup K a × upperGroup K b)
    (c : Cut a ⊕ Cut b) :
    blockSuffixEquiv g ∈ (cutGroups K (a+b) (cutSplitEquiv c).val).comap
      (suffixGroup K (a+b) ⟨a,Nat.lt_succ_of_le (Nat.le_add_right a b)⟩).subtype ↔
    match c with
    | Sum.inl c => g.1 ∈ cutGroups K a c
    | Sum.inr c => g.2 ∈ cutGroups K b c := by
  cases c with
  | inl c => exact blockUpper_suffix_left g ⟨c.val,by have h := c.property; omega⟩
  | inr c => exact blockUpper_suffix_right g ⟨c.val,by have h := c.property; omega⟩

end CoboundaryExpanders.MatrixOpposition

end

end OAI
