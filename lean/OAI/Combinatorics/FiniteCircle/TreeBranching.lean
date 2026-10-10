import OAI.Combinatorics.FiniteCircle.MaskBranching

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

@[reducible] def TreeLeaf (J : ℕ → Type) : ℕ → Type
  | 0 => PUnit
  | l+1 => J (l+1) × TreeLeaf J l

instance treeLeafFintype (J : ℕ → Type) [∀ l, Fintype (J l)] (l : ℕ) :
    Fintype (TreeLeaf J l) := by
  induction l with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ l ih => exact @instFintypeProd _ _ inferInstance ih

noncomputable instance treeLeafDecidableEq (J : ℕ → Type) (l : ℕ) :
    DecidableEq (TreeLeaf J l) := Classical.decEq _

noncomputable def treeCheap (J Z : ℕ → Type) [∀ l, AddCommGroup (Z l)] {M : ℕ}
    (σ : ∀ l, Z l →+ (J l → ZMod M)) : (l : ℕ) → AddSubgroup (TreeLeaf J l → ZMod M)
  | 0 => ⊥
  | l+1 => {
    carrier := {v | ∃ c : J (l+1) → TreeLeaf J l → ZMod M,
      (∀ j, c j ∈ treeCheap J Z σ l) ∧ ∃ z : Z (l+1), ∀ j i, v (j,i) = c j i + σ (l+1) z j}
    zero_mem' := by
      refine ⟨0, fun j => (treeCheap J Z σ l).zero_mem, 0, ?_⟩
      intro j i
      change (0:ZMod M) = 0 + σ (l+1) 0 j
      simp
    add_mem' := by
      rintro v w ⟨c,hc,z,hz⟩ ⟨d,hd,u,hu⟩
      refine ⟨c+d, fun j => (treeCheap J Z σ l).add_mem (hc j) (hd j), z+u, ?_⟩
      intro j i
      change v (j,i)+w (j,i) = c j i+d j i+σ (l+1) (z+u) j
      simp only [hz, hu, map_add, Pi.add_apply]
      abel
    neg_mem' := by
      rintro v ⟨c,hc,z,hz⟩
      refine ⟨-c, fun j => (treeCheap J Z σ l).neg_mem (hc j), -z, ?_⟩
      intro j i
      change -v (j,i) = -c j i+σ (l+1) (-z) j
      simp only [hz, map_neg, Pi.neg_apply]
      abel }

 theorem treeCheap_generator (J Z : ℕ → Type) [∀ l, AddCommGroup (Z l)] {M : ℕ}
    (σ : ∀ l, Z l →+ (J l → ZMod M)) (l : ℕ) (z : Z (l+1)) :
    (fun i : TreeLeaf J (l+1) => σ (l+1) z i.1) ∈ treeCheap J Z σ (l+1) := by
  exact ⟨0, fun _ => (treeCheap J Z σ l).zero_mem, z, fun _ _ => (zero_add _).symm⟩

 theorem treeCheap_child (J Z : ℕ → Type) [∀ l, AddCommGroup (Z l)] {M : ℕ}
    (σ : ∀ l, Z l →+ (J l → ZMod M)) (l : ℕ) [DecidableEq (J (l+1))] (j : J (l+1))
    (c : TreeLeaf J l → ZMod M) (hc : c ∈ treeCheap J Z σ l) :
    (fun i : TreeLeaf J (l+1) => if i.1 = j then c i.2 else 0) ∈ treeCheap J Z σ (l+1) := by
  classical
  refine ⟨fun k => if k = j then c else 0, ?_, 0, ?_⟩
  · intro k
    dsimp only
    split_ifs
    · exact hc
    · exact (treeCheap J Z σ l).zero_mem
  · intro k i
    simp only [map_zero, Pi.zero_apply, add_zero]
    split_ifs <;> rfl

noncomputable def treeFrequency (J : ℕ → Type) :
    (l : ℕ) → (TreeLeaf J l → ℤ) → FrequencyTree J l
  | 0, ξ => ξ PUnit.unit
  | l+1, ξ => fun j => treeFrequency J l (fun i => ξ (j,i))

 theorem treeFrequency_sum (J : ℕ → Type) [∀ l, Fintype (J l)] (l : ℕ)
    (ξ : TreeLeaf J l → ℤ) : frequencySum J l (treeFrequency J l ξ) = ∑ i, ξ i := by
  induction l with
  | zero =>
    change ξ PUnit.unit = ∑ i : PUnit, ξ i
    exact (Fintype.sum_unique (fun i : PUnit => ξ i)).symm
  | succ l ih =>
    change (∑ j, frequencySum J l (treeFrequency J l (fun i => ξ (j,i)))) =
      ∑ i : J (l+1) × TreeLeaf J l, ξ i
    simp only [ih]
    exact (Fintype.sum_prod_type (fun i : J (l+1) × TreeLeaf J l => ξ i)).symm

 theorem treeFrequency_mass (J : ℕ → Type) [∀ l, Fintype (J l)] (l : ℕ)
    (ξ : TreeLeaf J l → ℤ) : frequencyMass J l (treeFrequency J l ξ) = ∑ i, (ξ i).natAbs := by
  induction l with
  | zero =>
    change (ξ PUnit.unit).natAbs = ∑ i : PUnit, (ξ i).natAbs
    exact (Fintype.sum_unique (fun i : PUnit => (ξ i).natAbs)).symm
  | succ l ih =>
    change (∑ j, frequencyMass J l (treeFrequency J l (fun i => ξ (j,i)))) =
      ∑ i : J (l+1) × TreeLeaf J l, (ξ i).natAbs
    simp only [ih]
    exact (Fintype.sum_prod_type (fun i : J (l+1) × TreeLeaf J l => (ξ i).natAbs)).symm

noncomputable def flatMaskState (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ) :
    (l : ℕ) → (TreeLeaf (MaskChildren h p) l → ZMod M) → MaskState h p M l
  | 0, v => v PUnit.unit
  | l+1, v => fun j => flatMaskState h p M l (fun i => v (j,i))

 theorem flatMaskState_shift (h : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (v : TreeLeaf (MaskChildren h p) l → ZMod M) (θ : ZMod M) :
    flatMaskState h p M l (fun i => v i+θ) = shiftMaskState h p M l (flatMaskState h p M l v) θ := by
  induction l with
  | zero => rfl
  | succ l ih =>
    funext j
    exact ih (fun i => v (j,i))

noncomputable def flatExcludedState (m M : ℕ) :
    (l : ℕ) → (TreeLeaf (fun _ => Fin m) l → ZMod M) → ExcludedState m M l
  | 0, v => v PUnit.unit
  | l+1, v => fun j => flatExcludedState m M l (fun i => v (j,i))

 theorem flatExcludedState_shift (m M l : ℕ)
    (v : TreeLeaf (fun _ => Fin m) l → ZMod M) (θ : ZMod M) :
    flatExcludedState m M l (fun i => v i+θ) = shiftExcludedState m M l (flatExcludedState m M l v) θ := by
  induction l with
  | zero => rfl
  | succ l ih =>
    funext j
    exact ih (fun i => v (j,i))

 theorem char_sum {G : Type*} [AddCommMonoid G] {I : Type*} (χ : AddChar G ℂ)
    (s : Finset I) (f : I → G) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi,
      AddChar.map_add_eq_mul, ih]

 theorem character_dot {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (v : I → ZMod M) :
    χ v = AddChar.zmodAddEquiv (∑ i, coordinateFrequency χ i * v i) 1 := by
  classical
  have hv : v = ∑ i, Pi.single i (v i) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [char_sum]
  rw [map_sum, AddChar.sum_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [character_single, zmod_character_mul]

 theorem character_dot_eq_one {I : Type*} [Fintype I] [DecidableEq I] {M : ℕ} [NeZero M]
    (χ : AddChar (I → ZMod M) ℂ) (v : I → ZMod M) :
    χ v = 1 ↔ ∑ i, coordinateFrequency χ i * v i = 0 := by
  rw [character_dot, zmod_character_eq_one, mul_one]

 theorem dot_restrict_child (J Z : ℕ → Type) [∀ l, Fintype (J l)]
    [∀ l, AddCommGroup (Z l)] {M : ℕ} (σ : ∀ l, Z l →+ (J l → ZMod M))
    (l : ℕ) (ξ : TreeLeaf J (l+1) → ℤ)
    (ha : ∀ c ∈ treeCheap J Z σ (l+1), ∑ i, (ξ i : ZMod M)*c i = 0)
    (j : J (l+1)) (c : TreeLeaf J l → ZMod M) (hc : c ∈ treeCheap J Z σ l) :
    ∑ i, (ξ (j,i):ZMod M)*c i = 0 := by
  classical
  have ht := ha _ (treeCheap_child J Z σ l j c hc)
  change (∑ k : J (l+1) × TreeLeaf J l, (ξ k : ZMod M)*(if k.1=j then c k.2 else 0)) = 0 at ht
  simpa only [Fintype.sum_prod_type, mul_ite, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using ht

@[simp] theorem subcircle_intCast {M p : ℕ} (hp : p ∣ M) (a : ℤ) :
    subcircle hp (a : ZMod p) = (M/p : ZMod M)*(a : ZMod M) := by
  have h := map_zsmul (subcircle hp) a (1 : ZMod p)
  have hc : subcircle hp 1 = (M/p : ZMod M) := by
    simpa only [Nat.cast_one, mul_one] using subcircle_natCast hp 1
  rw [zsmul_eq_mul, mul_one, hc, zsmul_eq_mul] at h
  simpa only [mul_comm] using h

 theorem mask_generator_apply {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p l k ∣ M) (k : Fin h) (j : MaskTag h p l) :
    maskPhaseHom h p M l hd (Pi.single k 1) j =
      subcircle (hd k) 1 + if j.1 = k then j.2.val • subcircle (hd k) 1 else 0 := by
  classical
  have hs : (∑ a : Fin h, subcircle (hd a) ((Pi.single k 1 : MaskResidues h p l) a)) =
      subcircle (hd k) 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro a _ ha
      simp [Pi.single_eq_of_ne ha]
    · simp
  change (∑ a : Fin h, subcircle (hd a) ((Pi.single k 1 : MaskResidues h p l) a)) +
    j.2.val • subcircle (hd j.1) ((Pi.single k 1 : MaskResidues h p l) j.1) = _
  rw [hs]
  congr 1
  by_cases he : j.1 = k
  · subst k
    simp
  · simp [he]

noncomputable def maskCheap (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (l : ℕ) :
    AddSubgroup (TreeLeaf (MaskChildren h p) l → ZMod M) :=
  treeCheap (MaskChildren h p) (MaskResidues h p) (fun l => maskPhaseHom h p M l (hd l)) l

 theorem mask_dot_generator {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p (l+1) k ∣ M) (k : Fin h)
    (ξ : TreeLeaf (MaskChildren h p) (l+1) → ℤ) :
    (∑ i, (ξ i:ZMod M)*maskPhaseHom h p M (l+1) hd (Pi.single k 1) i.1) =
      subcircle (hd k) (((∑ i, ξ i) + ∑ b : Fin (p (l+1) k), (b.val:ℤ)*
        ∑ i : TreeLeaf (MaskChildren h p) l, ξ (⟨k,b⟩,i) : ℤ) : ZMod (p (l+1) k)) := by
  classical
  rw [subcircle_intCast]
  let q : ZMod M := subcircle (hd k) 1
  have hq : q = (M/p (l+1) k : ZMod M) := by
    simpa only [Nat.cast_one, mul_one] using subcircle_natCast (hd k) 1
  simp_rw [mask_generator_apply]
  change (∑ i : MaskTag h p (l+1) × TreeLeaf (MaskChildren h p) l,
      (ξ i:ZMod M)*(q+if i.1.1=k then i.1.2.val • q else 0)) = _
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul]
  have hs : (∑ i : MaskTag h p (l+1) × TreeLeaf (MaskChildren h p) l,
      (ξ i:ZMod M)*(if i.1.1=k then i.1.2.val • q else 0)) =
      (∑ b : Fin (p (l+1) k), (b.val:ZMod M)*∑ i : TreeLeaf (MaskChildren h p) l,
        (ξ (⟨k,b⟩,i):ZMod M))*q := by
    rw [Fintype.sum_prod_type, Fintype.sum_sigma]
    simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ k)]
    simp_rw [nsmul_eq_mul, ← Finset.sum_mul]
    conv_rhs => rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hs, hq]
  push_cast
  ring

theorem mask_annihilator_congruences {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) (ξ : TreeLeaf (MaskChildren h p) l → ℤ)
    (ha : ∀ c ∈ maskCheap h p M hd l, ∑ i, (ξ i:ZMod M)*c i = 0) :
    MaskCongruences h p l (treeFrequency (MaskChildren h p) l ξ) := by
  classical
  induction l with
  | zero => trivial
  | succ l ih =>
    change (∀ k : Fin h, (p (l+1) k:ℤ) ∣ _ ) ∧ _
    constructor
    · intro k
      let : NeZero (p (l+1) k) := ⟨(hn _ k).ne'⟩
      have hg := treeCheap_generator (MaskChildren h p) (MaskResidues h p)
        (fun l => maskPhaseHom h p M l (hd _)) l (Pi.single k 1)
      have hz := ha _ hg
      rw [mask_dot_generator (hd (l+1)) k ξ] at hz
      have he : (((∑ i, ξ i) + ∑ b : Fin (p (l+1) k), (b.val:ℤ)*
          ∑ i : TreeLeaf (MaskChildren h p) l, ξ (⟨k,b⟩,i) : ℤ) : ZMod (p (l+1) k)) = 0 :=
        subcircle_injective (hd _ k) (hz.trans (map_zero _).symm)
      have he' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
      simp only [treeFrequency, frequencySum, treeFrequency_sum]
      convert he' using 1
      congr 1
      exact (Fintype.sum_prod_type (fun i : MaskChildren h p (l+1) × TreeLeaf (MaskChildren h p) l => ξ i)).symm
    · intro j
      apply ih
      intro c hc
      exact dot_restrict_child (MaskChildren h p) (MaskResidues h p)
        (fun l => maskPhaseHom h p M l (hd _)) l ξ ha j c hc

theorem mask_character_branching {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hh : 2 ≤ h) (hd : ∀ l (k : Fin h), p l k ∣ M)
    (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (χ : AddChar (TreeLeaf (MaskChildren h p) h → ZMod M) ℂ)
    (ha : χ.compAddMonoidHom (maskCheap h p M hd h).subtype = 0)
    (θ : ZMod M) (hw : χ (fun _ => θ) ≠ 1) :
    ((h:ℝ)/2)^h ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ) := by
  classical
  let ξ := fun i => (coordinateFrequency χ i).valMinAbs
  have hc := mask_annihilator_congruences hd hn h ξ (fun c hc => by
    have hv := congrArg (fun ψ : AddChar (maskCheap h p M hd h) ℂ => ψ ⟨c,hc⟩) ha
    have he : χ c = 1 := hv
    have hz := (character_dot_eq_one χ c).mp he
    simpa only [ξ, ZMod.coe_valMinAbs] using hz)
  have hroot : frequencySum (MaskChildren h p) h (treeFrequency (MaskChildren h p) h ξ) ≠ 0 := by
    rw [treeFrequency_sum]
    intro he
    apply hw
    rw [character_dot_eq_one, ← Finset.sum_mul]
    have hz : ∑ i, coordinateFrequency χ i = 0 := by
      have ht := congrArg (fun n : ℤ => (n : ZMod M)) he
      simpa only [Int.cast_sum, ξ, ZMod.coe_valMinAbs, Int.cast_zero] using ht
    rw [hz, zero_mul]
  have hb := mask_frequency_branching hh p hp hinj hlarge _ hc hroot
  rw [treeFrequency_mass] at hb
  simp only [Nat.cast_sum, ξ] at hb
  convert hb using 1
  congr 1

noncomputable def ExcludedCongruences (h : ℕ) (p : ℕ → ℕ → ℕ) :
    (l : ℕ) → FrequencyTree (fun _ => Fin h) l → Prop
  | 0, _ => True
  | l+1, t =>
    (∀ k : Fin h, (p (l+1) k:ℤ) ∣ frequencySum (fun _ => Fin h) (l+1) t -
      frequencySum (fun _ => Fin h) l (t k)) ∧
    ∀ j, ExcludedCongruences h p l (t j)

 theorem many_excluded_children {h : ℕ} (hh : 2 ≤ h) (p : Fin h → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (hlarge : ∀ i, h ^ 3 ≤ p i) (f : Fin h → ℤ)
    {β : ℤ} (hβ : β ≠ 0) (hsmall : β.natAbs < h ^ h)
    (hc : ∀ k, (p k : ℤ) ∣ β - f k) :
    h ≤ 2 * (Finset.univ.filter fun j => f j ≠ 0).card := by
  classical
  let s := Finset.univ.filter fun j => f j ≠ 0
  let t := Finset.univ.filter fun k => ¬ (p k : ℤ) ∣ β
  let q := Finset.univ.filter fun k => (p k : ℤ) ∣ β
  have hq : 3 * q.card < h := few_large_prime_divisors hh p hp hinj hlarge hβ hsmall
  have ht : t ⊆ s := by
    intro k hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ k, ?_⟩
    intro he
    have hc' := hc k
    rw [he, sub_zero] at hc'
    exact (Finset.mem_filter.mp hk).2 hc'
  have hcard : t.card ≤ s.card := Finset.card_le_card ht
  have hcount : q.card + t.card = h := by
    simpa [q, t] using (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin h))) (fun k => (p k : ℤ) ∣ β))
  change h ≤ 2 * s.card
  omega

theorem excluded_branching_induction {h : ℕ} (hh : 2 ≤ h) (p : ℕ → ℕ → ℕ)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (l : ℕ) (hl : l ≤ h) (t : FrequencyTree (fun _ => Fin h) l)
    (hc : ExcludedCongruences h p l t)
    (hroot : frequencySum (fun _ => Fin h) l t ≠ 0)
    (hsmall : frequencyMass (fun _ => Fin h) l t < h ^ h) :
    ((h : ℝ) / 2) ^ l ≤ (frequencyMass (fun _ => Fin h) l t : ℝ) := by
  classical
  induction l with
  | zero =>
    have : 1 ≤ frequencyMass (fun _ => Fin h) 0 t :=
      (Int.natAbs_pos.mpr hroot).trans_le (frequencySum_natAbs_le_mass _ _ _)
    simpa using (show (1 : ℝ) ≤ frequencyMass (fun _ => Fin h) 0 t by exact_mod_cast this)
  | succ l ih =>
    let f : Fin h → ℤ := fun j => frequencySum (fun _ => Fin h) l (t j)
    let s := Finset.univ.filter fun j => f j ≠ 0
    have hsumSmall : (frequencySum (fun _ => Fin h) (l + 1) t).natAbs < h ^ h :=
      (frequencySum_natAbs_le_mass _ _ _).trans_lt hsmall
    have hcard : h ≤ 2 * s.card :=
      many_excluded_children hh (fun k => p (l + 1) k)
        (fun k => hp _ k (by omega) hl) (hinj _ (by omega) hl)
        (fun k => hlarge _ k (by omega) hl) f hroot hsumSmall hc.1
    have hchild : ∀ j, frequencyMass (fun _ => Fin h) l (t j) < h ^ h := by
      intro j
      apply lt_of_le_of_lt _ hsmall
      change frequencyMass (fun _ => Fin h) l (t j) ≤ ∑ j, frequencyMass (fun _ => Fin h) l (t j)
      exact Finset.single_le_sum (f := fun j => frequencyMass (fun _ => Fin h) l (t j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hm : ∀ j ∈ s, ((h : ℝ) / 2) ^ l ≤ frequencyMass (fun _ => Fin h) l (t j) := by
      intro j hj
      exact ih (by omega) (t j) (hc.2 j) (Finset.mem_filter.mp hj).2 (hchild j)
    have hcardR : (h : ℝ) / 2 ≤ s.card := by
      have : (h : ℝ) ≤ 2 * (s.card : ℝ) := by exact_mod_cast hcard
      linarith
    calc
      ((h : ℝ) / 2) ^ (l + 1) = ((h : ℝ) / 2) * ((h : ℝ) / 2) ^ l := by ring
      _ ≤ s.card * ((h : ℝ) / 2) ^ l := mul_le_mul_of_nonneg_right hcardR (by positivity)
      _ = ∑ j ∈ s, ((h : ℝ) / 2) ^ l := by simp
      _ ≤ ∑ j ∈ s, (frequencyMass (fun _ => Fin h) l (t j) : ℝ) := Finset.sum_le_sum hm
      _ ≤ ∑ j, (frequencyMass (fun _ => Fin h) l (t j) : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
      _ = (frequencyMass (fun _ => Fin h) (l + 1) t : ℝ) := by
        simp only [frequencyMass, Nat.cast_sum]

theorem excluded_frequency_branching {h : ℕ} (hh : 2 ≤ h) (p : ℕ → ℕ → ℕ)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (t : FrequencyTree (fun _ => Fin h) h) (hc : ExcludedCongruences h p h t)
    (hroot : frequencySum (fun _ => Fin h) h t ≠ 0) :
    ((h : ℝ) / 2) ^ h ≤ (frequencyMass (fun _ => Fin h) h t : ℝ) := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hcap : ((h : ℝ) / 2) ^ h ≤ (h : ℝ) ^ h := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    linarith
  have hsmall : frequencyMass (fun _ => Fin h) h t < h ^ h := by
    exact_mod_cast hlt.trans_le hcap
  exact (not_lt_of_ge (excluded_branching_induction hh p hp hinj hlarge h le_rfl t hc hroot hsmall)) hlt

 theorem excluded_generator_apply {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p l k ∣ M) (k j : Fin h) :
    excludedPhaseHom h p M l hd (Pi.single k 1) j =
      subcircle (hd k) 1 - if j = k then subcircle (hd k) 1 else 0 := by
  classical
  rw [excludedPhaseHom_apply]
  have hs : (∑ a : Fin h, subcircle (hd a) ((Pi.single k 1 : MaskResidues h p l) a)) =
      subcircle (hd k) 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro a _ ha
      simp [Pi.single_eq_of_ne ha]
    · simp
  rw [hs]
  congr 1
  by_cases he : j = k
  · subst j
    simp
  · simp [he]

noncomputable def excludedCheap (h : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (l : ℕ) :
    AddSubgroup (TreeLeaf (fun _ => Fin h) l → ZMod M) :=
  treeCheap (fun _ => Fin h) (MaskResidues h p) (fun l => excludedPhaseHom h p M l (hd l)) l

 theorem excluded_dot_generator {h M l : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ k : Fin h, p (l+1) k ∣ M) (k : Fin h)
    (ξ : TreeLeaf (fun _ => Fin h) (l+1) → ℤ) :
    (∑ i, (ξ i:ZMod M)*excludedPhaseHom h p M (l+1) hd (Pi.single k 1) i.1) =
      subcircle (hd k) (((∑ i, ξ i) -
        ∑ i : TreeLeaf (fun _ => Fin h) l, ξ (k,i) : ℤ) : ZMod (p (l+1) k)) := by
  classical
  rw [subcircle_intCast]
  let q : ZMod M := subcircle (hd k) 1
  have hq : q = (M/p (l+1) k : ZMod M) := by
    simpa only [Nat.cast_one, mul_one] using subcircle_natCast (hd k) 1
  simp_rw [excluded_generator_apply]
  change (∑ i : Fin h × TreeLeaf (fun _ => Fin h) l,
      (ξ i:ZMod M)*(q-if i.1=k then q else 0)) = _
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  have hs : (∑ i : Fin h × TreeLeaf (fun _ => Fin h) l,
      (ξ i:ZMod M)*(if i.1=k then q else 0)) =
      (∑ i : TreeLeaf (fun _ => Fin h) l, (ξ (k,i):ZMod M))*q := by
    simp only [Fintype.sum_prod_type, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_mul]
  rw [hs, hq]
  push_cast
  ring

 theorem excluded_annihilator_congruences {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (l : ℕ) (ξ : TreeLeaf (fun _ => Fin h) l → ℤ)
    (ha : ∀ c ∈ excludedCheap h p M hd l, ∑ i, (ξ i:ZMod M)*c i = 0) :
    ExcludedCongruences h p l (treeFrequency (fun _ => Fin h) l ξ) := by
  classical
  induction l with
  | zero => trivial
  | succ l ih =>
    change (∀ k : Fin h, (p (l+1) k:ℤ) ∣ _ ) ∧ _
    constructor
    · intro k
      let : NeZero (p (l+1) k) := ⟨(hn _ k).ne'⟩
      have hg := treeCheap_generator (fun _ => Fin h) (MaskResidues h p)
        (fun l => excludedPhaseHom h p M l (hd _)) l (Pi.single k 1)
      have hz := ha _ hg
      rw [excluded_dot_generator (hd (l+1)) k ξ] at hz
      have he : (((∑ i, ξ i) -
          ∑ i : TreeLeaf (fun _ => Fin h) l, ξ (k,i) : ℤ) : ZMod (p (l+1) k)) = 0 :=
        subcircle_injective (hd _ k) (hz.trans (map_zero _).symm)
      have he' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp he
      simp only [treeFrequency, frequencySum, treeFrequency_sum]
      convert he' using 1
      congr 1
      exact (Fintype.sum_prod_type (fun i : Fin h × TreeLeaf (fun _ => Fin h) l => ξ i)).symm
    · intro j
      apply ih
      intro c hc
      exact dot_restrict_child (fun _ => Fin h) (MaskResidues h p)
        (fun l => excludedPhaseHom h p M l (hd _)) l ξ ha j c hc

 theorem excluded_character_branching {h M : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M]
    (hh : 2 ≤ h) (hd : ∀ l (k : Fin h), p l k ∣ M)
    (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → Nat.Prime (p l k))
    (hinj : ∀ l, 1 ≤ l → l ≤ h → Function.Injective (fun k : Fin h => p l k))
    (hlarge : ∀ l (k : Fin h), 1 ≤ l → l ≤ h → h ^ 3 ≤ p l k)
    (χ : AddChar (TreeLeaf (fun _ => Fin h) h → ZMod M) ℂ)
    (ha : χ.compAddMonoidHom (excludedCheap h p M hd h).subtype = 0)
    (θ : ZMod M) (hw : χ (fun _ => θ) ≠ 1) :
    ((h:ℝ)/2)^h ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ) := by
  classical
  let ξ := fun i => (coordinateFrequency χ i).valMinAbs
  have hc := excluded_annihilator_congruences hd hn h ξ (fun c hc => by
    have hv := congrArg (fun ψ : AddChar (excludedCheap h p M hd h) ℂ => ψ ⟨c,hc⟩) ha
    have he : χ c = 1 := hv
    have hz := (character_dot_eq_one χ c).mp he
    simpa only [ξ, ZMod.coe_valMinAbs] using hz)
  have hroot : frequencySum (fun _ => Fin h) h (treeFrequency (fun _ => Fin h) h ξ) ≠ 0 := by
    rw [treeFrequency_sum]
    intro he
    apply hw
    rw [character_dot_eq_one, ← Finset.sum_mul]
    have hz : ∑ i, coordinateFrequency χ i = 0 := by
      have ht := congrArg (fun n : ℤ => (n : ZMod M)) he
      simpa only [Int.cast_sum, ξ, ZMod.coe_valMinAbs, Int.cast_zero] using ht
    rw [hz, zero_mul]
  have hb := excluded_frequency_branching hh p hp hinj hlarge _ hc hroot
  rw [treeFrequency_mass] at hb
  simp only [Nat.cast_sum, ξ] at hb
  simpa only [Nat.cast_sum, ξ] using hb

end FiniteCircle

end OAI
