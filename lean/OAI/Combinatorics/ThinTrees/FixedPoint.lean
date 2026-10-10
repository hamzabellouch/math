import OAI.Combinatorics.ThinTrees.SimultaneousResponse

namespace OAI

universe uV uV2 uW uI uV3 uV4 uV5 uE

section

namespace StrongThinTree.FixedPoint
noncomputable section
open Finset

abbrev Chain (V : Type uV) := Finset V →₀ ZMod 2

variable {V : Type uV2} {W : Type uW} [DecidableEq V] [DecidableEq W]

def face (s : Finset V) : Chain V := Finsupp.single s 1

def boundary : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2) (fun s : Finset V => ∑ v ∈ s, face (s.erase v))

lemma boundary_face (s : Finset V) : boundary (face s) = ∑ v ∈ s, face (s.erase v) := by
  simp [face, boundary]

lemma boundary_empty : boundary (face (∅ : Finset V)) = 0 := by
  simp [boundary_face]

def cone (v : V) : Chain V →ₗ[ZMod 2] Chain V :=
  Finsupp.linearCombination (ZMod 2) (fun s : Finset V =>
    if v ∈ s then 0 else face (insert v s))

lemma cone_face (v : V) (s : Finset V) :
    cone v (face s) = if v ∈ s then 0 else face (insert v s) := by
  simp [cone, face]

omit [DecidableEq V] in
lemma add_self (c : Chain V) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero (c s)

lemma boundary_cone_face (v : V) (s : Finset V) :
    boundary (cone v (face s)) + cone v (boundary (face s)) = face s := by
  classical
  by_cases hv : v ∈ s
  · rw [cone_face, ite_eq_left hv, map_zero, zero_add, boundary_face, map_sum]
    rw [Finset.sum_eq_single_of_mem v hv]
    · rw [cone_face, ite_eq_right (by simp), Finset.insert_erase hv]
    · intro w hw hwv
      rw [cone_face, ite_eq_left (Finset.mem_erase.mpr ⟨Ne.symm hwv, hv⟩)]
  · rw [cone_face, ite_eq_right hv, boundary_face, Finset.sum_insert hv, Finset.erase_insert hv,
      boundary_face, map_sum]
    simp only [cone_face]
    have heq : (∑ w ∈ s, face ((insert v s).erase w)) =
        ∑ w ∈ s, if v ∈ s.erase w then 0 else face (insert v (s.erase w)) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [ite_eq_right (fun h => hv (Finset.mem_of_mem_erase h)),
        Finset.erase_insert_of_ne (ne_of_mem_of_not_mem hw hv).symm]
    rw [heq, add_assoc, add_self, add_zero]

lemma boundary_cone (v : V) (c : Chain V) :
    boundary (cone v c) + cone v (boundary c) = c := by
  have h : boundary.comp (cone v) + (cone v).comp boundary =
      (LinearMap.id : Chain V →ₗ[ZMod 2] Chain V) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using boundary_cone_face v s
  exact congrArg (fun f : Chain V →ₗ[ZMod 2] Chain V => f c) h

lemma boundary_cone_eq (v : V) (c : Chain V) :
    boundary (cone v c) = c + cone v (boundary c) := by
  have h := congrArg (fun z => z + cone v (boundary c)) (boundary_cone v c)
  simpa only [add_assoc, add_self, add_zero] using h

lemma boundary_boundary_face (s : Finset V) : boundary (boundary (face s)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp [boundary_empty]
  | @insert v s hv ih =>
    have hs : face (insert v s) = cone v (face s) := by simp [cone_face, hv]
    rw [hs, boundary_cone_eq, map_add, boundary_cone_eq, ih, map_zero, add_zero,
      add_self]

lemma boundary_boundary (c : Chain V) : boundary (boundary c) = 0 := by
  have h : boundary.comp boundary = (0 : Chain V →ₗ[ZMod 2] Chain V) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using boundary_boundary_face s
  exact congrArg (fun f : Chain V →ₗ[ZMod 2] Chain V => f c) h

def subdivFace (s : Finset V) : Chain (Finset V) :=
  if _hs : s = ∅ then face ∅ else
    cone s (∑ v : s, subdivFace (s.erase v.1))
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem v.2

def subdivision : Chain V →ₗ[ZMod 2] Chain (Finset V) :=
  Finsupp.linearCombination (ZMod 2) subdivFace

lemma subdivision_face (s : Finset V) : subdivision (face s) = subdivFace s := by
  simp [subdivision, face]

lemma subdiv_empty : subdivFace (∅ : Finset V) = face ∅ := by rw [subdivFace, dite_eq_left rfl]

lemma subdiv_nonempty (s : Finset V) (hs : s.Nonempty) :
    subdivFace s = cone s (subdivision (boundary (face s))) := by
  rw [subdivFace, dite_eq_right hs.ne_empty, boundary_face]
  simp only [map_sum, subdivision_face]
  exact Finset.sum_coe_sort s (fun v => cone s (subdivFace (s.erase v)))

lemma boundary_subdivFace (s : Finset V) :
    boundary (subdivFace s) = subdivision (boundary (face s)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      simp [subdiv_empty, boundary_empty]
    · rw [subdiv_nonempty s (Finset.nonempty_iff_ne_empty.mpr hs), boundary_cone_eq]
      suffices boundary (subdivision (boundary (face s))) = 0 by simp [this]
      rw [boundary_face, map_sum, map_sum]
      simp only [subdivision_face]
      have heq : (∑ v ∈ s, boundary (subdivFace (s.erase v))) =
          subdivision (boundary (boundary (face s))) := by
        rw [boundary_face, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih (s.erase v) (Finset.erase_ssubset hv)
      rw [heq, boundary_boundary, map_zero]

lemma boundary_subdivision (c : Chain V) :
    boundary (subdivision c) = subdivision (boundary c) := by
  have h : (boundary : Chain (Finset V) →ₗ[ZMod 2] Chain (Finset V)).comp subdivision =
      (subdivision : Chain V →ₗ[ZMod 2] _).comp boundary := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change boundary (subdivision (face s)) = subdivision (boundary (face s))
    rw [subdivision_face]
    exact boundary_subdivFace s
  exact congrArg (fun f : Chain V →ₗ[ZMod 2] Chain (Finset V) => f c) h

def rename (f : V → W) : Chain V →ₗ[ZMod 2] Chain W := by
  classical
  exact Finsupp.linearCombination (ZMod 2) (fun s : Finset V =>
    if Set.InjOn f (s : Set V) then face (s.image f) else 0)

omit [DecidableEq V] in
lemma rename_face (f : V → W) (s : Finset V) :
    rename f (face s) = if Set.InjOn f (s : Set V) then face (s.image f) else 0 := by
  classical
  simp [rename, face]

lemma rename_cone_face (f : V → W) (v : V) (s : Finset V) :
    rename f (cone v (face s)) = cone (f v) (rename f (face s)) := by
  classical
  by_cases hv : v ∈ s
  · rw [cone_face, ite_eq_left hv, map_zero, rename_face]
    split_ifs with h
    · simp [cone_face, Finset.mem_image_of_mem f hv]
    · simp
  · rw [cone_face, ite_eq_right hv, rename_face, rename_face]
    have hinj : Set.InjOn f (↑(insert v s) : Set V) ↔
        Set.InjOn f (s : Set V) ∧ f v ∉ s.image f := by
      simpa using (Set.injOn_insert (f := f) (s := (s : Set V)) hv)
    simp only [hinj]
    by_cases hs : Set.InjOn f (s : Set V)
    · by_cases hf : f v ∈ s.image f
      · simp [hs, hf, cone_face]
      · simp [hs, hf, cone_face, Finset.image_insert]
    · simp [hs]

lemma rename_cone (f : V → W) (v : V) (c : Chain V) :
    rename f (cone v c) = cone (f v) (rename f c) := by
  have h : (rename f).comp (cone v) = (cone (f v)).comp (rename f) := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using rename_cone_face f v s
  exact congrArg (fun g : Chain V →ₗ[ZMod 2] Chain W => g c) h

lemma boundary_rename_face (f : V → W) (s : Finset V) :
    boundary (rename f (face s)) = rename f (boundary (face s)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rename_face, boundary_empty]
  | @insert v s hv ih =>
    have heq : face (insert v s) = cone v (face s) := by simp [cone_face, hv]
    rw [heq, rename_cone, boundary_cone_eq, boundary_cone_eq, map_add, rename_cone, ih]

lemma boundary_rename (f : V → W) (c : Chain V) :
    boundary (rename f c) = rename f (boundary c) := by
  have h : boundary.comp (rename f) = (rename f).comp boundary := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    simpa [face] using boundary_rename_face f s
  exact congrArg (fun g : Chain V →ₗ[ZMod 2] Chain W => g c) h

def Supported (P : Finset V → Prop) (c : Chain V) : Prop :=
  ∀ s, ¬ P s → c s = 0

omit [DecidableEq V] in
lemma supported_zero (P : Finset V → Prop) : Supported P 0 := by
  intro s hs; rfl

omit [DecidableEq V] in
lemma supported_face {P : Finset V → Prop} {s : Finset V} (hs : P s) :
    Supported P (face s) := by
  intro t ht
  have hne : s ≠ t := fun h => ht (h ▸ hs)
  simp [face, Ne.symm hne]

omit [DecidableEq V] in
lemma supported_add {P : Finset V → Prop} {c d : Chain V}
    (hc : Supported P c) (hd : Supported P d) : Supported P (c + d) := by
  intro s hs
  simp [hc s hs, hd s hs]

omit [DecidableEq V] in
lemma supported_smul {P : Finset V → Prop} {c : Chain V}
    (hc : Supported P c) (a : ZMod 2) : Supported P (a • c) := by
  intro s hs
  simp [hc s hs]

omit [DecidableEq V] in
lemma supported_sum {I : Type uI} (s : Finset I) (f : I → Chain V)
    {P : Finset V → Prop} (h : ∀i ∈ s, Supported P (f i)) :
    Supported P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using supported_zero P
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact supported_add (h i (Finset.mem_insert_self ..))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [DecidableEq V] in
lemma chain_expansion (c : Chain V) : c = ∑ s ∈ c.support, c s • face s := by
  simpa [Finsupp.sum, face] using (Finsupp.sum_single c).symm

omit [DecidableEq V] in
omit [DecidableEq W] in
lemma supported_map (L : Chain V →ₗ[ZMod 2] Chain W)
    {P : Finset V → Prop} {Q : Finset W → Prop} {c : Chain V}
    (hc : Supported P c) (hL : ∀s, P s → Supported Q (L (face s))) :
    Supported Q (L c) := by
  classical
  rw [chain_expansion c, map_sum]
  apply supported_sum
  intro s hs
  rw [map_smul]
  apply supported_smul
  apply hL s
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hs) (hc s hn)

lemma supported_cone (v : V) {P Q : Finset V → Prop} {c : Chain V}
    (hc : Supported P c) (h : ∀ s, P s → v ∉ s → Q (insert v s)) :
    Supported Q (cone v c) := by
  apply supported_map (cone v) hc
  intro s hs
  rw [cone_face]
  split_ifs with hv
  · exact supported_zero Q
  · exact supported_face (h s hs hv)

omit [DecidableEq V] in
lemma supported_mono {P Q : Finset V → Prop} {c : Chain V}
    (hc : Supported P c) (h : ∀s, P s → Q s) : Supported Q c := by
  intro s hs
  exact hc s (fun hp => hs (h s hp))

def Flag (s : Finset V) (t : Finset (Finset V)) : Prop :=
  t.card = s.card ∧ (∀ a ∈ t, a.Nonempty ∧ a ⊆ s) ∧
    ∀ a ∈ t, ∀ b ∈ t, a ⊆ b ∨ b ⊆ a

lemma subdiv_supported (s : Finset V) : Supported (Flag s) (subdivFace s) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      rw [subdiv_empty]
      apply supported_face
      simp [Flag]
    · rw [subdiv_nonempty s (Finset.nonempty_iff_ne_empty.mpr hs), boundary_face]
      simp only [map_sum, subdivision_face]
      apply supported_sum
      intro v hv
      apply supported_cone s (ih (s.erase v) (Finset.erase_ssubset hv))
      intro t ht hst
      rcases ht with ⟨hcard, hsub, hnest⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hst, hcard, Finset.card_erase_of_mem hv]
        have hpos : 0 < s.card := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      · intro a ha
        rcases Finset.mem_insert.mp ha with ha | ha
        · subst a
          exact ⟨Finset.nonempty_iff_ne_empty.mpr hs, Finset.Subset.refl s⟩
        · exact ⟨(hsub a ha).1, (hsub a ha).2.trans (Finset.erase_subset v s)⟩
      · intro a ha b hb
        rcases Finset.mem_insert.mp ha with ha | ha
        · subst a
          rcases Finset.mem_insert.mp hb with hb | hb
          · subst b
            exact Or.inl (Finset.Subset.refl s)
          · exact Or.inr ((hsub b hb).2.trans (Finset.erase_subset v s))
        · rcases Finset.mem_insert.mp hb with hb | hb
          · subst b
            exact Or.inl ((hsub a ha).2.trans (Finset.erase_subset v s))
          · exact hnest a ha b hb

omit [DecidableEq V] in
lemma supported_rename (f : V → W) {P : Finset V → Prop} {Q : Finset W → Prop}
    {c : Chain V} (hc : Supported P c)
    (h : ∀s, P s → Set.InjOn f (s : Set V) → Q (s.image f)) :
    Supported Q (rename f c) := by
  classical
  apply supported_map (rename f) hc
  intro s hs
  rw [rename_face]
  split_ifs with hf
  · exact supported_face (h s hs hf)
  · exact supported_zero Q

lemma boundary_face_erase {s : Finset V} {v : V} (hv : v ∈ s) :
    boundary (face s) (s.erase v) = 1 := by
  classical
  rw [boundary_face, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single_of_mem v hv]
  · simp [face]
  · intro w hw hwv
    have hne : s.erase w ≠ s.erase v := fun h => hwv ((Finset.erase_inj s hw).mp h)
    simp [face, Ne.symm hne]

lemma supported_singleton_eq {c : Chain V} {s : Finset V}
    (hc : Supported (fun t => t = s) c) : c = c s • face s := by
  ext t
  by_cases ht : t = s
  · subst t; simp [face]
  · simp [hc t ht, face, ht]

theorem sperner_chain (F : Chain V →ₗ[ZMod 2] Chain W) (f : W → V)
    (hboundary : ∀c, boundary (F c) = F (boundary c))
    (hempty : F (face ∅) = face ∅) (s : Finset V)
    (hcarrier : ∀u ⊆ s, Supported
      (fun t => t.card = u.card ∧ ∀w ∈ t, f w ∈ u) (F (face u))) :
    rename f (F (face s)) = face s := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      rw [hempty]
      simp [rename_face]
    · have hsupport : Supported (fun t => t = s) (rename f (F (face s))) := by
        apply supported_rename f (hcarrier s (Finset.Subset.refl s))
        intro t ht hf
        apply Finset.eq_of_subset_of_card_le
        · intro v hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          exact ht.2 w hw
        · rw [Finset.card_image_of_injOn hf, ht.1]
      have hb : boundary (rename f (F (face s))) = boundary (face s) := by
        rw [boundary_rename, hboundary, boundary_face]
        simp only [map_sum]
        apply Finset.sum_congr rfl
        intro v hv
        exact ih (s.erase v) (Finset.erase_ssubset hv)
          (fun u hu => hcarrier u (hu.trans (Finset.erase_subset v s)))
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have heq := supported_singleton_eq hsupport
      rw [heq, map_smul] at hb
      have hcoeff := congrArg (fun c : Chain V => c (s.erase v)) hb
      simp only [Finsupp.smul_apply, smul_eq_mul, boundary_face_erase hv, mul_one] at hcoeff
      rw [heq, hcoeff, one_smul]

omit [DecidableEq W] in
omit [DecidableEq V] in
lemma map_coefficient_witness (L : Chain V →ₗ[ZMod 2] Chain W)
    (c : Chain V) (s : Finset W) (hs : (L c) s ≠ 0) :
    ∃t ∈ c.support, (L (face t)) s ≠ 0 := by
  classical
  by_contra! hn
  apply hs
  conv_lhs => rw [chain_expansion c]
  rw [map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro t ht
  simp [map_smul, hn t ht]

theorem sperner_witness (F : Chain V →ₗ[ZMod 2] Chain W) (f : W → V)
    (hboundary : ∀c, boundary (F c) = F (boundary c))
    (hempty : F (face ∅) = face ∅) (s : Finset V)
    (hcarrier : ∀u ⊆ s, Supported
      (fun t => t.card = u.card ∧ ∀w ∈ t, f w ∈ u) (F (face u))) :
    ∃t ∈ (F (face s)).support, Set.InjOn f (t : Set W) ∧ t.image f = s := by
  classical
  have hmain := sperner_chain F f hboundary hempty s hcarrier
  have hcoeff : (rename f (F (face s))) s ≠ 0 := by rw [hmain]; simp [face]
  obtain ⟨t, ht, hn⟩ := map_coefficient_witness (rename f) (F (face s)) s hcoeff
  rw [rename_face] at hn
  split_ifs at hn with hf
  · refine ⟨t, ht, hf, ?_⟩
    by_contra heq
    exact hn (by simp [face, Ne.symm heq])
  · exact (hn rfl).elim

def IterV (V : Type uV3) : ℕ → Type _
  | 0 => V
  | k+1 => Finset (IterV V k)

instance iterVDecidableEq (V : Type uV4) [DecidableEq V] :
    (k : ℕ) → DecidableEq (IterV V k)
  | 0 => inferInstanceAs (DecidableEq V)
  | k+1 => letI := iterVDecidableEq V k
      inferInstanceAs (DecidableEq (Finset (IterV V k)))

def iterSubdivision : (k : ℕ) → Chain V →ₗ[ZMod 2] Chain (IterV V k)
  | 0 => LinearMap.id
  | k+1 => subdivision.comp (iterSubdivision k)

lemma boundary_iterSubdivision (k : ℕ) (c : Chain V) :
    boundary (iterSubdivision k c) = iterSubdivision k (boundary c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change boundary (subdivision (iterSubdivision k c)) =
      subdivision (iterSubdivision k (boundary c))
    rw [boundary_subdivision, ih]

lemma iterSubdivision_empty (k : ℕ) :
    iterSubdivision k (face (∅ : Finset V)) = face ∅ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change subdivision (iterSubdivision k (face (∅ : Finset V))) = face ∅
    rw [ih, subdivision_face, subdiv_empty]

def mean (z : V → ℝ) (s : Finset V) : ℝ := (∑ v ∈ s, z v) / s.card

omit [DecidableEq V] in
lemma mean_nonneg {z : V → ℝ} {s : Finset V} (h : ∀v ∈ s, 0 ≤ z v) :
    0 ≤ mean z s := div_nonneg (Finset.sum_nonneg h) (Nat.cast_nonneg _)

omit [DecidableEq V] in
lemma mean_zero {z : V → ℝ} {s : Finset V} (h : ∀v ∈ s, z v = 0) :
    mean z s = 0 := by simp [mean, Finset.sum_eq_zero h]

omit [DecidableEq V] in
lemma mean_difference (z : V → ℝ) (a b : Finset V) (ha : a.Nonempty)
    (hb : b.Nonempty) :
    mean z a - mean z b =
      (∑ w ∈ a ×ˢ b, (z w.1 - z w.2)) / ((a.card : ℝ) * b.card) := by
  have hac : (a.card : ℝ) ≠ 0 := by exact_mod_cast ha.card_ne_zero
  have hbc : (b.card : ℝ) ≠ 0 := by exact_mod_cast hb.card_ne_zero
  have hsum : (∑ w ∈ a ×ˢ b, (z w.1 - z w.2)) =
      (b.card : ℝ) * (∑v ∈ a, z v) - (a.card : ℝ) * (∑v ∈ b, z v) := by
    rw [Finset.sum_product]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mul_sum]
  rw [hsum]
  unfold mean
  field_simp

lemma mean_mesh {z : V → ℝ} {a b t : Finset V} {N : ℕ} {D : ℝ}
    (ha : a ⊆ t) (hb : b ⊆ t) (hab : (a ∩ b).Nonempty)
    (ht : t.card ≤ N) (hD : 0 ≤ D)
    (hz : ∀u ∈ t, ∀v ∈ t, |z u - z v| ≤ D) :
    |mean z a - mean z b| ≤ (1 - 1 / (N : ℝ)^2) * D := by
  classical
  obtain ⟨w, hw⟩ := hab
  obtain ⟨hwa, hwb⟩ := Finset.mem_inter.mp hw
  have hane : a.Nonempty := ⟨w, hwa⟩
  have hbne : b.Nonempty := ⟨w, hwb⟩
  have hac : 0 < (a.card : ℝ) := by exact_mod_cast hane.card_pos
  have hbc : 0 < (b.card : ℝ) := by exact_mod_cast hbne.card_pos
  have hprod : 0 < (a.card : ℝ) * b.card := mul_pos hac hbc
  have hN : 0 < (N : ℝ) := by
    have : 0 < N := lt_of_lt_of_le hane.card_pos ((Finset.card_le_card ha).trans ht)
    exact_mod_cast this
  have hbound : (a.card : ℝ) * b.card ≤ (N : ℝ)^2 := by
    have h1 : (a.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card ha).trans ht
    have h2 : (b.card : ℝ) ≤ N := by exact_mod_cast (Finset.card_le_card hb).trans ht
    nlinarith [mul_le_mul h1 h2 hbc.le hN.le]
  have hwprod : (w,w) ∈ a ×ˢ b := Finset.mem_product.mpr ⟨hwa,hwb⟩
  have hsum : |∑ p ∈ a ×ˢ b, (z p.1 - z p.2)| ≤
      ((a.card : ℝ) * b.card - 1) * D := by
    rw [← Finset.sum_erase_add _ _ hwprod]
    simp only [sub_self, add_zero]
    calc
      |∑ p ∈ (a ×ˢ b).erase (w,w), (z p.1 - z p.2)| ≤
          ∑ p ∈ (a ×ˢ b).erase (w,w), |z p.1 - z p.2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ (a ×ˢ b).erase (w,w), D := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hu,hv⟩ := Finset.mem_product.mp (Finset.mem_of_mem_erase hp)
        exact hz p.1 (ha hu) p.2 (hb hv)
      _ = ((a.card : ℝ) * b.card - 1) * D := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Finset.card_erase_of_mem hwprod, Nat.cast_sub (Finset.card_pos.mpr ⟨_, hwprod⟩),
          Finset.card_product, Nat.cast_mul, Nat.cast_one]
  rw [mean_difference z a b hane hbne, abs_div, abs_of_pos hprod]
  apply le_trans (div_le_div_of_nonneg_right hsum hprod.le)
  apply (div_le_iff₀ hprod).mpr
  have hNsq : 0 < (N : ℝ)^2 := sq_pos_of_pos hN
  have hrat : ((a.card : ℝ) * b.card) / (N : ℝ)^2 ≤ 1 :=
    (div_le_one hNsq).mpr hbound
  have : (((a.card : ℝ) * b.card) / (N : ℝ)^2) * D ≤ D :=
    (mul_le_mul_of_nonneg_right hrat hD).trans_eq (one_mul D)
  nlinarith [show (1 / (N : ℝ)^2) * ((a.card : ℝ) * b.card) =
      ((a.card : ℝ) * b.card) / (N : ℝ)^2 by ring]

section Coordinates
variable [Fintype V]

def CoordFace (s : Finset V) (x : V → ℝ) : Prop :=
  (∀i, 0 ≤ x i) ∧ (∑i, x i) = 1 ∧ ∀i, i ∉ s → x i = 0

def baryPoint (p : W → V → ℝ) (s : Finset W) : V → ℝ :=
  fun i => mean (fun w => p w i) s

omit [DecidableEq V] in
omit [DecidableEq W] in
lemma coordFace_bary {s : Finset V} {t : Finset W} {p : W → V → ℝ}
    (ht : t.Nonempty) (hp : ∀w ∈ t, CoordFace s (p w)) :
    CoordFace s (baryPoint p t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact mean_nonneg (fun w hw => (hp w hw).1 i)
  · change (∑i, (∑w ∈ t, p w i) / (t.card : ℝ)) = 1
    rw [← Finset.sum_div, Finset.sum_comm]
    have hsum : (∑w ∈ t, ∑i, p w i) = (t.card : ℝ) := by
      calc
        _ = ∑_w ∈ t, (1 : ℝ) := Finset.sum_congr rfl (fun w hw => (hp w hw).2.1)
        _ = _ := by simp
    rw [hsum, div_self]
    exact_mod_cast ht.card_ne_zero
  · intro i hi
    exact mean_zero (fun w hw => (hp w hw).2.2 i hi)

def iterPoint : (k : ℕ) → IterV V k → V → ℝ
  | 0 => fun (v : V) i => if v = i then 1 else 0
  | k+1 => baryPoint (iterPoint k)

def meshFactor (N : ℕ) : ℝ := 1 - 1 / (N : ℝ)^2

lemma meshFactor_nonneg {N : ℕ} (hN : 0 < N) : 0 ≤ meshFactor N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < (N : ℝ)^2 := by positivity
  unfold meshFactor
  have hsq : (1 : ℝ) ≤ (N : ℝ)^2 := by nlinarith
  exact sub_nonneg.mpr ((div_le_one hs).mpr hsq)

lemma meshFactor_lt_one {N : ℕ} (hN : 0 < N) : meshFactor N < 1 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold meshFactor
  have : 0 < 1 / (N : ℝ)^2 := by positivity
  linarith

def GeometricFacet (k : ℕ) (s : Finset V) (t : Finset (IterV V k)) : Prop :=
  t.card = s.card ∧ (∀v ∈ t, CoordFace s (iterPoint k v)) ∧
    ∀u ∈ t, ∀v ∈ t, ∀i,
      |iterPoint k u i - iterPoint k v i| ≤ (meshFactor (Fintype.card V))^k

lemma iterSubdivision_supported (hV : 0 < Fintype.card V) (k : ℕ) (s : Finset V) :
    Supported (GeometricFacet k s) (iterSubdivision k (face s)) := by
  classical
  induction k with
  | zero =>
    change Supported (GeometricFacet 0 s) (face s)
    apply supported_face
    refine ⟨rfl, ?_, ?_⟩
    · intro v hv
      change V at v
      refine ⟨?_, ?_, ?_⟩
      · intro i
        simp only [iterPoint]
        split_ifs <;> norm_num
      · simp [iterPoint]
      · intro i hi
        have hne : v ≠ i := fun h => hi (h ▸ hv)
        simp only [iterPoint]
        exact ite_eq_right hne
    · intro u hu v hv i
      simp only [iterPoint, pow_zero]
      split_ifs <;> norm_num
  | succ k ih =>
    change Supported (GeometricFacet (k+1) s)
      (subdivision (iterSubdivision k (face s)))
    apply supported_map subdivision ih
    intro t ht
    rw [subdivision_face]
    apply supported_mono (subdiv_supported t)
    intro u hu
    refine ⟨hu.1.trans ht.1, ?_, ?_⟩
    · intro a ha
      exact coordFace_bary (hu.2.1 a ha).1
        (fun w hw => ht.2.1 w ((hu.2.1 a ha).2 hw))
    · intro a ha b hb i
      change Finset (IterV V k) at a b
      have hab : (a ∩ b).Nonempty := by
        rcases hu.2.2 a ha b hb with hab | hba
        · obtain ⟨w, hw⟩ := (hu.2.1 a ha).1
          exact ⟨w, Finset.mem_inter.mpr ⟨hw, hab hw⟩⟩
        · obtain ⟨w, hw⟩ := (hu.2.1 b hb).1
          exact ⟨w, Finset.mem_inter.mpr ⟨hba hw, hw⟩⟩
      have hcard : t.card ≤ Fintype.card V := by
        rw [ht.1]
        exact Finset.card_le_univ s
      have hm := mean_mesh (z := fun w => iterPoint k w i)
        (hu.2.1 a ha).2 (hu.2.1 b hb).2 hab hcard
        (pow_nonneg (meshFactor_nonneg hV) k)
        (fun v hv w hw => ht.2.2 v hv w hw i)
      simpa [iterPoint, baryPoint, meshFactor, pow_succ, mul_comm] using hm

def simplex (V : Type uV5) [Fintype V] : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

omit [DecidableEq V] in

lemma simplex_label {x y : V → ℝ}
    (hx : x ∈ simplex V) (hy : y ∈ simplex V) :
    ∃i, 0 < x i ∧ y i ≤ x i := by
  by_contra! hn
  have hex : ∃i, 0 < x i := by
    by_contra! h
    have hs := Finset.sum_nonpos (s := (univ : Finset V)) (fun i _ => h i)
    rw [hx.2] at hs
    norm_num at hs
  obtain ⟨i, hi⟩ := hex
  have hle : ∀j, x j ≤ y j := by
    intro j
    by_cases hj : 0 < x j
    · exact (hn j hj).le
    · have he : x j = 0 := le_antisymm (not_lt.mp hj) (hx.1 j)
      rw [he]
      exact hy.1 j
  have hs := Finset.sum_lt_sum (fun j (_ : j ∈ (univ : Finset V)) => hle j)
    ⟨i, mem_univ i, hn i hi⟩
  rw [hx.2, hy.2] at hs
  exact (lt_irrefl (1 : ℝ)) hs

abbrev Delta (V : Type uV5) [Fintype V] := {x : V → ℝ // x ∈ simplex V}

theorem simplex_approximation [Nonempty V] (F : Delta V → Delta V) (k : ℕ) :
    ∃ x : V → Delta V, (∀i, (F (x i)).1 i ≤ (x i).1 i) ∧
      ∀i j a, |(x i).1 a - (x j).1 a| ≤ (meshFactor (Fintype.card V))^k := by
  classical
  let label : IterV V k → V := fun v =>
    if h : iterPoint k v ∈ simplex V then
      (simplex_label h (F ⟨iterPoint k v, h⟩).2).choose
    else Classical.choice inferInstance
  have hlabel (v : IterV V k) (hv : iterPoint k v ∈ simplex V) :
      0 < iterPoint k v (label v) ∧
      (F ⟨iterPoint k v, hv⟩).1 (label v) ≤ iterPoint k v (label v) := by
    dsimp [label]
    rw [dite_eq_left hv]
    exact (simplex_label hv (F ⟨iterPoint k v, hv⟩).2).choose_spec
  have hV : 0 < Fintype.card V := Fintype.card_pos
  have hcarrier (u : Finset V) (_ : u ⊆ univ) :
      Supported (fun t => t.card = u.card ∧ ∀w ∈ t, label w ∈ u)
        (iterSubdivision k (face u)) := by
    apply supported_mono (iterSubdivision_supported hV k u)
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro w hw
    have hp := ht.2.1 w hw
    have hl := (hlabel w ⟨hp.1, hp.2.1⟩).1
    by_contra hn
    rw [hp.2.2 _ hn] at hl
    exact (lt_irrefl 0) hl
  obtain ⟨t, ht, _, heq⟩ := sperner_witness (iterSubdivision k) label
    (boundary_iterSubdivision k) (iterSubdivision_empty k) univ hcarrier
  have hgeom : GeometricFacet k univ t := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp ht)
      (iterSubdivision_supported hV k univ t hn)
  have hpre : ∀i : V, ∃v ∈ t, label v = i := by
    intro i
    have : i ∈ t.image label := heq ▸ mem_univ i
    exact mem_image.mp this
  choose v hv hl using hpre
  let x : V → Delta V := fun i =>
    ⟨iterPoint k (v i), (hgeom.2.1 (v i) (hv i)).1,
      (hgeom.2.1 (v i) (hv i)).2.1⟩
  refine ⟨x, ?_, ?_⟩
  · intro i
    have hi := (hlabel (v i) (x i).2).2
    simpa only [hl i] using hi
  · intro i j a
    exact hgeom.2.2 (v i) (hv i) (v j) (hv j) a

theorem simplex_fixed_point [Nonempty V] (F : Delta V → Delta V) (hF : Continuous F) :
    ∃x, F x = x := by
  classical
  have hclosed : IsClosed (simplex V) := by
    have heq : simplex V = (⋂ i : V, {x : V → ℝ | 0 ≤ x i}) ∩
        {x : V → ℝ | ∑ i, x i = 1} := by
      ext x
      simp [simplex]
    rw [heq]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  have hcompact : IsCompact (simplex V) :=
    IsCompact.of_isClosed_subset (s := Set.Icc (0 : V → ℝ) 1) isCompact_Icc hclosed (by
      intro x hx
      refine ⟨hx.1, fun i => ?_⟩
      change x i ≤ 1
      exact hx.2 ▸ Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i))
  let : CompactSpace (Delta V) := isCompact_iff_compactSpace.mp hcompact
  choose x hlabel hmesh using simplex_approximation F
  let i₀ : V := Classical.choice inferInstance
  obtain ⟨z, _, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq
    (x := fun k => x k i₀) (fun _ => Set.mem_univ _)
  have hq0 := meshFactor_nonneg (Fintype.card_pos (α := V))
  have hq1 := meshFactor_lt_one (Fintype.card_pos (α := V))
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp hφ.tendsto_atTop
  have hdist (n : ℕ) (i : V) :
      dist (x (φ n) i) (x (φ n) i₀) ≤ (meshFactor (Fintype.card V))^(φ n) := by
    change dist (x (φ n) i).1 (x (φ n) i₀).1 ≤ _
    apply (dist_pi_le_iff (pow_nonneg hq0 _)).mpr
    intro a
    exact hmesh (φ n) i i₀ a
  have hlim (i : V) : Filter.Tendsto (fun n => x (φ n) i) Filter.atTop (nhds z) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hz' := tendsto_iff_dist_tendsto_zero.mp hz
    apply squeeze_zero (fun _ => dist_nonneg)
      (fun n => (dist_triangle _ (x (φ n) i₀) _).trans (_root_.add_le_add (hdist n i) le_rfl))
    simpa only [zero_add, Function.comp_def] using hpow.add hz'
  have hle (i : V) : (F z).1 i ≤ z.1 i := by
    have hc : Continuous (fun y : Delta V => y.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact le_of_tendsto_of_tendsto ((hc.comp hF).tendsto z |>.comp (hlim i))
      (hc.tendsto z |>.comp (hlim i)) (Filter.Eventually.of_forall (fun n => hlabel (φ n) i))
  refine ⟨z, Subtype.ext (funext fun i => ?_)⟩
  have he := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ (univ : Finset V)) => hle i)).mp ((F z).2.2.trans z.2.2.symm)
  exact he i (mem_univ i)

end Coordinates

section ConvexFixedPoint
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_convex_approximation {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hc : Convex ℝ K) (F : K → K) (hF : Continuous F)
    {ε : ℝ} (hε : 0 < ε) : ∃x : K, dist x (F x) ≤ ε := by
  classical
  obtain ⟨t, htK, htfin, htcover⟩ := hK.finite_cover_balls hε
  let : Fintype t := htfin.fintype
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    have h := htcover hx
    simp only [Set.mem_iUnion] at h
    obtain ⟨y, hy, _⟩ := h
    exact ⟨y, hy⟩
  let : Nonempty t := htne.to_subtype
  let bump (x : K) (i : t) : ℝ := max 0 (ε - dist x.1 i.1)
  let total (x : K) : ℝ := ∑i : t, bump x i
  have hbump (x : K) (i : t) : 0 ≤ bump x i := le_max_left _ _
  have htotal (x : K) : 0 < total x := by
    obtain ⟨y, hyx⟩ := Set.mem_iUnion.mp (htcover x.2)
    obtain ⟨hy, hxy⟩ := Set.mem_iUnion.mp hyx
    apply Finset.sum_pos' (fun i _ => hbump x i)
    refine ⟨⟨y, hy⟩, mem_univ _, ?_⟩
    exact lt_of_lt_of_le (sub_pos.mpr hxy) (le_max_right _ _)
  let weights (x : K) : Delta t := ⟨fun i => bump x i / total x,
    (fun i => div_nonneg (hbump x i) (htotal x).le), by
      rw [← Finset.sum_div]
      exact div_self (htotal x).ne'⟩
  have cbump (i : t) : Continuous (fun x : K => bump x i) :=
    continuous_const.max (continuous_const.sub (continuous_subtype_val.dist continuous_const))
  have ctotal : Continuous total := continuous_finsetSum _ (fun i _ => cbump i)
  have cweights : Continuous weights := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun i => (cbump i).div ctotal (fun x => (htotal x).ne'))
  let combo (u : Delta t) : K := ⟨∑i : t, u.1 i • i.1,
    hc.sum_mem (fun i _ => u.2.1 i) u.2.2 (fun i _ => htK i.2)⟩
  have ccombo : Continuous combo := by
    apply Continuous.subtype_mk
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const
  have happrox (y : K) : dist (combo (weights y)) y ≤ ε := by
    change dist (∑i : t, (weights y).1 i • i.1) y.1 ≤ ε
    rw [dist_eq_norm]
    have he : (∑i : t, (weights y).1 i • i.1) - y.1 =
        ∑i : t, (weights y).1 i • (i.1 - y.1) := by
      rw [Finset.sum_congr rfl (fun i _ => smul_sub _ _ _), Finset.sum_sub_distrib,
        ← Finset.sum_smul, (weights y).2.2, one_smul]
    rw [he]
    calc
      _ ≤ ∑i : t, ‖(weights y).1 i • (i.1 - y.1)‖ := norm_sum_le _ _
      _ ≤ ∑i : t, (weights y).1 i * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((weights y).2.1 i)]
        by_cases hi : bump y i = 0
        · have hw : (weights y).1 i = 0 := by simp [weights, hi]
          simp only [hw, zero_mul, le_refl]
        · have hd : dist y.1 i.1 < ε := by
            have hp : 0 < bump y i := (hbump y i).lt_of_ne' hi
            dsimp [bump] at hp
            exact sub_pos.mp ((lt_max_iff.mp hp).resolve_left (lt_irrefl 0))
          apply mul_le_mul_of_nonneg_left _ ((weights y).2.1 i)
          simpa only [← dist_eq_norm, dist_comm] using hd.le
      _ = ε := by rw [← Finset.sum_mul, (weights y).2.2, one_mul]
  obtain ⟨u, hu⟩ := simplex_fixed_point (fun u => weights (F (combo u)))
    (cweights.comp (hF.comp ccombo))
  refine ⟨combo u, ?_⟩
  have := happrox (F (combo u))
  rwa [hu] at this

theorem compact_convex_fixed_point {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hc : Convex ℝ K) (F : K → K) (hF : Continuous F) :
    ∃x, F x = x := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have heps (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  choose x hx using fun n => compact_convex_approximation hK hne hc F hF (heps n)
  obtain ⟨z, _, φ, hφ, hz⟩ := isCompact_univ.tendsto_subseq
    (x := x) (fun _ => Set.mem_univ _)
  have hlim : Filter.Tendsto (fun n => dist (x (φ n)) (F (x (φ n))))
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => hx (φ n))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  have hzero : dist z (F z) = 0 := tendsto_nhds_unique
    ((continuous_id.dist hF).tendsto z |>.comp hz) hlim
  exact ⟨z, (dist_eq_zero.mp hzero).symm⟩
end ConvexFixedPoint

end
end StrongThinTree.FixedPoint

end

end OAI
