import Mathlib

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

open scoped LinearAlgebra.Projectivization
open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def subspacePointsEquiv (W : Submodule K V) :
    ℙ K W ≃ {p : ℙ K V // p.submodule ≤ W} := by
  let f : ℙ K W → {p : ℙ K V // p.submodule ≤ W} := fun p =>
    ⟨Projectivization.map W.subtype W.injective_subtype p, by
      induction p using Projectivization.ind with | h v hv =>
      rw [Projectivization.map_mk, Projectivization.submodule_mk,
        Submodule.span_singleton_le_iff_mem]
      exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val hpq)
  · intro p
    have hp : p.val.rep ∈ W := by
      apply p.property
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    let v : W := ⟨p.val.rep, hp⟩
    have hv : v ≠ 0 := fun h => p.val.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact p.val.mk_rep

theorem card_subspacePoints [Finite K] (W : Submodule K V) :
    Nat.card {p : ℙ K V // p.submodule ≤ W} =
      ∑ i ∈ Finset.range (finrank K W), Nat.card K ^ i := by
  rw [← Nat.card_congr (subspacePointsEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

def Incident (a : ℙ K V) (b : ℙ K (Module.Dual K V)) : Prop :=
  a.submodule ≤ LinearMap.ker b.rep

lemma incident_iff (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident a b ↔ b.rep a.rep = 0 := by
  rw [Incident, Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    LinearMap.mem_ker]

lemma incident_iff_dualAnnihilator (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident a b ↔ b.submodule ≤ a.submodule.dualAnnihilator := by
  rw [Projectivization.submodule_eq b, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  rfl

theorem card_points_on_hyperplane [Finite K] [FiniteDimensional K V]
    (b : ℙ K (Module.Dual K V)) :
    Nat.card {a : ℙ K V // Incident a b} =
      ∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero b.rep_nonzero
  have hk : finrank K (LinearMap.ker b.rep) = finrank K V - 1 := by omega
  change Nat.card {a : ℙ K V // a.submodule ≤ LinearMap.ker b.rep} = _
  rw [card_subspacePoints, hk]

theorem card_hyperplanes_through_point [Finite K] [FiniteDimensional K V]
    (a : ℙ K V) :
    Nat.card {b : ℙ K (Module.Dual K V) // Incident a b} =
      ∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (incident_iff_dualAnnihilator a)),
    card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq a.submodule
  rw [a.finrank_submodule] at h
  congr 2
  omega

lemma finrank_sup_points {a a' : ℙ K V} (haa : a ≠ a') :
    finrank K (a.submodule ⊔ a'.submodule : Submodule K V) = 2 := by
  have hli := Projectivization.independent_iff.mp
    ((Projectivization.independent_pair_iff_ne a a').mpr haa)
  have hr : Set.range (Projectivization.rep ∘ ![a, a']) = {a.rep, a'.rep} := by
    ext x
    simp only [Set.mem_range, Function.comp_apply, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have h := finrank_span_eq_card hli
  rw [hr, show ({a.rep, a'.rep} : Set V) = {a.rep} ∪ {a'.rep} by ext; simp [or_comm],
    Submodule.span_union, ← a.submodule_eq, ← a'.submodule_eq] at h
  simpa using h

theorem card_hyperplanes_through_pair [Finite K] [FiniteDimensional K V]
    {a a' : ℙ K V} (haa : a ≠ a') :
    Nat.card {b : ℙ K (Module.Dual K V) // Incident a b ∧ Incident a' b} =
      ∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      Incident a b ∧ Incident a' b ↔
        b.submodule ≤ (a.submodule ⊔ a'.submodule).dualAnnihilator := by
    rw [incident_iff_dualAnnihilator, incident_iff_dualAnnihilator,
      Submodule.dualAnnihilator_sup_eq, le_inf_iff]
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (a.submodule ⊔ a'.submodule)
  rw [finrank_sup_points haa] at h
  congr 2
  omega

def RadialLine (x : ℙ K V) :=
  {W : Submodule K V // finrank K W = 2 ∧ x.submodule ≤ W}

namespace RadialLine

instance (x : ℙ K V) [Finite V] : Finite (RadialLine x) := by
  unfold RadialLine
  infer_instance

lemma finrank_sup [FiniteDimensional K V] {x : ℙ K V}
    {l m : RadialLine x} (hlm : l ≠ m) :
    finrank K (l.val ⊔ m.val : Submodule K V) = 3 := by
  have hn : ¬l.val ≤ m.val := by
    intro h
    apply hlm
    exact Subtype.ext (Submodule.eq_of_le_of_finrank_eq h
      (l.property.1.trans m.property.1.symm))
  have hi : l.val ⊓ m.val < l.val := lt_of_le_of_ne inf_le_left (by
    intro h
    apply hn
    rw [← h]
    exact inf_le_right)
  have hlt := Submodule.finrank_lt_finrank_of_lt hi
  have hge := Submodule.finrank_mono (le_inf l.property.2 m.property.2)
  have he := Submodule.finrank_sup_add_finrank_inf_eq l.val m.val
  rw [x.finrank_submodule] at hge
  rw [l.property.1] at hlt
  rw [l.property.1, m.property.1] at he
  omega

theorem card_hyperplanes [Finite K] [FiniteDimensional K V]
    {x : ℙ K V} (l : RadialLine x) :
    Nat.card {b : ℙ K (Module.Dual K V) // l.val ≤ LinearMap.ker b.rep} =
      ∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      l.val ≤ LinearMap.ker b.rep ↔ b.submodule ≤ l.val.dualAnnihilator := by
    rw [Projectivization.submodule_eq b, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_dualAnnihilator]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq l.val
  rw [l.property.1] at h
  congr 2
  omega

theorem card_hyperplanes_pair [Finite K] [FiniteDimensional K V]
    {x : ℙ K V} {l m : RadialLine x} (hlm : l ≠ m) :
    Nat.card {b : ℙ K (Module.Dual K V) //
      l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep} =
      ∑ i ∈ Finset.range (finrank K V - 3), Nat.card K ^ i := by
  have he (b : ℙ K (Module.Dual K V)) :
      l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep ↔
        b.submodule ≤ (l.val ⊔ m.val).dualAnnihilator := by
    rw [← sup_le_iff, Projectivization.submodule_eq b,
      Submodule.span_singleton_le_iff_mem, Submodule.mem_dualAnnihilator]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he), card_subspacePoints]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (l.val ⊔ m.val)
  rw [finrank_sup hlm] at h
  congr 2
  omega

noncomputable def through (x y : ℙ K V) (hxy : x ≠ y) : RadialLine x :=
  ⟨x.submodule ⊔ y.submodule, finrank_sup_points hxy, le_sup_left⟩

lemma through_eq_iff [FiniteDimensional K V] {x y : ℙ K V} (hxy : x ≠ y)
    (l : RadialLine x) : through x y hxy = l ↔ y.submodule ≤ l.val := by
  constructor
  · intro h
    rw [← h]
    exact le_sup_right
  · intro h
    apply Subtype.ext
    exact Submodule.eq_of_le_of_finrank_eq (sup_le l.property.2 h)
      ((finrank_sup_points hxy).trans l.property.1.symm)

lemma through_le_iff {x y : ℙ K V} (hxy : x ≠ y) (W : Submodule K V) :
    (through x y hxy).val ≤ W ↔ x.submodule ≤ W ∧ y.submodule ≤ W :=
  sup_le_iff

section RadialMass

open scoped Classical

variable [FiniteDimensional K V] {x : ℙ K V} [Fintype (RadialLine x)]

noncomputable def inFlat (W : Submodule K V) : Finset (RadialLine x) := by
  classical
  exact Finset.univ.filter (fun l => l.val ≤ W)

noncomputable def trainingOnLine (X : Finset {y : ℙ K V // x ≠ y})
    (l : RadialLine x) : Finset {y : ℙ K V // x ≠ y} := by
  classical
  exact X.filter (fun y => y.val.submodule ≤ l.val)

omit [Fintype (RadialLine x)] in
lemma trainingOnLine_eq_fiber (X : Finset {y : ℙ K V // x ≠ y})
    (l : RadialLine x) :
    trainingOnLine X l = X.filter (fun y => through x y.val y.property = l) := by
  classical
  ext y
  simp only [trainingOnLine, Finset.mem_filter, through_eq_iff]

lemma sum_trainingOnLine (X : Finset {y : ℙ K V // x ≠ y})
    (W : Submodule K V) (hx : x.submodule ≤ W) :
    ∑ l ∈ inFlat W, (trainingOnLine X l).card =
      (X.filter (fun y => y.val.submodule ≤ W)).card := by
  classical
  simp_rw [trainingOnLine_eq_fiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter X (inFlat W)
    (fun y => through x y.val y.property)]
  congr 1
  ext y
  simp [inFlat, through_le_iff, hx]

noncomputable def strength (X : Finset {y : ℙ K V // x ≠ y})
    (q n : ℝ) (l : RadialLine x) : ℝ := q / n * (trainingOnLine X l).card

lemma sum_strength (X : Finset {y : ℙ K V // x ≠ y})
    (q n : ℝ) (W : Submodule K V) (hx : x.submodule ≤ W) :
    ∑ l ∈ inFlat W, strength X q n l =
      q / n * (X.filter (fun y => y.val.submodule ≤ W)).card := by
  classical
  simp only [strength, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [sum_trainingOnLine X W hx]

omit [FiniteDimensional K V] in
lemma inFlat_inf (W U : Submodule K V) :
    (inFlat (x := x) W) ∩ inFlat U = inFlat (W ⊓ U) := by
  classical
  ext l
  simp [inFlat]

lemma overlap_strength (X : Finset {y : ℙ K V // x ≠ y}) (q n : ℝ)
    (b c : ℙ K (Module.Dual K V)) (hb : Incident x b) (hc : Incident x c) :
    ∑ l ∈ inFlat (LinearMap.ker b.rep) ∩ inFlat (LinearMap.ker c.rep),
      strength X q n l =
        q / n * (X.filter (fun y => Incident y.val b ∧ Incident y.val c)).card := by
  rw [inFlat_inf, sum_strength X q n _ (le_inf hb hc)]
  simp only [Incident, le_inf_iff]
  rfl

end RadialMass

open scoped BigOperators Classical

variable [Finite K] [FiniteDimensional K V] {x : ℙ K V}
  [Fintype (ℙ K (Module.Dual K V))] [Fintype (RadialLine x)]

noncomputable def hyperplanesOn (l : RadialLine x) : Finset (ℙ K (Module.Dual K V)) :=
  Finset.univ.filter (fun b => l.val ≤ LinearMap.ker b.rep)

noncomputable def hyperplanesOnPair (l m : RadialLine x) :
    Finset (ℙ K (Module.Dual K V)) := hyperplanesOn l ∩ hyperplanesOn m

omit [Fintype (RadialLine x)] in
lemma card_hyperplanesOn (l : RadialLine x) :
    (hyperplanesOn l).card = ∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i := by
  rw [hyperplanesOn, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact card_hyperplanes l

omit [Fintype (RadialLine x)] in
lemma card_hyperplanesOnPair {l m : RadialLine x} (hlm : l ≠ m) :
    (hyperplanesOnPair l m).card =
      ∑ i ∈ Finset.range (finrank K V - 3), Nat.card K ^ i := by
  have he : hyperplanesOnPair l m = Finset.univ.filter
      (fun b => l.val ≤ LinearMap.ker b.rep ∧ m.val ≤ LinearMap.ker b.rep) := by
    ext b
    simp [hyperplanesOnPair, hyperplanesOn]
  rw [he, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact card_hyperplanes_pair hlm

omit [Fintype (RadialLine x)] in

theorem weighted_one_anchor (T : Finset (RadialLine x)) (w : RadialLine x → ℝ) :
    (∑ l ∈ T, ∑ _b ∈ hyperplanesOn l, w l) =
      (∑ i ∈ Finset.range (finrank K V - 2), (Nat.card K : ℝ) ^ i) * ∑ l ∈ T, w l := by
  simp only [Finset.sum_const, nsmul_eq_mul, card_hyperplanesOn,
    Nat.cast_sum, Nat.cast_pow]
  rw [Finset.mul_sum]

omit [Fintype (RadialLine x)] in

theorem weighted_two_anchors (T U : Finset (RadialLine x))
    (w z : RadialLine x → ℝ) (hw : ∀ l ∈ T, 0 ≤ w l) (hz : ∀ m ∈ U, 0 ≤ z m) :
    (∑ l ∈ T, ∑ m ∈ U.filter (fun m => l ≠ m),
      ∑ _b ∈ hyperplanesOnPair l m, w l * z m) ≤
      (∑ i ∈ Finset.range (finrank K V - 3), (Nat.card K : ℝ) ^ i) *
        (∑ l ∈ T, w l) * ∑ m ∈ U, z m := by
  let Q : ℝ := ∑ i ∈ Finset.range (finrank K V - 3), (Nat.card K : ℝ) ^ i
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ = ∑ l ∈ T, ∑ m ∈ U.filter (fun m => l ≠ m), Q * (w l * z m) := by
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.sum_const, nsmul_eq_mul,
        card_hyperplanesOnPair (Finset.mem_filter.mp hm).2, Nat.cast_sum, Nat.cast_pow, Q]
    _ ≤ ∑ l ∈ T, ∑ m ∈ U, Q * (w l * z m) := by
      apply Finset.sum_le_sum
      intro l hl
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (by intro m hm _; exact mul_nonneg hQ (mul_nonneg (hw l hl) (hz m hm)))
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] [Fintype (RadialLine x)] in

theorem fresh_anchor_weight {Batch : Type*} [Fintype Batch]
    (T : Finset (RadialLine x)) (L : ℝ) (a : RadialLine x → ℝ) :
    (∑ _r : Batch, ∑ l ∈ T, L * a l) =
      Fintype.card Batch * L * ∑ l ∈ T, a l := by
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] [Fintype (RadialLine x)] in

theorem old_anchor_weight (T D : Finset (RadialLine x)) :
    (∑ _l ∈ T ∩ D, (1 : ℝ)) ≤ D.card := by
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := D))

end RadialLine

open scoped Classical

variable [Finite K] [FiniteDimensional K V]
variable [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

noncomputable def incidenceEntry (a : ℙ K V) (b : ℙ K (Module.Dual K V)) : ℝ :=
  if Incident a b then 1 else 0

noncomputable def weightOnHyperplane (w : ℙ K V → ℝ) (b : ℙ K (Module.Dual K V)) : ℝ :=
  ∑ a, incidenceEntry a b * w a

omit [Fintype (ℙ K V)] in
lemma sum_entry (a : ℙ K V) :
    ∑ b, incidenceEntry a b =
      ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) := by
  classical
  unfold incidenceEntry
  rw [Finset.sum_boole, ← Fintype.card_subtype, Fintype.card_eq_nat_card,
    card_hyperplanes_through_point]

omit [Fintype (ℙ K V)] in
lemma sum_entry_mul_entry (a a' : ℙ K V) :
    ∑ b, incidenceEntry a b * incidenceEntry a' b =
      if a = a' then ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ)
      else ((∑ i ∈ Finset.range (finrank K V - 2), Nat.card K ^ i : ℕ) : ℝ) := by
  classical
  by_cases haa : a = a'
  · subst a'
    simp only [ite_true]
    convert sum_entry a using 1
    apply Finset.sum_congr rfl
    intro b _
    simp [incidenceEntry]
  · rw [ite_eq_right haa]
    trans ∑ b : ℙ K (Module.Dual K V), if Incident a b ∧ Incident a' b then (1 : ℝ) else 0
    · apply Finset.sum_congr rfl
      intro b _
      simp only [incidenceEntry]
      split_ifs <;> simp_all
    · rw [Finset.sum_boole, ← Fintype.card_subtype, Fintype.card_eq_nat_card,
        card_hyperplanes_through_pair haa]

theorem sum_weightOnHyperplane (w : ℙ K V → ℝ) :
    ∑ b, weightOnHyperplane w b =
      ((∑ i ∈ Finset.range (finrank K V - 1), Nat.card K ^ i : ℕ) : ℝ) * ∑ a, w a := by
  classical
  unfold weightOnHyperplane
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, sum_entry, ← Finset.mul_sum]

end SharpRamseyFive.ProjectiveIncidence

end OAI
