import Mathlib

namespace OAI

/-! Finite hard-core cylinder partitions and planar polygon bounds. -/

open scoped BigOperators Topology

open Polynomial Classical

noncomputable section

namespace HoneycombCylinder
namespace FiniteHardCore

variable {α : Type*} [DecidableEq α]

abbrev Independent (I : α → α → Prop) (s : Finset α) : Prop :=
  (s : Set α).Pairwise (fun a b => ¬ I a b)

def partition (I : α → α → Prop) (w : α → ℝ) (U : Finset α) : ℝ[X] := by
  classical
  exact ∑ s ∈ U.powerset,
    if Independent I s then Polynomial.monomial s.card (∏ a ∈ s, w a) else 0

def neighbors (I : α → α → Prop) (U : Finset α) (a : α) : Finset α := by
  classical
  exact U.filter (fun b => ¬ I a b)

lemma independent_insert {I : α → α → Prop} (hI : ∀ ⦃a b⦄, I a b → I b a)
    {U : Finset α} {a : α} (ha : a ∉ U) :
    Independent I (insert a U) ↔ Independent I U ∧ ∀ b ∈ U, ¬ I a b := by
  classical
  unfold Independent
  rw [Finset.coe_insert, Set.pairwise_insert]
  constructor
  · rintro ⟨h, h₁⟩
    exact ⟨h, fun b hb => (h₁ b hb (by rintro rfl; exact ha hb)).1⟩
  · rintro ⟨h, hU⟩
    exact ⟨h, fun b hb _ => ⟨hU b hb, fun hba => hU b hb (hI hba)⟩⟩

lemma partition_insert {I : α → α → Prop} (hI : ∀ ⦃a b⦄, I a b → I b a)
    (w : α → ℝ) {U : Finset α} {a : α} (ha : a ∉ U) :
    partition I w (insert a U) = partition I w U +
      Polynomial.monomial 1 (w a) * partition I w (neighbors I U a) := by
  classical
  rw [partition, Finset.sum_powerset_insert ha]
  congr 1
  rw [partition, Finset.mul_sum]
  have hsub : (neighbors I U a).powerset ⊆ U.powerset := by
    intro s hs
    exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hs).trans (Finset.filter_subset _ _))
  have has (s : Finset α) (hs : s ∈ U.powerset) : a ∉ s :=
    fun h => ha (Finset.mem_powerset.mp hs h)
  have hn (s : Finset α) (hs : s ∈ U.powerset) :
      s ∈ (neighbors I U a).powerset ↔ ∀ b ∈ s, ¬ I a b := by
    simp only [Finset.mem_powerset, neighbors, Finset.subset_iff, Finset.mem_filter]
    exact ⟨fun h b hb => (h hb).2, fun h b hb => ⟨Finset.mem_powerset.mp hs hb, h b hb⟩⟩
  calc
    _ = ∑ s ∈ (neighbors I U a).powerset,
        if Independent I (insert a s) then
          Polynomial.monomial (insert a s).card (∏ b ∈ insert a s, w b) else 0 := by
      symm
      apply Finset.sum_subset hsub
      intro s hs hsn
      have hc : ¬ ∀ b ∈ s, ¬ I a b := fun h => hsn ((hn s hs).mpr h)
      simp [independent_insert hI (has s hs), hc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      have hc := (hn s (hsub hs)).mp hs
      by_cases hi : Independent I s
      · rw [ite_eq_left ((independent_insert hI (has s (hsub hs))).mpr ⟨hi, hc⟩),
          ite_eq_left hi]
        rw [Finset.card_insert_of_notMem (has s (hsub hs)),
          Finset.prod_insert (has s (hsub hs)), Polynomial.monomial_mul_monomial]
        simp only [Nat.add_comm]

      · simp [independent_insert hI (has s (hsub hs)), hi]

@[simp] lemma partition_empty (I : α → α → Prop) (w : α → ℝ) :
    partition I w ∅ = 1 := by
  simp [partition, Independent]

lemma coeff_zero (I : α → α → Prop) (w : α → ℝ) (U : Finset α) :
    (partition I w U).coeff 0 = 1 := by
  classical
  simp only [partition, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (∅ : Finset α)]
  · simp [Independent]
  · intro s hs hns
    by_cases hi : Independent I s
    · simp [hi, Polynomial.coeff_monomial, Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hns)]
    · simp [hi]
  · simp

lemma coeff_one (I : α → α → Prop) (hI : ∀ ⦃a b⦄, I a b → I b a)
    (w : α → ℝ) (U : Finset α) :
    (partition I w U).coeff 1 = ∑ a ∈ U, w a := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | @insert a U ha ih =>
    rw [partition_insert hI w ha, Polynomial.coeff_add]
    rw [Polynomial.coeff_monomial_mul _ 1 0, coeff_zero, mul_one]
    rw [Finset.sum_insert ha, ih, add_comm]

def compatiblePairs (I : α → α → Prop) (w : α → ℝ) (U : Finset α) : ℝ := by
  classical
  exact ∑ a ∈ U, ∑ b ∈ U, if a ≠ b ∧ ¬ I a b then w a * w b else 0

lemma compatiblePairs_insert (I : α → α → Prop)
    (hI : ∀ ⦃a b⦄, I a b → I b a)
    (w : α → ℝ) {U : Finset α} {a : α} (ha : a ∉ U) :
    compatiblePairs I w (insert a U) = compatiblePairs I w U +
      2 * w a * ∑ b ∈ neighbors I U a, w b := by
  classical
  have hsymm (b : α) : I b a ↔ I a b := ⟨fun h => hI h, fun h => hI h⟩
  have hne {b} (hb : b ∈ U) : a ≠ b := fun h => ha (h ▸ hb)
  unfold compatiblePairs
  rw [Finset.sum_insert ha]
  simp only [Finset.sum_insert ha, ne_eq, not_true_eq_false, false_and, ↓reduceIte, zero_add]
  rw [Finset.sum_add_distrib]
  have h₁ : (∑ b ∈ U, if a ≠ b ∧ ¬ I a b then w a * w b else 0) =
      w a * ∑ b ∈ neighbors I U a, w b := by
    rw [neighbors, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp [hne hb, mul_ite]
  have h₂ : (∑ b ∈ U, if b ≠ a ∧ ¬ I b a then w b * w a else 0) =
      w a * ∑ b ∈ neighbors I U a, w b := by
    rw [← h₁]
    apply Finset.sum_congr rfl
    intro b hb
    simp [hne hb, (hne hb).symm, hsymm, mul_comm]
  rw [h₁, h₂]
  ring

lemma twice_coeff_two (I : α → α → Prop)
    (hI : ∀ ⦃a b⦄, I a b → I b a) (w : α → ℝ) (U : Finset α) :
    2 * (partition I w U).coeff 2 = compatiblePairs I w U := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [compatiblePairs, Polynomial.coeff_one]
  | @insert a U ha ih =>
    rw [partition_insert hI w ha, Polynomial.coeff_add,
      Polynomial.coeff_monomial_mul _ 1 1]
    rw [coeff_one I hI, compatiblePairs_insert I hI w ha, ← ih]
    ring

def incompatiblePairs (I : α → α → Prop) (w : α → ℝ) (U : Finset α) : ℝ := by
  classical
  exact ∑ a ∈ U, ∑ b ∈ U, if I a b then w a * w b else 0

lemma pair_decomposition (I : α → α → Prop) (hdiag : ∀ a, I a a)
    (w : α → ℝ) (U : Finset α) :
    (∑ a ∈ U, w a)^2 - compatiblePairs I w U = incompatiblePairs I w U := by
  classical
  rw [pow_two, Finset.sum_mul_sum]
  unfold compatiblePairs incompatiblePairs
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hi : I a b
  · simp [hi]
  · have hab : a ≠ b := fun h => hi (h ▸ hdiag a)
    simp [hi, hab]

lemma negative_log_second_derivative (P : ℝ[X]) (hP : P.coeff 0 = 1) :
    -(deriv (deriv (fun g : ℝ => Real.log (P.eval g))) 0) =
      P.coeff 1 ^ 2 - 2 * P.coeff 2 := by
  have hp : P.eval 0 ≠ 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero, hP]; norm_num
  have heq : deriv (fun g : ℝ => Real.log (P.eval g)) =ᶠ[𝓝 (0 : ℝ)]
      (fun g => P.derivative.eval g / P.eval g) := by
    filter_upwards [P.continuous.continuousAt.eventually_ne hp] with g hg
    exact ((P.hasDerivAt g).log hg).deriv
  rw [heq.deriv_eq]
  have hd := ((P.derivative.hasDerivAt 0).div (P.hasDerivAt 0) hp).deriv
  change deriv (fun g => P.derivative.eval g / P.eval g) 0 = _ at hd
  rw [hd]
  simp only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, hP]
  norm_num
  ring

theorem log_second_derivative_eq_incompatiblePairs (I : α → α → Prop)
    (hI : ∀ ⦃a b⦄, I a b → I b a) (hdiag : ∀ a, I a a)
    (w : α → ℝ) (U : Finset α) :
    -(deriv (deriv (fun g : ℝ => Real.log ((partition I w U).eval g))) 0) =
      incompatiblePairs I w U := by
  rw [negative_log_second_derivative _ (coeff_zero I w U), coeff_one I hI,
    twice_coeff_two I hI]
  exact pair_decomposition I hdiag w U

lemma eval_partition (I : α → α → Prop) (w : α → ℝ) (U : Finset α) (g : ℝ) :
    (partition I w U).eval g =
      ∑ s ∈ U.powerset, if Independent I s then ∏ a ∈ s, g * w a else 0 := by
  classical
  rw [partition, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hi : Independent I s
  · simp only [hi, ↓reduceIte, Polynomial.eval_monomial, Finset.prod_mul_distrib,
      Finset.prod_const]
    ring
  · simp [hi]

end FiniteHardCore
end HoneycombCylinder


open Classical
open scoped BigOperators Topology

namespace HoneycombCylinder
namespace Lattice

abbrev Face (H : Type*) := H × ℤ
abbrev Vertex (H : Type*) := Face H × Bool
abbrev Bond (H : Type*) := Face H × Fin 3

variable {H : Type*} [AddGroupWithOne H]

def bondSource (e : Bond H) : Vertex H := (e.1, true)

def bondTarget (e : Bond H) : Vertex H :=
  if e.2 = 0 then (e.1, false)
  else if e.2 = 1 then ((e.1.1, e.1.2 - 1), false)
  else ((e.1.1 - 1, e.1.2), false)

def dualEnds (e : Bond H) : Face H × Face H :=
  if e.2 = 0 then ((e.1.1 + 1, e.1.2), (e.1.1, e.1.2 + 1))
  else if e.2 = 1 then (e.1, (e.1.1 + 1, e.1.2))
  else (e.1, (e.1.1, e.1.2 + 1))

def vertices (E : Finset (Bond H)) : Finset (Vertex H) :=
  E.image bondSource ∪ E.image bondTarget

def Incident (v : Vertex H) (e : Bond H) : Prop :=
  v = bondSource e ∨ v = bondTarget e

def AdjWithin (E : Finset (Bond H)) (u v : Vertex H) : Prop :=
  ∃ e ∈ E, (u = bondSource e ∧ v = bondTarget e) ∨
    (v = bondSource e ∧ u = bondTarget e)

def IsCycle (E : Finset (Bond H)) : Prop :=
  E.Nonempty ∧
  (∀ v ∈ vertices E, (E.filter (Incident v)).card = 2) ∧
  (∀ u ∈ vertices E, ∀ v ∈ vertices E,
    Relation.ReflTransGen (AdjWithin E) u v)

abbrev Polygon (H : Type*) [AddGroupWithOne H] :=
  {E : Finset (Bond H) // IsCycle E}

namespace Polygon

def vertices (p : Polygon H) : Finset (Vertex H) := Lattice.vertices p.val

def length (p : Polygon H) : ℕ := p.val.card

def Incompatible (p q : Polygon H) : Prop :=
  ∃ v, v ∈ p.vertices ∧ v ∈ q.vertices

lemma vertices_nonempty (p : Polygon H) : p.vertices.Nonempty := by
  obtain ⟨e, he⟩ := p.property.1
  refine ⟨bondSource e, ?_⟩
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

lemma incompatible_symm {p q : Polygon H} (h : Incompatible p q) :
    Incompatible q p := by
  obtain ⟨v, hp, hq⟩ := h
  exact ⟨v, hq, hp⟩

lemma incompatible_self (p : Polygon H) : Incompatible p p := by
  obtain ⟨v, hv⟩ := vertices_nonempty p
  exact ⟨v, hv, hv⟩

lemma not_incompatible_iff_disjoint (p q : Polygon H) :
    ¬ Incompatible p q ↔ Disjoint p.vertices q.vertices := by
  simp [Incompatible, Finset.disjoint_left]

end Polygon

def DualAvoiding (E : Finset (Bond H)) (a b : Face H) : Prop :=
  ∃ e : Bond H, e ∉ E ∧
    ((dualEnds e).1 = a ∧ (dualEnds e).2 = b ∨
     (dualEnds e).1 = b ∧ (dualEnds e).2 = a)

def Separates (p : Polygon H) (a b : Face H) : Prop :=
  ¬ Relation.ReflTransGen (DualAvoiding p.val) a b

def InHex (R : ℕ) (q : Face ℤ) : Prop :=
  |q.1| ≤ (R : ℤ) ∧ |q.2| ≤ (R : ℤ) ∧ |q.1 + q.2| ≤ (R : ℤ)

def TriangleInHex (R : ℕ) (v : Vertex ℤ) : Prop :=
  InHex R (v.1.1 + 1, v.1.2) ∧ InHex R (v.1.1, v.1.2 + 1) ∧
    if v.2 then InHex R v.1 else InHex R (v.1.1 + 1, v.1.2 + 1)

def ContainedInHex (R : ℕ) (p : Polygon ℤ) : Prop :=
  ∀ v ∈ p.vertices, TriangleInHex R v

def SurroundsOrigin (p : Polygon ℤ) : Prop :=
  ∃ R : ℕ, ∀ q : Face ℤ,
    Relation.ReflTransGen (DualAvoiding p.val) (0, 0) q → InHex R q

end Lattice

open HoneycombCylinder.Lattice

def criticalActivity : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)

abbrev CylFace (m : ℕ) := Face (ZMod (2 * m))
abbrev CylPolygon (m : ℕ) := Lattice.Polygon (ZMod (2 * m))

def firstMark (m : ℕ) : CylFace m := (0, 0)
def secondMark (m : ℕ) : CylFace m := ((m : ZMod (2 * m)), 0)

abbrev SeparatingPolygon (m : ℕ) :=
  {p : CylPolygon m // Separates p (firstMark m) (secondMark m)}

def cylinderLength {m : ℕ} (p : SeparatingPolygon m) : ℕ := p.val.length

def CylinderIncompatible {m : ℕ} (p q : SeparatingPolygon m) : Prop :=
  Lattice.Polygon.Incompatible p.val q.val

abbrev CylinderConfiguration (m : ℕ) :=
  {s : Finset (SeparatingPolygon m) //
    (s : Set (SeparatingPolygon m)).Pairwise (fun p q => ¬ CylinderIncompatible p q)}

def cylinderWeight (m : ℕ) (g : ℝ) (s : CylinderConfiguration m) : ℝ :=
  ∏ p ∈ s.val, g * criticalActivity ^ cylinderLength p

def cylinderComplexWeight (m : ℕ) (g : ℂ) (s : CylinderConfiguration m) : ℂ :=
  ∏ p ∈ s.val, g * (criticalActivity : ℂ) ^ cylinderLength p

def G (m : ℕ) (g : ℝ) : ℝ := ∑' s, cylinderWeight m g s

def GComplex (m : ℕ) (g : ℂ) : ℂ := ∑' s, cylinderComplexWeight m g s

def pairWeight (m : ℕ) (pq : SeparatingPolygon m × SeparatingPolygon m) : ℝ :=
  if CylinderIncompatible pq.1 pq.2 then
    criticalActivity ^ (cylinderLength pq.1 + cylinderLength pq.2) else 0

def pairMass (m : ℕ) : ℝ := ∑' pq, pairWeight m pq

def cylinderFluctuation (m : ℕ) : ℝ :=
  -(deriv (deriv (fun g : ℝ => Real.log (G m g))) 0)

abbrev PlanarPolygon (R : ℕ) :=
  {p : Lattice.Polygon ℤ // ContainedInHex R p ∧ SurroundsOrigin p}

def PlanarIncompatible {R : ℕ} (p q : PlanarPolygon R) : Prop :=
  Lattice.Polygon.Incompatible p.val q.val

abbrev PlanarConfiguration (R : ℕ) :=
  {s : Finset (PlanarPolygon R) //
    (s : Set (PlanarPolygon R)).Pairwise (fun p q => ¬ PlanarIncompatible p q)}

def planarWeight (R : ℕ) (s : PlanarConfiguration R) : ℝ :=
  ∏ p ∈ s.val, 2 * criticalActivity ^ p.val.length

def Z (R : ℕ) : ℝ := ∑' s, planarWeight R s

def evenAtTop : Filter ℕ := Filter.atTop ⊓ Filter.principal {m : ℕ | Even m}

def stripExponent (θ : ℂ) : ℝ :=
  ((1 / 6 : ℂ) - 2 * θ ^ 2 / (3 * (Real.pi : ℂ) ^ 2)).re

lemma criticalActivity_pos : 0 < criticalActivity := by
  unfold criticalActivity
  apply one_div_pos.mpr
  exact Real.sqrt_pos.mpr (by positivity)

def cutBond (m i : ℕ) : Bond (ZMod (2 * m)) := (((i : ZMod (2 * m)), 0), 1)

lemma cutBond_dualEnds (m i : ℕ) :
    dualEnds (cutBond m i) = (((i : ZMod (2 * m)), 0), (((i + 1 : ℕ) : ZMod (2 * m)), 0)) := by
  simp [cutBond, dualEnds, Nat.cast_add, Nat.cast_one]

lemma separator_meets_cut {m : ℕ} (p : SeparatingPolygon m) :
    ∃ i : ℕ, i < m ∧ cutBond m i ∈ p.val.val := by
  by_contra h
  push Not at h
  have hpath (i : ℕ) (hi : i ≤ m) :
      Relation.ReflTransGen (DualAvoiding p.val.val) (firstMark m)
        ((i : ZMod (2 * m)), 0) := by
    induction i with
    | zero => simpa [firstMark] using
      (Relation.ReflTransGen.refl : Relation.ReflTransGen (DualAvoiding p.val.val)
        (firstMark m) (firstMark m))
    | succ i ih =>
      refine (ih (Nat.le_trans (Nat.le_succ i) hi)).tail ?_
      refine ⟨cutBond m i, h i (by omega), Or.inl ?_⟩
      simp [cutBond_dualEnds]
  exact p.property (hpath m le_rfl)

def cutIndex {m : ℕ} (p : SeparatingPolygon m) : ℕ :=
  Nat.find (separator_meets_cut p)

lemma cutIndex_spec {m : ℕ} (p : SeparatingPolygon m) :
    cutIndex p < m ∧ cutBond m (cutIndex p) ∈ p.val.val :=
  Nat.find_spec (separator_meets_cut p)

lemma source_mem_vertices {H : Type*} [AddGroupWithOne H]
    {E : Finset (Bond H)} {e : Bond H} (he : e ∈ E) :
    bondSource e ∈ Lattice.vertices E :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

lemma cylinder_configuration_card_le {m : ℕ} (s : CylinderConfiguration m) :
    s.val.card ≤ m := by
  suffices s.val.card ≤ (Finset.range m).card by simpa using this
  apply Finset.card_le_card_of_injOn cutIndex
  · intro p hp
    exact Finset.mem_range.mpr (cutIndex_spec p).1
  · intro p hp q hq hpq
    by_contra hne
    apply s.property hp hq hne
    unfold CylinderIncompatible Lattice.Polygon.Incompatible
    refine ⟨bondSource (cutBond m (cutIndex p)),
      source_mem_vertices (cutIndex_spec p).2, ?_⟩
    rw [hpq]
    exact source_mem_vertices (cutIndex_spec q).2

lemma cylinder_configuration_card_le_two_mul {m : ℕ} (s : CylinderConfiguration m) :
    s.val.card ≤ 2 * m := by
  have := cylinder_configuration_card_le s
  omega

def emptyCylinderConfiguration (m : ℕ) : CylinderConfiguration m :=
  ⟨∅, by simp⟩

@[simp] lemma cylinderWeight_empty (m : ℕ) (g : ℝ) :
    cylinderWeight m g (emptyCylinderConfiguration m) = 1 := by
  simp [cylinderWeight, emptyCylinderConfiguration]

@[simp] lemma cylinderComplexWeight_empty (m : ℕ) (g : ℂ) :
    cylinderComplexWeight m g (emptyCylinderConfiguration m) = 1 := by
  simp [cylinderComplexWeight, emptyCylinderConfiguration]

lemma cylinderWeight_zero_of_ne_empty (m : ℕ) (s : CylinderConfiguration m)
    (h : s ≠ emptyCylinderConfiguration m) : cylinderWeight m 0 s = 0 := by
  have hn : s.val ≠ ∅ := fun he => h (Subtype.ext he)
  have hcard : s.val.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
  simp [cylinderWeight, hcard]

lemma cylinderComplexWeight_zero_of_ne_empty (m : ℕ) (s : CylinderConfiguration m)
    (h : s ≠ emptyCylinderConfiguration m) : cylinderComplexWeight m 0 s = 0 := by
  have hn : s.val ≠ ∅ := fun he => h (Subtype.ext he)
  have hcard : s.val.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
  simp [cylinderComplexWeight, hcard]

@[simp] theorem G_zero (m : ℕ) : G m 0 = 1 := by
  rw [G, tsum_eq_single (emptyCylinderConfiguration m)]
  · exact cylinderWeight_empty m 0
  · exact fun s h => cylinderWeight_zero_of_ne_empty m s h

@[simp] theorem GComplex_zero (m : ℕ) : GComplex m 0 = 1 := by
  rw [GComplex, tsum_eq_single (emptyCylinderConfiguration m)]
  · exact cylinderComplexWeight_empty m 0
  · exact fun s h => cylinderComplexWeight_zero_of_ne_empty m s h

end HoneycombCylinder

end

noncomputable section
open Classical Polynomial
open scoped BigOperators Topology

namespace HoneycombCylinder

def cylinderCutoff (m : ℕ) (B : Finset (Lattice.Bond (ZMod (2 * m)))) :
    Finset (SeparatingPolygon m) :=
  B.powerset.preimage (fun p : SeparatingPolygon m => p.val.val)
    (by intro p hp q hq h; exact Subtype.ext (Subtype.ext h))

@[simp] lemma mem_cylinderCutoff (m : ℕ) (B : Finset (Lattice.Bond (ZMod (2 * m))))
    (p : SeparatingPolygon m) : p ∈ cylinderCutoff m B ↔ p.val.val ⊆ B := by
  exact Finset.mem_preimage.trans Finset.mem_powerset

def heightBonds (m h : ℕ) : Finset (Lattice.Bond (ZMod (2 * m))) :=
  ((Finset.range (2 * m)).product (Finset.Icc (-(h : ℤ)) (h : ℤ))).biUnion
    (fun ij => (Finset.univ : Finset (Fin 3)).image
      (fun k => (((ij.1 : ZMod (2 * m)), ij.2), k)))

def finiteCylinderPolynomial (m : ℕ) (B : Finset (Lattice.Bond (ZMod (2 * m)))) : ℝ[X] :=
  FiniteHardCore.partition CylinderIncompatible
    (fun p => criticalActivity ^ cylinderLength p) (cylinderCutoff m B)

lemma finiteCylinderPolynomial_eval (m : ℕ) (B : Finset (Lattice.Bond (ZMod (2 * m))))
    (g : ℝ) :
    (finiteCylinderPolynomial m B).eval g =
      ∑ s ∈ (cylinderCutoff m B).powerset,
        if (s : Set (SeparatingPolygon m)).Pairwise (fun p q => ¬ CylinderIncompatible p q)
          then ∏ p ∈ s, g * criticalActivity ^ cylinderLength p else 0 :=
  by
    simpa only [finiteCylinderPolynomial, FiniteHardCore.Independent] using
      (FiniteHardCore.eval_partition (CylinderIncompatible (m := m))
        (fun p => criticalActivity ^ cylinderLength p) (cylinderCutoff m B) g)

@[simp] lemma finiteCylinderPolynomial_coeff_zero (m : ℕ)
    (B : Finset (Lattice.Bond (ZMod (2 * m)))) :
    (finiteCylinderPolynomial m B).coeff 0 = 1 :=
  FiniteHardCore.coeff_zero _ _ _

lemma finiteCylinderPolynomial_degree_le (m : ℕ)
    (B : Finset (Lattice.Bond (ZMod (2 * m)))) :
    (finiteCylinderPolynomial m B).natDegree ≤ 2 * m := by
  unfold finiteCylinderPolynomial FiniteHardCore.partition
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  split_ifs with hind
  · exact (Polynomial.natDegree_monomial_le _).trans
      (cylinder_configuration_card_le_two_mul (⟨s, hind⟩ : CylinderConfiguration m))
  · simp

theorem finite_cylinder_negative_log_second_derivative (m : ℕ)
    (B : Finset (Lattice.Bond (ZMod (2 * m)))) :
    -(deriv (deriv (fun g : ℝ => Real.log ((finiteCylinderPolynomial m B).eval g))) 0) =
      ∑ p ∈ cylinderCutoff m B, ∑ q ∈ cylinderCutoff m B,
        if CylinderIncompatible p q then
          criticalActivity ^ (cylinderLength p + cylinderLength q) else 0 := by
  simpa only [finiteCylinderPolynomial, FiniteHardCore.incompatiblePairs, pow_add] using
    (FiniteHardCore.log_second_derivative_eq_incompatiblePairs
      (CylinderIncompatible (m := m))
      (fun {_ _} h => Lattice.Polygon.incompatible_symm h)
      (fun p => Lattice.Polygon.incompatible_self p.val)
      (fun p => criticalActivity ^ cylinderLength p) (cylinderCutoff m B))

def planarBondBox (R : ℕ) : Finset (Lattice.Bond ℤ) :=
  ((Finset.Icc (-(R : ℤ)) (R : ℤ)).product
    (Finset.Icc (-(R : ℤ)) (R : ℤ))).product Finset.univ

lemma planarPolygon_bonds_subset (R : ℕ) (p : PlanarPolygon R) :
    p.val.val ⊆ planarBondBox R := by
  intro e he
  have hv : Lattice.bondSource e ∈ p.val.vertices := source_mem_vertices he
  have hc := p.property.1 _ hv
  have hanchor : Lattice.InHex R e.1 := by
    simpa only [Lattice.TriangleInHex, Lattice.bondSource, Bool.true_eq, ↓reduceIte] using hc.2.2
  rcases hanchor with ⟨hx, hy, _⟩
  rcases e with ⟨⟨i, j⟩, k⟩
  exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (abs_le.mp hx), Finset.mem_Icc.mpr (abs_le.mp hy)⟩,
    Finset.mem_univ k⟩

def planarPolygonCode (R : ℕ) : PlanarPolygon R ↪ (planarBondBox R).powerset where
  toFun p := ⟨p.val.val, Finset.mem_powerset.mpr (planarPolygon_bonds_subset R p)⟩
  inj' := by
    intro p q h
    have h' : p.val.val = q.val.val :=
      congrArg (fun x : (planarBondBox R).powerset => x.val) h
    exact Subtype.ext (Subtype.ext h')

instance planarPolygon_finite (R : ℕ) : Finite (PlanarPolygon R) :=
  Finite.of_injective (planarPolygonCode R) (planarPolygonCode R).injective

theorem planarWeight_summable (R : ℕ) : Summable (planarWeight R) :=
  Summable.of_finite

lemma planarWeight_nonneg (R : ℕ) (s : PlanarConfiguration R) :
    0 ≤ planarWeight R s := by
  apply Finset.prod_nonneg
  intro p hp
  exact mul_nonneg (by norm_num) (pow_nonneg criticalActivity_pos.le _)

def emptyPlanarConfiguration (R : ℕ) : PlanarConfiguration R := ⟨∅, by simp⟩

@[simp] lemma planarWeight_empty (R : ℕ) :
    planarWeight R (emptyPlanarConfiguration R) = 1 := by
  simp [planarWeight, emptyPlanarConfiguration]

theorem one_le_Z (R : ℕ) : 1 ≤ Z R := by
  simpa only [Z, planarWeight_empty] using
    (planarWeight_summable R).le_tsum (emptyPlanarConfiguration R)
      (fun s _ => planarWeight_nonneg R s)

instance evenAtTop_neBot : Filter.NeBot evenAtTop := by
  apply Filter.frequently_iff_neBot.mp
  apply Filter.frequently_atTop.mpr
  intro n
  exact ⟨2 * n, by omega, even_two_mul n⟩

end HoneycombCylinder
end

noncomputable section
open Classical
open scoped BigOperators

namespace HoneycombCylinder

lemma inHex_mono {R S : ℕ} (h : R ≤ S) {q : Lattice.Face ℤ}
    (hq : Lattice.InHex R q) : Lattice.InHex S q := by
  have hRS : (R : ℤ) ≤ S := Int.ofNat_le.mpr h
  exact ⟨hq.1.trans hRS, hq.2.1.trans hRS, hq.2.2.trans hRS⟩

lemma triangleInHex_mono {R S : ℕ} (h : R ≤ S) {v : Lattice.Vertex ℤ}
    (hv : Lattice.TriangleInHex R v) : Lattice.TriangleInHex S v := by
  refine ⟨inHex_mono h hv.1, inHex_mono h hv.2.1, ?_⟩
  have hv' := hv.2.2
  split_ifs at hv' ⊢ <;> exact inHex_mono h hv'

def planarPolygonInclusion {R S : ℕ} (h : R ≤ S) : PlanarPolygon R ↪ PlanarPolygon S where
  toFun p := ⟨p.val, (fun v hv => triangleInHex_mono h (p.property.1 v hv)), p.property.2⟩
  inj' := by
    intro p q hpq
    have hval : p.val = q.val := congrArg (fun z : PlanarPolygon S => z.val) hpq
    exact Subtype.ext hval

def planarConfigurationInclusion {R S : ℕ} (h : R ≤ S) :
    PlanarConfiguration R ↪ PlanarConfiguration S where
  toFun s := ⟨s.val.map (planarPolygonInclusion h), by
    intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q', hq', rfl⟩ := Finset.mem_map.mp hq
    exact s.property hp' hq' (fun heq => hpq (congrArg (planarPolygonInclusion h) heq))⟩
  inj' := by
    intro s t hst
    exact Subtype.ext ((Finset.map_injective (planarPolygonInclusion h))
      (congrArg (fun z : PlanarConfiguration S => z.val) hst))

@[simp] lemma planarWeight_inclusion {R S : ℕ} (h : R ≤ S) (s : PlanarConfiguration R) :
    planarWeight S (planarConfigurationInclusion h s) = planarWeight R s := by
  change (∏ p ∈ s.val.map (planarPolygonInclusion h), 2 * criticalActivity ^ p.val.length) =
    ∏ p ∈ s.val, 2 * criticalActivity ^ p.val.length
  rw [Finset.prod_map]
  rfl

theorem Z_mono : Monotone Z := by
  intro R S h
  exact Summable.tsum_le_tsum_of_inj
    (planarConfigurationInclusion h) (planarConfigurationInclusion h).injective
    (fun s _ => planarWeight_nonneg S s)
    (fun s => (planarWeight_inclusion h s).ge)
    (planarWeight_summable R) (planarWeight_summable S)

end HoneycombCylinder
end

end OAI
