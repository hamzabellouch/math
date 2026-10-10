import OAI.Geometry.CylinderCovering.Barycentric.SweepsDefinitions
import OAI.Geometry.CylinderCovering.Angular.Caps
import OAI.Geometry.CylinderCovering.Barycentric.SweepCompact

namespace OAI

open Set
open scoped BigOperators Convex

noncomputable section
namespace CylinderCovering.BarycentricClosure

theorem closure_positive_simplex {ι : Type*} [Fintype ι] [Nonempty ι] :
    closure {x : ι → ℝ | (∀ i, 0 < x i) ∧ ∑ i, x i = 1} =
      {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro x hx
      exact ⟨fun i => (hx.1 i).le, hx.2⟩
    · have hnonneg : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
        have heq : {x : ι → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x | 0 ≤ x i} := by
          ext x
          simp
        rw [heq]
        exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
      exact hnonneg.inter (isClosed_eq (by fun_prop) continuous_const)
  · intro x hx
    let y : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
    have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
    have hypos : ∀ i, 0 < y i := fun _ => inv_pos.mpr hn
    have hy : (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1 := by
      refine ⟨fun i => (hypos i).le, ?_⟩
      simp [y, ne_of_gt hn]
    have hseg : openSegment ℝ x y ⊆
        {z : ι → ℝ | (∀ i, 0 < z i) ∧ ∑ i, z i = 1} := by
      rintro z ⟨a, b, ha, hb, hab, rfl⟩
      refine ⟨fun i => ?_, ?_⟩
      · change 0 < a * x i + b * y i
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hx.1 i))
          (mul_pos hb (hypos i))
      · change ∑ i, (a * x i + b * y i) = 1
        rwa [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hx.2, hy.2, mul_one, mul_one]
    exact closure_mono hseg
      (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

theorem simplex_subset_of_positive_subset {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (ι → ℝ)} (hC : IsClosed C)
    (hcover : ∀ x : ι → ℝ, (∀ i, 0 < x i) → (∑ i, x i = 1) → x ∈ C) :
    {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} ⊆ C := by
  rw [← closure_positive_simplex]
  exact closure_minimal (fun x hx => hcover x hx.1 hx.2) hC

theorem simplex_subset_compact_union {ι : Type*} [Fintype ι] [Nonempty ι]
    {U V : Set (ι → ℝ)} (hU : IsCompact U) (hV : IsCompact V)
    (hcover : ∀ x : ι → ℝ, (∀ i, 0 < x i) → (∑ i, x i = 1) → x ∈ U ∪ V) :
    {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1} ⊆ U ∪ V :=
  simplex_subset_of_positive_subset (hU.isClosed.union hV.isClosed) hcover

theorem barycentricSimplex_subset_of_positive_subset
    {C : Set RadialCoordinates.BarycentricSpace} (hC : IsClosed C)
    (hcover : ∀ x : RadialCoordinates.BarycentricSpace,
      (∀ i, 0 < x i) → (∑ i, x i = 1) → x ∈ C) :
    RadialCoordinates.barycentricSimplex ⊆ C := by
  intro x hx
  have hc : IsClosed ((WithLp.toLp 2) ⁻¹' C) :=
    hC.preimage (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ))
  have hsub := simplex_subset_of_positive_subset hc
    (fun y hy hsum => hcover (WithLp.toLp 2 y) hy hsum)
  exact hsub (show (∀ i, 0 ≤ WithLp.ofLp x i) ∧ ∑ i, WithLp.ofLp x i = 1 from hx)

end CylinderCovering.BarycentricClosure

namespace RadialCoordinates

theorem mem_firstSweepWithCap_iff (k : ℝ) (R : ℝ → ℝ) (x : BarycentricSpace) :
    x ∈ firstSweepWithCap k R ↔ ∃ t S p : ℝ,
      t ∈ Icc 0 1 ∧ S ∈ Icc 0 (R t) ∧ |p| ≤ 1 ∧ firstSweepPoint k t S p = x := by
  constructor
  · rintro ⟨⟨⟨t, S⟩, p⟩, ⟨⟨ht, hS⟩, hp⟩, hx⟩
    exact ⟨t, S, p, ht, hS, abs_le.mpr hp, hx⟩
  · rintro ⟨t, S, p, ht, hS, hp, hx⟩
    exact ⟨((t, S), p), ⟨⟨ht, hS⟩, abs_le.mp hp⟩, hx⟩

theorem mem_secondSweepWithCap_iff (k : ℝ) (R : ℝ → ℝ) (x : BarycentricSpace) :
    x ∈ secondSweepWithCap k R ↔ ∃ t S p : ℝ,
      t ∈ Icc 0 1 ∧ S ∈ Icc 0 (R t) ∧ |p| ≤ 1 ∧ secondSweepPoint k t S p = x := by
  constructor
  · rintro ⟨⟨⟨t, S⟩, p⟩, ⟨⟨ht, hS⟩, hp⟩, hx⟩
    exact ⟨t, S, p, ht, hS, abs_le.mpr hp, hx⟩
  · rintro ⟨t, S, p, ht, hS, hp, hx⟩
    exact ⟨((t, S), p), ⟨⟨ht, hS⟩, abs_le.mp hp⟩, hx⟩

theorem firstSweepPoint_sum (k t S p : ℝ) : ∑ i, firstSweepPoint k t S p i = 1 := by
  simp [firstSweepPoint, barycentricPoint, Fin.sum_univ_succ]
  ring

theorem secondSweepPoint_sum (k t S p : ℝ) : ∑ i, secondSweepPoint k t S p i = 1 := by
  simp [secondSweepPoint, barycentricPoint, Fin.sum_univ_succ]
  ring

theorem firstSweepPoint_coordinates (k t S p : ℝ) :
    firstSweepPoint k t S p 0 = S * t + k * p * t ^ 2 ∧
    firstSweepPoint k t S p 1 = S * (1 - t) - k * p * (1 - t) ^ 2 ∧
    firstSweepPoint k t S p 2 - firstSweepPoint k t S p 3 = p := by
  simp only [firstSweepPoint, barycentricPoint, angular]
  constructor
  · simp; ring
  constructor <;> simp <;> ring

theorem secondSweepPoint_coordinates (k r T q : ℝ) :
    secondSweepPoint k r T q 2 = T * r - k * q * r ^ 2 ∧
    secondSweepPoint k r T q 3 = T * (1 - r) + k * q * (1 - r) ^ 2 ∧
    secondSweepPoint k r T q 0 - secondSweepPoint k r T q 1 = q := by
  simp only [secondSweepPoint, barycentricPoint, angular]
  constructor
  · simp; ring
  constructor <;> simp <;> ring

theorem continuous_firstSweepPoint (k : ℝ) :
    Continuous (fun z : (ℝ × ℝ) × ℝ => firstSweepPoint k z.1.1 z.1.2 z.2) := by
  unfold firstSweepPoint barycentricPoint angular
  fun_prop

theorem continuous_secondSweepPoint (k : ℝ) :
    Continuous (fun z : (ℝ × ℝ) × ℝ => secondSweepPoint k z.1.1 z.1.2 z.2) := by
  unfold secondSweepPoint barycentricPoint angular
  fun_prop

theorem isCompact_firstSweepWithCap (k : ℝ) {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc 0 1)) (hR : ∀ t ∈ Icc 0 1, 0 ≤ R t) :
    IsCompact (firstSweepWithCap k R) :=
  ((AngularCaps.isCompact_radialParameterSet hRcont hR).prod isCompact_Icc).image
    (continuous_firstSweepPoint k)

theorem isCompact_secondSweepWithCap (k : ℝ) {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc 0 1)) (hR : ∀ t ∈ Icc 0 1, 0 ≤ R t) :
    IsCompact (secondSweepWithCap k R) :=
  ((AngularCaps.isCompact_radialParameterSet hRcont hR).prod isCompact_Icc).image
    (continuous_secondSweepPoint k)

theorem continuous_barycentric_cap (k : ℝ) : Continuous (cap k) := by
  unfold cap capPolynomial angular
  fun_prop

theorem barycentric_cap_nonneg (k t : ℝ) : 0 ≤ cap k t := by
  unfold cap capPolynomial
  positivity

theorem isCompact_firstSweep (k : ℝ) : IsCompact (firstSweep k) :=
  firstSweep_isCompact k

theorem isCompact_secondSweep (k : ℝ) : IsCompact (secondSweep k) :=
  secondSweep_isCompact k

theorem barycentric_cover_of_positive_cover (k : ℝ)
    (hcover : ∀ x : BarycentricSpace, (∀ i, 0 < x i) →
      (∑ i, x i = 1) → x ∈ firstSweep k ∪ secondSweep k) :
    barycentricSimplex ⊆ firstSweep k ∪ secondSweep k :=
  CylinderCovering.BarycentricClosure.barycentricSimplex_subset_of_positive_subset
    ((isCompact_firstSweep k).isClosed.union (isCompact_secondSweep k).isClosed) hcover

end RadialCoordinates

end

end OAI
