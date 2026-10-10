import OAI.MeasureTheory.Falconer.Estimates.WeightedLowpass
import OAI.MeasureTheory.Falconer.Shells.PositiveLowFrequency

namespace OAI

/-! # Bounds for the original masked distance measure

Here `m` is the unit-interval regularized profile. Descriptor predicates
receive its depth parametrization `u ↦ m (u/N)`.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

 theorem descriptorPairWeight_bounds (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i a : ℕ)
    (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L) (z : Space d × Space d)
    (hz : L ≤ dist z.1 z.2*(2:ℝ)^a) :
    0 ≤ descriptorPairWeight w₀ Q ρ m N σ J i a B S z ∧
      descriptorPairWeight w₀ Q ρ m N σ J i a B S z ≤ L^(-(((d:ℝ)-1)/2)) := by
  have h₁ := descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover
    z.1 (normalizeToSphere w₀ (z.1-z.2))
  have h₂ := descriptorProduct_bounds Q ρ (fun u => m (u/N)) N σ J i B S hcover
    z.2 (normalizeToSphere w₀ (z.1-z.2))
  have hd' : (1:ℝ) ≤ d := Nat.one_le_cast.mpr hd
  have hh : -(((d:ℝ)-1)/2) ≤ 0 := by linarith
  have hr : 0 ≤ (dist z.1 z.2*(2:ℝ)^a)^(-(((d:ℝ)-1)/2)) :=
    (Real.rpow_pos_of_pos (hL.trans_le hz) _).le
  constructor
  · exact mul_nonneg (mul_nonneg hr h₁.1) h₂.1
  · apply (mul_le_of_le_one_right (mul_nonneg hr h₁.1) h₂.2).trans
    exact (mul_le_of_le_one_right hr h₁.2).trans (Real.rpow_le_rpow_of_nonpos hL hz hh)

 theorem maskedCellDistance_finite (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ) (N : ℕ)
    (σ : ℝ) (J i a : ℕ) (B : Finset PlanarFalconer.PolicyDescriptor)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ B, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) {L : ℝ} (hL : 0 < L) (X Y : DyadicCube d)
    (hsep : ∀ᵐ z ∂(ρ.restrict X.carrier).prod (ρ.restrict Y.carrier),
      L ≤ dist z.1 z.2*(2:ℝ)^a) :
    IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a B S X Y) := by
  let π := (ρ.restrict X.carrier).prod (ρ.restrict Y.carrier)
  have hbound : ∀ᵐ z ∂π,
      ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * descriptorPairWeight w₀ Q ρ m N σ J i a B S z) ≤
        ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * L^(-(((d:ℝ)-1)/2))) := by
    filter_upwards [hsep] with z hz
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (descriptorPairWeight_bounds w₀ Q ρ m N σ J i a B S hcover hd hL z hz).2 (sq_nonneg _))
  let := finite_withDensity_of_bounded π _ ENNReal.ofReal_lt_top hbound
  unfold maskedCellDistance
  infer_instance

 theorem uniform_maskedCellDistance_dominates {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) (hd : 1 ≤ d) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube d), Q.side = 1 →
      ∀ (ρ : Measure (Space d)) [IsFiniteMeasure ρ] (m : ℝ → ℝ)
        (B : Finset PlanarFalconer.PolicyDescriptor), (∀ b ∈ B, descriptorValid N b) →
      ∀ (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)),
      (∀ b ∈ B, ∀ w : Sphere d,
        ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2) →
      ∀ (i a : ℕ) (w₀ : Sphere d) (X Y : List (Fin d → Bool)) (U : ℝ), 0 < U →
      (∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
        0 < dist z.1 z.2*(2:ℝ)^a ∧ dist z.1 z.2*(2:ℝ)^a ≤ U) →
      ENNReal.ofReal ((profileModelMass m N a)⁻¹^2 * U^(-(((d:ℝ)-1)/2))) •
        testedCellDistance ρ ρ (Q.descendant X) (Q.descendant Y)
          (descriptorPairTests w₀ Q ρ (fun u => m (u/N)) N σ J i B) ≤
        maskedCellDistance w₀ Q ρ m N σ J i a B S (Q.descendant X) (Q.descendant Y) := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorProduct_core (d := d) hσ hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ m B hB S hS i a w₀ X Y U hU hdist
  have hmem : ∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
      z.1 ∈ Q.carrier ∧ z.2 ∈ Q.carrier := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem (Q.descendant X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (Q.descendant Y).measurable)] with z hx hy
    exact ⟨Q.descendant_subset X hx,Q.descendant_subset Y hy⟩
  apply maskedCellDistance_dominates w₀ Q ρ m N σ J i a B S _ _ _
    (descriptorPairTests_measurable w₀ Q ρ _ N σ J i B) _ (by positivity)
  · filter_upwards [hmem] with z hz
    intro hzg
    exact ⟨h₀ N hN Q hQ ρ (fun u => m (u/N)) B hB S hS i z.1 hz.1 _
      (fun b hb => (hzg b hb).1),
      h₀ N hN Q hQ ρ (fun u => m (u/N)) B hB S hS i z.2 hz.2 _
      (fun b hb => (hzg b hb).2)⟩
  · filter_upwards [hdist] with z hz
    intro _
    apply Real.rpow_le_rpow_of_nonpos hz.1 hz.2
    have hd' : (1:ℝ) ≤ d := Nat.one_le_cast.mpr hd
    linarith

end Falconer

end OAI
