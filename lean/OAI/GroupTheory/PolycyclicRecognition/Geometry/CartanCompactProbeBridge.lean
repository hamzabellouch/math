import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanProbeBridgeLength
import OAI.GroupTheory.PolycyclicRecognition.Analysis.NormalizedProbeGenerator
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceSmallExponentialProducts

namespace OAI

/-! # The source bridge for a compact section and an actual neighbor step

The compact section, normalized generator and pivot cancellation are combined
before using the metric estimate. The constants are independent of the small
parameter and of every ideal probe and starting sheet.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- This is the actual neighboring-sheet source bridge. The section is any
fixed linear section on a compact cube; the height identity is precisely the
contact-facet pivot identity. No geometric bridge bound is assumed. -/
theorem exists_compact_source_probe_bridge_bound
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {d : ℕ} (σ : (Fin d → ℝ) →ₗ[ℝ] cartanRootIdeal H)
    {Z : Set (Fin d → ℝ)} (hZ : IsCompact Z)
    (letter : Fin M.letterCount) {q c : ℝ} (hq : 0 ≤ q) (hc : 0 ≤ c)
    (scale RH R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ → ∀ (h : H) (S : MulAut F.N.carrier)
        (n i : F.N.carrier) (x : G) (t : ℝ) (z : Fin d → ℝ),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH j →
        (∀ v, S (F.ExpN (F.N.equiv v)) =
          F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) →
        M.weight letter h = (1 - c * δ) * q * scale j →
        |t| ≤ R j * Real.exp ((1 + δ) * q * scale j) → z ∈ Z →
        dist (x * (F.inclusionN (coneProbeFirst S n i (F.ExpN (F.N.equiv (σ z)))) *
              F.inclusionD (F.ExpD (F.D.equiv h))))
          (x * (F.inclusionN (n * S i * F.ExpN (F.N.equiv (t • M.letter letter))) *
              F.inclusionD (F.ExpD (F.D.equiv h)))) ≤
          (C * δ + D * ε) * scale j := by
  obtain ⟨β, D, hD, hd⟩ := exists_cartan_n_log_metric_bound T M F
    hExpG realize haarN dynkinN b₀
  let b := WordBasisSelections.basis M.letter M.wordList β
  let f : (Fin d → ℝ) →ₗ[ℝ] (Fin (finrank ℝ (cartanRootIdeal H)) → ℝ) :=
    b.equivFun.toLinearMap.comp σ
  obtain ⟨K, hK⟩ := hZ.exists_bound_of_continuousOn f.continuous_of_finiteDimensional.continuousOn
  let R₁ := fun _ : ℕ => max K 0
  let R₂ := fun n => R n * ‖b.equivFun (M.letter letter)‖
  have hR₁0 : ∀ n, 0 ≤ R₁ n := fun _ => le_max_right _ _
  have hR₂0 : ∀ n, 0 ≤ R₂ n := fun n => mul_nonneg (hR0 n) (norm_nonneg _)
  have hR₁ : HasSubexponentialUpperBoundSeq scale R₁ := sequence_subexponential_upper_const hs _
  have hR₂ : HasSubexponentialUpperBoundSeq scale R₂ :=
    hR.mul (sequence_subexponential_upper_const hs _) (Eventually.of_forall hR0)
  obtain ⟨R₃, hR₃0, hR₃, hprod⟩ := exists_sequence_small_product_bound F.N.equiv F.ExpN
    F.isExpN dynkinN M.bound_zero b scale R₁ R₂ hs hscale0 hR₁0 hR₂0 hR₁ hR₂
  have hm := source_probe_bridge_bound_in_basis T M F hExpG realize haarN haarD dynkinN
    β hD hd scale RH R₃ hs hscale0 hRH0 hR₃0 hRH hR₃
  let A : ℝ := (M.bound : ℝ) * ((c + 1) * q)
  have hA : 0 ≤ A := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by linarith) hq)
  refine ⟨D * A, D, mul_nonneg hD hA, hD, ?_⟩
  intro ε hε
  filter_upwards [hm ε hε] with j hj
  intro δ hδ h S n i x t z hh hS hhweight ht hz
  let vq := cartanIdealWeightDilation T H (-h) (t • M.letter letter)
  have hnorm := normalized_probe_generator_coordinate_le T M b h letter ht hhweight
  have hsection : ‖b.equivFun (-σ z)‖ ≤ R₁ j := by
    rw [map_neg, norm_neg]
    exact (hK z hz).trans (le_max_left K 0)
  obtain ⟨v, hv, hvbound⟩ := hprod j (((c + 1) * q) * δ)
    (mul_nonneg (mul_nonneg (by linarith) hq) hδ) (-σ z) vq hsection
    (by simpa only [R₂, vq, mul_assoc] using hnorm)
  have hsk : (F.ExpN (F.N.equiv (σ z)))⁻¹ * F.ExpN (F.N.equiv vq) =
      F.ExpN (F.N.equiv v) := by
    rw [← F.isExpN.map_neg, ← map_neg]
    exact hv.symm
  have hcancel : cartanIdealWeightDilation T H h vq = t • M.letter letter :=
    (cartanIdealWeightDilation T H h).right_inv _
  have hk : S (F.ExpN (F.N.equiv vq)) = F.ExpN (F.N.equiv (t • M.letter letter)) := by
    rw [hS, hcancel]
  have he := hj (A * δ) (mul_nonneg hA hδ) h S n i
    (F.ExpN (F.N.equiv (σ z))) (F.ExpN (F.N.equiv vq)) x v hh hS hsk
    (by simpa [A, mul_assoc] using hvbound)
  simpa only [coneProbeSecond, hk, mul_add, mul_assoc] using he

end PolycyclicRecognition

end

end OAI
