import OAI.Geometry.IsometricImmersion.Immersions.ActualShearHeight
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetReverseNorm

namespace OAI

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def inverseShearCLM (q0 : ℝ) : Coord →L[ℝ] Coord :=
  LinearMap.toContinuousLinearMap
    { toFun := inverseShearCoordinates q0
      map_add' := by
        intro left right
        ext index
        fin_cases index
        · rfl
        · dsimp [inverseShearCoordinates]
          ring
      map_smul' := by
        intro scalar point
        ext index
        fin_cases index
        · rfl
        · dsimp [inverseShearCoordinates]
          ring }

@[simp] theorem inverseShearCLM_apply (q0 : ℝ) (p : Coord) :
    inverseShearCLM q0 p = inverseShearCoordinates q0 p := rfl

theorem inverseShearCLM_norm_le (q0 : ℝ) : ‖inverseShearCLM q0‖ ≤ 1 + |q0| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (1 + |q0|) * ‖v‖)).mpr
  intro i
  fin_cases i
  · change ‖v 0‖ ≤ _
    exact (norm_le_pi_norm v 0).trans (by nlinarith [mul_nonneg (abs_nonneg q0) (norm_nonneg v)])
  · change ‖v 1 - q0 * v 0‖ ≤ _
    calc
      _ ≤ ‖v 1‖ + ‖q0 * v 0‖ := norm_sub_le _ _
      _ = ‖v 1‖ + |q0| * ‖v 0‖ := by rw [norm_mul, Real.norm_eq_abs q0]
      _ ≤ ‖v‖ + |q0| * ‖v‖ := add_le_add (norm_le_pi_norm v 1)
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (abs_nonneg q0))
      _ = _ := by ring

theorem local_linear_full_jet_norm_bound {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (L : Coord →L[ℝ] Coord)
    {p : Coord} (hp : L p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ n f (L p)‖ * ‖L‖^n := by
  have hpre := hU.preimage L.continuous
  have heq := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hU hp] at heq
  rw [heq]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n f (L p)) (fun _ : Fin n => L)

theorem sheared_full_jet_bound_of_coordinateBound {z : Coord → ℝ} {U S : Set Coord}
    {N n : ℕ} {B : ℝ} (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hSU : S ⊆ U) (hbound : CoordinateBound z S N B) (hB : 0 ≤ B)
    (q0 : ℝ) (hn : n ≤ N) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ S) :
    ‖iteratedFDeriv ℝ n (heightInShearCoordinates z q0) p‖ ≤
      (2 * (1 + |q0|))^N * B := by
  have hlocal := local_linear_full_jet_norm_bound hz hU (inverseShearCLM q0) (hSU hp) n
  have hbase := hbound.full_jet_norm_bound hz hU hSU hB hn hp
  have hscale : 1 ≤ 2 * (1 + |q0|) := by nlinarith [abs_nonneg q0]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n z (inverseShearCoordinates q0 p)‖ * ‖inverseShearCLM q0‖^n := hlocal
    _ ≤ ((2 : ℝ)^n * B) * (1 + |q0|)^n := mul_le_mul hbase
      (pow_le_pow_left₀ (norm_nonneg _) (inverseShearCLM_norm_le q0) n)
      (pow_nonneg (norm_nonneg _) n) (mul_nonneg (by positivity) hB)
    _ = (2 * (1 + |q0|))^n * B := by rw [mul_pow]; ring
    _ ≤ (2 * (1 + |q0|))^N * B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hscale hn) hB

theorem CoordinateBound.inverse_shear {z : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {B : ℝ} (hbound : CoordinateBound z S N B)
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U) (hSU : S ⊆ U) (hB : 0 ≤ B) (q0 : ℝ) :
    CoordinateBound (heightInShearCoordinates z q0) (inverseShearCoordinates q0 ⁻¹' S)
      N ((2 * (1 + |q0|))^N * B) := by
  intro ds hds p hp
  apply (norm_iteratedCoordPartial_le_jet (heightInShearCoordinates_contDiffOn hz q0)
    (hU.preimage (inverseShearCoordinates_contDiff q0).continuous) ds (hSU hp)).trans
  exact sheared_full_jet_bound_of_coordinateBound hz hU hSU hbound hB q0 hds hp

end SmoothLocal.Pulse

end

end OAI
