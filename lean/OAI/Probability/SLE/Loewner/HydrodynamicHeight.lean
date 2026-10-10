import OAI.Probability.SLE.Geometry.HalfPlaneJulia
import OAI.Probability.SLE.Loewner.SlitInverseAtInfinity

namespace OAI

/-! Normalization at infinity forces a half-plane self-map to increase
height. This compares the inverse maps of nested slit domains. -/
noncomputable section
open Set Filter Complex Function Metric
open scoped Topology

namespace SLEExactGauge

def verticalInfinity (n : ℕ) : ℂ := (((n:ℝ)+1:ℝ):ℂ)*I

lemma verticalHeights_tendsto : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop := by
  convert! (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1) using 1
  ext n
  simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one]

lemma verticalInfinity_mem (n : ℕ) : verticalInfinity n ∈ upperHalfPlane := by
  simp only [verticalInfinity,upperHalfPlane,mem_ofPred_eq,mul_im,ofReal_re,I_im,mul_one,
    ofReal_im,I_re,mul_zero,add_zero]
  positivity

lemma verticalInfinity_tendsto :
    Tendsto verticalInfinity atTop (cocompact ℂ ⊓ 𝓟 upperHalfPlane) := by
  apply tendsto_inf.mpr
  constructor
  · rw [← Metric.cobounded_eq_cocompact,← tendsto_norm_atTop_iff_cobounded]
    have hh : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
      verticalHeights_tendsto
    have hnorm : (fun n : ℕ => ‖verticalInfinity n‖)=(fun n : ℕ => (n:ℝ)+1) := by
      funext n
      simp only [verticalInfinity,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_I,
        mul_one,abs_of_pos (by positivity : 0<(n:ℝ)+1)]
    rw [hnorm]
    exact hh
  · exact tendsto_principal.mpr (Eventually.of_forall verticalInfinity_mem)

theorem normalized_halfPlane_height {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upperHalfPlane) (hmap : MapsTo F upperHalfPlane upperHalfPlane)
    (hn : Tendsto (fun z : ℂ => F z/z) (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 1))
    {z : ℂ} (hz : z ∈ upperHalfPlane) : z.im ≤ (F z).im := by
  have hr := hn.comp verticalInfinity_tendsto
  have he (n : ℕ) : F (verticalInfinity n)/(((n:ℝ)+1:ℝ):ℂ) =
      (F (verticalInfinity n)/verticalInfinity n)*I := by
    have hne : (((n:ℝ)+1:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
    simp only [verticalInfinity]
    field_simp
  have hlim : Tendsto (fun n : ℕ => F (verticalInfinity n)/(((n:ℝ)+1:ℝ):ℂ)) atTop (𝓝 I) := by
    simpa only [Function.comp_apply,he,one_mul] using hr.mul_const I
  exact halfPlane_julia_at_infinity hF hmap (fun n => (n:ℝ)+1)
    (fun n => by positivity)
    (tendsto_inv_atTop_zero.comp (verticalHeights_tendsto)) hlim hz

end SLEExactGauge

end

end OAI
