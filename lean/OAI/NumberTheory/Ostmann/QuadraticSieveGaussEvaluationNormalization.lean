import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationPhases
import OAI.NumberTheory.Ostmann.QuadraticSieveGaussEvaluationRoots

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open Complex Filter
open scoped Topology BigOperators

theorem normalized_quadratic_gaussian_transfer (q : ℕ) [NeZero q] {ε : ℝ} (hε : 0<ε) :
    (((ε : ℂ)*(q : ℂ)^2)^(1/2 : ℂ))*
      periodicGaussian q (quadraticResidueWeight q) (ε : ℂ) =
    gaussNormalizationRatio q ε *
      ((gaussResidual q ε*16)^(1/2 : ℂ)*
        periodicGaussian 4 (inverseResidueWeight q) (gaussResidual q ε)) := by
  have hq : (0 : ℝ)<q := by exact_mod_cast Nat.pos_of_neZero q
  have hz : 0<(gaussParameter q ε).re := by simpa using hε
  have htheta : (∑' n : ℤ, gaussianWave (gaussParameter q ε) n) =
      ((gaussParameter q ε)^(1/2 : ℂ))⁻¹*
        ∑' n : ℤ, gaussianWave (gaussParameter q ε)⁻¹ n := by
    simpa using shifted_gaussian_poisson hz 0
  have hqre : 0<((q : ℂ)^2).re := by
    have hs : (q : ℂ)^2=(((q : ℝ)^2 : ℝ) : ℂ) := by norm_cast
    rw [hs,Complex.ofReal_re]
    positivity
  have hrre : 0<(gaussResidualRatio q ε*16).re := by
    simpa using mul_pos (gaussResidualRatio_re_pos q ε) (by norm_num : (0 : ℝ)<16)
  have hleft : (((ε : ℂ)*(q : ℂ)^2)^(1/2 : ℂ))=(Real.sqrt ε : ℂ)*(q : ℂ) := by
    rw [principal_sqrt_mul_real hε hqre,one_div,
      Complex.sq_cpow_two_inv (by simpa using hq)]
  have hright : (gaussResidual q ε*16)^(1/2 : ℂ)=
      (Real.sqrt ε : ℂ)*(gaussResidualRatio q ε*16)^(1/2 : ℂ) := by
    rw [gaussResidual_eq_mul_ratio,mul_assoc,principal_sqrt_mul_real hε hrre]
  have hrr : (gaussResidualRatio q ε*16)^(1/2 : ℂ)≠0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    left
    intro h
    simp [h] at hrre
  have hzz : (gaussParameter q ε)^(1/2 : ℂ)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (gaussParameter_ne_zero q ε))
  rw [periodicGaussian_quadratic,htheta,periodicGaussian_inverse,hleft,hright]
  unfold gaussNormalizationRatio
  field_simp

theorem quadratic_phase_sum_identity (q : ℕ) [NeZero q] :
    (∑ a : Fin q, quadraticResidueWeight q a) =
      ((Real.sqrt (q : ℝ) : ℂ)*(1+I)/4)*(∑ a : Fin 4, inverseResidueWeight q a) := by
  have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0<(ε : ℂ).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε
  have hRe : Tendsto (fun ε : ℝ => ((ε : ℂ)⁻¹).re) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [←Complex.ofReal_inv,Complex.ofReal_re] using tendsto_inv_nhdsGT_zero
  have hleft := periodicGaussian_tendsto q (quadraticResidueWeight q) (fun ε : ℝ => (ε : ℂ)) hb hRe
  have hbr : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0<(gaussResidual q ε).re := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact gaussResidual_re_pos q hε
  have hright := ((gaussNormalizationRatio_continuousAt_zero q).tendsto.mono_left
    nhdsWithin_le_nhds).mul (periodicGaussian_tendsto 4 (inverseResidueWeight q)
      (gaussResidual q) hbr (tendsto_gaussResidual_inv_re q))
  norm_num only [show (4 : ℂ)^2=16 by norm_num] at hright
  rw [gaussNormalizationRatio_zero] at hright
  have heq : (fun ε : ℝ => (((ε : ℂ)*(q : ℂ)^2)^(1/2 : ℂ))*
      periodicGaussian q (quadraticResidueWeight q) (ε : ℂ)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => gaussNormalizationRatio q ε *
        ((gaussResidual q ε*16)^(1/2 : ℂ)*
          periodicGaussian 4 (inverseResidueWeight q) (gaussResidual q ε))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact normalized_quadratic_gaussian_transfer q hε
  exact tendsto_nhds_unique (hleft.congr' heq) hright

end Ostmann.QuadraticSieve

end

end OAI
