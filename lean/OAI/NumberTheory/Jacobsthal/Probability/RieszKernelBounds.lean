import OAI.NumberTheory.Jacobsthal.Primes.RieszMellinKernel

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory _root_.Filter
open scoped Topology

lemma rieszKernel_norm_bound {sigma : ℝ} (hs : 1/2 ≤ sigma) (t : ℝ) :
    ‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖ ≤ 4/(1+t^2) := by
  let z : ℂ := (sigma:ℂ)+(t:ℂ)*Complex.I
  have hr : z.re = sigma := by simp [z]
  have hi : z.im = t := by simp [z]
  have h0 : ‖z‖^2 = sigma^2+t^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,hr,hi]
    ring
  have h1 : ‖z+1‖^2 = (sigma+1)^2+t^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,add_zero,hr,hi]
    ring
  have hle : ‖z‖ ≤ ‖z+1‖ := by nlinarith [norm_nonneg z,norm_nonneg (z+1)]
  have hp := mul_le_mul_of_nonneg_left hle (norm_nonneg z)
  have hsig : (1/4:ℝ) ≤ sigma^2 := by nlinarith [sq_nonneg (sigma-1/2)]
  have hden : (1+t^2)/4 ≤ ‖z‖*‖z+1‖ := by nlinarith only [h0,hp,hsig,sq_nonneg t]
  have hdp : 0 < ‖z‖*‖z+1‖ := by nlinarith only [hden,sq_nonneg t]
  change ‖1/(z*(z+1))‖ ≤ _
  rw [norm_div,norm_one,norm_mul]
  apply (div_le_div_iff₀ hdp (by positivity : 0 < 1+t^2)).mpr
  nlinarith only [hden]

lemma rieszMajorant_integrable : Integrable (fun t:ℝ => 4/(1+t^2)) := by
  simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul (4:ℝ)

lemma continuous_rieszKernel_line {sigma : ℝ} (hs : 1/2 ≤ sigma) :
    Continuous (fun t:ℝ => rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  unfold rieszKernel
  apply continuous_const.div (by fun_prop)
  intro t
  apply mul_ne_zero
  · intro hz
    have h := congrArg Complex.re hz
    simp at h
    linarith
  · intro hz
    have h := congrArg Complex.re hz
    simp at h
    linarith

lemma integrable_rieszKernel_line {sigma : ℝ} (hs : 1/2 ≤ sigma) :
    Integrable (fun t:ℝ => rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)) := by
  apply rieszMajorant_integrable.mono' (continuous_rieszKernel_line hs).aestronglyMeasurable
  exact Filter.Eventually.of_forall (rieszKernel_norm_bound hs)

lemma integral_norm_rieszKernel_line_le {sigma : ℝ} (hs : 1/2 ≤ sigma) :
    (∫ t:ℝ, ‖rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I)‖) ≤ 4*Real.pi := by
  calc
    _ ≤ ∫ t:ℝ, 4/(1+t^2) := integral_mono (integrable_rieszKernel_line hs).norm
      rieszMajorant_integrable (rieszKernel_norm_bound hs)
    _ = _ := by simp only [div_eq_mul_inv,integral_const_mul,integral_univ_inv_one_add_sq]

theorem riesz_mellin_inversion {sigma x : ℝ} (hs : 1/2 ≤ sigma) (hx : 0 < x) :
    mellinInv sigma rieszKernel x = (rieszWeight x:ℂ) := by
  have hsp : 0 < sigma := by linarith
  have he (t:ℝ) : mellin rieszProfile ((sigma:ℂ)+(t:ℂ)*Complex.I) =
      rieszKernel ((sigma:ℂ)+(t:ℂ)*Complex.I) :=
    (hasMellin_rieszProfile (by simpa using hsp)).2
  have hvi : Complex.VerticalIntegrable (mellin rieszProfile) sigma := by
    apply (integrable_rieszKernel_line hs).congr
    exact Filter.Eventually.of_forall (fun t => (he t).symm)
  have h := mellinInv_mellin_eq sigma rieszProfile hx (hasMellin_rieszProfile (by simpa using hsp)).1
    hvi (continuousAt_rieszProfile hx)
  rw [rieszProfile_eq_weight hx] at h
  rw [← h]
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by dsimp only; rw [he t])

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
