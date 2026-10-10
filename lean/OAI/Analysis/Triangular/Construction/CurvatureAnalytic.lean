import OAI.Analysis.Triangular.Envelope.TailEnvelopeSeries
import OAI.Analysis.Triangular.Construction.CurvatureBoxes
import OAI.Analysis.Triangular.Construction.AtomicCurvature

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma taylorPhase_re_nonpos (q br : Fin 2) {t : ℝ} (ht : |t|≤5/6) :
    (taylorPhase q br t).re≤0 := by
  fin_cases br
  · simp only [taylorPhase,↓reduceIte,sub_re,mul_re,mul_im,I_re,I_im,
      ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,zero_sub]
    have hh : h≤damping q := by fin_cases q <;> norm_num [damping,h,H]
    exact neg_nonpos.mpr (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hh))
  · change (I*Real.pi*zeta (damping q) h t).re≤0
    rw [wavePhase_re]
    have hh := (frequencyDecay_pos q 0 ht).le
    change 0≤Real.pi*(damping q*Xwave (damping q) t-h) at hh
    nlinarith

lemma curvatureWave_nonneg (q br : Fin 2) (s t : ℝ) : 0≤curvatureWave q br s t := by
  unfold curvatureWave; positivity
lemma curvatureWave_antitone (q br : Fin 2) {s u t : ℝ} (ht : |t|≤5/6) (hsu : s≤ u) :
    curvatureWave q br u t≤curvatureWave q br s t := by
  unfold curvatureWave
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsu (taylorPhase_re_nonpos q br ht))
lemma curvatureWave_direct (q : Fin 2) (s t : ℝ) :
    curvatureWave q 0 s t = Real.pi^2*(t^2+(damping q-h)^2)*Real.exp (-Real.pi*(damping q-h)*s) := by
  unfold curvatureWave
  rw [←Complex.normSq_eq_norm_sq]
  simp only [taylorPhase,taylorAmplitude,Fin.val_zero,↓reduceIte,norm_one,mul_one,
    Complex.normSq_apply,sub_re,sub_im,mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,
    zero_mul,mul_zero,one_mul,sub_zero,zero_sub,zero_add]
  ring_nf
lemma curvatureWave_transformed (q : Fin 2) (s t : ℝ) :
    curvatureWave q 1 s t = Real.pi^2*(h^2+(4/3-2*damping q*h)*Xwave (damping q) t)*
      Real.sqrt (Xwave (damping q) t)*Real.exp (-Real.pi*(damping q*Xwave (damping q) t-h)*s) := by
  simp only [curvatureWave,taylorPhase,taylorAmplitude,Fin.val_one,Nat.one_ne_zero,↓reduceIte]
  rw [norm_wavePhase (damping_pos q),norm_lambda (damping_pos q),wavePhase_re,mul_pow,
    Real.sq_sqrt]
  rw [←normSq_zeta (damping_pos q)]
  exact normSq_nonneg _
lemma curvatureWave_even (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s (-t)=curvatureWave q br s t := by
  fin_cases br
  · simp [curvatureWave_direct]
  · simp [curvatureWave_transformed,Xwave,waveDen]
lemma curvatureWave_abs (q br : Fin 2) (s t : ℝ) :
    curvatureWave q br s |t|=curvatureWave q br s t := by
  rcases le_total 0 t with ht|ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht,curvatureWave_even]
lemma curvature_tail_direct {s t : ℝ} (ht : |t|≤5/6) :
    curvatureWave 0 0 s t≤curvatureWave 0 0 s (5/6) := by
  rw [curvatureWave_direct,curvatureWave_direct]
  norm_num [damping]
  have hh : t^2≤(5/6:ℝ)^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by norm_num)).mpr ht
  nlinarith [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hh)]
lemma curvature_tail_zero {t : ℝ} (_ht : |t|≤5/6) :
    curvatureWave 0 1 0 t≤curvatureWave 0 1 0 0 := by
  rw [curvatureWave_transformed,curvatureWave_transformed]
  simp only [mul_zero,Real.exp_zero,mul_one]
  have hx : Xwave (damping 0) t≤Xwave (damping 0) 0 := by
    rw [←show Xwave (damping 0) |t|=Xwave (damping 0) t by simp [Xwave,waveDen]]
    exact Xwave_antitone (damping_pos 0) le_rfl (abs_nonneg t)
  have h1 : 0≤4/3-2*damping 0*h := by norm_num [damping,h]
  apply mul_le_mul (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hx h1) _) (sq_nonneg _)) (Real.sqrt_le_sqrt hx) (Real.sqrt_nonneg _)
  exact mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (mul_nonneg h1 (Xwave_pos (damping_pos 0) 0).le))
lemma curvature_tail_positive {s t : ℝ} (hs : 1 ≤ s) (ht : |t| ≤ 5/6) :
    curvatureWave 0 1 s t≤curvatureWave 0 1 s (5/6) := by
  rw [←curvatureWave_abs 0 1 s t]
  rw [curvatureWave_transformed,curvatureWave_transformed]
  have hx := Xwave_pos (damping_pos 0) (5/6)
  have hxy := Xwave_antitone (damping_pos 0) (abs_nonneg t) ht
  have hbase : (3/2:ℝ)≤Real.pi*h*Xwave h (5/6) := by
    have hp := Real.pi_gt_three
    norm_num [Xwave,waveDen,h] at *
    linarith
  have hb : (3/2:ℝ)≤(Real.pi*damping 0*s)*Xwave (damping 0) (5/6) := by
    change (3/2:ℝ)≤(Real.pi*h*s)*Xwave h (5/6)
    have hh : 0 ≤ h := by norm_num [h]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg Real.pi_pos.le (mul_nonneg hh hx.le))]
  have hh := Envelope.linear_sqrt_exp_antitone hx hxy (sq_nonneg h)
    (show 0≤4/3-2*damping 0*h by norm_num [damping,h]) hb
  have he (x : ℝ) : Real.exp (-Real.pi*(damping 0*x-h)*s) =
      Real.exp (Real.pi*h*s)*Real.exp (-(Real.pi*damping 0*s)*x) := by
    rw [←Real.exp_add]; congr 1; ring
  rw [he,he]
  convert mul_le_mul_of_nonneg_left hh (show 0≤Real.pi^2*Real.exp (Real.pi*h*s) by positivity) using 1 <;> first | rfl | ring
end AtomicTriangular.Construction
end

end OAI
