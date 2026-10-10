import OAI.Analysis.Triangular.Certificate.WaveIntervals
import OAI.Analysis.Triangular.Envelope.Basic

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
open Complex

lemma Xwave_pos {k : ℝ} (hk : 0<k) (t : ℝ) : 0<Xwave k t := by
  unfold Xwave
  exact div_pos (by norm_num) (waveDen_pos hk t)
lemma Xwave_square {k : ℝ} (hk : 0<k) (t : ℝ) :
    (k^2+t^2)*Xwave k t=4/3 := by
  unfold Xwave waveDen
  field_simp [ne_of_gt (waveDen_pos hk t)]
lemma normSq_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : normSq (lambda k t)=Xwave k t := by
  unfold lambda
  rw [map_div₀]
  simp only [normSq_apply,add_re,ofReal_re,mul_re,I_re,zero_mul,I_im,ofReal_im,
    mul_zero,sub_zero,add_zero,add_im,mul_im,one_mul,zero_add]
  dsimp [Xwave,waveDen]
  have hb := b_sq
  have hd : k^2+t^2≠0 := ne_of_gt (waveDen_pos hk t)
  field_simp [ne_of_gt b_pos, hd]
  nlinarith [mul_nonneg (sq_nonneg k) (sq_nonneg t)]
lemma norm_lambda {k : ℝ} (hk : 0<k) (t : ℝ) : ‖lambda k t‖=Real.sqrt (Xwave k t) := by
  rw [Complex.norm_def,normSq_lambda hk]
lemma normSq_zeta {k : ℝ} (hk : 0<k) (v t : ℝ) :
    normSq (zeta k v t)=v^2+(4/3-2*k*v)*Xwave k t := by
  unfold zeta
  simp only [normSq_apply,add_re,neg_re,mul_re,ofReal_re,ofReal_im,mul_zero,
    sub_zero,I_re,zero_mul,I_im,one_mul,add_zero,add_im,neg_im,mul_im,zero_add]
  linear_combination Xwave k t * Xwave_square hk t
lemma wavePhase_re (k v t : ℝ) : (I*Real.pi*zeta k v t).re = -Real.pi*(k*Xwave k t-v) := by
  simp [zeta,mul_re,mul_im]
lemma norm_wavePhase {k : ℝ} (hk : 0<k) (v t : ℝ) :
    ‖I*Real.pi*zeta k v t‖=Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t) := by
  rw [norm_mul,norm_mul,norm_I,one_mul,norm_real,Real.norm_eq_abs,
    abs_of_pos Real.pi_pos,Complex.norm_def,normSq_zeta hk]

def jetEnvelope (k v : ℝ) (n : ℤ) (t : ℝ) : ℝ :=
  (1+|D n|+Real.pi*Real.sqrt (v^2+(4/3-2*k*v)*Xwave k t))*
    Real.sqrt (Xwave k t)/Q n*Real.exp (-Real.pi*(k*Xwave k t-v)*n)

def frequencyDecay (k v t : ℝ) : ℝ := Real.pi*(k*Xwave k t-v)

lemma Xwave_antitone {k s t : ℝ} (hk : 0<k) (hs : 0 ≤ s) (hst : s ≤ t) :
    Xwave k t≤Xwave k s := by
  unfold Xwave
  apply div_le_div_of_nonneg_left (by norm_num) (waveDen_pos hk s)
  unfold waveDen
  nlinarith
lemma damping_Xwave_lower (q : Fin 2) {t : ℝ} (ht0 : 0≤t) (ht : t≤5/6) :
    1≤Real.pi*damping q*Xwave (damping q) t := by
  have hx := Xwave_antitone (damping_pos q) ht0 ht
  have hl : 1<3*damping q*Xwave (damping q) (5/6) := by
    fin_cases q <;> norm_num [damping,h,H,Xwave,waveDen]
  have hp := Real.pi_gt_three
  have hq := damping_pos q
  have hxpos := Xwave_pos hq t
  calc
    1 ≤ 3*damping q*Xwave (damping q) (5/6) := hl.le
    _ ≤ 3*damping q*Xwave (damping q) t := mul_le_mul_of_nonneg_left hx (by positivity)
    _ ≤ Real.pi*damping q*Xwave (damping q) t := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp.le hq.le) hxpos.le

lemma jetEnvelope_monotone {q v : Fin 2} {n : ℤ} (hn : 1≤n) (hQ : 0<Q n)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t≤5/6) :
    jetEnvelope (damping q) (damping v) n s ≤jetEnvelope (damping q) (damping v) n t := by
  have ht0 : 0≤t := hs.trans hst
  have hx := Xwave_pos (damping_pos q) t
  have hxy := Xwave_antitone (damping_pos q) hs hst
  have hb := damping_Xwave_lower q ht0 ht
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hδ : 1≤(Real.pi*damping q*n)*Xwave (damping q) t := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (le_of_lt hx),damping_pos q,Real.pi_pos]
  have hh := Envelope.sqrt_exp_antitone (a:=1+|D n|) (p:=Real.pi)
    (c:=(damping v)^2) (d:=4/3-2*damping q*damping v) hx hxy
    (by positivity) Real.pi_pos.le (sq_nonneg _) hδ
  have he (x : ℝ) : Real.exp (-Real.pi*(damping q*x-damping v)*n) =
      Real.exp (Real.pi*damping v*n)*Real.exp (-(Real.pi*damping q*n)*x) := by
    rw [←Real.exp_add]
    congr 1
    ring
  unfold jetEnvelope
  rw [he,he]
  convert! mul_le_mul_of_nonneg_left hh (show 0 ≤ Real.exp (Real.pi*damping v*n)/Q n from
    div_nonneg (Real.exp_pos _).le hQ.le) using 1 <;> ring
end AtomicTriangular.Construction
end

end OAI
