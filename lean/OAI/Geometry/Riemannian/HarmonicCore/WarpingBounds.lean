import OAI.Geometry.Riemannian.HarmonicCore.WarpingLimit

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample
def tailBarrier (C J t : ℝ) : ℝ :=
  Real.exp t * (-deriv (b C J) t - 2*C*t^(-(3/2 : ℝ)))

lemma tailBarrier_hasDerivAt {C J t : ℝ} (hJ : 4 ≤ J)
    (ht : (7/10 : ℝ)*J ≤ t) :
    HasDerivAt (tailBarrier C J)
      (Real.exp t * C * t^(-(3/2 : ℝ)) * (-1 + 3/t)) t := by
  have htpos : 0 < t := by linarith
  have hb := b_deriv_hasDerivAt (C := C) (by linarith : 0 < J) t
  have hbd : HasDerivAt (deriv (b C J))
      (-C*t^(-(3/2 : ℝ)) - deriv (b C J) t) t := by
    convert hb using 1
    have heq := b_second_equation (C := C) hJ ht
    rw [b_second_deriv (by linarith : 0 < J)] at heq
    linarith
  have hp := Real.hasDerivAt_rpow_const (p := -(3/2 : ℝ)) (Or.inl htpos.ne')
  have hd := (Real.hasDerivAt_exp t).mul (hbd.neg.sub (hp.const_mul (2*C)))
  convert hd using 1 <;> try rfl
  simp only [Pi.sub_apply, Pi.neg_apply, Real.rpow_sub_one htpos.ne']
  ring

lemma tailBarrier_antitone {C J : ℝ} (hJ : 5 ≤ J) (hC : 0 ≤ C) :
    AntitoneOn (tailBarrier C J) (Ici ((7/10 : ℝ)*J)) := by
  have hJ4 : 4 ≤ J := by linarith
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · apply continuousOn_of_forall_continuousAt
    intro t ht
    exact (tailBarrier_hasDerivAt hJ4 ht).continuousAt
  · intro t ht
    exact (tailBarrier_hasDerivAt hJ4 (le_of_lt (by simpa using ht))).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : (7/10 : ℝ)*J ≤ t := le_of_lt (by simpa using ht)
    rw [(tailBarrier_hasDerivAt hJ4 ht').deriv]
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact mul_nonneg (mul_nonneg (Real.exp_pos t).le hC)
        (Real.rpow_nonneg (by linarith) _)
    · have htpos : 0 < t := by linarith
      have hdiv : 3/t ≤ (1 : ℝ) := (div_le_one htpos).2 (by linarith)
      linarith

lemma b_deriv_transient_bound {C J t : ℝ} (hJ : 5 ≤ J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J) (ht : (7/10 : ℝ)*J ≤ t) :
    |deriv (b C J) t| ≤
      Real.exp ((7/10 : ℝ)*J-t)*(1-a) + 2*C*t^(-(3/2 : ℝ)) := by
  have hJpos : 0 < J := by linarith
  have hu : 0 < (7/10 : ℝ)*J := by linarith
  have hab := tailBarrier_antitone hJ hC (show (7/10 : ℝ)*J ∈ Ici ((7/10 : ℝ)*J) from (by simp only [mem_Ici]; exact le_rfl))
    ht ht
  have hinitial : -deriv (b C J) ((7/10 : ℝ)*J) ≤ 1-a := by
    exact (neg_le_abs _).trans (b_deriv_bounded hJpos hC hm _)
  have hp : 0 ≤ 2*C*((7/10 : ℝ)*J)^(-(3/2 : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg hu.le _)
  unfold tailBarrier at hab
  have hupper : Real.exp t * (-deriv (b C J) t - 2*C*t^(-(3/2 : ℝ))) ≤
      Real.exp ((7/10 : ℝ)*J) * (1-a) := by
    exact hab.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
  have hdivide := (le_div_iff₀ (Real.exp_pos t)).2
    (show (-deriv (b C J) t - 2*C*t^(-(3/2 : ℝ))) * Real.exp t ≤
      Real.exp ((7/10 : ℝ)*J) * (1-a) by nlinarith [hupper])
  rw [abs_of_nonpos (b_deriv_nonpos hJpos hC hm t)]
  rw [Real.exp_sub, div_mul_eq_mul_div]
  linarith [hdivide]

def transientWeight (t : ℝ) : ℝ := t^(3/2 : ℝ)*Real.exp (-t)

lemma transientWeight_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt transientWeight
      (t^(3/2 : ℝ)*Real.exp (-t)*(-1+(3/2 : ℝ)/t)) t := by
  have hp := Real.hasDerivAt_rpow_const (p := (3/2 : ℝ)) (Or.inl ht.ne')
  have he := (hasDerivAt_id t).neg.exp
  convert hp.mul he using 1 <;> try rfl
  simp only [Pi.neg_apply, id_eq, Real.rpow_sub_one ht.ne']
  ring

lemma transientWeight_antitone : AntitoneOn transientWeight (Ici (3/2 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro t ht
    have ht' : (3/2 : ℝ) ≤ t := ht
    exact (transientWeight_hasDerivAt (by linarith : 0 < t)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : (3/2 : ℝ) < t := by simpa using ht
    exact (transientWeight_hasDerivAt (by linarith)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : (3/2 : ℝ) < t := by simpa using ht
    have htpos : 0 < t := by linarith
    rw [(transientWeight_hasDerivAt htpos).deriv]
    apply mul_nonpos_of_nonneg_of_nonpos
    · positivity
    · have hh : (3/2 : ℝ)/t ≤ 1 := (div_le_one htpos).2 ht'.le
      linarith

lemma transient_uniform {J t : ℝ} (hJ : 5 ≤ J) (ht : (4/5 : ℝ)*J ≤ t) :
    t^(3/2 : ℝ)*Real.exp ((7/10 : ℝ)*J-t) ≤
      J^(3/2 : ℝ)*Real.exp (-J/10) := by
  have hx : (3/2 : ℝ) ≤ (4/5 : ℝ)*J := by linarith
  have hab := transientWeight_antitone hx (hx.trans ht) ht
  unfold transientWeight at hab
  have he := mul_le_mul_of_nonneg_left hab (Real.exp_pos ((7/10 : ℝ)*J)).le
  have h0 : Real.exp ((7/10 : ℝ)*J) * Real.exp (-t) =
      Real.exp ((7/10 : ℝ)*J-t) := by rw [← Real.exp_add]; congr 1
  have h1 : Real.exp ((7/10 : ℝ)*J) * Real.exp (-((4/5 : ℝ)*J)) =
      Real.exp (-J/10) := by rw [← Real.exp_add]; congr 1; ring
  have hrearrange : t^(3/2 : ℝ)*Real.exp ((7/10 : ℝ)*J-t) ≤
      ((4/5 : ℝ)*J)^(3/2 : ℝ)*Real.exp (-J/10) := by
    calc
      _ = Real.exp ((7/10 : ℝ)*J) * (t^(3/2 : ℝ)*Real.exp (-t)) := by rw [← h0]; ring
      _ ≤ Real.exp ((7/10 : ℝ)*J) * (((4/5 : ℝ)*J)^(3/2 : ℝ)*Real.exp (-((4/5 : ℝ)*J))) := he
      _ = _ := by rw [mul_left_comm, h1]
  exact hrearrange.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num : 0 ≤ (3/2 : ℝ)))
    (Real.exp_pos _).le)

lemma b_uniform_bounds {C J t : ℝ} (hJ : 5 ≤ J) (hC : 0 ≤ C)
    (hm : 0 ≤ compactLoss C J)
    (htrans : (1-a)*J^(3/2 : ℝ)*Real.exp (-J/10) ≤ C)
    (ht : (4/5 : ℝ)*J ≤ t) :
    |deriv (b C J) t| ≤ 3*C*t^(-(3/2 : ℝ)) ∧
    |deriv (deriv (b C J)) t| ≤ 4*C*t^(-(3/2 : ℝ)) ∧
    0 ≤ b C J t-a ∧ b C J t-a ≤ 5*C*t^(-(1/2 : ℝ)) := by
  have hJpos : 0 < J := by linarith
  have htpos : 0 < t := by linarith
  have ht7 : (7/10 : ℝ)*J ≤ t := by linarith
  have hT := mul_le_mul_of_nonneg_left (transient_uniform hJ ht)
    (show 0 ≤ 1-a by norm_num [a])
  have hT' : t^(3/2 : ℝ)*(Real.exp ((7/10 : ℝ)*J-t)*(1-a)) ≤ C := by
    nlinarith [hT, htrans]
  have hrpow : t^(3/2 : ℝ)*t^(-(3/2 : ℝ)) = 1 := by
    rw [← Real.rpow_add htpos]
    norm_num
  have hpnonneg := Real.rpow_nonneg htpos.le (-(3/2 : ℝ))
  have hsmall : Real.exp ((7/10 : ℝ)*J-t)*(1-a) ≤ C*t^(-(3/2 : ℝ)) := by
    calc
      _ = (t^(3/2 : ℝ)*(Real.exp ((7/10 : ℝ)*J-t)*(1-a)))*t^(-(3/2 : ℝ)) := by
        calc
          _ = (t^(3/2 : ℝ)*t^(-(3/2 : ℝ)))*(Real.exp ((7/10 : ℝ)*J-t)*(1-a)) := by rw [hrpow, one_mul]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hT' hpnonneg
  have hb1 : |deriv (b C J) t| ≤ 3*C*t^(-(3/2 : ℝ)) := by
    have hbound := b_deriv_transient_bound hJ hC hm ht7
    linarith
  refine ⟨hb1, ?_, ?_, ?_⟩
  · have hbeq := b_second_equation (C := C) (by linarith : 4 ≤ J) ht7
    have hbpair := abs_le.mp hb1
    apply abs_le.mpr
    constructor <;> nlinarith [hbpair.1, hbpair.2, mul_nonneg hC hpnonneg]
  · exact sub_nonneg.mpr (b_bounds hJpos hC hm t).1
  · have hbeq := b_first_equation_tail (C := C) (by linarith : 4 ≤ J) ht7
    have hbpair := abs_le.mp hb1
    have hpow : t^(-(3/2 : ℝ)) ≤ t^(-(1/2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hpow hC]

lemma transient_eventually_small (C : ℝ) (hC : 0 < C) :
    ∀ᶠ J : ℝ in atTop, (1-a)*J^(3/2 : ℝ)*Real.exp (-J/10) ≤ C := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3/2 : ℝ) (1/10 : ℝ)
    (by norm_num)).const_mul (1-a)
  have ht' : Tendsto (fun J : ℝ ↦ (1-a)*J^(3/2 : ℝ)*Real.exp (-J/10)) atTop (𝓝 0) := by
    convert ht using 1 <;> try simp
    funext J
    have he : -J/10 = -(1/10 : ℝ)*J := by ring
    rw [he]
    ring_nf
  exact (ht'.eventually_lt_const hC).mono (fun _ h ↦ h.le)

theorem scalar_warping_realization (C : ℝ) (hC : 0 < C) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      4 ≤ J ∧ 0 < compactLoss C J ∧
      ContDiff ℝ ∞ (warping C J) ∧
      (∀ r : ℝ, r ≤ 1 → warping C J r = r) ∧
      (∀ r : ℝ, 0 ≤ r → a ≤ deriv (warping C J) r ∧
        deriv (warping C J) r ≤ 1) ∧
      (∀ r : ℝ, 0 ≤ r → deriv (deriv (warping C J)) r =
        -compactLoss C J * beta r - C * radialDensity J r) ∧
      Tendsto (deriv (warping C J)) atTop (𝓝 a) ∧
      Tendsto (b C J) atTop (𝓝 a) ∧
      (∀ t : ℝ, (7/10 : ℝ) * J ≤ t →
        deriv (deriv (b C J)) t + deriv (b C J) t = -C * t ^ (-(3/2 : ℝ))) ∧
      (∀ t : ℝ, (4/5 : ℝ) * J ≤ t →
        |deriv (b C J) t| ≤ 3*C*t^(-(3/2 : ℝ)) ∧
        |deriv (deriv (b C J)) t| ≤ 4*C*t^(-(3/2 : ℝ)) ∧
        0 ≤ b C J t - a ∧ b C J t - a ≤ 5*C*t^(-(1/2 : ℝ))) := by
  have he := (compactLoss_eventually_pos C hC.le).and
    ((transient_eventually_small C hC).and (eventually_ge_atTop (5 : ℝ)))
  rcases eventually_atTop.1 he with ⟨R, hR⟩
  rcases exists_nat_ge R with ⟨J₀, hJ₀⟩
  refine ⟨J₀, ?_⟩
  intro J hJ
  have hJR : R ≤ (J : ℝ) := hJ₀.trans (by exact_mod_cast hJ)
  rcases hR (J : ℝ) hJR with ⟨hm, htrans, h5⟩
  have h4 : (4 : ℝ) ≤ J := by linarith
  have hpos : (0 : ℝ) < J := by linarith
  refine ⟨by exact_mod_cast h4, hm, warping_smooth hpos, ?_, ?_, ?_, ?_,
    b_tendsto hpos hC.le hm.le, ?_, ?_⟩
  · intro r hr
    exact warping_eq_id_near_zero hr
  · intro r _
    rw [warping_deriv hpos]
    exact ⟨a_le_slope hpos hC.le hm.le r, slope_le_one hpos hC.le hm.le r⟩
  · intro r _
    exact warping_second_deriv hpos r
  · rw [warping_deriv hpos]
    exact slope_tendsto hpos
  · intro t ht
    exact b_second_equation h4 ht
  · intro t ht
    exact b_uniform_bounds h5 hC.le hm.le htrans ht

end HarmonicCounterexample

end

end OAI
