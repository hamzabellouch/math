import OAI.Geometry.HarmonicGrowth.Realization

namespace OAI

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace HarmonicCounterexample.LinearODE
open Set
/-- Exact integrated scalar damping for the genuine positive diagonal-leg
solution, allowing its incoming logarithmic derivative to differ from the
limiting dwell root. This retains the finite initial-discrepancy cost. -/
theorem actual_scalar_baseline_integrated {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ d γ M T : ℝ}
    (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hγ : 0 < γ) (hT : 0 ≤ T)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t)
    (hF : ∀ t ∈ Icc 0 T,|A t-p t*d-d^2| ≤ M) :
    (∫ t in (0:ℝ)..T,|scalarBaseline A p θ t-d|) ≤ (|θ-d|+M*T)/γ := by
  let v := scalarBaseline A p θ
  have hder (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt (fun s => v s-d) ((A t-p t*d-d^2)-(p t+v t+d)*(v t-d)) t := by
    apply ((actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht.1).sub_const d).congr_deriv
    dsimp only [v]; ring
  have he (t : ℝ) (ht : t ∈ Icc 0 T) :
      ⟪v t-d,(A t-p t*d-d^2)-(p t+v t+d)*(v t-d)⟫_ℝ ≤
        -γ*‖v t-d‖^2+M*‖v t-d‖ := by
    have hv := (actual_scalar_baseline_positive hA hp hMA hMp hAn hpn hAp hθ ht.1).2
    change 0 ≤ v t at hv
    have hc : γ ≤ p t+v t+d := by linarith [hpl t ht]
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (v t-d))
    have hf : (v t-d)*(A t-p t*d-d^2) ≤ M*|v t-d| := by
      calc
        _ ≤ |(v t-d)*(A t-p t*d-d^2)| := le_abs_self _
        _ = |v t-d| * |A t-p t*d-d^2| := abs_mul _ _
        _ ≤ |v t-d| * M := mul_le_mul_of_nonneg_left (hF t ht) (abs_nonneg _)
        _ = _ := mul_comm _ _
    simp only [RCLike.inner_apply,conj_trivial,Real.norm_eq_abs,sq_abs]
    nlinarith
  have hz (t : ℝ) (ht : t ∈ Icc 0 T) (h : v t-d=0) :
      ‖(A t-p t*d-d^2)-(p t+v t+d)*(v t-d)‖ ≤ M := by
    simpa only [h,mul_zero,sub_zero,Real.norm_eq_abs] using hF t ht
  have hh := dissipative_integral_on (r := fun _ => M) hT hder continuousOn_const he hz
  simp only [Real.norm_eq_abs,v,scalarBaseline_init,intervalIntegral.integral_const,
    sub_zero,smul_eq_mul] at hh
  apply (le_div_iff₀ hγ).2
  nlinarith [abs_nonneg (scalarBaseline A p θ T-d)]

/-- The logarithm of the ACTUAL positive scalar value is the integral of its
actual baseline. This is the bridge from Riccati estimates to diagonal growth. -/
lemma actual_scalar_log_value {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ T : ℝ}
    (hθ : 0 ≤ θ) (hT : 0 ≤ T) :
    Real.log (scalarPhase A p 1 θ T).1=∫ t in (0:ℝ)..T,scalarBaseline A p θ t := by
  have hn (t : ℝ) (ht : 0 ≤ t) : (scalarPhase A p 1 θ t).1 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (actual_scalar_baseline_positive hA hp hMA hMp hAn hpn hAp hθ ht).1)
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt (fun s => Real.log (scalarPhase A p 1 θ s).1) (scalarBaseline A p θ t) t := by
    exact (scalarPhase_value_deriv hA hp hMA hMp hAn hpn 1 θ t).log (hn t ht.1)
  have hc : ContinuousOn (scalarBaseline A p θ) (Icc 0 T) := fun t ht =>
    (actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht.1).continuousAt.continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hT] using ht))
    (hc.intervalIntegrable_of_Icc hT)
  simpa only [scalarPhase_init,Real.log_one,sub_zero] using hh.symm

/-- Genuine logarithmic growth of the diagonal multiplier. Unlike an
unproved asymptotic symbol this bound holds for every finite dwell length. -/
theorem actual_scalar_diagonal_growth {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ d γ M T : ℝ}
    (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hγ : 0 < γ) (hT : 0 ≤ T)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t)
    (hF : ∀ t ∈ Icc 0 T,|A t-p t*d-d^2| ≤ M) :
    |Real.log (scalarU A p T+θ*scalarV A p T)-d*T| ≤ (|θ-d|+M*T)/γ := by
  have hy := scalarPhase_linear hA hp hMA hMp hAn hpn 1 θ T
  simp only [one_mul] at hy
  rw [← hy,actual_scalar_log_value hA hp hMA hMp hAn hpn hAp hθ hT]
  have hc : ContinuousOn (scalarBaseline A p θ) (Icc 0 T) := fun t ht =>
    (actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht.1).continuousAt.continuousWithinAt
  have he : (∫ t in (0:ℝ)..T,scalarBaseline A p θ t)-d*T=
      ∫ t in (0:ℝ)..T,scalarBaseline A p θ t-d := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc hT) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm d T]
  rw [he]
  have hh := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun t => scalarBaseline A p θ t-d) hT
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans (actual_scalar_baseline_integrated hA hp hMA hMp hAn hpn hAp hθ hd hγ hT hpl hF)

end HarmonicCounterexample.LinearODE

end

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace HarmonicCounterexample.LinearODE
open Set
/-- Integrated damping with the actual time-dependent forcing. Rise/fall
costs need not be artificially small; only their relative duration matters. -/
theorem actual_scalar_variable_integrated {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ d γ T : ℝ}
    (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hγ : 0 < γ) (hT : 0 ≤ T)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t) :
    (∫ t in (0:ℝ)..T,|scalarBaseline A p θ t-d|) ≤
      (|θ-d|+∫ t in (0:ℝ)..T,|A t-p t*d-d^2|)/γ := by
  let v := scalarBaseline A p θ
  let r := fun t => |A t-p t*d-d^2|
  have hder (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt (fun s => v s-d) ((A t-p t*d-d^2)-(p t+v t+d)*(v t-d)) t := by
    apply ((actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht.1).sub_const d).congr_deriv
    dsimp only [v];ring
  have he (t : ℝ) (ht : t ∈ Icc 0 T) :
      ⟪v t-d,(A t-p t*d-d^2)-(p t+v t+d)*(v t-d)⟫_ℝ ≤
        -γ*‖v t-d‖^2+r t*‖v t-d‖ := by
    have hv := (actual_scalar_baseline_positive hA hp hMA hMp hAn hpn hAp hθ ht.1).2
    change 0 ≤ v t at hv
    have hc : γ ≤ p t+v t+d := by linarith [hpl t ht]
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (v t-d))
    have hf : (v t-d)*(A t-p t*d-d^2) ≤ r t*|v t-d| := by
      calc
        _ ≤ |(v t-d)*(A t-p t*d-d^2)| := le_abs_self _
        _ = _ := by rw [abs_mul];exact mul_comm _ _
    simp only [RCLike.inner_apply,conj_trivial,Real.norm_eq_abs,sq_abs]
    nlinarith
  have hz (t : ℝ) (_ : t ∈ Icc 0 T) (h : v t-d=0) :
      ‖(A t-p t*d-d^2)-(p t+v t+d)*(v t-d)‖ ≤ r t := by
    simp only [h,mul_zero,sub_zero,Real.norm_eq_abs,r,le_refl]
  have hr : Continuous r := ((hA.sub (hp.mul continuous_const)).sub continuous_const).abs
  have hh := dissipative_integral_on hT hder hr.continuousOn he hz
  simp only [Real.norm_eq_abs,v,scalarBaseline_init] at hh
  apply (le_div_iff₀ hγ).2
  nlinarith [abs_nonneg (scalarBaseline A p θ T-d)]

/-- Finite complete-leg logarithmic error, with its exact forcing integral. -/
theorem actual_scalar_variable_growth {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p)
    {MA Mp : ℝ} (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,|A t| ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ A t) {θ d γ T : ℝ}
    (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hγ : 0 < γ) (hT : 0 ≤ T)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t) :
    |Real.log (scalarU A p T+θ*scalarV A p T)-d*T| ≤
      (|θ-d|+∫ t in (0:ℝ)..T,|A t-p t*d-d^2|)/γ := by
  have hy := scalarPhase_linear hA hp hMA hMp hAn hpn 1 θ T
  simp only [one_mul] at hy
  rw [←hy,actual_scalar_log_value hA hp hMA hMp hAn hpn hAp hθ hT]
  have hc : ContinuousOn (scalarBaseline A p θ) (Icc 0 T) := fun t ht =>
    (actual_scalar_baseline_deriv hA hp hMA hMp hAn hpn hAp hθ ht.1).continuousAt.continuousWithinAt
  have he : (∫ t in (0:ℝ)..T,scalarBaseline A p θ t)-d*T=
      ∫ t in (0:ℝ)..T,scalarBaseline A p θ t-d := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc hT) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm d T]
  rw [he]
  have hh := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=fun t => scalarBaseline A p θ t-d) hT
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans (actual_scalar_variable_integrated hA hp hMA hMp hAn hpn hAp hθ hd hγ hT hpl)
end HarmonicCounterexample.LinearODE

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace HarmonicCounterexample.LinearODE
/-- Complete-leg forcing estimate. The two short transition/rest pieces cost
only their true total duration; the long dwell uses its separate small bound. -/
lemma integral_three_piece_bound {f : ℝ → ℝ} (hf : Continuous f)
    {T L C ε : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hbound : ∀ t ∈ Icc 0 (3*T+L),f t ≤ C)
    (hsmall : ∀ t ∈ Icc T (T+L),f t ≤ ε) :
    (∫ t in (0:ℝ)..3*T+L,f t) ≤ 3*C*T+ε*L := by
  have h1 := intervalIntegral.integral_mono_on (μ:=volume) hT (hf.intervalIntegrable 0 T) intervalIntegrable_const
    (fun t ht => hbound t ⟨ht.1,by linarith [ht.2]⟩)
  have h2 := intervalIntegral.integral_mono_on (μ:=volume) (show T ≤ T+L by linarith)
    (hf.intervalIntegrable T (T+L)) intervalIntegrable_const hsmall
  have h3 := intervalIntegral.integral_mono_on (μ:=volume) (show T+L ≤ 3*T+L by linarith)
    (hf.intervalIntegrable (T+L) (3*T+L)) intervalIntegrable_const
    (fun t ht => hbound t ⟨by linarith [ht.1],ht.2⟩)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 T)
    (hf.intervalIntegrable T (T+L))
  have he' := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable 0 (T+L))
    (hf.intervalIntegrable (T+L) (3*T+L))
  simp only [intervalIntegral.integral_const,smul_eq_mul,sub_zero] at h1 h2 h3
  linarith

/-- True scalar U+theta V has the dwell-normalized root exponent whenever
only the DWELL forcing tends to zero and the actual transition fraction does.
No uniform smallness on the short rise/fall/rest portions is asserted. -/
theorem scalar_complete_leg_limit (A p : ℕ → ℝ → ℝ) (T L : ℕ → ℝ)
    {θ d γ MA Mp C : ℝ}
    (hA : ∀ j,Continuous (A j)) (hp : ∀ j,Continuous (p j))
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ j t,|A j t| ≤ MA) (hpn : ∀ j t,|p j t| ≤ Mp)
    (hAp : ∀ j t,0 ≤ t → 0 ≤ A j t)
    (hθ : 0 ≤ θ) (hd : 0 ≤ d) (hγ : 0 < γ)
    (hT : ∀ j,0 ≤ T j) (hL : ∀ j,0 < L j)
    (hLtop : Tendsto L atTop atTop)
    (hratio : Tendsto (fun j => T j/L j) atTop (𝓝 0))
    (hpl : ∀ᶠ j in atTop,∀ t ∈ Icc 0 (3*T j+L j),γ ≤ p j t)
    (hbound : ∀ j,∀ t ∈ Icc 0 (3*T j+L j),|A j t-p j t*d-d^2| ≤ C)
    (hsmall : ∀ ε>0,∀ᶠ j in atTop,∀ t ∈ Icc (T j) (T j+L j),|A j t-p j t*d-d^2| ≤ ε) :
    Tendsto (fun j => Real.log (scalarU (A j) (p j) (3*T j+L j)+
      θ*scalarV (A j) (p j) (3*T j+L j))/L j) atTop (𝓝 d) := by
  have hInv : Tendsto (fun j => (L j)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hLtop
  have hrem : Tendsto (fun j => |θ-d|/(γ*L j)+(3*C/γ+3*d)*(T j/L j)) atTop (𝓝 0) := by
    have hh := ((hInv.const_mul (|θ-d|/γ)).add (hratio.const_mul (3*C/γ+3*d)))
    simp only [mul_zero,add_zero] at hh
    convert hh using 1
    ext j;ring
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hs := hsmall (ε*γ/2) (by positivity)
  have he := hrem.eventually (eventually_lt_nhds (show (0:ℝ)<ε/2 by positivity))
  obtain ⟨N,hN⟩ := eventually_atTop.1 (hpl.and (hs.and he))
  refine ⟨N,fun j hj => ?_⟩
  obtain ⟨hjpl,hjs,hjr⟩ := hN j hj
  have hlen : 0 ≤ 3*T j+L j := by linarith [hT j,hL j]
  have hh := actual_scalar_variable_growth (hA j) (hp j) hMA hMp
    (hAn j) (hpn j) (hAp j) hθ hd hγ hlen hjpl
  have hi := integral_three_piece_bound
    (((hA j).sub ((hp j).mul continuous_const)).sub continuous_const).abs
    (hT j) (hL j).le (hbound j) hjs
  let v := Real.log (scalarU (A j) (p j) (3*T j+L j)+θ*scalarV (A j) (p j) (3*T j+L j))
  change |v-d*(3*T j+L j)| ≤ _ at hh
  have hhh : |v-d*(3*T j+L j)| ≤ (|θ-d|+(3*C*T j+(ε*γ/2)*L j))/γ :=
    hh.trans (div_le_div_of_nonneg_right (add_le_add_right hi |θ-d|) hγ.le)
  have hv : |v-d*L j| ≤ |v-d*(3*T j+L j)|+3*d*T j := by
    have heq : v-d*L j=(v-d*(3*T j+L j))+3*d*T j := by ring
    rw [heq]
    exact (abs_add_le _ _).trans_eq (by rw [abs_of_nonneg (by exact mul_nonneg (mul_nonneg (by norm_num) hd) (hT j) : 0 ≤ 3*d*T j)])
  rw [Real.dist_eq]
  change |v/L j-d| < ε
  have heq : |v/L j-d|=|v-d*L j|/L j := by
    calc
      _ = |(v-d*L j)/L j| := congrArg abs (by field_simp [ne_of_gt (hL j)])
      _ = _ := by rw [abs_div,abs_of_pos (hL j)]
  rw [heq]
  apply lt_of_le_of_lt (div_le_div_of_nonneg_right (hv.trans (add_le_add_left hhh _)) (hL j).le)
  have heq' : ((|θ-d|+(3*C*T j+(ε*γ/2)*L j))/γ+3*d*T j)/L j=
      (|θ-d|/(γ*L j)+(3*C/γ+3*d)*(T j/L j))+ε/2 := by
    field_simp [ne_of_gt hγ,ne_of_gt (hL j)];ring
  rw [heq'];linarith
end HarmonicCounterexample.LinearODE

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace HarmonicCounterexample.Schedule
lemma dwell_atTop_limit : Tendsto dwell atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : 7 ≠ 0)).comp
    (tendsto_atTop_mono (fun j : ℕ => show (j:ℝ) ≤ (j:ℝ)+1 by linarith)
      tendsto_natCast_atTop_atTop)
lemma pulse_dwell_limit : Tendsto (fun j => pulse j/dwell j) atTop (𝓝 0) := by
  have h : Tendsto (fun j : ℕ => ((j:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_mono (fun j : ℕ => show (j:ℝ) ≤ (j:ℝ)+1 by linarith) tendsto_natCast_atTop_atTop)
  convert h using 1
  ext j
  have hj : (j:ℝ)+1 ≠ 0 := by positivity
  dsimp [pulse,dwell]
  field_simp
end HarmonicCounterexample.Schedule

end

noncomputable section


namespace HarmonicCounterexample.LinearODE
open Set Filter Schedule Pulses AngularStream FiniteControl.SmoothWord
open HarmonicCounterexample.Transmission HarmonicCounterexample.FiniteControl
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {ξ κ : Type*} [Fintype ξ] [Nonempty ξ] [Nonempty κ]
  {E : ξ → Type*} {ι : ξ → Type*}
  [∀ b,NormedAddCommGroup (E b)] [∀ b,InnerProductSpace ℝ (E b)] [∀ b,FiniteDimensional ℝ (E b)]
  [∀ b,Fintype (ι b)] [∀ b,DecidableEq (ι b)] [∀ b,Nontrivial (ι b)]
variable {S : PulseSystem E ι κ} (G : HistoryGeometry S) {n : ℕ} [NeZero n]

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
lemma HistoryGeometry.legLambda_dwell (d₀ : ∀ b,ι b → ℝ) {j0 j : ℕ} (hj : j0 ≤ j)
    (b : ξ) (i : ι b) {t : ℝ} (ht : t ∈ Icc (pulse j) (pulse j+dwell j)) :
    G.legLambda d₀ j0 b i (time j+pulse j+t)=
      G.α (time j+pulse j+t)*(G.qstar^S.r*S.B b+
       (G.qstar^S.r-G.qstar^(S.r-1))*d₀ b i) := by
  unfold HistoryGeometry.legLambda base
  rw [Pulses.profile_dwell (by simp) (by simp) hj
    (by linarith [ht.1]) (by linarith [ht.2])]

omit [Fintype ξ] [Nonempty ξ] [Nonempty κ] [∀ b,Nontrivial (ι b)] in
/-- Exact root exponent of every true complete-leg diagonal entry. The pulse,
ramp, fall and final round rest are not discarded in the solution definition. -/
theorem HistoryGeometry.leg_root_limit (slot : Fin n → κ) (d₀ : ∀ b,ι b → ℝ)
    (hd₀ : ∀ b,orthogonalMatrix (S.basis b) (G.D₀ b)=Matrix.diagonal (d₀ b))
    (j0 : ℕ) (b : ξ) (i : ι b) {d : ℝ} (hd : 0 ≤ d)
    (hroot : d^2+S.p₀*d=S.β b*(G.qstar^S.r*S.B b+
        (G.qstar^S.r-G.qstar^(S.r-1))*d₀ b i)) :
    Tendsto (fun j => Real.log ((G.legU d₀ j0 j b+S.θ b • G.legV d₀ j0 j b) i i)/dwell j)
      atTop (𝓝 d) := by
  obtain ⟨N,hN,hc,hb,hp⟩ := G.legLambda_properties slot d₀ hd₀ j0 b
  let A : ℕ → ℝ → ℝ := fun j t => G.legLambda d₀ j0 b i (time j+pulse j+t)
  let p : ℕ → ℝ → ℝ := fun j t => G.drift (time j+pulse j+t)
  have hlow : ∀ᶠ j in atTop,∀ t ∈ Icc 0 (3*pulse j+dwell j),S.γ ≤ p j t := by
    obtain ⟨T,hT⟩ := eventually_atTop.1 G.driftLower
    filter_upwards [time_atTop.eventually_ge_atTop T] with j hj t ht
    apply hT
    linarith [pulse_pos j,ht.1]
  have hbound : ∀ j,∀ t ∈ Icc 0 (3*pulse j+dwell j),
      |A j t-p j t*d-d^2| ≤ N i+G.Mp*|d|+|d^2| := by
    intro j t _
    calc
      _ ≤ |A j t-p j t*d|+|d^2| := abs_sub _ _
      _ ≤ |A j t|+|p j t*d|+|d^2| := add_le_add_left (abs_sub _ _) _
      _ ≤ N i+G.Mp*|d|+|d^2| := by
        rw [abs_mul]
        exact add_le_add_left (add_le_add (hb i _) (mul_le_mul_of_nonneg_right (G.driftBound _) (abs_nonneg _))) _
  let W : ℝ := G.qstar^S.r*S.B b+(G.qstar^S.r-G.qstar^(S.r-1))*d₀ b i
  have hf : Tendsto (fun t => |G.α t*W-G.drift t*d-d^2|) atTop (𝓝 0) := by
    have hh := ((((G.αlimit b).mul_const W).sub (G.driftLimit.mul_const d)).sub_const (d^2)).abs
    have he : |S.β b*W-S.p₀*d-d^2|=0 := by
      rw [abs_eq_zero];dsimp [W] at *;linarith [hroot]
    simpa only [he] using hh
  have hsmall : ∀ ε>0,∀ᶠ j in atTop,∀ t ∈ Icc (pulse j) (pulse j+dwell j),
      |A j t-p j t*d-d^2| ≤ ε := by
    intro ε hε
    obtain ⟨T,hT⟩ := eventually_atTop.1 (hf.eventually (eventually_lt_nhds hε))
    filter_upwards [time_atTop.eventually_ge_atTop T,eventually_ge_atTop j0] with j hj hj0 t ht
    have he := G.legLambda_dwell d₀ hj0 b i ht
    dsimp [A,p]
    rw [he]
    exact (hT _ (by linarith [pulse_pos j,ht.1])).le
  have hh := scalar_complete_leg_limit A p pulse dwell
    (fun j => (hc i).comp (continuous_const.add continuous_id))
    (fun j => G.driftContinuous.comp (continuous_const.add continuous_id))
    (hN i) G.Mpnonneg (fun _ _ => hb i _) (fun _ _ => G.driftBound _)
    (fun _ _ _ => hp i _) (S.hθ b).le hd S.hγ
    (fun j => (pulse_pos j).le) dwell_pos dwell_atTop_limit pulse_dwell_limit
    hlow hbound hsmall
  convert hh using 1
  ext j
  simp only [HistoryGeometry.legU,HistoryGeometry.legV,Matrix.add_apply,Matrix.smul_apply,
    Matrix.diagonal_apply_eq,smul_eq_mul]
  have he : time (j+1)-(time j+pulse j)=3*pulse j+dwell j := by rw [time_succ];ring
  rw [he]
end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Schedule LinearODE Pulses
open scoped Topology BigOperators
variable {L:ℕ} {target:∀l:Fin L,Matrix.SpecialLinearGroup (Index l.val) ℝ}
namespace Stream
variable (F:Stream L target)

def legMatrix (j:ℕ) (l:Fin L) : Matrix (Index l.val) (Index l.val) ℝ :=
  (geometry L).legU (fun l=>d0 l.val) F.j0 j l+
    theta l.val • (geometry L).legV (fun l=>d0 l.val) F.j0 j l

def legDiagonal (j:ℕ) (l:Fin L) (i:Index l.val) : ℝ := F.legMatrix j l i i

lemma leg_diagonal (j:ℕ) (l:Fin L) : F.legMatrix j l=Matrix.diagonal (F.legDiagonal j l) := by
  classical
  ext i k
  by_cases h:i=k
  · subst k;simp only [Matrix.diagonal_apply_eq,legDiagonal]
  · simp only [legMatrix,HistoryGeometry.legU,HistoryGeometry.legV,
      Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply_ne _ h,smul_eq_mul,mul_zero,add_zero]

lemma leg_positive (j:ℕ) (l:Fin L) (i:Index l.val) : 0<F.legDiagonal j l i := by
  obtain ⟨D,hD,hp,_⟩ := (geometry L).leg_normalizer F.word.slot (fun l=>d0 l.val)
    (fun l=>by convert Dround_diagonal l.val using 1;simp only [geometry,system]) F.j0 j l
  rw [hD] at hp
  exact hp i

lemma leg_limit (l:Fin L) (i:Index l.val) :
    Tendsto (fun j=>Real.log (F.legDiagonal j l i)/dwell j) atTop (𝓝 (root l.val i)) := by
  apply (geometry L).leg_root_limit F.word.slot (fun l=>d0 l.val)
    (fun l=>by convert Dround_diagonal l.val using 1;simp only [geometry,system])
    F.j0 l i (root_pos l.val i).le
  change (root l.val i)^2+14*root l.val i=lambda l.val i
  nlinarith [root_eq l.val i]

def slip (j:ℕ) (l:Fin L) : ℝ :=
  if h:F.j0≤j then (F.period j h l).choose else 1

lemma slip_bounds (j:ℕ) (l:Fin L) : F.slip j l∈Ioo (1/2:ℝ) (3/2) := by
  unfold slip
  split_ifs with h
  · exact (F.period j h l).choose_spec.1
  · norm_num

def factor (j:ℕ) (l:Fin L) : ℝ :=
  Real.exp (∫t in time j..time j+pulse j,(geometry L).baseline j l t)*F.slip j l

lemma factor_positive (j:ℕ) (l:Fin L) : 0<F.factor j l :=
  mul_pos (Real.exp_pos _) (lt_trans (by norm_num) (F.slip_bounds j l).1)

lemma period_factor {j:ℕ} (hj:F.j0≤j) (l:Fin L) :
    (geometry L).transmission F.word.slot F.s F.j0 j l=
      F.factor j l • (F.legMatrix j l*(target l:Matrix _ _ ℝ)) := by
  unfold factor slip
  rw [dite_eq_left hj]
  exact (F.period j hj l).choose_spec.2

lemma baseline_cost (j:ℕ) (l:Fin L) :
    |∫t in time j..time j+pulse j,(geometry L).baseline j l t|≤
      (theta l.val+(|B l.val|+|theta l.val|)/10*(30+beta))*pulse j := by
  have hclose (t:ℝ) : |alpha t-beta|≤30+beta := by
    have h := abs_sub (alpha t) beta
    rw [abs_of_pos beta_pos] at h
    linarith [alpha_bound t]
  have hpclose (t:ℝ) : |drift t-14|≤30+beta := by
    have h := abs_sub (drift t) (14:ℝ)
    rw [abs_of_pos (by norm_num : (0:ℝ)<14)] at h
    linarith [(drift_bounds t).2,beta_pos]
  have hb := actual_baseline_log_cost (α:=fun t=>alpha (time j+t))
    (p:=fun t=>drift (time j+t))
    (alpha_smooth.continuous.comp (continuous_const.add continuous_id))
    (drift_smooth.continuous.comp (continuous_const.add continuous_id))
    (M:=2) (Mp:=14) (B:=B l.val) (β:=beta) (p₀:=14) (θ:=theta l.val) (γ:=10)
    (δ:=30+beta) (T:=pulse j) (by norm_num) (by norm_num) (theta_pos l.val).le
    (by norm_num) (by linarith [beta_pos]) (pulse_pos j).le
    (fun t=>alpha_bound _) (fun t=>(drift_bounds _).2)
    (fun t _=>mul_nonneg (alpha_pos _).le (B_pos l.val).le) (theta_root l.val)
    (fun t _=>hclose _) (fun t _=>hpclose _) (fun t _=>(drift_bounds _).1)
  have he : (∫t in time j..time j+pulse j,(geometry L).baseline j l t)=
      ∫t in (0:ℝ)..pulse j,scalarBaseline (fun u=>alpha (time j+u)*B l.val)
        (fun u=>drift (time j+u)) (theta l.val) t := by
    calc
      _ = ∫t in (0:ℝ)..pulse j,(geometry L).baseline j l (time j+t) := by
        rw [intervalIntegral.integral_comp_add_left];simp only [add_zero]
      _ = _ := ?_
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (pulse_pos j).le] at ht
    simp only [HistoryGeometry.baseline,geometry,system,add_sub_cancel_left,max_eq_right ht.1]
  rw [he]
  exact hb

lemma factor_log_bound (l:Fin L) : ∃C:ℝ,∀ᶠ j in atTop,|Real.log (F.factor j l)|≤C*pulse j := by
  let V:=theta l.val+(|B l.val|+|theta l.val|)/10*(30+beta)
  refine ⟨V+Real.log 2,?_⟩
  filter_upwards [pulse_atTop_limit.eventually_ge_atTop 1] with j hj
  have h := (lifted_target_log (F.slip_bounds j l) (baseline_cost j l)).2
  change |Real.log (F.factor j l)|≤V*pulse j+Real.log 2 at h
  exact h.trans (by nlinarith [Real.log_nonneg (by norm_num : (1:ℝ)≤2)])

end Stream
end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Schedule LinearODE Cycling Pulses
open scoped Topology BigOperators InnerProductSpace

abbrev SelectedIndex (l:Fin L) := Fin (selectionCount l)

def selectionEquiv (l:Fin L) : SelectedIndex l ≃ {i//i∈selected l} :=
  (Finset.equivFinOfCardEq (selected_card l)).symm

def selectedIndex (l:Fin L) (i:SelectedIndex l) : Index l.val := (selectionEquiv l i).val

lemma selectedIndex_injective (l:Fin L) : Function.Injective (selectedIndex l) :=
  Subtype.val_injective.comp (selectionEquiv l).injective

def cyclePermutation (l:Fin L) : Equiv.Perm (Index l.val) := by
  classical
  exact (finRotate (selectionCount l)).extendDomain (selectionEquiv l)

lemma cyclePermutation_apply (l:Fin L) (i:SelectedIndex l) :
    cyclePermutation l (selectedIndex l i)=selectedIndex l (finRotate (selectionCount l) i) := by
  classical
  exact Equiv.Perm.extendDomain_apply_image _ _ i

def cycleTarget (l:Fin L) : Matrix.SpecialLinearGroup (Index l.val) ℝ :=
  ⟨signedPermutation (cyclePermutation l) (selectedIndex l 0),signedPermutation_det _ _⟩

def constructedStream : Stream L cycleTarget := Classical.choice (exists_stream L cycleTarget)

def selectedBasis (l:Fin L) (i:SelectedIndex l) : H l.val := basis l.val (selectedIndex l i)
lemma selectedBasis_norm (l:Fin L) (i:SelectedIndex l) : ‖selectedBasis l i‖=1 :=
  (basis l.val).norm_eq_one _
lemma selectedBasis_independent (l:Fin L) : LinearIndependent ℝ (selectedBasis l) :=
  (basis l.val).toBasis.linearIndependent.comp (selectedIndex l) (selectedIndex_injective l)

def meanRoot (l:Fin L) : ℝ := (∑i:SelectedIndex l,root l.val (selectedIndex l i))/(selectionCount l:ℝ)

lemma selectedRoot_sum (l:Fin L) :
    (∑i:SelectedIndex l,root l.val (selectedIndex l i))=∑j∈selected l,root l.val j := by
  classical
  change (∑i:SelectedIndex l,(fun j:{j//j∈selected l}=>root l.val j.val) (selectionEquiv l i))=_
  calc
    _ = ∑j:{j//j∈selected l},root l.val j.val := Equiv.sum_comp (selectionEquiv l) _
    _ = _ := Finset.sum_coe_sort (selected l) (fun j=>root l.val j)

lemma meanRoot_pos (l:Fin L) : 0 < meanRoot l := by
  apply div_pos
  · exact Finset.sum_pos (fun i _=>root_pos l.val _) Finset.univ_nonempty
  · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))

lemma meanRoot_lt (l:Fin L) : meanRoot l<50000 := by
  rw [meanRoot,div_lt_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))),selectedRoot_sum]
  rw [← selected_card]
  exact selected_mean l

namespace Stream
variable (F:Stream L cycleTarget)

def virtualTransfer (l:Fin L) (j:ℕ) : H l.val→L[ℝ]H l.val :=
  weightedCycle (basis l.val) (cyclePermutation l) (selectedIndex l 0) (F.factor j l) (F.legDiagonal j l)

lemma virtualTransfer_action (l:Fin L) (j:ℕ) (i:SelectedIndex l) :
    F.virtualTransfer l j (selectedBasis l i)=
      (F.factor j l*(if selectedIndex l i=selectedIndex l 0 then ((cyclePermutation l).sign:ℝ) else 1)*
        F.legDiagonal j l (selectedIndex l (finRotate (selectionCount l) i))) •
        selectedBasis l (finRotate (selectionCount l) i) := by
  rw [virtualTransfer,selectedBasis,weightedCycle_action,cyclePermutation_apply]
  rfl

lemma virtualTransfer_injective (l:Fin L) (j:ℕ) : Function.Injective (F.virtualTransfer l j) :=
  weightedCycle_injective _ _ _ (F.factor_positive j l).ne' (fun i=>(F.leg_positive j l i).ne')

lemma virtualTransfer_matrix (l:Fin L) {j:ℕ} (hj:F.j0≤j) :
    orthogonalMatrix (basis l.val) (F.virtualTransfer l j)=
      (geometry L).transmission F.word.slot F.s F.j0 j l := by
  rw [virtualTransfer,weightedCycle,fromMatrix_matrix,F.period_factor hj,F.leg_diagonal]
  rfl

lemma virtualOrbit_rate (l:Fin L) (i:SelectedIndex l) :
    Tendsto (fun j=>Real.log ‖transferOrbit (F.virtualTransfer l) (selectedBasis l i) j‖/time j)
      atTop (𝓝 (meanRoot l)) := by
  let d := fun j k=>F.legDiagonal j l (selectedIndex l (finRotate (selectionCount l) k))
  let d₀ := fun k=>root l.val (selectedIndex l (finRotate (selectionCount l) k))
  let e := fun j k=>Real.log (d j k)/dwell j-d₀ k
  have he (k:SelectedIndex l) : Tendsto (fun j=>e j k) atTop (𝓝 0) := by
    simpa only [e,d,d₀,sub_self] using (F.leg_limit l (selectedIndex l (finRotate (selectionCount l) k))).sub_const (d₀ k)
  have hlog (j:ℕ) (k:SelectedIndex l) : Real.log (d j k)=dwell j*(d₀ k+e j k) := by
    dsimp only [e]
    field_simp [(dwell_pos j).ne']
    ring
  obtain ⟨C,hC⟩:=F.factor_log_bound l
  have h := endpoint_operator_rate (selectedBasis l) (selectedBasis_norm l)
    (fun k=>if selectedIndex l k=selectedIndex l 0 then ((cyclePermutation l).sign:ℝ) else 1)
    (fun j=>F.factor j l) d (F.virtualTransfer l) (F.virtualTransfer_action l)
    (fun k=>signedPermutation_abs_sign _ _ _) (fun j=>F.factor_positive j l)
    (fun j k=>F.leg_positive j l _) d₀ e hlog he hC i
  have hm : (∑k:SelectedIndex l,d₀ k)/(selectionCount l:ℝ)=meanRoot l := by
    unfold d₀ meanRoot
    exact congrArg (fun z:ℝ=>z/(selectionCount l:ℝ))
      (Equiv.sum_comp (finRotate (selectionCount l)) (fun k=>root l.val (selectedIndex l k)))
  rw [hm] at h
  exact h

end Stream
end HarmonicCounterexample.Construction

end

noncomputable section
open Filter
open scoped Topology InnerProductSpace

namespace HarmonicCounterexample.GlobalGrowth
open scoped Topology
open Filter Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma ode_local_log_bound {Y : ℝ → E} {P : ℝ → E →L[ℝ] E}
    {a b t C : ℝ} (hC : 0 ≤ C) (ht : t ∈ Icc a b)
    (hY : ∀ s ∈ Icc a b,HasDerivAt Y (P s (Y s)) s)
    (hP : ∀ s ∈ Icc a b,‖P s‖ ≤ C) (hnz : ∀ s ∈ Icc a b,Y s ≠ 0) :
    Real.log ‖Y t‖ ≤ Real.log ‖Y a‖+C*(b-a) := by
  have hab : a ≤ b := ht.1.trans ht.2
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hgrowth := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun s hs => (hY s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hY s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt)
    (le_refl ‖Y a‖)
    (K := C) (ε := 0) (fun s hs => by
      simp only [add_zero]
      exact (P s).le_opNorm (Y s) |>.trans
        (mul_le_mul_of_nonneg_right (hP s ⟨hs.1,hs.2.le⟩) (norm_nonneg _))) t ht
  rw [gronwallBound_ε0] at hgrowth
  have hna : 0 < ‖Y a‖ := norm_pos_iff.2 (hnz a ha)
  have hnt : 0 < ‖Y t‖ := norm_pos_iff.2 (hnz t ht)
  have hlog := Real.log_le_log hnt hgrowth
  rw [Real.log_mul hna.ne' (Real.exp_pos _).ne',Real.log_exp] at hlog
  exact hlog.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hC))

/-- Actual bounded Riccati ODEs have the source's all-real-time logarithmic
bound. No local log-growth estimate is supplied as an extra assumption. -/
theorem ode_all_time_log_growth {Y : ℝ → E} {P : ℝ → E →L[ℝ] E}
    {τ : ℕ → ℝ} {d α C : ℝ}
    (hτ : Tendsto τ atTop atTop) (hτpos : ∀ j,0 < τ j)
    (hend : Tendsto (fun j => Real.log ‖Y (τ j)‖/τ j) atTop (𝓝 d))
    (hduration : Tendsto (fun j => (τ (j+1)-τ j)/τ j) atTop (𝓝 0))
    (hC : 0 ≤ C) (hY : ∀ t,HasDerivAt Y (P t (Y t)) t)
    (hP : ∀ᶠ t in atTop,‖P t‖ ≤ C) (hnz : ∀ t,Y t ≠ 0)
    (hd : 0 ≤ d) (hα : d < α) :
    ∀ᶠ t in atTop,Real.log ‖Y t‖ ≤ α*t := by
  obtain ⟨a,ha⟩ := eventually_atTop.1 hP
  have he : ∀ᶠ j in atTop,a ≤ τ j := hτ.eventually (eventually_ge_atTop a)
  apply all_time_log_bound (C := C) hτ hτpos hend hduration ?_ hd hα
  filter_upwards [he] with j hj t ht
  exact ode_local_log_bound hC ht (fun s _ => hY s)
    (fun s hs => ha s (hj.trans hs.1)) (fun s _ => hnz s)

/-- A polynomial bound at EVERY sufficiently large radius, derived from the
actual ODE and the endpoint limit. -/
theorem ode_radial_growth {Y : ℝ → E} {P : ℝ → E →L[ℝ] E}
    {τ : ℕ → ℝ} {d α C : ℝ}
    (hτ : Tendsto τ atTop atTop) (hτpos : ∀ j,0 < τ j)
    (hend : Tendsto (fun j => Real.log ‖Y (τ j)‖/τ j) atTop (𝓝 d))
    (hduration : Tendsto (fun j => (τ (j+1)-τ j)/τ j) atTop (𝓝 0))
    (hC : 0 ≤ C) (hY : ∀ t,HasDerivAt Y (P t (Y t)) t)
    (hP : ∀ᶠ t in atTop,‖P t‖ ≤ C) (hnz : ∀ t,Y t ≠ 0)
    (hd : 0 ≤ d) (hα : d < α) :
    ∀ᶠ r in atTop,‖Y (Real.log r)‖ ≤ r^α :=
  radial_power_bound (fun _ => norm_nonneg _)
    (ode_all_time_log_growth hτ hτpos hend hduration hC hY hP hnz hd hα)

end HarmonicCounterexample.GlobalGrowth

end

noncomputable section
open Filter
open scoped Topology InnerProductSpace

namespace HarmonicCounterexample.LinearODE
open Filter
open scoped Topology InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Select the actual center-regular solution by its value at a positive late
sphere. No arbitrary two-sided ODE solution is introduced. -/
def regularAt (A : ℝ → E →L[ℝ] E) (p : ℝ → ℝ) (l a : ℝ) (x : E) (t : ℝ) : E :=
  operatorValue A p l t (Ring.inverse (operatorValue A p l a) x)

omit [FiniteDimensional ℝ E] in
lemma regularAt_initial {A : ℝ → E →L[ℝ] E} {p : ℝ → ℝ} {l a : ℝ}
    (ha : IsUnit (operatorValue A p l a)) (x : E) : regularAt A p l a x a=x := by
  change (operatorValue A p l a*Ring.inverse (operatorValue A p l a)) x=x
  rw [Ring.mul_inverse_cancel _ ha,one_apply_eq_self]

/-- True smooth coefficient solutions with an endpoint rate satisfy power
bounds at ALL sufficiently large radii. The uniform Riccati bound and all-time
nonvanishing are produced from the angular coefficients and Euclidean core. -/
theorem actual_regular_radial_growth {A : ℝ → E →L[ℝ] E} {p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p) {MA Mp : ℝ}
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp)
    (hAn : ∀ t,‖A t‖ ≤ MA) (hpn : ∀ t,|p t| ≤ Mp)
    (hAs : ∀ t x y,inner ℝ (A t x) y=inner ℝ x (A t y))
    (hAp : ∀ t x,0 ≤ inner ℝ x (A t x))
    {l B a : ℝ} (hl : 0 < l) (hAc : ∀ t ≤ 0,∀ x,A t x=(l*(l+B)) • x)
    (hpc : ∀ t ≤ 0,p t=B) {x : E} (hx : x ≠ 0)
    {τ : ℕ → ℝ} {d α : ℝ} (hτ : Tendsto τ atTop atTop) (hτp : ∀ j,0 < τ j)
    (hend : Tendsto (fun j => Real.log ‖regularAt A p l a x (τ j)‖/τ j) atTop (𝓝 d))
    (hdur : Tendsto (fun j => (τ (j+1)-τ j)/τ j) atTop (𝓝 0))
    (hd : 0 ≤ d) (hα : d < α) :
    ∀ᶠ r in atTop,‖regularAt A p l a x (Real.log r)‖ ≤ r^α := by
  have hu (t : ℝ) := actual_value_unit_all_time hA hp hMA hMp hAn hpn hAp hl hAc hpc t
  have hi : Function.Injective (Ring.inverse (operatorValue A p l a) : E →L[ℝ] E) := by
    apply (ContinuousLinearMap.isUnit_iff_bijective.1 ?_).1
    exact (hu a).ringInverse
  have hxn : Ring.inverse (operatorValue A p l a) x ≠ 0 := by
    intro he
    apply hx
    apply hi
    simpa using he
  have hyn (t : ℝ) : regularAt A p l a x t ≠ 0 := by
    intro he
    apply hxn
    apply (ContinuousLinearMap.isUnit_iff_bijective.1 (hu t)).1
    simpa only [regularAt,map_zero] using he
  have hder (t : ℝ) : HasDerivAt (regularAt A p l a x)
      (slope A p l t (regularAt A p l a x t)) t := by
    have he := (operatorValue_deriv hA hp hMA hMp hAn hpn l t).clm_apply
      (hasDerivAt_const t (Ring.inverse (operatorValue A p l a) x))
    simp only [map_zero,add_zero] at he
    rw [← slope_value (hu t)] at he
    exact he
  apply HarmonicCounterexample.GlobalGrowth.ode_radial_growth hτ hτp hend hdur
    (C := l+MA+Mp+1) (by linarith) hder ?_ hyn hd hα
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact actual_slope_norm_bound hA hp hMA hMp hAn hpn hAs hAp hl hAc hpc ht

end HarmonicCounterexample.LinearODE

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Schedule LinearODE
open scoped Topology ContDiff InnerProductSpace
variable {L:ℕ} {target:∀l:Fin L,Matrix.SpecialLinearGroup (Index l.val) ℝ}
namespace Stream
variable (F:Stream L target)

def A (l:Fin L) : ℝ→H l.val→L[ℝ]H l.val := (geometry L).coefficient F.word.slot F.s F.j0 l
def bound (l:Fin L) : ℝ := (geometry L).bound F.word.slot l

lemma bound_nonneg (l:Fin L) : 0≤F.bound l := (geometry L).bound_nonneg F.word.slot l
lemma A_smooth (l:Fin L) : ContDiff ℝ ∞ (F.A l) :=
  (geometry L).coefficient_smooth F.word.slot F.s F.j0 F.packet l
lemma A_bound (l:Fin L) (t:ℝ) : ‖F.A l t‖≤F.bound l :=
  (geometry L).coefficient_bound F.word.slot F.s F.j0 F.packet l t
lemma A_nonnegative (l:Fin L) (t:ℝ) (x:H l.val) : 0 ≤ inner ℝ x (F.A l t x) :=
  (geometry L).coefficient_nonnegative F.word.slot F.s F.j0 F.packet l t x
lemma A_symmetric (l:Fin L) (t:ℝ) (x y:H l.val) :
    inner ℝ (F.A l t x) y=inner ℝ x (F.A l t y) :=
  (geometry L).coefficient_symmetric F.word.slot F.s F.j0 F.packet l t x y
lemma A_center (l:Fin L) (t:ℝ) (ht:t≤0) (x:H l.val) :
    F.A l t x=(degree l.val*(degree l.val+14)) • x :=
  (geometry L).coefficient_center F.word.slot F.s F.j0 l t ht x
lemma A_eq (l:Fin L) : F.A l=fun t=>Angular.angularOperator (F.J t) (l.val+2) (F.c t) (F.q t) :=
  funext (F.coefficient_eq l)

lemma value_unit (l:Fin L) (t:ℝ) : IsUnit (operatorValue (F.A l) drift (degree l.val) t) :=
  actual_value_unit_all_time (F.A_smooth l).continuous drift_smooth.continuous
    (F.bound_nonneg l) (by norm_num) (F.A_bound l) (fun t=>(drift_bounds t).2)
    (F.A_nonnegative l) (degree_pos l.val) (F.A_center l) drift_center t

lemma degree_cast (l:Fin L) : degree l.val=((l.val+2:ℕ):ℝ) := by simp only [degree,Nat.cast_add,Nat.cast_ofNat]

lemma angular_smooth (l:Fin L) : ContDiff ℝ ∞
    (fun t=>Angular.angularOperator (F.J t) (l.val+2) (F.c t) (F.q t)) :=
  F.A_eq l ▸ F.A_smooth l
lemma angular_bound (l:Fin L) (t:ℝ) :
    ‖Angular.angularOperator (F.J t) (l.val+2) (F.c t) (F.q t)‖≤F.bound l := by
  rw [←F.coefficient_eq]
  exact F.A_bound l t

end Stream
end HarmonicCounterexample.Construction

end

noncomputable section


namespace HarmonicCounterexample.Construction
open Filter Set Schedule LinearODE Cycling
open scoped Topology InnerProductSpace
namespace Stream
variable (F:Stream L cycleTarget)

def orbitOperator (l:Fin L) : H l.val→L[ℝ]H l.val :=
  (transferOrbit_linear (F.virtualTransfer l) F.j0).choose
lemma orbitOperator_apply (l:Fin L) (x:H l.val) :
    F.orbitOperator l x=transferOrbit (F.virtualTransfer l) x F.j0 :=
  ((transferOrbit_linear (F.virtualTransfer l) F.j0).choose_spec x).symm
lemma orbitOperator_injective (l:Fin L) : Function.Injective (F.orbitOperator l) := by
  intro x y h
  apply transferOrbit_injective (F.virtualTransfer l) (F.virtualTransfer_injective l) F.j0
  simpa only [F.orbitOperator_apply] using h

def initialOperator (l:Fin L) : H l.val→L[ℝ]H l.val :=
  Ring.inverse (operatorValue (F.A l) drift (degree l.val) (time F.j0))*F.orbitOperator l
lemma initialOperator_injective (l:Fin L) : Function.Injective (F.initialOperator l) :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp (F.value_unit l (time F.j0)).ringInverse).1.comp
    (F.orbitOperator_injective l)

def initialPolynomial (l:Fin L) (i:SelectedIndex l) : H l.val := F.initialOperator l (selectedBasis l i)
lemma initialPolynomial_independent (l:Fin L) : LinearIndependent ℝ (F.initialPolynomial l) :=
  (selectedBasis_independent l).map' (F.initialOperator l).toLinearMap
    (LinearMap.ker_eq_bot.mpr (F.initialOperator_injective l))
lemma initialPolynomial_eq (l:Fin L) (i:SelectedIndex l) : F.initialPolynomial l i=
    Ring.inverse (operatorValue (F.A l) drift (degree l.val) (time F.j0))
      (transferOrbit (F.virtualTransfer l) (selectedBasis l i) F.j0) := by
  change (Ring.inverse (operatorValue (F.A l) drift (degree l.val) (time F.j0)) : H l.val→L[ℝ]H l.val) (F.orbitOperator l (selectedBasis l i))=_
  rw [F.orbitOperator_apply]

def trajectory (l:Fin L) (i:SelectedIndex l) (t:ℝ) : H l.val :=
  operatorValue (F.A l) drift (degree l.val) t (F.initialPolynomial l i)

lemma virtualTransfer_actual (l:Fin L) {j:ℕ} (hj:F.j0≤j) :
    F.virtualTransfer l j=operatorValue (F.A l) drift (degree l.val) (time (j+1))*
      Ring.inverse (operatorValue (F.A l) drift (degree l.val) (time j)) := by
  apply orthogonalMatrix_injective (basis l.val)
  rw [F.virtualTransfer_matrix l hj]
  rfl

lemma trajectory_initial (l:Fin L) (i:SelectedIndex l) :
    F.trajectory l i (time F.j0)=transferOrbit (F.virtualTransfer l) (selectedBasis l i) F.j0 := by
  unfold trajectory
  rw [F.initialPolynomial_eq]
  change (operatorValue (F.A l) drift (degree l.val) (time F.j0)*Ring.inverse (operatorValue (F.A l) drift (degree l.val) (time F.j0))) (transferOrbit (F.virtualTransfer l) (selectedBasis l i) F.j0)=_
  rw [Ring.mul_inverse_cancel _ (F.value_unit l (time F.j0)),one_apply_eq_self]

lemma trajectory_step (l:Fin L) (i:SelectedIndex l) {j:ℕ} (hj:F.j0≤j) :
    F.trajectory l i (time (j+1))=F.virtualTransfer l j (F.trajectory l i (time j)) := by
  rw [F.virtualTransfer_actual l hj]
  change _=((operatorValue (F.A l) drift (degree l.val) (time (j+1))*
    Ring.inverse (operatorValue (F.A l) drift (degree l.val) (time j)))*
    operatorValue (F.A l) drift (degree l.val) (time j)) (F.initialPolynomial l i)
  rw [mul_assoc,Ring.inverse_mul_cancel _ (F.value_unit l (time j)),mul_one]
  rfl

lemma trajectory_samples (l:Fin L) (i:SelectedIndex l) (j:ℕ) (hj:F.j0≤j) :
    F.trajectory l i (time j)=transferOrbit (F.virtualTransfer l) (selectedBasis l i) j := by
  obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le hj
  induction m with
  | zero => simpa only [Nat.add_zero] using F.trajectory_initial l i
  | succ m ih =>
    rw [Nat.add_succ,F.trajectory_step l i (Nat.le_add_right _ _),ih (Nat.le_add_right _ _),transferOrbit]

lemma trajectory_rate (l:Fin L) (i:SelectedIndex l) :
    Tendsto (fun j=>Real.log ‖F.trajectory l i (time j)‖/time j) atTop (𝓝 (meanRoot l)) := by
  apply (F.virtualOrbit_rate l i).congr'
  filter_upwards [eventually_ge_atTop F.j0] with j hj
  rw [F.trajectory_samples l i j hj]

lemma orbit_nonzero (l:Fin L) (i:SelectedIndex l) :
    transferOrbit (F.virtualTransfer l) (selectedBasis l i) F.j0≠0 := by
  intro h
  have hz : selectedBasis l i=0 := by
    apply F.orbitOperator_injective l
    rw [F.orbitOperator_apply,h,map_zero]
  have hn := selectedBasis_norm l i
  rw [hz,norm_zero] at hn
  norm_num at hn

lemma trajectory_regularAt (l:Fin L) (i:SelectedIndex l) : F.trajectory l i=
    regularAt (F.A l) drift (degree l.val) (time F.j0)
      (transferOrbit (F.virtualTransfer l) (selectedBasis l i) F.j0) := by
  funext t
  rw [trajectory,F.initialPolynomial_eq]
  rfl

lemma trajectory_radial_growth (l:Fin L) (i:SelectedIndex l) :
    ∀ᶠ r in atTop,‖F.trajectory l i (Real.log r)‖≤r^(50000:ℝ) := by
  have hend := F.trajectory_rate l i
  rw [F.trajectory_regularAt l i] at hend
  have h := actual_regular_radial_growth (a:=time F.j0)
    (F.A_smooth l).continuous drift_smooth.continuous
    (F.bound_nonneg l) (by norm_num) (F.A_bound l) (fun t=>(drift_bounds t).2)
    (F.A_symmetric l) (F.A_nonnegative l) (degree_pos l.val) (F.A_center l) drift_center
    (F.orbit_nonzero l i) time_atTop time_pos hend
    duration_time (meanRoot_pos l).le (meanRoot_lt l)
  rw [←F.trajectory_regularAt l i] at h
  exact h

lemma trajectory_exp_growth (l:Fin L) (i:SelectedIndex l) :
    ∃T:ℝ,∀t,T≤t→‖F.trajectory l i t‖≤Real.exp ((50000:ℝ)*t) := by
  have h := Real.tendsto_exp_atTop.eventually (F.trajectory_radial_growth l i)
  simp only [Real.log_exp,←Real.exp_mul] at h
  apply eventually_atTop.mp
  filter_upwards [h] with t ht
  rwa [mul_comm t (50000:ℝ)] at ht

end Stream
end HarmonicCounterexample.Construction

end

end OAI
