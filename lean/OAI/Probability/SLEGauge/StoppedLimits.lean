import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.EulerConvergence

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
open scoped ContDiff Manifold
noncomputable section
open Filter Topology
noncomputable section
open Complex Real Set Filter
open scoped Topology
noncomputable section
open scoped Topology
namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

 

theorem expected_stopped_local_eq {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (f : E × ℝ → ℝ) (K O : Set (E × ℝ))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (g : Driver → ℝ → E) (z : E) {L M T t : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖)
    (hg0 : ∀ b, g b 0 = z)
    (hder : ∀ b u, u ∈ Icc 0 T → HasDerivWithinAt (g b) (v (g b u) (b u.toNNReal)) (Icc 0 T) u)
    (hcf : ∀ b, ContinuousOn (fun u => v (g b u) (b u.toNNReal)) (Icc 0 T))
    (τ : (ℝ≥0 → ℝ) → ℝ) (mτ : Measurable τ)
    (hτpast : ∀ (s : ℝ≥0) b c, (∀ u ≤ s, b u = c u) → ((s:ℝ) < τ b ↔ (s:ℝ) < τ c))
    (hτ : ∀ b : Driver, 0 ≤ τ b ∧ τ b < T)
    (hD : ∀ b : Driver, ∃ ε > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < ε → (x,b u.toNNReal) ∈ K)
    (hgen : ∀ q ∈ K,
      fderiv ℝ (fun x => f (x,q.2)) q.1 (v q.1 q.2) +
        deriv (deriv (fun b => f (q.1,b))) q.2 / 2 = 0)
    (hz : (z,0) ∈ K) (ht : 0 ≤ t) :
    (∫ b : Driver, f (g b (min t (τ b)), b (min t (τ b)).toNNReal) ∂W) = f (z,0) := by
  have hle := expected_stopped_local hW f K O hK hO hKO hf v mv g z hL hM hv hlip
    hg0 hder hcf τ mτ hτpast hτ hD (fun q hq => (hgen q hq).le) hz ht
  have hneg : ∀ q ∈ K,
      fderiv ℝ (fun x => -f (x,q.2)) q.1 (v q.1 q.2) +
        deriv (deriv (fun b => -f (q.1,b))) q.2 / 2 ≤ 0 := by
    intro q hq
    have hfd : DifferentiableAt ℝ (fun x => f (x,q.2)) q.1 :=
      ((hf q (hKO hq)).contDiffAt (hO.mem_nhds (hKO hq))).differentiableAt (by simp) |>.comp q.1
        (by fun_prop)
    rw [fderiv_fun_neg]
    simp only [neg_apply,deriv.fun_neg',deriv.fun_neg]
    linarith [hgen q hq]
  have hge := expected_stopped_local hW (fun q => -f q) K O hK hO hKO hf.neg v mv g z hL hM hv hlip
    hg0 hder hcf τ mτ hτpast hτ hD hneg hz ht
  rw [integral_neg] at hge
  linarith
end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.OnePoint
open Parameter AngleCalculus
open scoped ContDiff
abbrev State := ℝ × ℂ

def domain : Set (State × ℝ) := {q | 0 < q.1.2.im}
def field (P : Parameter) (x : State) (b : ℝ) : State :=
  ((V (x.2-b))^2, (P.a:ℂ)/(x.2-b))
 
def green (P : Parameter) (q : State × ℝ) : ℝ :=
  Real.exp (P.p*q.1.1/2) * Real.sin (q.1.2-q.2).arg ^ P.p

lemma isOpen_domain : IsOpen domain := by
  exact isOpen_lt continuous_const (by fun_prop)

lemma green_nonneg (P : Parameter) {q : State × ℝ} (hq : q ∈ domain) : 0 ≤ green P q := by
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (sin_angle_pos (by simpa [domain] using hq)).le _)

lemma green_le (P : Parameter) {s : ℝ} {q : State × ℝ} (hu : q.1.1 ≤ s)
    (hq : q ∈ domain) : green P q ≤ Real.exp (P.p*s/2) := by
  have hs : 0 < Real.sin (q.1.2-(q.2:ℂ)).arg := sin_angle_pos (by simpa [domain] using hq)
  have hp : Real.sin (q.1.2-(q.2:ℂ)).arg ^ P.p ≤ 1 :=
    Real.rpow_le_one hs.le (Real.sin_le_one _) P.p_pos.le
  calc
    green P q ≤ Real.exp (P.p*q.1.1/2) := by
      exact mul_le_of_le_one_right (Real.exp_pos _).le hp
    _ ≤ Real.exp (P.p*s/2) := Real.exp_le_exp.mpr (by nlinarith [P.p_pos])

lemma contDiffOn_green (P : Parameter) : ContDiffOn ℝ ∞ (green P) domain := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have hh : 0 < (q.1.2-(q.2:ℂ)).im := by simpa [domain] using hq
  have ha := (contDiffAt_arg_real (show q.1.2-(q.2:ℂ) ∈ Complex.slitPlane from Or.inr hh.ne') ∞).comp q
    (show ContDiffAt ℝ ∞ (fun r : State × ℝ => r.1.2-(r.2:ℂ)) q from
      (contDiffAt_snd.comp q contDiffAt_fst).sub
        (Complex.ofRealCLM.contDiff.contDiffAt.comp q contDiffAt_snd))
  have hs := ha.sin.rpow_const_of_ne (p := P.p) (sin_angle_pos hh).ne'
  exact (show ContDiffAt ℝ ∞ (fun r : State × ℝ => Real.exp (P.p*r.1.1/2)) q by fun_prop).mul hs

lemma green_generator (P : Parameter) {q : State × ℝ} (hq : q ∈ domain) :
    fderiv ℝ (fun x => green P (x,q.2)) q.1 (field P q.1 q.2) +
      deriv (deriv (fun b => green P (q.1,b))) q.2 / 2 = 0 := by
  rcases q with ⟨⟨u,z⟩,b⟩
  have hy : 0 < z.im := hq
  have hs : 0 < Real.sin (z-(b:ℂ)).arg := sin_angle_pos (by simpa using hy)
  have hphy := physical_generator_angle P.a (fun θ => Real.sin θ^P.p)
    (fun θ hθ => (hasDerivAt_sinePower P.p θ hθ).differentiableAt.hasDerivAt)
    (fun θ hθ => by
      have he : deriv (fun t => Real.sin t^P.p) =ᶠ[𝓝 θ] fun t => P.p*Real.cos t*Real.sin t^(P.p-1) := by
        filter_upwards [Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds hθ)] with t ht
        exact deriv_sinePower P.p t ht
      exact ((hasDerivAt_sinePower_first P.p θ hθ).congr_of_eventuallyEq he).differentiableAt.hasDerivAt)
    hy b
  have hzero := P.shifted_sine_generator P.p (z-b).arg hs
  simp only [sub_self,zero_mul,mul_zero,zero_div] at hzero
  have heq : (fun x : State => green P (x,b)) = fun x => 3*P.physicalFactor (fun _ => 0) x b := by
    funext x
    simp only [green,Parameter.physicalFactor,Parameter.f,zero_mul,add_zero]
    ring
  have hfd := P.contDiffAt_physical_factor (fun _ => 0) u b z hy ∞ contDiffAt_const
  rw [heq,fderiv_const_mul (hfd.differentiableAt (by simp))]
  simp only [smul_apply,smul_eq_mul]
  rw [P.physical_factor_state_derivative (fun _ => 0) u 0 b _ z _ hy (by simpa using hasDerivAt_const u (0:ℝ))]
  simp only [Parameter.f,zero_mul,add_zero]
  have hsecond : deriv (deriv (fun c => green P ((u,z),c))) b =
      Real.exp (P.p*u/2)*deriv (deriv (fun c : ℝ => Real.sin (z-c).arg^P.p)) b := by
    change deriv (deriv (fun c : ℝ => Real.exp (P.p*u/2)*Real.sin (z-c).arg^P.p)) b = _
    rw [deriv_const_mul_field',deriv_const_mul_field]
  rw [hsecond]
  unfold physicalGenerator at hphy
  change _ = (V (z-b))^2*P.angleGenerator (fun θ => Real.sin θ^P.p) (z-b).arg at hphy
  dsimp [field]
  linear_combination Real.exp (P.p*u/2)*hphy + Real.exp (P.p*u/2)*(V (z-b))^2*hzero
end SLEExactGauge.OnePoint

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
omit [CompleteSpace E] in
theorem expected_stopped_smooth_grid {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (A : SmoothTest E) (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (g : Driver → ℝ → E) (z : E) {L M T t : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖)
    (hg0 : ∀ b, g b 0 = z)
    (hder : ∀ b u, u ∈ Icc 0 T → HasDerivWithinAt (g b) (v (g b u) (b u.toNNReal)) (Icc 0 T) u)
    (hcf : ∀ b, ContinuousOn (fun u => v (g b u) (b u.toNNReal)) (Icc 0 T))
    (τ : Driver → ℝ)
    (hτ : ∀ b : Driver, 0 ≤ τ b ∧ τ b < T)
    (D : Set (E × ℝ)) (_mD : MeasurableSet D)
    (hD : ∀ b : Driver, ∃ ε > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < ε → (x,b u.toNNReal) ∈ D)
    (hgen : ∀ x ∈ D, A.D x.1 x.2 (v x.1 x.2)+deriv (deriv (A.F x.1)) x.2/2 ≤ 0)
    (S : ℝ≥0 → Set ((ℝ≥0 → ℝ) × (E × ℝ))) (mS : ∀ r, MeasurableSet (S r))
    (hSpast : ∀ r b c, (∀ u ≤ r, b u = c u) → ∀ x, ((b,x) ∈ S r ↔ (c,x) ∈ S r))
    (hSeq : ∀ (b : Driver) r x, (((b:ℝ≥0 → ℝ),x) ∈ S r ↔ (r:ℝ) < τ b ∧ x ∈ D))
    (hSD : ∀ r q, q ∈ S r → q.2 ∈ D)
    (ht : 0 ≤ t) :
    (∫ b : Driver, A.F (g b (min t (τ b))) (b (min t (τ b)).toNNReal) ∂W) ≤ A.F z 0 := by
  let h : ℕ → ℝ≥0 := fun n => (1/2)^n
  have hh : ∀ n, 0 < h n := fun n => pow_pos (by norm_num) n
  have hh0 : Tendsto (fun n => (h n:ℝ)) atTop (𝓝 0) := by
    simp only [h,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let U : ℕ → ℕ → Set ((ℝ≥0 → ℝ) × (E × ℝ)) := fun n k => S ((k:ℝ≥0)*h n)
  have mU : ∀ n k, MeasurableSet (U n k) := fun n k => mS _
  have hu : ∀ n (k : ℕ) b c, (∀ u ≤ (k:ℝ≥0)*h n, b u = c u) → ∀ x,
      ((b,x) ∈ U n k ↔ (c,x) ∈ U n k) := fun _ _ _ _ => hSpast _ _ _
  apply expected_frozen_limit hW A v mv U mU h (fun n => ⌊t/(h n:ℝ)⌋₊) (z,0) hu M hv
    (fun _ _ b x hx => hgen x (hSD _ (b,x) hx))
    (fun b => (g b (min t (τ b)), b (min t (τ b)).toNNReal)) t hh0
    (EulerGeneral.mesh_times_converge (fun n => hh n) hh0 ht)
  filter_upwards [] with b
  obtain ⟨ε,hε,hDb⟩ := hD b
  have hp := frozen_nodes_path_limit v (g b) z b b.continuous D U hL hM (hg0 b)
    (fun _ _ => hlip _) (hder b) (hcf b) (fun u _ => hv _ _) (hτ b).1 (hτ b).2 ht
    hε hDb hh hh0 (fun n k x => by simpa only [U,NNReal.coe_mul,NNReal.coe_natCast] using hSeq b ((k:ℝ≥0)*h n) x)
  simpa only [map_zero] using hp

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem expected_stopped_local_grid {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (f : E × ℝ → ℝ) (K O : Set (E × ℝ))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (g : Driver → ℝ → E) (z : E) {L M T t : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖)
    (hg0 : ∀ b, g b 0 = z)
    (hder : ∀ b u, u ∈ Icc 0 T → HasDerivWithinAt (g b) (v (g b u) (b u.toNNReal)) (Icc 0 T) u)
    (hcf : ∀ b, ContinuousOn (fun u => v (g b u) (b u.toNNReal)) (Icc 0 T))
    (τ : Driver → ℝ)
    (hτ : ∀ b : Driver, 0 ≤ τ b ∧ τ b < T)
    (hD : ∀ b : Driver, ∃ ε > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < ε → (x,b u.toNNReal) ∈ K)
    (hgen : ∀ q ∈ K,
      fderiv ℝ (fun x => f (x,q.2)) q.1 (v q.1 q.2) +
        deriv (deriv (fun b => f (q.1,b))) q.2 / 2 ≤ 0)
    (S : ℝ≥0 → Set ((ℝ≥0 → ℝ) × (E × ℝ))) (mS : ∀ r, MeasurableSet (S r))
    (hSpast : ∀ r b c, (∀ u ≤ r, b u = c u) → ∀ x, ((b,x) ∈ S r ↔ (c,x) ∈ S r))
    (hSeq : ∀ (b : Driver) r x, (((b:ℝ≥0 → ℝ),x) ∈ S r ↔ (r:ℝ) < τ b ∧ x ∈ K))
    (hSD : ∀ r q, q ∈ S r → q.2 ∈ K)
    (hz : (z,0) ∈ K) (ht : 0 ≤ t) :
    (∫ b : Driver, f (g b (min t (τ b)), b (min t (τ b)).toNNReal) ∂W) ≤ f (z,0) := by
  obtain ⟨G,hG,hGc,hGeq⟩ := Localization.compact_extension hK hO hKO f hf
  obtain ⟨A,hA⟩ := exists_smoothTest_of_compact G hG hGc
  have heq (q : E × ℝ) (hq : q ∈ K) : A.F q.1 q.2 = f q := by
    rw [hA]
    exact (hGeq q hq).self_of_nhds
  have hDgen (q : E × ℝ) (hq : q ∈ K) :
      A.D q.1 q.2 (v q.1 q.2)+deriv (deriv (A.F q.1)) q.2/2 ≤ 0 := by
    have hx : (fun x => A.F x q.2) =ᶠ[𝓝 q.1] fun x => f (x,q.2) := by
      rw [hA]
      exact (hGeq q hq).comp_tendsto (continuousAt_id.prodMk continuousAt_const)
    have hb : A.F q.1 =ᶠ[𝓝 q.2] fun b => f (q.1,b) := by
      rw [hA]
      exact (hGeq q hq).comp_tendsto (continuousAt_const.prodMk continuousAt_id)
    rw [← (A.hD q.1 q.2).fderiv, hx.fderiv_eq, hb.deriv.deriv_eq]
    exact hgen q hq
  have hineq := expected_stopped_smooth_grid hW A v mv g z hL hM hv hlip hg0 hder hcf
    τ hτ K hK.measurableSet hD hDgen S mS hSpast hSeq hSD ht
  rw [heq (z,0) hz] at hineq
  convert hineq using 1
  apply integral_congr_ae
  filter_upwards [] with b
  symm
  apply heq (g b (min t (τ b)), b (min t (τ b)).toNNReal)
  obtain ⟨ε,hε,hDb⟩ := hD b
  exact hDb (min t (τ b)) ⟨le_min ht (hτ b).1,min_le_right _ _⟩ _ (by simpa using hε)

end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.BrownianCalculus
open Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
 

theorem expected_stopped_local_grid_eq {W : Measure Driver}
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b t) W)
    (f : E × ℝ → ℝ) (K O : Set (E × ℝ))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) (hf : ContDiffOn ℝ ∞ f O)
    (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (g : Driver → ℝ → E) (z : E) {L M T t : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hv : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖)
    (hg0 : ∀ b, g b 0 = z)
    (hder : ∀ b u, u ∈ Icc 0 T → HasDerivWithinAt (g b) (v (g b u) (b u.toNNReal)) (Icc 0 T) u)
    (hcf : ∀ b, ContinuousOn (fun u => v (g b u) (b u.toNNReal)) (Icc 0 T))
    (τ : Driver → ℝ)
    (hτ : ∀ b : Driver, 0 ≤ τ b ∧ τ b < T)
    (hD : ∀ b : Driver, ∃ ε > 0, ∀ u ∈ Icc 0 (τ b), ∀ x,
      ‖x-g b u‖ < ε → (x,b u.toNNReal) ∈ K)
    (hgen : ∀ q ∈ K,
      fderiv ℝ (fun x => f (x,q.2)) q.1 (v q.1 q.2) +
        deriv (deriv (fun b => f (q.1,b))) q.2 / 2 = 0)
    (S : ℝ≥0 → Set ((ℝ≥0 → ℝ) × (E × ℝ))) (mS : ∀ r, MeasurableSet (S r))
    (hSpast : ∀ r b c, (∀ u ≤ r, b u = c u) → ∀ x, ((b,x) ∈ S r ↔ (c,x) ∈ S r))
    (hSeq : ∀ (b : Driver) r x, (((b:ℝ≥0 → ℝ),x) ∈ S r ↔ (r:ℝ) < τ b ∧ x ∈ K))
    (hSD : ∀ r q, q ∈ S r → q.2 ∈ K)
    (hz : (z,0) ∈ K) (ht : 0 ≤ t) :
    (∫ b : Driver, f (g b (min t (τ b)), b (min t (τ b)).toNNReal) ∂W) = f (z,0) := by
  have hle := expected_stopped_local_grid hW f K O hK hO hKO hf v mv g z hL hM hv hlip
    hg0 hder hcf τ hτ hD (fun q hq => (hgen q hq).le) S mS hSpast hSeq hSD hz ht
  have hneg : ∀ q ∈ K,
      fderiv ℝ (fun x => -f (x,q.2)) q.1 (v q.1 q.2) +
        deriv (deriv (fun b => -f (q.1,b))) q.2 / 2 ≤ 0 := by
    intro q hq
    have hfd : DifferentiableAt ℝ (fun x => f (x,q.2)) q.1 :=
      ((hf q (hKO hq)).contDiffAt (hO.mem_nhds (hKO hq))).differentiableAt (by simp) |>.comp q.1
        (by fun_prop)
    rw [fderiv_fun_neg]
    simp only [neg_apply,deriv.fun_neg',deriv.fun_neg]
    linarith [hgen q hq]
  have hge := expected_stopped_local_grid hW (fun q => -f q) K O hK hO hKO hf.neg v mv g z hL hM hv hlip
    hg0 hder hcf τ hτ hD hneg S mS hSpast hSeq hSD hz ht
  rw [integral_neg] at hge
  linarith
end SLEExactGauge.BrownianCalculus

namespace SLEExactGauge.Localization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 

theorem bounded_lipschitz_ode (v : E → ℝ → E)
    (cv : Continuous (Function.uncurry v)) (b : ℝ → ℝ) (cb : Continuous b)
    (z : E) {M L T : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hbound : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖) :
    ∃ g : ℝ → E, g 0 = z ∧ ∀ t ∈ Icc 0 T,
      HasDerivWithinAt g (v (g t) (b t)) (Icc 0 T) t := by
  let M' : ℝ≥0 := ⟨M,hM⟩
  let L' : ℝ≥0 := ⟨L,hL⟩
  let R : ℝ≥0 := ⟨M*T,mul_nonneg hM hT⟩
  have hp : IsPicardLindelof (fun t x => v x (b t)) (tmin := 0) (tmax := T)
      ⟨0,⟨le_rfl,hT⟩⟩ z R 0 M' L' := by
    constructor
    · intro t _
      apply LipschitzWith.lipschitzOnWith
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change dist (v x (b t)) (v y (b t)) ≤ L * dist x y
      simpa only [dist_eq_norm] using hlip (b t) x y
    · intro x _
      exact (cv.comp (continuous_const.prodMk cb)).continuousOn
    · intro t _ x _
      exact hbound x (b t)
    · change M*max (T-0) (0-0) ≤ M*T-0
      simp only [sub_zero,sub_self,max_eq_left hT,le_refl]
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

end SLEExactGauge.Localization

open MeasureTheory
namespace SLEExactGauge.ODEPath
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def mesh (n : ℕ) : ℝ := (1/2)^n
lemma mesh_pos (n : ℕ) : 0 < mesh n := pow_pos (by norm_num) n
lemma mesh_zero : Tendsto mesh atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

def drift (v : E → ℝ → E) (b : ℝ≥0 → ℝ) (t : ℝ) (x : E) : E := v x (b t.toNNReal)
def flow (v : E → ℝ → E) (z : E) (b : ℝ≥0 → ℝ) (t : ℝ) : E :=
  limUnder atTop (fun n => EulerGeneral.interpolate (drift v b) (mesh n) z t)

omit [CompleteSpace E] in
lemma measurable_nodes (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (h : ℝ) (z : E) (k : ℕ) :
    Measurable (fun b : ℝ≥0 → ℝ => EulerGeneral.nodes (drift v b) h z k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact ih.add (measurable_const.smul (mv.comp (ih.prodMk (measurable_pi_apply _))))

omit [CompleteSpace E] in
lemma measurable_interpolate (v : E → ℝ → E) (mv : Measurable (Function.uncurry v))
    (h : ℝ) (z : E) (t : ℝ) :
    Measurable (fun b : ℝ≥0 → ℝ => EulerGeneral.interpolate (drift v b) h z t) := by
  unfold EulerGeneral.interpolate
  exact (measurable_const.smul (measurable_nodes v mv h z _)).add
    (measurable_const.smul (measurable_nodes v mv h z _))

lemma measurable_flow (v : E → ℝ → E) (mv : Measurable (Function.uncurry v)) (z : E) (t : ℝ) :
    Measurable (fun b : ℝ≥0 → ℝ => flow v z b t) :=
  (StronglyMeasurable.limUnder (fun n => (measurable_interpolate v mv (mesh n) z t).stronglyMeasurable)).measurable

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma nodes_past (v : E → ℝ → E) {h : ℝ} (hh : 0 < h) (z : E)
    {b c : ℝ≥0 → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (he : ∀ u : ℝ≥0, (u:ℝ) ≤ s → b u = c u)
    (k : ℕ) (hk : (k:ℝ)*h ≤ s+h) :
    EulerGeneral.nodes (drift v b) h z k = EulerGeneral.nodes (drift v c) h z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : (k:ℝ)*h ≤ s := by push_cast at hk; nlinarith
    have hb : b (((k:ℝ)*h).toNNReal) = c (((k:ℝ)*h).toNNReal) :=
      he _ (by simpa only [Real.coe_toNNReal',max_le_iff] using And.intro hk' hs)
    simp only [EulerGeneral.nodes,drift,ih (by linarith),hb]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma interpolate_past (v : E → ℝ → E) {h : ℝ} (hh : 0 < h) (z : E)
    {b c : ℝ≥0 → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (he : ∀ u : ℝ≥0, (u:ℝ) ≤ s → b u = c u) :
    EulerGeneral.interpolate (drift v b) h z s = EulerGeneral.interpolate (drift v c) h z s := by
  have hk : (⌊s/h⌋₊:ℝ)*h ≤ s := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg hs hh.le))
  unfold EulerGeneral.interpolate
  dsimp only
  rw [nodes_past v hh z hs he _ (by linarith),nodes_past v hh z hs he _ (by push_cast; linarith)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma flow_past (v : E → ℝ → E) (z : E) {b c : ℝ≥0 → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (he : ∀ u : ℝ≥0, (u:ℝ) ≤ s → b u = c u) : flow v z b s = flow v z c s := by
  unfold flow
  congr 1
  funext n
  exact interpolate_past v (mesh_pos n) z hs he

 

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem flow_solution (v : E → ℝ → E) (cv : Continuous (Function.uncurry v))
    (z : E) (b : ℝ≥0 → ℝ) (cb : Continuous b) {M L T : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hbound : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖) :
    flow v z b 0 = z ∧ ∀ t ∈ Icc 0 T, HasDerivWithinAt (flow v z b)
      (v (flow v z b t) (b t.toNNReal)) (Icc 0 T) t := by
  obtain ⟨g,hg0,hg⟩ := Localization.bounded_lipschitz_ode v cv
    (fun t => b t.toNNReal) (cb.comp continuous_real_toNNReal) z hM hL (by linarith : 0 ≤ T+1) hbound hlip
  have hgc : ContinuousOn g (Icc 0 (T+1)) := fun t ht => (hg t ht).continuousWithinAt
  have hcf : ContinuousOn (fun t => v (g t) (b t.toNNReal)) (Icc 0 (T+1)) :=
    cv.comp_continuousOn (hgc.prodMk ((cb.comp continuous_real_toNNReal).continuousOn))
  have hconv : TendstoUniformlyOn (fun n => EulerGeneral.interpolate (drift v b) (mesh n) z)
      g atTop (Icc 0 T) :=
    EulerGeneral.converge_uniformOn hL hM hg0 (fun _ _ => hlip _) hg hcf
      (fun _ _ => hbound _ _) hT (by linarith) mesh_pos mesh_zero
  have heq : ∀ t ∈ Icc 0 T, flow v z b t = g t :=
    fun t ht => (hconv.tendsto_at ht).limUnder_eq
  refine ⟨(heq 0 ⟨le_rfl,hT⟩).trans hg0,?_⟩
  intro t ht
  rw [heq t ht]
  exact ((hg t ⟨ht.1,by linarith [ht.2]⟩).mono
    (show Icc 0 T ⊆ Icc 0 (T+1) from fun u hu => ⟨hu.1,by linarith [hu.2]⟩)).congr heq (heq t ht)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma continuousOn_flow (v : E → ℝ → E) (cv : Continuous (Function.uncurry v))
    (z : E) (b : ℝ≥0 → ℝ) (cb : Continuous b) {M L T : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hbound : ∀ x b, ‖v x b‖ ≤ M) (hlip : ∀ b x y, ‖v x b-v y b‖ ≤ L*‖x-y‖) :
    ContinuousOn (flow v z b) (Icc 0 T) :=
  fun t ht => ((flow_solution v cv z b cb hM hL hT hbound hlip).2 t ht).continuousWithinAt

end SLEExactGauge.ODEPath

namespace SLEExactGauge.RationalStop

def sample (s r : ℝ) : ℝ := max 0 (min s r)
lemma sample_mem {s : ℝ} (hs : 0 ≤ s) (r : ℝ) : sample s r ∈ Icc 0 s :=
  ⟨le_max_left _ _,max_le hs (min_le_left _ _)⟩
lemma sample_self {s u : ℝ} (hu : u ∈ Icc 0 s) : sample s u = u := by
  simp [sample,min_eq_right hu.2,max_eq_right hu.1]
lemma continuous_sample (s : ℝ) : Continuous (sample s) := by unfold sample; fun_prop

 

def Safe (f : ℝ → ℝ) (R s : ℝ) : Prop :=
  ∃ n : ℕ, ∀ r : ℚ, f (sample s r) ≤ R-1/((n:ℝ)+1)

lemma safe_iff {f : ℝ → ℝ} {R s : ℝ} (hs : 0 ≤ s)
    (hf : ContinuousOn f (Icc 0 s)) : Safe f R s ↔ ∀ u ∈ Icc 0 s, f u < R := by
  constructor
  · rintro ⟨n,hn⟩ u hu
    have hc : Continuous (fun x => f (sample s x)) :=
      hf.comp_continuous (continuous_sample s) (sample_mem hs)
    have h : f (sample s u) ≤ R-1/((n:ℝ)+1) := Rat.denseRange_cast.induction_on u
      (isClosed_le hc continuous_const) hn
    rw [sample_self hu] at h
    have hp : 0 < 1/((n:ℝ)+1) := by positivity
    linarith
  · intro h
    obtain ⟨u,hu,hm⟩ := isCompact_Icc.exists_isMaxOn ⟨0,⟨le_rfl,hs⟩⟩ hf
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (h u hu))
    refine ⟨n,fun r => ?_⟩
    have hr : f (sample s r) ≤ f u := hm (sample_mem hs (r:ℝ))
    linarith

end SLEExactGauge.RationalStop
end
end
end
end
end
end
end
end
end
end

end OAI
