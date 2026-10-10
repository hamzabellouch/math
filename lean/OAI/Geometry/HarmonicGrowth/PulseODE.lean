import OAI.Geometry.HarmonicGrowth.ScalarODE
import OAI.Geometry.HarmonicGrowth.Taylor

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Exact scalar-baseline cancellation. Keeping v exact removes a term of
size (a-a_*) times the long pulse duration. -/
lemma slow_residual_identity (A₀ p p₀ v θ τ : ℝ) (S Sdot Err : R) :
    (A₀ • (1:R)+((p₀+2*θ)*τ) • S+Err)-
      p • (v • (1:R)+τ • S)-(v • (1:R)+τ • S)*(v • (1:R)+τ • S)-
      ((A₀-p*v-v^2) • (1:R)+(τ^2) • Sdot) =
      Err+((p₀+2*θ-p-2*v)*τ) • S-(τ^2) • (S*S+Sdot) := by
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_smul,smul_add]
  module

/-- Exact first parameter derivative of that residual. The scalar baseline and
p are independent of the CURRENT control parameter. -/
lemma slow_residual_jet_identity (p p₀ v θ τ : ℝ) (S Sh Shdot Errh : R) :
    (((p₀+2*θ)*τ) • Sh+Errh)-p • (τ • Sh)-
      (τ • Sh)*(v • (1:R)+τ • S)-(v • (1:R)+τ • S)*(τ • Sh)-
      (τ^2) • Shdot =
      Errh+((p₀+2*θ-p-2*v)*τ) • Sh-(τ^2) • (Sh*S+S*Sh+Shdot) := by
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_smul,smul_add]
  module

/-- A uniform slow-pulse residual bound with completely explicit constants. -/
lemma slow_residual_bound {Err S Sdot : R} {C δ τ ε : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (he : ‖Err‖ ≤ C*(δ*τ+τ^2)) (hε : |ε| ≤ 3*C*δ)
    (hS : ‖S‖ ≤ C) (hSd : ‖Sdot‖ ≤ C) :
    ‖Err+(ε*τ) • S-(τ^2) • (S*S+Sdot)‖ ≤
      (3*C^2+2*C)*(δ*τ+τ^2) := by
  have hn : ‖S*S+Sdot‖ ≤ C^2+C := by
    calc
      _ ≤ ‖S*S‖+‖Sdot‖ := norm_add_le _ _
      _ ≤ ‖S‖*‖S‖+C := add_le_add (norm_mul_le _ _) hSd
      _ ≤ C*C+C := by nlinarith [mul_self_le_mul_self (norm_nonneg S) hS]
      _ = _ := by ring
  calc
    _ ≤ ‖Err‖+‖(ε*τ) • S‖+‖(τ^2) • (S*S+Sdot)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = ‖Err‖+|ε| *τ*‖S‖+τ^2*‖S*S+Sdot‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hτ,abs_of_nonneg (sq_nonneg τ),mul_assoc]
    _ ≤ C*(δ*τ+τ^2)+(3*C*δ)*τ*C+τ^2*(C^2+C) := by
      gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg τ),mul_nonneg hC (mul_nonneg hδ hτ)]

lemma slow_residual_jet_bound {Errh S Sh Shdot : R} {C δ τ ε : ℝ}
    (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (he : ‖Errh‖ ≤ C*(δ*τ+τ^2)) (hε : |ε| ≤ 3*C*δ)
    (hS : ‖S‖ ≤ C) (hSh : ‖Sh‖ ≤ C) (hShd : ‖Shdot‖ ≤ C) :
    ‖Errh+(ε*τ) • Sh-(τ^2) • (Sh*S+S*Sh+Shdot)‖ ≤
      (3*C^2+2*C)*(δ*τ+τ^2) := by
  have hn : ‖Sh*S+S*Sh+Shdot‖ ≤ 2*C^2+C := by
    calc
      _ ≤ ‖Sh*S+S*Sh‖+‖Shdot‖ := norm_add_le _ _
      _ ≤ (‖Sh*S‖+‖S*Sh‖)+C := add_le_add (norm_add_le _ _) hShd
      _ ≤ (‖Sh‖*‖S‖+‖S‖*‖Sh‖)+C := by gcongr <;> exact norm_mul_le _ _
      _ ≤ (C*C+C*C)+C := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖Errh‖+‖(ε*τ) • Sh‖+‖(τ^2) • (Sh*S+S*Sh+Shdot)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ = ‖Errh‖+|ε| *τ*‖Sh‖+τ^2*‖Sh*S+S*Sh+Shdot‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hτ,abs_of_nonneg (sq_nonneg τ),mul_assoc]
    _ ≤ C*(δ*τ+τ^2)+(3*C*δ)*τ*C+τ^2*(2*C^2+C) := by gcongr
    _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg C) (sq_nonneg τ),mul_nonneg hC (mul_nonneg hδ hτ)]

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open HarmonicCounterexample.PulseTaylor
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The source's first-order slow generator, including its precise
Riccati denominator. The angular infinitesimal is r B Id+D. -/
def bergerSlowGenerator (r B β p₀ θ z : ℝ) (D : R) : R :=
  (β/(p₀+2*θ)*z) • (r • (B • (1:R))+D)

/-- Uniform residual AND true parameter-direction residual estimates for the
exact Berger comparison. The constant is chosen before the scalar history,
small deviation, duration, pulse position and parameters. All nonlinear
angular remainders are proved, not hypotheses. -/
theorem berger_comparison_residuals (r B β p₀ θ : ℝ) (D : R)
    {M Z K : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hK : 0 ≤ K)
    (hc : p₀+2*θ ≠ 0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ α p v δ τ z zd zh zhd : ℝ,
      0 ≤ δ → 0 ≤ τ → |α| ≤ M → |α-β| ≤ δ → |p-p₀| ≤ δ → |v-θ| ≤ K*δ →
      |z| ≤ Z → |zd| ≤ Z → |zh| ≤ Z → |zhd| ≤ Z →
      1+τ*z ∈ Set.Icc (1/2:ℝ) (3/2) →
      let S := bergerSlowGenerator r B β p₀ θ z D
      let Sd := bergerSlowGenerator r B β p₀ θ zd D
      let Sh := bergerSlowGenerator r B β p₀ θ zh D
      let Shd := bergerSlowGenerator r B β p₀ θ zhd D
      let Q := v • (1:R)+τ • S
      ‖α • angular r (B • (1:R)) D (1+τ*z)-p • Q-Q*Q-
        ((α*B-p*v-v^2) • (1:R)+(τ^2) • Sd)‖ ≤ C*(δ*τ+τ^2) ∧
      ‖(τ*zh) • (α • angularD r (B • (1:R)) D (1+τ*z))-
        p • (τ • Sh)-(τ • Sh)*Q-Q*(τ • Sh)-(τ^2) • Shd‖ ≤ C*(δ*τ+τ^2) := by
  obtain ⟨C₀,hC₀,hrem⟩ := berger_slow_pulse_remainders r (B • (1:R)) D hM hZ
  let L := r • (B • (1:R))+D
  let A := |β/(p₀+2*θ)| *Z*‖L‖
  let C₁ := C₀+A+K+1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁];linarith
  have h₀ : C₀ ≤ C₁ := by dsimp [C₁];linarith
  have h₁ : A ≤ C₁ := by dsimp [C₁];linarith
  have h₂ : K ≤ C₁ := by dsimp [C₁];linarith
  have h₃ : 1 ≤ C₁ := by dsimp [C₁];linarith
  refine ⟨3*C₁^2+2*C₁,by positivity,?_⟩
  intro α p v δ τ z zd zh zhd hδ hτ hα hscale hp hv hz hzd hzh hzhd hq
  dsimp only
  have hSn (x : ℝ) (hx : |x| ≤ Z) : ‖bergerSlowGenerator r B β p₀ θ x D‖ ≤ C₁ := by
    calc
      _ = |β/(p₀+2*θ)| *|x| *‖L‖ := by simp only [bergerSlowGenerator,norm_smul,Real.norm_eq_abs,abs_mul,L]
      _ ≤ A := by dsimp [A];gcongr
      _ ≤ C₁ := h₁
  have hε : |p₀+2*θ-p-2*v| ≤ 3*C₁*δ := by
    have he : p₀+2*θ-p-2*v= -(p-p₀)-2*(v-θ) := by ring
    rw [he]
    calc
      _ ≤ |-(p-p₀)|+|2*(v-θ)| := abs_sub _ _
      _ = |p-p₀|+2*|v-θ| := by rw [abs_neg,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      _ ≤ δ+2*(K*δ) := by gcongr
      _ ≤ 3*C₁*δ := by nlinarith [mul_le_mul_of_nonneg_right h₂ hδ,mul_le_mul_of_nonneg_right h₃ hδ]
  obtain ⟨he,hej⟩ := hrem α β δ τ z zh hδ hτ hα hscale hz hzh hq
  have hfac (x : ℝ) : ((p₀+2*θ)*τ) • bergerSlowGenerator r B β p₀ θ x D=
      (β*τ*x) • L := by
    rw [bergerSlowGenerator,smul_smul]
    change (((p₀+2*θ)*τ)*(β/(p₀+2*θ)*x)) • L=(β*τ*x) • L
    congr 1
    field_simp
  let Err := α • angular r (B • (1:R)) D (1+τ*z)-α • (B • (1:R))-(β*τ*z) • L
  let Errh := (τ*zh) • (α • angularD r (B • (1:R)) D (1+τ*z)-β • L)
  have he' : ‖Err‖ ≤ C₁*(δ*τ+τ^2) := he.trans (mul_le_mul_of_nonneg_right h₀ (by positivity))
  have hej' : ‖Errh‖ ≤ C₁*(δ*τ+τ^2) := hej.trans (mul_le_mul_of_nonneg_right h₀ (by positivity))
  have hvId : (α*B) • (1:R)+((p₀+2*θ)*τ) • bergerSlowGenerator r B β p₀ θ z D+Err=
      α • angular r (B • (1:R)) D (1+τ*z) := by
    rw [hfac]
    dsimp only [Err]
    simp only [smul_smul]
    abel
  have hjId : ((p₀+2*θ)*τ) • bergerSlowGenerator r B β p₀ θ zh D+Errh=
      (τ*zh) • (α • angularD r (B • (1:R)) D (1+τ*z)) := by
    rw [hfac]
    dsimp only [Errh]
    simp only [smul_sub,smul_smul]
    rw [show τ*zh*β=β*τ*zh by ring]
    abel
  constructor
  · rw [← hvId,slow_residual_identity]
    exact slow_residual_bound hC₁ hδ hτ he' hε (hSn z hz) (hSn zd hzd)
  · rw [← hjId,slow_residual_jet_identity]
    exact slow_residual_jet_bound hC₁ hδ hτ hej' hε (hSn z hz) (hSn zh hzh) (hSn zhd hzhd)

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open Set

/-- The exact source scalar baseline, forced by B/a(t)^2, deviates from
its limiting root by O(delta), uniformly in the pulse length. -/
theorem berger_scalar_baseline_close {α p : ℝ → ℝ}
    (hα : Continuous α) (hp : Continuous p)
    {M Mp B β p₀ θ γ δ T : ℝ}
    (hM : 0 ≤ M) (hMp : 0 ≤ Mp) (hθ : 0 ≤ θ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hαn : ∀ t,|α t| ≤ M) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ α t*B) (hroot : β*B-p₀*θ-θ^2=0)
    (hscale : ∀ t ∈ Icc 0 T,|α t-β| ≤ δ)
    (hpt : ∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t) :
    ∀ t ∈ Icc 0 T,|scalarBaseline (fun s => α s*B) p θ t-θ| ≤
      ((|B|+|θ|)/γ)*δ := by
  have hAB (t : ℝ) : |α t*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn t
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) :
      |α t*B-p t*θ-θ^2| ≤ (|B|+|θ|)*δ := by
    have he : α t*B-p t*θ-θ^2=(α t-β)*B-(p t-p₀)*θ := by nlinarith [hroot]
    rw [he]
    calc
      _ ≤ |(α t-β)*B|+|(p t-p₀)*θ| := abs_sub _ _
      _ = |α t-β| *|B|+|p t-p₀| *|θ| := by rw [abs_mul,abs_mul]
      _ ≤ δ*|B|+δ*|θ| := by gcongr;exact hscale t ht;exact hpt t ht
      _ = _ := by ring
  have hh := actual_scalar_baseline_close (hα.mul continuous_const) hp
    (show 0 ≤ M*|B| by positivity) hMp hAB hpn hAp hθ hγ
    (show 0 ≤ (|B|+|θ|)*δ by positivity) hpl hF
  intro t ht
  exact (hh t ht).trans_eq (by ring)

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- Model-specific residuals with the actual scalar PB baseline substituted.
The resulting C is fixed BEFORE all histories, scalar coefficient functions,
period lengths, pulse positions and control parameters. This is the analytic
uniformity required for recursive attainment, not a compactness claim about
an unspecified incoming Riccati matrix. -/
theorem actual_berger_comparison_residuals (r B β p₀ θ γ : ℝ) (D : R)
    {M Z : ℝ} (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hc : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (α p : ℝ → ℝ) (Mp δ T τ : ℝ),
      Continuous α → Continuous p → 0 ≤ Mp → 0 ≤ δ → 0 ≤ τ →
      (∀ t,|α t| ≤ M) → (∀ t,|p t| ≤ Mp) →
      (∀ t,0 ≤ t → 0 ≤ α t*B) →
      (∀ t ∈ Icc 0 T,|α t-β| ≤ δ) →
      (∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ) →
      (∀ t ∈ Icc 0 T,γ ≤ p t) →
      ∀ t ∈ Icc 0 T,∀ z zd zh zhd : ℝ,
        |z| ≤ Z → |zd| ≤ Z → |zh| ≤ Z → |zhd| ≤ Z →
        1+τ*z ∈ Icc (1/2:ℝ) (3/2) →
        let v := scalarBaseline (fun s => α s*B) p θ t
        let S := bergerSlowGenerator r B β p₀ θ z D
        let Sd := bergerSlowGenerator r B β p₀ θ zd D
        let Sh := bergerSlowGenerator r B β p₀ θ zh D
        let Shd := bergerSlowGenerator r B β p₀ θ zhd D
        let Q := v • (1:R)+τ • S
        ‖α t • PulseTaylor.angular r (B • (1:R)) D (1+τ*z)-p t • Q-Q*Q-
          ((α t*B-p t*v-v^2) • (1:R)+(τ^2) • Sd)‖ ≤ C*(δ*τ+τ^2) ∧
        ‖(τ*zh) • (α t • PulseTaylor.angularD r (B • (1:R)) D (1+τ*z))-
          p t • (τ • Sh)-(τ • Sh)*Q-Q*(τ • Sh)-(τ^2) • Shd‖ ≤ C*(δ*τ+τ^2) := by
  obtain ⟨C,hC,hres⟩ := berger_comparison_residuals r B β p₀ θ D hM hZ
    (show 0 ≤ (|B|+|θ|)/γ by positivity) hc
  refine ⟨C,hC,?_⟩
  intro α p Mp δ T τ hα hp hMp hδ hτ hαn hpn hAp hscale hpt hpl t ht z zd zh zhd hz hzd hzh hzhd hq
  exact hres (α t) (p t) (scalarBaseline (fun s => α s*B) p θ t) δ τ z zd zh zhd
    hδ hτ (hαn t) (hscale t ht) (hpt t ht)
    (berger_scalar_baseline_close hα hp hM hMp hθ hγ hδ hαn hpn hAp hroot hscale hpt hpl t ht)
    hz hzd hzh hzhd hq

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The tau-square factor in the source residual is the TRUE time derivative
of the rescaled comparison, not a syntactically assigned jet. -/
lemma bergerComparison_time_deriv (r B β p₀ θ τ : ℝ) (D : R)
    {v z : ℝ → ℝ} {v' z' t : ℝ}
    (hv : HasDerivAt v v' t) (hz : HasDerivAt z z' (τ*t)) :
    HasDerivAt (fun s => v s • (1:R)+τ • bergerSlowGenerator r B β p₀ θ (z (τ*s)) D)
      (v' • (1:R)+(τ^2) • bergerSlowGenerator r B β p₀ θ z' D) t := by
  have hτ : HasDerivAt (fun s : ℝ => τ*s) τ t := by simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul τ
  have hh := (hv.smul_const (1:R)).add
    ((((hz.comp t hτ).const_mul (β/(p₀+2*θ))).smul_const (r • (B • (1:R))+D)).const_smul τ)
  apply hh.congr_deriv
  simp only [bergerSlowGenerator,smul_smul]
  module

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The comparison's parameter variation is its GENUINE Frechet derivative;
the exact scalar baseline is independent of the current control parameter. -/
lemma bergerComparison_parameter_deriv (r B β p₀ θ τ v : ℝ) (D : R)
    {z : H → ℝ} {z' : H →L[ℝ] ℝ} {x : H} (hz : HasFDerivAt z z' x) :
    HasFDerivAt (fun y => v • (1:R)+τ • bergerSlowGenerator r B β p₀ θ (z y) D)
      (z'.smulRight (τ • bergerSlowGenerator r B β p₀ θ 1 D)) x := by
  have h1 := (hz.const_mul (β/(p₀+2*θ))).smul_const (r • (B • (1:R))+D)
  have hh := (h1.const_smul τ).const_add (v • (1:R))
  apply hh.congr_fderiv
  ext h
  simp only [bergerSlowGenerator,ContinuousLinearMap.smulRight_apply,
    smul_apply,smul_smul,mul_one,smul_eq_mul]
  module

/-- True directional derivative of the exact Berger angular coefficient,
including the current scale alpha and slow-pulse factor tau. -/
lemma bergerAngular_parameter_deriv (r B α τ : ℝ) (D : R)
    {z : H → ℝ} {z' : H →L[ℝ] ℝ} {x : H} (hz : HasFDerivAt z z' x)
    (hq : 1+τ*z x ≠ 0) :
    HasFDerivAt (fun y => α • PulseTaylor.angular r (B • (1:R)) D (1+τ*z y))
      (z'.smulRight ((α*τ) • PulseTaylor.angularD r (B • (1:R)) D (1+τ*z x))) x := by
  have hh := (((PulseTaylor.angular_hasDerivAt r (B • (1:R)) D hq).hasFDerivAt).comp x
    ((hz.const_mul τ).const_add 1)).const_smul α
  apply hh.congr_fderiv
  ext h
  simp only [ContinuousLinearMap.smulRight_apply,smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    smul_smul,smul_eq_mul]
  module

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Positivity of the comparison follows from a small pulse and the actual
positive scalar baseline. Symmetry is not used or silently assumed here. -/
lemma scalar_plus_small_positive {S : E →L[ℝ] E} {v τ C : ℝ}
    (hτ : 0 ≤ τ) (hSn : ‖S‖ ≤ C) (hgap : τ*C ≤ v) :
    ∀ x : E,0 ≤ inner ℝ x ((v • (1:E →L[ℝ] E)+τ • S) x) := by
  intro x
  have hn := S.le_opNorm x
  have hb : ‖S x‖ ≤ C*‖x‖ := hn.trans (mul_le_mul_of_nonneg_right hSn (norm_nonneg x))
  have hh := neg_le_of_abs_le (abs_real_inner_le_norm x (S x))
  have he := mul_le_mul_of_nonneg_left hb (norm_nonneg x)
  have hτh := mul_le_mul_of_nonneg_left hh hτ
  have ht := mul_le_mul_of_nonneg_left he hτ
  have hv := mul_le_mul_of_nonneg_right hgap (sq_nonneg ‖x‖)
  simp only [add_apply,smul_apply,
    one_apply_eq_self,inner_add_right,inner_smul_right, real_inner_self_eq_norm_sq]
  nlinarith

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open MeasureTheory Set

/-- Global measurability of the genuine quotient holds even at irrelevant
negative-time zeros. No global nonvanishing hypothesis is needed for FTC. -/
lemma scalarBaseline_stronglyMeasurable {A p : ℝ → ℝ}
    (hA : Continuous A) (hp : Continuous p) {MA Mp : ℝ}
    (hMA : 0 ≤ MA) (hMp : 0 ≤ Mp) (hAn : ∀ t,|A t| ≤ MA)
    (hpn : ∀ t,|p t| ≤ Mp) (θ : ℝ) :
    StronglyMeasurable (scalarBaseline A p θ) := by
  have hy : Continuous (fun t => (scalarPhase A p 1 θ t).1) :=
    continuous_iff_continuousAt.2 fun t =>
      (scalarPhase_value_deriv hA hp hMA hMp hAn hpn 1 θ t).continuousAt
  have hv : Continuous (fun t => (scalarPhase A p 1 θ t).2) :=
    continuous_iff_continuousAt.2 fun t =>
      (scalarPhase_velocity_deriv hA hp hMA hMp hAn hpn 1 θ t).continuousAt
  exact (hv.measurable.div hy.measurable).stronglyMeasurable

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]

/-- The actual comparison used in the slow pulse: the scalar part is built
from PB flow, not chosen as an unproved solution of a Riccati equation. -/
def actualBergerComparison (α p : ℝ → ℝ) (r B β p₀ θ τ : ℝ) (D : R)
    (z : ℝ → ℝ) (t : ℝ) : R :=
  scalarBaseline (fun s => α s*B) p θ t • (1:R)+
    τ • bergerSlowGenerator r B β p₀ θ (z (τ*t)) D

lemma actualBergerComparison_deriv {α p : ℝ → ℝ}
    (hα : Continuous α) (hp : Continuous p) {M Mp B : ℝ}
    (hM : 0 ≤ M) (hMp : 0 ≤ Mp) (hαn : ∀ t,|α t| ≤ M)
    (hpn : ∀ t,|p t| ≤ Mp) (hAp : ∀ t,0 ≤ t → 0 ≤ α t*B)
    {θ : ℝ} (hθ : 0 ≤ θ) (r β p₀ τ : ℝ) (D : R)
    {z : ℝ → ℝ} {zd t : ℝ} (ht : 0 ≤ t) (hz : HasDerivAt z zd (τ*t)) :
    let v := scalarBaseline (fun s => α s*B) p θ t
    HasDerivAt (actualBergerComparison α p r B β p₀ θ τ D z)
      ((α t*B-p t*v-v^2) • (1:R)+(τ^2) • bergerSlowGenerator r B β p₀ θ zd D) t := by
  have hn (s : ℝ) : |α s*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn s
  exact bergerComparison_time_deriv r B β p₀ θ τ D
    (actual_scalar_baseline_deriv (hα.mul continuous_const) hp (by positivity) hMp hn hpn hAp hθ ht) hz

lemma actualBergerComparison_initial (α p : ℝ → ℝ) (r B β p₀ θ τ : ℝ) (D : R)
    {z : ℝ → ℝ} (hz : z 0=0) :
    actualBergerComparison α p r B β p₀ θ τ D z 0=θ • (1:R) := by
  simp only [actualBergerComparison,scalarBaseline_init,mul_zero,hz,bergerSlowGenerator,
    zero_smul,smul_zero,add_zero]

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The comparison's parameter jet is actual Frechet differentiation of the
PB-based expression. The baseline does not depend on the current parameter. -/
lemma actualBergerComparison_parameter_deriv (α p : ℝ → ℝ) (r B β p₀ θ τ : ℝ) (D : R)
    {z : H → ℝ → ℝ} {z' : H →L[ℝ] ℝ} {x : H} (t : ℝ)
    (hz : HasFDerivAt (fun y => z y (τ*t)) z' x) :
    HasFDerivAt (fun y => actualBergerComparison α p r B β p₀ θ τ D (z y) t)
      (z'.smulRight (τ • bergerSlowGenerator r B β p₀ θ 1 D)) x :=
  bergerComparison_parameter_deriv r B β p₀ θ τ _ D hz

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma scalar_plus_small_coercive {S : E →L[ℝ] E} {v τ C : ℝ}
    (hτ : 0 ≤ τ) (hSn : ‖S‖ ≤ C) :
    ∀ x : E,(v-τ*C)*‖x‖^2 ≤ inner ℝ x ((v • (1:E →L[ℝ] E)+τ • S) x) := by
  intro x
  have hb : ‖S x‖ ≤ C*‖x‖ := (S.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hSn (norm_nonneg x))
  have hh := neg_le_of_abs_le (abs_real_inner_le_norm x (S x))
  have he := mul_le_mul_of_nonneg_left hb (norm_nonneg x)
  have hτh := mul_le_mul_of_nonneg_left hh hτ
  have ht := mul_le_mul_of_nonneg_left he hτ
  simp only [add_apply,smul_apply,one_apply_eq_self,inner_add_right,inner_smul_right,
    real_inner_self_eq_norm_sq]
  nlinarith

/-- Uniform positivity of the actual comparison is derived from the actual
baseline estimate and smallness conditions, not assumed for the Riccati bound. -/
lemma actualBergerComparison_coercive {α p : ℝ → ℝ}
    (hα : Continuous α) (hp : Continuous p) {M Mp B β p₀ θ γ δ T τ r Z : ℝ}
    (hM : 0 ≤ M) (hMp : 0 ≤ Mp) (hθ : 0 ≤ θ) (hγ : 0 < γ) (hδ : 0 ≤ δ)
    (hτ : 0 ≤ τ) (hαn : ∀ t,|α t| ≤ M) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ α t*B) (hroot : β*B-p₀*θ-θ^2=0)
    (hscale : ∀ t ∈ Set.Icc 0 T,|α t-β| ≤ δ)
    (hpt : ∀ t ∈ Set.Icc 0 T,|p t-p₀| ≤ δ)
    (hpl : ∀ t ∈ Set.Icc 0 T,γ ≤ p t)
    (D : E →L[ℝ] E) {z : ℝ → ℝ}
    (hz : ∀ t ∈ Set.Icc 0 T,|z (τ*t)| ≤ Z)
    (hsmall : ((|B|+|θ|)/γ)*δ+
      τ*(|β/(p₀+2*θ)| * Z * ‖r • (B • (1:E →L[ℝ] E))+D‖) ≤ θ/2) :
    ∀ t ∈ Set.Icc 0 T,∀ x : E,
      (θ/2)*‖x‖^2 ≤ inner ℝ x (actualBergerComparison α p r B β p₀ θ τ D z t x) := by
  intro t ht x
  have hv := neg_le_of_abs_le
    (berger_scalar_baseline_close hα hp hM hMp hθ hγ hδ hαn hpn hAp hroot hscale hpt hpl t ht)
  have hn : ‖bergerSlowGenerator r B β p₀ θ (z (τ*t)) D‖ ≤
      |β/(p₀+2*θ)| * Z * ‖r • (B • (1:E →L[ℝ] E))+D‖ := by
    simp only [bergerSlowGenerator,norm_smul,Real.norm_eq_abs,abs_mul]
    gcongr
    exact hz t ht
  have hh := scalar_plus_small_coercive
    (v := scalarBaseline (fun s => α s*B) p θ t) hτ hn x
  have hnum : θ/2 ≤ scalarBaseline (fun s => α s*B) p θ t-
      τ*(|β/(p₀+2*θ)| * Z * ‖r • (B • (1:E →L[ℝ] E))+D‖) := by linarith
  exact (mul_le_mul_of_nonneg_right hnum (sq_nonneg ‖x‖)).trans hh

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open Set Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

/-- Actual Berger pulse, with the nonlinear angular coefficient and exact
scalar Peano--Baker baseline substituted into the actual center-regular
Riccati and variational equations. The constant is chosen before all histories,
start times, durations, scalar backgrounds, and pulse shapes. -/
theorem actual_berger_pulse_integrated (basis : OrthonormalBasis ι ℝ E)
    (r B β p₀ θ γ : ℝ) (D : E →L[ℝ] E) {M Z : ℝ}
    (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hc : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
      (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
      (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (x h : H)
      (α p z zd zh zhd : ℝ → ℝ) (Mp MB MA Mb l B₀ a T δ ε : ℝ),
      Continuous (A x) → Continuous b → Continuous (B' x) →
      Continuous (fun t => A' x t h) →
      (∀ t v w,B' x t v w=(0,A' x t v*w.1)) →
      0 ≤ MB → 0 ≤ MA → 0 ≤ Mb →
      (∀ t,‖block (leftAction (A x)) b t‖ ≤ MB) → (∀ t,‖B' x t‖ ≤ MB) →
      (∀ t,‖A x t‖ ≤ MA) → (∀ t,|b t| ≤ Mb) →
      (∀ t v,0 ≤ inner ℝ v (A x t v)) → 0 < l →
      (∀ t ≤ 0,∀ v,A x t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      Continuous α → Continuous p → 0 ≤ Mp →
      (∀ t,|α t| ≤ M) → (∀ t,|p t| ≤ Mp) → (∀ t,0 ≤ t → 0 ≤ α t*B) →
      0 ≤ a → 1 ≤ T → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc 0 T,|α t-β| ≤ δ) → (∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ) →
      (∀ t ∈ Icc 0 T,γ ≤ p t) →
      (∀ u,HasDerivAt z (zd u) u) → (∀ u,HasDerivAt zh (zhd u) u) →
      Continuous zd → Continuous zhd → z 0=0 → zh 0=0 →
      (∀ t ∈ Icc 0 T,|z (T⁻¹*t)| ≤ Z ∧ |zd (T⁻¹*t)| ≤ Z ∧
        |zh (T⁻¹*t)| ≤ Z ∧ |zhd (T⁻¹*t)| ≤ Z) →
      (∀ t ∈ Icc 0 T,1+T⁻¹*z (T⁻¹*t) ∈ Icc (1/2:ℝ) (3/2)) →
      ((|B|+|θ|)/γ)*δ+T⁻¹*(|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D‖) ≤ θ/2 →
      (∀ t ∈ Icc a (a+T),b t=p (t-a)) →
      (∀ t ∈ Icc a (a+T),A x t=
        α (t-a) • PulseTaylor.angular r (B • (1:E →L[ℝ] E)) D (1+T⁻¹*z (T⁻¹*(t-a)))) →
      (∀ t ∈ Icc a (a+T),A' x t h=
        (T⁻¹*zh (T⁻¹*(t-a))) • (α (t-a) •
          PulseTaylor.angularD r (B • (1:E →L[ℝ] E)) D (1+T⁻¹*z (T⁻¹*(t-a))))) →
      ‖orthogonalMatrix basis (slope (A x) b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      orthogonalMatrix basis (slopeJet A b B' l x a h)=0 →
      let Q := fun t => orthogonalMatrix basis
        (actualBergerComparison α p r B β p₀ θ T⁻¹ D z (t-a))
      let Qh := fun t => orthogonalMatrix basis
        (T⁻¹ • bergerSlowGenerator r B β p₀ θ (zh (T⁻¹*(t-a))) D)
      (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖) ≤
        2*C*(δ+T⁻¹+ε)/γ ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b B' l x t h)-Qh t‖) ≤
        C*(δ+T⁻¹+ε)/γ+4*C^2*(δ+T⁻¹+ε)/γ^2 := by
  obtain ⟨R,hR,hres⟩ := actual_berger_comparison_residuals r B β p₀ θ γ D hM hZ hθ hγ hc hroot
  let G := |β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D‖
  let L := orthogonalMatrix basis
  let C := 1+‖L‖*(R+G)
  have hG : 0 ≤ G := by dsimp [G];positivity
  have hC₁ : 1 ≤ C := by dsimp [C];exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg L) (add_nonneg hR hG))
  have hC : 0 ≤ C := zero_le_one.trans hC₁
  have hCR : ‖L‖*R ≤ C := by dsimp [C];nlinarith [norm_nonneg L,mul_nonneg (norm_nonneg L) hG]
  have hCG : ‖L‖*G ≤ C := by dsimp [C];nlinarith [norm_nonneg L,mul_nonneg (norm_nonneg L) hR]
  refine ⟨C,hC₁,?_⟩
  intro A b B' A' x h α p z zd zh zhd Mp MB MA Mb l B₀ a T δ ε
    hA hb hB' hA' hBeval hMB hMA hMb hnB hnB' hnA hnb hAp hl hAc hbc
    hα hp hMp hαn hpn hαp ha hT hδ hε hscale hpt hpl hzd hzhd hczd hczhd hz₀ hzh₀
    hzn hq hsmall hbmodel hAmodel hA'model hinit hjet
  let τ := T⁻¹
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hτ : 0 ≤ τ := inv_nonneg.mpr hT₀.le
  let v := scalarBaseline (fun s => α s*B) p θ
  let S := fun u => bergerSlowGenerator r B β p₀ θ u D
  let q := actualBergerComparison α p r B β p₀ θ τ D z
  let qd := fun t => (α t*B-p t*v t-(v t)^2) • (1:E →L[ℝ] E)+(τ^2) • S (zd (τ*t))
  let qh := fun t => τ • S (zh (τ*t))
  let qhd := fun t => (τ^2) • S (zhd (τ*t))
  let Q := fun t => L (q (t-a))
  let Qd := fun t => L (qd (t-a))
  let Qh := fun t => L (qh (t-a))
  let Qhd := fun t => L (qhd (t-a))
  have hshift (t : ℝ) (ht : t ∈ Icc a (a+T)) : t-a ∈ Icc 0 T := by
    constructor <;> linarith [ht.1,ht.2]
  have hdq (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt q (qd t) t :=
    actualBergerComparison_deriv hα hp hM hMp hαn hpn hαp hθ r β p₀ τ D ht.1 (hzd _)
  have hdqh (t : ℝ) : HasDerivAt qh (qhd t) t := by
    have htau : HasDerivAt (fun s : ℝ => τ*s) τ t := by
      simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul τ
    have hh := ((((hzhd (τ*t)).comp t htau).const_mul (β/(p₀+2*θ))).smul_const
      (r • (B • (1:E →L[ℝ] E))+D)).const_smul τ
    apply hh.congr_deriv
    dsimp [qh,qhd,S,bergerSlowGenerator]
    simp only [smul_smul]
    module
  have hdQ (t : ℝ) (ht : t ∈ Icc a (a+T)) : HasDerivAt Q (Qd t) t := by
    simpa only [Q,Qd,L,Function.comp_def,id_eq,one_smul] using orthogonalMatrix_hasDerivAt basis
      ((hdq (t-a) (hshift t ht)).scomp t ((hasDerivAt_id t).sub_const a))
  have hdQh (t : ℝ) (_ht : t ∈ Icc a (a+T)) : HasDerivAt Qh (Qhd t) t := by
    simpa only [Qh,Qhd,L,Function.comp_def,id_eq,one_smul] using orthogonalMatrix_hasDerivAt basis
      ((hdqh (t-a)).scomp t ((hasDerivAt_id t).sub_const a))
  have hvc : ContinuousOn v (Icc 0 T) := fun t ht => by
    have hn (s : ℝ) : |α s*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn s
    exact (actual_scalar_baseline_deriv (hα.mul continuous_const) hp
      (by positivity) hMp hn hpn hαp hθ ht.1).continuousAt.continuousWithinAt
  have hSc : Continuous S := by unfold S bergerSlowGenerator;fun_prop
  have hqdc : ContinuousOn qd (Icc 0 T) := by
    exact (((hα.continuousOn.mul_const B).sub (hp.continuousOn.mul hvc)).sub
      (hvc.pow 2)).smul continuousOn_const |>.add
        ((hSc.comp (hczd.comp ((continuous_const : Continuous (fun _ : ℝ => τ)).mul continuous_id))).continuousOn.const_smul (τ^2))
  have hqhdc : Continuous qhd :=
    (hSc.comp (hczhd.comp ((continuous_const : Continuous (fun _ : ℝ => τ)).mul continuous_id))).const_smul (τ^2)
  have hQdc : ContinuousOn Qd (Icc a (a+T)) :=
    L.continuous.comp_continuousOn (hqdc.comp (continuous_id.sub continuous_const).continuousOn hshift)
  have hQhdc : ContinuousOn Qhd (Icc a (a+T)) :=
    (L.continuous.comp (hqhdc.comp (continuous_id.sub continuous_const))).continuousOn
  have hQpos (t : ℝ) (ht : t ∈ Icc a (a+T)) (w : ι → ℝ) :
      0 ≤ ∑ i,∑ j,w i*Q t i j*w j := by
    have hh := actualBergerComparison_coercive hα hp hM hMp hθ hγ hδ hτ hαn hpn hαp
      hroot hscale hpt hpl D (fun s hs => (hzn s hs).1) hsmall (t-a) (hshift t ht)
    have hm := orthogonalMatrix_coercive basis (q (t-a)) hh w
    exact (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg (w i))).trans hm
  have hSn (u : ℝ) (hu : |u| ≤ Z) : ‖S u‖ ≤ G := by
    dsimp [S,bergerSlowGenerator,G]
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    gcongr
  have hη : 0 ≤ δ+τ+ε := by positivity
  have hbound : δ*τ+τ^2 ≤ (δ+τ+ε)/T := by
    rw [div_eq_mul_inv]
    change δ*τ+τ^2 ≤ (δ+τ+ε)*τ
    nlinarith [mul_nonneg hε hτ]
  have hρt (t : ℝ) (ht : t ∈ Icc a (a+T)) :=
    hres α p Mp δ T τ hα hp hMp hδ hτ hαn hpn hαp hscale hpt hpl
      (t-a) (hshift t ht) (z (τ*(t-a))) (zd (τ*(t-a))) (zh (τ*(t-a))) (zhd (τ*(t-a)))
      (hzn (t-a) (hshift t ht)).1 (hzn (t-a) (hshift t ht)).2.1
      (hzn (t-a) (hshift t ht)).2.2.1 (hzn (t-a) (hshift t ht)).2.2.2
      (hq (t-a) (hshift t ht))
  have hρ (t : ℝ) (ht : t ∈ Icc a (a+T)) :
      ‖L (A x t)-b t • Q t-Q t*Q t-Qd t‖ ≤ C*(δ+τ+ε)/T := by
    have hh := (L.le_opNorm
      (A x t-b t • q (t-a)-q (t-a)*q (t-a)-qd (t-a)))
    have he : ‖A x t-b t • q (t-a)-q (t-a)*q (t-a)-qd (t-a)‖ ≤ R*(δ*τ+τ^2) := by
      rw [hAmodel t ht,hbmodel t ht]
      exact (hρt t ht).1
    have hh' := hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg L))
    change ‖orthogonalMatrix basis _‖ ≤ ‖L‖*(R*(δ*τ+τ^2)) at hh'
    simp only [map_sub,map_smul,orthogonalMatrix_mul] at hh'
    calc
      _ ≤ ‖L‖*(R*(δ*τ+τ^2)) := hh'
      _ = (‖L‖*R)*(δ*τ+τ^2) := by ring
      _ ≤ C*((δ+τ+ε)/T) := mul_le_mul hCR hbound (by positivity) hC
      _ = _ := by ring
  have hρh (t : ℝ) (ht : t ∈ Icc a (a+T)) :
      ‖L (A' x t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhd t‖ ≤ C*(δ+τ+ε)/T := by
    have hh := L.le_opNorm
      (A' x t h-b t • qh (t-a)-qh (t-a)*q (t-a)-q (t-a)*qh (t-a)-qhd (t-a))
    have he : ‖A' x t h-b t • qh (t-a)-qh (t-a)*q (t-a)-q (t-a)*qh (t-a)-qhd (t-a)‖ ≤ R*(δ*τ+τ^2) := by
      rw [hA'model t ht,hbmodel t ht]
      exact (hρt t ht).2
    have hh' := hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg L))
    change ‖orthogonalMatrix basis _‖ ≤ ‖L‖*(R*(δ*τ+τ^2)) at hh'
    simp only [map_sub,map_smul,orthogonalMatrix_mul] at hh'
    calc
      _ ≤ ‖L‖*(R*(δ*τ+τ^2)) := hh'
      _ = (‖L‖*R)*(δ*τ+τ^2) := by ring
      _ ≤ C*((δ+τ+ε)/T) := mul_le_mul hCR hbound (by positivity) hC
      _ = _ := by ring
  have hQhn (t : ℝ) (ht : t ∈ Icc a (a+T)) : ‖Qh t‖ ≤ C/T := by
    calc
      _ ≤ ‖L‖*‖qh (t-a)‖ := L.le_opNorm _
      _ = ‖L‖*(τ*‖S (zh (τ*(t-a)))‖) := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hτ]
      _ ≤ ‖L‖*(τ*G) := by gcongr;exact hSn _ (hzn (t-a) (hshift t ht)).2.2.1
      _ = (‖L‖*G)/T := by dsimp [τ];ring
      _ ≤ C/T := div_le_div_of_nonneg_right hCG hT₀.le
  have hQi : Q a=θ • (1:Matrix ι ι ℝ) := by
    dsimp only [Q,q,L]
    rw [sub_self,actualBergerComparison_initial α p r B β p₀ θ τ D hz₀,map_smul,orthogonalMatrix_one]
  have hQhi : Qh a=0 := by
    dsimp [Qh,qh,S,τ,bergerSlowGenerator]
    simp only [sub_self,mul_zero,hzh₀,zero_smul,smul_zero,map_zero]
  have hini : ‖L (slope (A x) b l a)-Q a‖ ≤ C*(δ+τ+ε) := by
    rw [hQi]
    apply hinit.trans
    have he : ε ≤ δ+τ+ε := by linarith
    exact he.trans (le_mul_of_one_le_left hη hC₁)
  exact actual_slow_pulse_integrated_on basis A b B' A' x h hA hb hB' hA' hBeval
    hMB hMA hMb hnB hnB' hnA hnb hAp hl hAc hbc Q Qd Qh Qhd
    hdQ hdQh hQdc hQhdc ha hT hγ hC hη
    (fun t ht => by rw [hbmodel t ht];exact hpl (t-a) (hshift t ht))
    hQpos hρ hρh hQhn hini (by rw [hjet,hQhi])

end HarmonicCounterexample.LinearODE

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set

namespace HarmonicCounterexample.LinearODE
open Set Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [Fintype κ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [Fintype ι] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

local instance : NormedAddCommGroup ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ ((E →L[ℝ] E) →L[ℝ] Matrix ι ι ℝ) := ContinuousLinearMap.toNormedSpace

/-- Actual finite switched Berger word: its angular generator can change on
round gaps. The smooth first-order coefficient and its derivative are supplied
by the explicit finite pulse family, not by differentiating a discontinuous
selector. Nonlinear residuals are produced uniformly over the FINITE library.
The one constant is chosen before every history, selector, shape and duration. -/
theorem actual_switched_berger_estimates (basis : OrthonormalBasis ι ℝ E)
    (r B β p₀ θ γ : ℝ) (D : κ → E →L[ℝ] E) {M Z : ℝ}
    (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hc : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
      (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
      (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (x h : H)
      (α p z zd zh zhd : ℝ → ℝ) (d : ℝ → κ)
      (S Sd Sh Shd : ℝ → E →L[ℝ] E) (Mp MB MA Mb l B₀ a T δ ε : ℝ),
      Continuous (A x) → Continuous b → Continuous (B' x) →
      Continuous (fun t => A' x t h) →
      (∀ t v w,B' x t v w=(0,A' x t v*w.1)) →
      0 ≤ MB → 0 ≤ MA → 0 ≤ Mb →
      (∀ t,‖block (leftAction (A x)) b t‖ ≤ MB) → (∀ t,‖B' x t‖ ≤ MB) →
      (∀ t,‖A x t‖ ≤ MA) → (∀ t,|b t| ≤ Mb) →
      (∀ t v,0 ≤ inner ℝ v (A x t v)) → 0 < l →
      (∀ t ≤ 0,∀ v,A x t v=(l*(l+B₀)) • v) → (∀ t ≤ 0,b t=B₀) →
      Continuous α → Continuous p → 0 ≤ Mp →
      (∀ t,|α t| ≤ M) → (∀ t,|p t| ≤ Mp) → (∀ t,0 ≤ t → 0 ≤ α t*B) →
      0 ≤ a → 1 ≤ T → 0 ≤ δ → 0 ≤ ε →
      (∀ t ∈ Icc 0 T,|α t-β| ≤ δ) → (∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ) →
      (∀ t ∈ Icc 0 T,γ ≤ p t) →
      (∀ u,HasDerivAt S (Sd u) u) → (∀ u,HasDerivAt Sh (Shd u) u) →
      Continuous Sd → Continuous Shd → S 0=0 → Sh 0=0 →
      (∀ u,S u=bergerSlowGenerator r B β p₀ θ (z u) (D (d u)) ∧
        Sd u=bergerSlowGenerator r B β p₀ θ (zd u) (D (d u)) ∧
        Sh u=bergerSlowGenerator r B β p₀ θ (zh u) (D (d u)) ∧
        Shd u=bergerSlowGenerator r B β p₀ θ (zhd u) (D (d u))) →
      (∀ t ∈ Icc 0 T,|z (T⁻¹*t)| ≤ Z ∧ |zd (T⁻¹*t)| ≤ Z ∧
        |zh (T⁻¹*t)| ≤ Z ∧ |zhd (T⁻¹*t)| ≤ Z) →
      (∀ t ∈ Icc 0 T,1+T⁻¹*z (T⁻¹*t) ∈ Icc (1/2:ℝ) (3/2)) →
      ((|B|+|θ|)/γ)*δ+T⁻¹*(∑ j : κ,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ θ/2 →
      (∀ t ∈ Icc a (a+T),b t=p (t-a)) →
      (∀ t ∈ Icc a (a+T),A x t=
        α (t-a) • PulseTaylor.angular r (B • (1:E →L[ℝ] E)) (D (d (T⁻¹*(t-a)))) (1+T⁻¹*z (T⁻¹*(t-a)))) →
      (∀ t ∈ Icc a (a+T),A' x t h=
        (T⁻¹*zh (T⁻¹*(t-a))) • (α (t-a) •
          PulseTaylor.angularD r (B • (1:E →L[ℝ] E)) (D (d (T⁻¹*(t-a)))) (1+T⁻¹*z (T⁻¹*(t-a))))) →
      ‖orthogonalMatrix basis (slope (A x) b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      orthogonalMatrix basis (slopeJet A b B' l x a h)=0 →
      let Q := fun t => orthogonalMatrix basis
        (scalarBaseline (fun s => α s*B) p θ (t-a) • (1:E →L[ℝ] E)+T⁻¹ • S (T⁻¹*(t-a)))
      let Qh := fun t => orthogonalMatrix basis
        (T⁻¹ • Sh (T⁻¹*(t-a)))
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖ ≤
        (C+C/γ)*(δ+T⁻¹+ε)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖) ≤
        2*C*(δ+T⁻¹+ε)/γ ∧
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slopeJet A b B' l x t h)-Qh t‖ ≤
        (C+2*C*(C+C/γ))*(δ+T⁻¹+ε)/(γ*T)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b B' l x t h)-Qh t‖) ≤
        C*(δ+T⁻¹+ε)/γ+4*C^2*(δ+T⁻¹+ε)/γ^2 := by
  choose Rs hRs hres using fun j : κ =>
    actual_berger_comparison_residuals r B β p₀ θ γ (D j) hM hZ hθ hγ hc hroot
  let R := ∑ j : κ,Rs j
  let Gs := fun j : κ => |β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖
  let G := ∑ j : κ,Gs j
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ => hRs j
  have hRj (j : κ) : Rs j ≤ R := Finset.single_le_sum (fun i _ => hRs i) (Finset.mem_univ j)
  have hGs (j : κ) : 0 ≤ Gs j := by dsimp [Gs];positivity
  have hGj (j : κ) : Gs j ≤ G := Finset.single_le_sum (fun i _ => hGs i) (Finset.mem_univ j)
  let L := orthogonalMatrix basis
  let C := 1+‖L‖*(R+G)
  have hG : 0 ≤ G := Finset.sum_nonneg fun j _ => hGs j
  have hC₁ : 1 ≤ C := by dsimp [C];exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg L) (add_nonneg hR hG))
  have hC : 0 ≤ C := zero_le_one.trans hC₁
  have hCR : ‖L‖*R ≤ C := by dsimp [C];nlinarith [norm_nonneg L,mul_nonneg (norm_nonneg L) hG]
  have hCG : ‖L‖*G ≤ C := by dsimp [C];nlinarith [norm_nonneg L,mul_nonneg (norm_nonneg L) hR]
  refine ⟨C,hC₁,?_⟩
  intro A b B' A' x h α p z zd zh zhd d S Sd Sh Shd Mp MB MA Mb l B₀ a T δ ε
    hA hb hB' hA' hBeval hMB hMA hMb hnB hnB' hnA hnb hAp hl hAc hbc
    hα hp hMp hαn hpn hαp ha hT hδ hε hscale hpt hpl hSd hShd hcSd hcShd hS₀ hSh₀ hshape
    hzn hq hsmall hbmodel hAmodel hA'model hinit hjet
  let τ := T⁻¹
  have hT₀ : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hτ : 0 ≤ τ := inv_nonneg.mpr hT₀.le
  let v := scalarBaseline (fun s => α s*B) p θ
  let q := fun t => v t • (1:E →L[ℝ] E)+τ • S (τ*t)
  let qd := fun t => (α t*B-p t*v t-(v t)^2) • (1:E →L[ℝ] E)+(τ^2) • Sd (τ*t)
  let qh := fun t => τ • Sh (τ*t)
  let qhd := fun t => (τ^2) • Shd (τ*t)
  let Q := fun t => L (q (t-a))
  let Qd := fun t => L (qd (t-a))
  let Qh := fun t => L (qh (t-a))
  let Qhd := fun t => L (qhd (t-a))
  have hshift (t : ℝ) (ht : t ∈ Icc a (a+T)) : t-a ∈ Icc 0 T := by
    constructor <;> linarith [ht.1,ht.2]
  have hαBn (s : ℝ) : |α s*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn s
  have hdv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt v (α t*B-p t*v t-(v t)^2) t :=
    actual_scalar_baseline_deriv (hα.mul continuous_const) hp
      (by positivity) hMp hαBn hpn hαp hθ ht
  have hτd (t : ℝ) : HasDerivAt (fun s : ℝ => τ*s) τ t := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id t).const_mul τ
  have hdq (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt q (qd t) t := by
    have hh := ((hdv t ht.1).smul_const (1:E →L[ℝ] E)).add
      (((hSd (τ*t)).scomp t (hτd t)).const_smul τ)
    apply hh.congr_deriv
    dsimp [qd]
    simp only [smul_smul,pow_two]
  have hdqh (t : ℝ) : HasDerivAt qh (qhd t) t := by
    have hh := ((hShd (τ*t)).scomp t (hτd t)).const_smul τ
    apply hh.congr_deriv
    dsimp [qh,qhd]
    simp only [smul_smul,pow_two]
  have hdQ (t : ℝ) (ht : t ∈ Icc a (a+T)) : HasDerivAt Q (Qd t) t := by
    simpa only [Q,Qd,L,Function.comp_def,id_eq,one_smul] using orthogonalMatrix_hasDerivAt basis
      ((hdq (t-a) (hshift t ht)).scomp t ((hasDerivAt_id t).sub_const a))
  have hdQh (t : ℝ) (_ht : t ∈ Icc a (a+T)) : HasDerivAt Qh (Qhd t) t := by
    simpa only [Qh,Qhd,L,Function.comp_def,id_eq,one_smul] using orthogonalMatrix_hasDerivAt basis
      ((hdqh (t-a)).scomp t ((hasDerivAt_id t).sub_const a))
  have hvc : ContinuousOn v (Icc 0 T) := fun t ht => by
    have hn (s : ℝ) : |α s*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn s
    exact (actual_scalar_baseline_deriv (hα.mul continuous_const) hp
      (by positivity) hMp hn hpn hαp hθ ht.1).continuousAt.continuousWithinAt
  have hqdc : ContinuousOn qd (Icc 0 T) := by
    exact (((hα.continuousOn.mul_const B).sub (hp.continuousOn.mul hvc)).sub
      (hvc.pow 2)).smul continuousOn_const |>.add
        ((hcSd.comp (continuous_const.mul continuous_id)).continuousOn.const_smul (τ^2))
  have hqhdc : Continuous qhd :=
    (hcShd.comp (continuous_const.mul continuous_id)).const_smul (τ^2)
  have hQdc : ContinuousOn Qd (Icc a (a+T)) :=
    L.continuous.comp_continuousOn (hqdc.comp (continuous_id.sub continuous_const).continuousOn hshift)
  have hQhdc : ContinuousOn Qhd (Icc a (a+T)) :=
    (L.continuous.comp (hqhdc.comp (continuous_id.sub continuous_const))).continuousOn
  have hgen (j : κ) (u : ℝ) (hu : |u| ≤ Z) :
      ‖bergerSlowGenerator r B β p₀ θ u (D j)‖ ≤ G := by
    apply le_trans _ (hGj j)
    dsimp [bergerSlowGenerator,Gs]
    rw [norm_smul,Real.norm_eq_abs,abs_mul]
    gcongr
  have hSn (t : ℝ) (ht : t ∈ Icc 0 T) : ‖S (τ*t)‖ ≤ G := by
    rw [(hshape (τ*t)).1];exact hgen _ _ (hzn t ht).1
  have hShn (t : ℝ) (ht : t ∈ Icc 0 T) : ‖Sh (τ*t)‖ ≤ G := by
    rw [(hshape (τ*t)).2.2.1];exact hgen _ _ (hzn t ht).2.2.1
  have hQpos (t : ℝ) (ht : t ∈ Icc a (a+T)) (w : ι → ℝ) :
      0 ≤ ∑ i,∑ j,w i*Q t i j*w j := by
    have hh (y : E) : (θ/2)*‖y‖^2 ≤ inner ℝ y (q (t-a) y) := by
      have hv := neg_le_of_abs_le
        (berger_scalar_baseline_close hα hp hM hMp hθ hγ hδ hαn hpn hαp hroot hscale hpt hpl
          (t-a) (hshift t ht))
      have hco := scalar_plus_small_coercive (v := v (t-a)) hτ (hSn (t-a) (hshift t ht)) y
      have hnum : θ/2 ≤ v (t-a)-τ*G := by dsimp only [G,Gs,τ] at *;linarith
      exact (mul_le_mul_of_nonneg_right hnum (sq_nonneg ‖y‖)).trans hco
    have hm := orthogonalMatrix_coercive basis (q (t-a)) hh w
    exact (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg (w i))).trans hm
  have hη : 0 ≤ δ+τ+ε := by positivity
  have hbound : δ*τ+τ^2 ≤ (δ+τ+ε)/T := by
    rw [div_eq_mul_inv]
    change δ*τ+τ^2 ≤ (δ+τ+ε)*τ
    nlinarith [mul_nonneg hε hτ]
  have hρt (t : ℝ) (ht : t ∈ Icc a (a+T)) :=
    hres (d (τ*(t-a))) α p Mp δ T τ hα hp hMp hδ hτ hαn hpn hαp hscale hpt hpl
      (t-a) (hshift t ht) (z (τ*(t-a))) (zd (τ*(t-a))) (zh (τ*(t-a))) (zhd (τ*(t-a)))
      (hzn (t-a) (hshift t ht)).1 (hzn (t-a) (hshift t ht)).2.1
      (hzn (t-a) (hshift t ht)).2.2.1 (hzn (t-a) (hshift t ht)).2.2.2
      (hq (t-a) (hshift t ht))
  have hρ (t : ℝ) (ht : t ∈ Icc a (a+T)) :
      ‖L (A x t)-b t • Q t-Q t*Q t-Qd t‖ ≤ C*(δ+τ+ε)/T := by
    have hh := (L.le_opNorm
      (A x t-b t • q (t-a)-q (t-a)*q (t-a)-qd (t-a)))
    have he : ‖A x t-b t • q (t-a)-q (t-a)*q (t-a)-qd (t-a)‖ ≤ R*(δ*τ+τ^2) := by
      rw [hAmodel t ht,hbmodel t ht]
      dsimp only [q,qd]
      rw [(hshape (τ*(t-a))).1,(hshape (τ*(t-a))).2.1]
      exact (hρt t ht).1.trans (mul_le_mul_of_nonneg_right (hRj _) (by positivity))
    have hh' := hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg L))
    change ‖orthogonalMatrix basis _‖ ≤ ‖L‖*(R*(δ*τ+τ^2)) at hh'
    simp only [map_sub,map_smul,orthogonalMatrix_mul] at hh'
    calc
      _ ≤ ‖L‖*(R*(δ*τ+τ^2)) := hh'
      _ = (‖L‖*R)*(δ*τ+τ^2) := by ring
      _ ≤ C*((δ+τ+ε)/T) := mul_le_mul hCR hbound (by positivity) hC
      _ = _ := by ring
  have hρh (t : ℝ) (ht : t ∈ Icc a (a+T)) :
      ‖L (A' x t h)-b t • Qh t-Qh t*Q t-Q t*Qh t-Qhd t‖ ≤ C*(δ+τ+ε)/T := by
    have hh := L.le_opNorm
      (A' x t h-b t • qh (t-a)-qh (t-a)*q (t-a)-q (t-a)*qh (t-a)-qhd (t-a))
    have he : ‖A' x t h-b t • qh (t-a)-qh (t-a)*q (t-a)-q (t-a)*qh (t-a)-qhd (t-a)‖ ≤ R*(δ*τ+τ^2) := by
      rw [hA'model t ht,hbmodel t ht]
      dsimp only [q,qh,qhd]
      rw [(hshape (τ*(t-a))).1,(hshape (τ*(t-a))).2.2.1,(hshape (τ*(t-a))).2.2.2]
      exact (hρt t ht).2.trans (mul_le_mul_of_nonneg_right (hRj _) (by positivity))
    have hh' := hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg L))
    change ‖orthogonalMatrix basis _‖ ≤ ‖L‖*(R*(δ*τ+τ^2)) at hh'
    simp only [map_sub,map_smul,orthogonalMatrix_mul] at hh'
    calc
      _ ≤ ‖L‖*(R*(δ*τ+τ^2)) := hh'
      _ = (‖L‖*R)*(δ*τ+τ^2) := by ring
      _ ≤ C*((δ+τ+ε)/T) := mul_le_mul hCR hbound (by positivity) hC
      _ = _ := by ring
  have hQhn (t : ℝ) (ht : t ∈ Icc a (a+T)) : ‖Qh t‖ ≤ C/T := by
    calc
      _ ≤ ‖L‖*‖qh (t-a)‖ := L.le_opNorm _
      _ = ‖L‖*(τ*‖Sh (τ*(t-a))‖) := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hτ]
      _ ≤ ‖L‖*(τ*G) := by gcongr;exact hShn (t-a) (hshift t ht)
      _ = (‖L‖*G)/T := by dsimp [τ];ring
      _ ≤ C/T := div_le_div_of_nonneg_right hCG hT₀.le
  have hQi : Q a=θ • (1:Matrix ι ι ℝ) := by
    dsimp only [Q,q,L,v]
    simp only [sub_self,scalarBaseline_init,mul_zero,hS₀,smul_zero,add_zero,map_smul,orthogonalMatrix_one]
  have hQhi : Qh a=0 := by
    dsimp only [Qh,qh,L]
    simp only [sub_self,mul_zero,hSh₀,smul_zero,map_zero]
  have hini : ‖L (slope (A x) b l a)-Q a‖ ≤ C*(δ+τ+ε) := by
    rw [hQi]
    apply hinit.trans
    have he : ε ≤ δ+τ+ε := by linarith
    exact he.trans (le_mul_of_one_le_left hη hC₁)
  exact actual_slow_pulse_estimates_on basis A b B' A' x h hA hb hB' hA' hBeval
    hMB hMA hMb hnB hnB' hnA hnb hAp hl hAc hbc Q Qd Qh Qhd
    hdQ hdQh hQdc hQhdc ha hT hγ hC hη
    (fun t ht => by rw [hbmodel t ht];exact hpl (t-a) (hshift t ht))
    hQpos hρ hρh hQhn hini (by rw [hjet,hQhi])

end HarmonicCounterexample.LinearODE

end

end OAI
