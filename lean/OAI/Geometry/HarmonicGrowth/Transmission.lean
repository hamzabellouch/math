import OAI.Geometry.HarmonicGrowth.PulseODE
import OAI.Geometry.HarmonicGrowth.SmoothWord

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

lemma orthogonalMatrix_injective (b : OrthonormalBasis ι ℝ E) :
    Function.Injective (orthogonalMatrix b) := by
  intro T U h
  ext x
  apply b.repr.injective
  apply PiLp.ext
  intro i
  have hT := congrFun (orthogonalMatrix_mulVec b T x) i
  have hU := congrFun (orthogonalMatrix_mulVec b U x) i
  rw [h] at hT
  exact hT.symm.trans hU

/-- A fixed coordinate norm constant, chosen independently of the pulse,
its duration, its history and its parameters. -/
theorem orthogonalMatrix_norm_bound (b : OrthonormalBasis ι ℝ E) :
    ∃ C : ℝ,0 < C ∧ ∀ T : E →L[ℝ] E,‖T‖ ≤ C*‖orthogonalMatrix b T‖ := by
  obtain ⟨C,hC,h⟩ := (orthogonalMatrix b).toLinearMap.injective_iff_antilipschitz.1
    (orthogonalMatrix_injective b)
  exact ⟨C,by exact_mod_cast hC,fun T => ZeroHomClass.bound_of_antilipschitz (orthogonalMatrix b) h T⟩

lemma integrated_matrix_error_to_operator {a b C : ℝ} (hab : a ≤ b)
    (basis : OrthonormalBasis ι ℝ E)
    (hbound : ∀ T : E →L[ℝ] E,‖T‖ ≤ C*‖orthogonalMatrix basis T‖)
    {P Q : ℝ → E →L[ℝ] E} (hP : ContinuousOn P (Set.Icc a b))
    (hQ : ContinuousOn Q (Set.Icc a b)) :
    (∫ t in a..b,‖P t-Q t‖) ≤ C*(∫ t in a..b,‖orthogonalMatrix basis (P t)-orthogonalMatrix basis (Q t)‖) := by
  have hc := ((orthogonalMatrix basis).continuous.comp_continuousOn (hP.sub hQ)).norm
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  calc
    _ ≤ ∫ t in a..b,C*‖orthogonalMatrix basis (P t-Q t)‖ :=
      intervalIntegral.integral_mono_on hab ((hP.sub hQ).norm.intervalIntegrable_of_Icc hab)
        (hi.const_mul C) (fun t _ => hbound (P t-Q t))
    _ = C*(∫ t in a..b,‖orthogonalMatrix basis (P t)-orthogonalMatrix basis (Q t)‖) := by
      rw [intervalIntegral.integral_const_mul]
      simp only [map_sub]

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
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set MeasureTheory

/-- The bounded exact positive scalar from local attainment has a UNIFORM
logarithm cost. It cannot become exponentially small along histories. -/
lemma bounded_target_log {c : ℝ} (hc : c ∈ Ioo (1/2:ℝ) (3/2)) :
    |Real.log c| ≤ Real.log 2 := by
  have hc₀ : 0 < c := by linarith [hc.1]
  rw [abs_le]
  constructor
  · have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hc.1.le
    rw [Real.log_div one_ne_zero (by norm_num),Real.log_one,zero_sub] at h
    exact h
  · exact Real.log_le_log hc₀ (by linarith [hc.2])

/-- Undoing exactly the scalar baseline normalizer preserves an exact positive
scalar-permutation endpoint and adds only the genuine baseline integral to its
logarithm. This is an equality of actual operators, not a weighted model. -/
lemma undo_scalar_normalization {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    {Y perm : R} {I c : ℝ} (he : Real.exp (-I) • Y=c • perm) :
    Y=(Real.exp I*c) • perm := by
  have hh := congrArg (fun X : R => Real.exp I • X) he
  rw [smul_smul,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul,smul_smul] at hh
  exact hh

lemma lifted_target_log {I c V T : ℝ} (hc : c ∈ Ioo (1/2:ℝ) (3/2))
    (hI : |I| ≤ V*T) :
    0 < Real.exp I*c ∧ |Real.log (Real.exp I*c)| ≤ V*T+Real.log 2 := by
  have hc₀ : 0 < c := by linarith [hc.1]
  refine ⟨mul_pos (Real.exp_pos _) hc₀,?_⟩
  rw [Real.log_mul (Real.exp_ne_zero _) hc₀.ne',Real.log_exp]
  exact (abs_add_le _ _).trans (add_le_add hI (bounded_target_log hc))

/-- Actual scalar PB baseline integrated log cost. The constant precedes all
pulse histories and lengths; no value of an unproved scalar ODE is supplied. -/
theorem actual_baseline_log_cost {α p : ℝ → ℝ}
    (hα : Continuous α) (hp : Continuous p)
    {M Mp B β p₀ θ γ δ T : ℝ}
    (hM : 0 ≤ M) (hMp : 0 ≤ Mp) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hαn : ∀ t,|α t| ≤ M) (hpn : ∀ t,|p t| ≤ Mp)
    (hAp : ∀ t,0 ≤ t → 0 ≤ α t*B) (hroot : β*B-p₀*θ-θ^2=0)
    (hscale : ∀ t ∈ Icc 0 T,|α t-β| ≤ δ)
    (hpt : ∀ t ∈ Icc 0 T,|p t-p₀| ≤ δ)
    (hpl : ∀ t ∈ Icc 0 T,γ ≤ p t) :
    |∫ t in (0:ℝ)..T,scalarBaseline (fun s => α s*B) p θ t| ≤
      (θ+((|B|+|θ|)/γ)*δ)*T := by
  let v := scalarBaseline (fun s => α s*B) p θ
  have hn (s : ℝ) : |α s*B| ≤ M*|B| := by rw [abs_mul];gcongr;exact hαn s
  have hvc : ContinuousOn v (Icc 0 T) := fun t ht =>
    (actual_scalar_baseline_deriv (hα.mul continuous_const) hp
      (by positivity) hMp hn hpn hAp hθ ht.1).continuousAt.continuousWithinAt
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) : |v t| ≤ θ+((|B|+|θ|)/γ)*δ := by
    have hv := berger_scalar_baseline_close hα hp hM hMp hθ hγ hδ hαn hpn hAp
      hroot hscale hpt hpl t ht
    have he := abs_add_le (v t-θ) θ
    rw [sub_add_cancel,abs_of_nonneg hθ] at he
    linarith
  have hvi : IntervalIntegrable v volume 0 T := hvc.intervalIntegrable_of_Icc hT
  calc
    _ ≤ ∫ t in (0:ℝ)..T,|v t| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := v) hT
    _ ≤ ∫ _ in (0:ℝ)..T,θ+((|B|+|θ|)/γ)*δ :=
      intervalIntegral.integral_mono_on hT hvi.norm intervalIntegrable_const hbound
    _ = _ := by rw [intervalIntegral.integral_const];simp only [sub_zero,smul_eq_mul];ring

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
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
lemma bergerSlowGenerator_eq_smul (r B β p₀ θ z : ℝ) (D : R) :
    bergerSlowGenerator r B β p₀ θ z D=z • bergerSlowGenerator r B β p₀ θ 1 D := by
  simp only [bergerSlowGenerator,mul_one,smul_smul]
  rw [mul_comm z]
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
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.FiniteControl.SmoothWord
open HarmonicCounterexample.LinearODE
open Set Filter
open scoped Topology BigOperators
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] {n : ℕ}

/-- Exact representation of the normalized smooth finite-word coefficient
and its time derivative by the selected Berger angular generator. -/
theorem unitBergerPacket_selected (a : Fin n → ℝ) (D : Fin n → R)
    (r B β p₀ θ : ℝ) (d : ℝ → Fin n)
    (hd : ∀ t i,i ≠ d t → bump i t=0 ∧ deriv (bump i) t=0) (t : ℝ) :
    unitPacketCoefficient a (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) t=
      bergerSlowGenerator r B β p₀ θ (unitPacketScalar a t) (D (d (duration n*t))) ∧
    unitPacketCoefficientD a (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) t=
      bergerSlowGenerator r B β p₀ θ (unitPacketScalarD a t) (D (d (duration n*t))) := by
  obtain ⟨h₁,h₂⟩ := unitPacketCoefficient_selected a
    (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) d hd t
  exact ⟨h₁.trans (bergerSlowGenerator_eq_smul r B β p₀ θ _ _).symm,
    h₂.trans (bergerSlowGenerator_eq_smul r B β p₀ θ _ _).symm⟩

/-- The normalized selector is locally constant unless every actual scalar
packet vanishes on a neighborhood. Thus angular changes occur on ROUND gaps. -/
theorem exists_unit_round_gap_selector (n : ℕ) [NeZero n] :
    ∃ d : ℝ → Fin n,
      (∀ t i,i ≠ d t → bump i (duration n*t)=0 ∧ deriv (bump i) (duration n*t)=0) ∧
      ∀ t,(∀ᶠ s in 𝓝 t,d s=d t) ∨
        (∀ᶠ s in 𝓝 t,∀ a : Fin n → ℝ,unitPacketScalar a s=0) := by
  obtain ⟨d,hd,he⟩ := exists_round_gap_selector n
  refine ⟨fun t => d (duration n*t),fun t i hi => hd _ i hi,fun t => ?_⟩
  have hc : Tendsto (fun s : ℝ => duration n*s) (𝓝 t) (𝓝 (duration n*t)) :=
    (continuous_const.mul continuous_id).continuousAt
  rcases he (duration n*t) with h|h
  · exact Or.inl (hc.eventually h)
  · right
    filter_upwards [hc.eventually h] with s hs
    intro a
    simp only [unitPacketScalar,packetScalar,hs,mul_zero,Finset.sum_const_zero]

end HarmonicCounterexample.FiniteControl.SmoothWord

end

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology ENNReal ContDiff
open scoped Topology
open scoped Topology
open scoped Topology BigOperators ContDiff InnerProductSpace
open Filter MeasureTheory Set
open Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set Matrix
open scoped BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {E H ι : Type*} {n : ℕ} [NeZero n] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

open HarmonicCounterexample.FiniteControl.SmoothWord

/-- Model-specific value and variational-slope estimates for an EXPLICIT smooth
finite word, with all shape identities and bounds discharged. The selector and
constants are chosen before every history, amplitude vector and duration. -/
theorem actual_finite_berger_word_estimates (basis : OrthonormalBasis ι ℝ E)
    (r B β p₀ θ γ : ℝ) (D : Fin n → E →L[ℝ] E) {M U : ℝ}
    (hM : 0 ≤ M) (hU : 0 ≤ U) (hθ : 0 ≤ θ) (hγ : 0 < γ)
    (hc : p₀+2*θ ≠ 0) (hroot : β*B-p₀*θ-θ^2=0) :
    ∃ Z C : ℝ,∃ d : ℝ → Fin n,0 ≤ Z ∧ 1 ≤ C ∧
      (∀ t,(∀ᶠ s in 𝓝 t,d s=d t) ∨
        (∀ᶠ s in 𝓝 t,∀ v : Fin n → ℝ,unitPacketScalar v s=0)) ∧ ∀ (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
      (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
      (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (x h : H)
      (α p : ℝ → ℝ) (amps rays : Fin n → ℝ) (Mp MB MA Mb l B₀ a T δ ε : ℝ),
      (∀ j,|amps j| ≤ U) → (∀ j,|rays j| ≤ U) →
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
      2*Z ≤ T →
      ((|B|+|θ|)/γ)*δ+T⁻¹*(∑ j : Fin n,|β/(p₀+2*θ)| *Z*‖r • (B • (1:E →L[ℝ] E))+D j‖) ≤ θ/2 →
      (∀ t ∈ Icc a (a+T),b t=p (t-a)) →
      (∀ t ∈ Icc a (a+T),A x t=
        α (t-a) • PulseTaylor.angular r (B • (1:E →L[ℝ] E)) (D (d (T⁻¹*(t-a)))) (1+T⁻¹*unitPacketScalar amps (T⁻¹*(t-a)))) →
      (∀ t ∈ Icc a (a+T),A' x t h=
        (T⁻¹*unitPacketScalar rays (T⁻¹*(t-a))) • (α (t-a) •
          PulseTaylor.angularD r (B • (1:E →L[ℝ] E)) (D (d (T⁻¹*(t-a)))) (1+T⁻¹*unitPacketScalar amps (T⁻¹*(t-a))))) →
      ‖orthogonalMatrix basis (slope (A x) b l a)-θ • (1:Matrix ι ι ℝ)‖ ≤ ε →
      orthogonalMatrix basis (slopeJet A b B' l x a h)=0 →
      let Q := fun t => orthogonalMatrix basis
        (scalarBaseline (fun s => α s*B) p θ (t-a) • (1:E →L[ℝ] E)+T⁻¹ • unitPacketCoefficient amps (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) (T⁻¹*(t-a)))
      let Qh := fun t => orthogonalMatrix basis
        (T⁻¹ • unitPacketCoefficient rays (fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)) (T⁻¹*(t-a)))
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖ ≤
        (C+C/γ)*(δ+T⁻¹+ε)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slope (A x) b l t)-Q t‖) ≤
        2*C*(δ+T⁻¹+ε)/γ ∧
      (∀ t ∈ Icc a (a+T),‖orthogonalMatrix basis (slopeJet A b B' l x t h)-Qh t‖ ≤
        (C+2*C*(C+C/γ))*(δ+T⁻¹+ε)/(γ*T)) ∧
      (∫ t in a..a+T,‖orthogonalMatrix basis (slopeJet A b B' l x t h)-Qh t‖) ≤
        C*(δ+T⁻¹+ε)/γ+4*C^2*(δ+T⁻¹+ε)/γ^2 := by
  obtain ⟨K,hK,hbound⟩ := unitPacketScalar_uniform_bound n
  let Z := K*U
  have hZ : 0 ≤ Z := mul_nonneg hK hU
  obtain ⟨d₀,hd₀,hgap⟩ := exists_round_gap_selector n
  let d : ℝ → Fin n := fun u => d₀ (duration n*u)
  let X : Fin n → E →L[ℝ] E := fun j => bergerSlowGenerator r B β p₀ θ 1 (D j)
  obtain ⟨C,hC,hest⟩ := actual_switched_berger_estimates (H := H) basis r B β p₀ θ γ D hM hZ hθ hγ hc hroot
  refine ⟨Z,C,d,hZ,hC,?_,?_⟩
  · intro t
    have ht : Tendsto (fun s : ℝ => duration n*s) (𝓝 t) (𝓝 (duration n*t)) :=
      (continuous_const.mul continuous_id).continuousAt
    rcases hgap (duration n*t) with h|h
    · exact Or.inl (ht.eventually h)
    · right
      filter_upwards [ht.eventually h] with s hs
      intro v
      simp only [unitPacketScalar,packetScalar,hs,mul_zero,Finset.sum_const_zero]
  intro A b B' A' x h α p amps rays Mp MB MA Mb l B₀ a T δ ε hamper hray
    hA hb hB' hA' hblock hMB hMA hMb hbblock hbB' hbA hbb hpos hl hcore hcoreb
    hα hp hMp hbα hbp hαpos ha hT hδ hε hαclose hpclose hγp hZT hcoerc hpb hcoeff hjet hinit hjetinit
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hshape (u : ℝ) := unitBergerPacket_selected amps D r B β p₀ θ d₀ hd₀ u
  have hrayshape (u : ℝ) := unitBergerPacket_selected rays D r B β p₀ θ d₀ hd₀ u
  have hamps (u : ℝ) := hbound amps U hU hamper u
  have hrays (u : ℝ) := hbound rays U hU hray u
  have hq (t : ℝ) (_ht : t ∈ Icc 0 T) :
      1+T⁻¹*unitPacketScalar amps (T⁻¹*t) ∈ Icc (1/2:ℝ) (3/2) := by
    have hz := (hamps (T⁻¹*t)).1
    have hhalf : |T⁻¹*unitPacketScalar amps (T⁻¹*t)| ≤ (1/2:ℝ) := by
      rw [abs_mul,abs_of_pos (inv_pos.2 hTpos)]
      apply (mul_le_mul_of_nonneg_left hz (inv_nonneg.2 hTpos.le)).trans
      rw [inv_mul_eq_div]
      exact (div_le_iff₀ hTpos).2 (by linarith)
    exact ⟨by linarith [(abs_le.1 hhalf).1],by linarith [(abs_le.1 hhalf).2]⟩
  exact hest A b B' A' x h α p (unitPacketScalar amps) (unitPacketScalarD amps)
    (unitPacketScalar rays) (unitPacketScalarD rays) d
    (unitPacketCoefficient amps X) (unitPacketCoefficientD amps X)
    (unitPacketCoefficient rays X) (unitPacketCoefficientD rays X) Mp MB MA Mb l B₀ a T δ ε
    hA hb hB' hA' hblock hMB hMA hMb hbblock hbB' hbA hbb hpos hl hcore hcoreb
    hα hp hMp hbα hbp hαpos ha hT hδ hε hαclose hpclose hγp
    (unitPacketCoefficient_deriv amps X) (unitPacketCoefficient_deriv rays X)
    (unitPacketCoefficientD_smooth amps X).continuous (unitPacketCoefficientD_smooth rays X).continuous
    (unitPacketCoefficient_zero amps X) (unitPacketCoefficient_zero rays X)
    (fun u => ⟨(hshape u).1,(hshape u).2,(hrayshape u).1,(hrayshape u).2⟩)
    (fun t _ => ⟨(hamps _).1,(hamps _).2,(hrays _).1,(hrays _).2⟩)
    hq hcoerc hpb hcoeff hjet hinit hjetinit

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
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- The regular Riccati value and its entire Frechet jet are continuous in
physical time on the actual nonnegative half-line. Invertibility is produced
from positivity, not assumed as an analytic bridge. -/
theorem actual_slope_jet_continuousOn
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E) (p : H)
    (hA : Continuous (A p)) (hb : Continuous b) (hB' : Continuous (B' p))
    (hBeval : ∀ t z v,B' p t z v=(0,A' p t z*v.1))
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ t,‖block (leftAction (A p)) b t‖ ≤ M) (hnB' : ∀ t,‖B' p t‖ ≤ M)
    (hnA : ∀ t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hpos : ∀ t v,0 ≤ inner ℝ v (A p t v)) {l : ℝ} (hl : 0 < l) :
    ContinuousOn (slope (A p) b l) (Ici 0) ∧
    ContinuousOn (slopeJet A b B' l p) (Ici 0) := by
  have hu (t : ℝ) (ht : 0 ≤ t) := operatorValue_isUnit hA hb hMA hMb hnA hnb hpos hl ht
  constructor
  · intro t ht
    exact (slope_deriv hA hb hMA hMb hnA hnb l t (hu t ht)).continuousAt.continuousWithinAt
  · apply continuousOn_clm_apply.2
    intro h t ht
    exact (slopeJet_hasDerivAt_pointwise A b B' A' p h hA hb hB' hBeval
      hM hMA hMb hnB hnB' hnA hnb l t (hu t ht)).continuousAt.continuousWithinAt

omit [FiniteDimensional ℝ H] in
/-- The normalized coefficient's first jet is the genuine parameter derivative
of the actual center-regular PB slope after slow-time rescaling. -/
theorem actual_normalized_slope_hasFDerivAt
    (A : H → ℝ → E →L[ℝ] E) (b v : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    {S : Set H} (hS : IsOpen S) (hSc : IsPreconnected S)
    (hA : ∀ p ∈ S,Continuous (A p)) (hb : Continuous b) (hB' : ∀ p ∈ S,Continuous (B' p))
    (hdB : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => block (leftAction (A q)) b t) (B' p t) p)
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ p ∈ S,∀ t,‖block (leftAction (A p)) b t‖ ≤ M)
    (hnB' : ∀ p ∈ S,∀ t,‖B' p t‖ ≤ M)
    (hnA : ∀ p ∈ S,∀ t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hpos : ∀ p ∈ S,∀ t w,0 ≤ inner ℝ w (A p t w)) {l : ℝ} (hl : 0 < l)
    {p : H} (hp : p ∈ S) {a T u : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T) (hu : 0 ≤ u) :
    HasFDerivAt (fun q => T • (slope (A q) b l (a+T*u)-v (a+T*u) • (1:E →L[ℝ] E)))
      (T • slopeJet A b B' l p (a+T*u)) p := by
  have ht : 0 ≤ a+T*u := add_nonneg ha (mul_nonneg hT hu)
  have hunit := operatorValue_isUnit (hA p hp) hb hMA hMb (hnA p hp) hnb (hpos p hp) hl ht
  exact ((slope_hasFDerivAt_jet_on A b B' hS hSc hA hb hB' hdB hM hnB hnB'
    l hp (a+T*u) hunit).sub_const _).const_smul T

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE

/-- The variable-coefficient Gronwall estimate in precisely the integrated
norm used for long pulses. No supremum-times-pulse-length loss occurs. -/
theorem integral_gronwall {a b c : ℝ} (hab : a ≤ b)
    (u q r : ℝ → ℝ) (hu : Continuous u) (hq : Continuous q) (hr : Continuous r)
    (hq0 : ∀ t ∈ Icc a b,0 ≤ q t) (hr0 : ∀ t ∈ Icc a b,0 ≤ r t)
    (hineq : ∀ t ∈ Icc a b,u t ≤ c+∫ s in a..t,q s*u s+r s) :
    u b ≤ (c+∫ s in a..b,r s)*Real.exp (∫ s in a..b,q s) := by
  let B := fun t => c+∫ s in a..t,q s*u s+r s
  let Q := fun t => ∫ s in a..t,q s
  have hBc : Continuous (fun s => q s*u s+r s) := (hq.mul hu).add hr
  have hB (t : ℝ) : HasDerivAt B (q t*u t+r t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hBc.intervalIntegrable a t)
      hBc.stronglyMeasurable.stronglyMeasurableAtFilter hBc.continuousAt).const_add c
  have hQ (t : ℝ) : HasDerivAt Q (q t) t :=
    intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a t)
      hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hBcont : Continuous B := continuous_iff_continuousAt.2 (fun t => (hB t).continuousAt)
  have hQcont : Continuous Q := continuous_iff_continuousAt.2 (fun t => (hQ t).continuousAt)
  let G := fun t => B t*Real.exp (-Q t)
  let G' := fun t => (q t*u t+r t-q t*B t)*Real.exp (-Q t)
  have hG (t : ℝ) : HasDerivAt G (G' t) t := by
    convert (hB t).mul (hQ t).neg.exp using 1; first | rfl | dsimp [G']; ring
  have hGc : Continuous G' := ((hq.mul hu).add hr |>.sub (hq.mul hBcont)).mul (Real.continuous_exp.comp hQcont.neg)
  have hle (t : ℝ) (ht : t ∈ Icc a b) : G' t ≤ r t := by
    have hQ0 : 0 ≤ Q t := intervalIntegral.integral_nonneg ht.1
      (fun s hs => hq0 s ⟨hs.1,hs.2.trans ht.2⟩)
    have he1 : Real.exp (-Q t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hBbound : u t ≤ B t := hineq t ht
    have hqbound : q t*u t ≤ q t*B t := mul_le_mul_of_nonneg_left hBbound (hq0 t ht)
    calc
      _ ≤ r t*Real.exp (-Q t) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ r t*1 := mul_le_mul_of_nonneg_left he1 (hr0 t ht)
      _ = _ := mul_one _
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab (hGc.intervalIntegrable a b) (hr.intervalIntegrable a b) hle
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hG t) (hGc.intervalIntegrable a b)] at hi
  have he : G b ≤ c+∫ s in a..b,r s := by
    have hGa : G a=c := by simp [G,B,Q]
    rw [hGa] at hi
    linarith
  have hBfinal : B b ≤ (c+∫ s in a..b,r s)*Real.exp (Q b) := by
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (Q b)).le
    simpa only [G,mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] using hm
  exact (hineq b ⟨hab,le_rfl⟩).trans hBfinal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Sharp-in-L1 stability for a genuinely differentiable Banach-valued path. -/
theorem norm_le_integrated_gronwall {a b : ℝ} (hab : a ≤ b)
    (f f' : ℝ → E) (hf : ∀ t,HasDerivAt f (f' t) t) (hfc : Continuous f')
    (q r : ℝ → ℝ) (hq : Continuous q) (hr : Continuous r)
    (hq0 : ∀ t ∈ Icc a b,0 ≤ q t) (hr0 : ∀ t ∈ Icc a b,0 ≤ r t)
    (hbound : ∀ t ∈ Icc a b,‖f' t‖ ≤ q t*‖f t‖+r t) :
    ‖f b‖ ≤ (‖f a‖+∫ s in a..b,r s)*Real.exp (∫ s in a..b,q s) := by
  have hc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  apply integral_gronwall hab (fun t => ‖f t‖) q r hc.norm hq hr hq0 hr0
  intro t ht
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hf s) (hfc.intervalIntegrable a t)
  have hn : ‖f t-f a‖ ≤ ∫ s in a..t,‖f' s‖ := by
    rw [← he]
    exact intervalIntegral.norm_integral_le_integral_norm ht.1
  have hi := intervalIntegral.integral_mono_on (μ := volume) ht.1 (hfc.norm.intervalIntegrable a t)
    (((hq.mul hc.norm).add hr).intervalIntegrable a t)
    (fun s hs => hbound s ⟨hs.1,hs.2.trans ht.2⟩)
  change (∫ s in a..t,‖f' s‖) ≤ ∫ s in a..t,q s*‖f s‖+r s at hi
  have htri := norm_add_le (f t-f a) (f a)
  rw [sub_add_cancel] at htri
  linarith

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual Peano--Baker flow has the sharp L1 exponential bound. -/
lemma flow_norm_integral_bound {A : ℝ → E →L[ℝ] E} (hA : Continuous A)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ∀ t,‖A t‖ ≤ M) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖flow A x t‖ ≤ ‖x‖*Real.exp (∫ s in (0:ℝ)..t,‖A s‖) := by
  have hd := flow_hasDerivAt hA hM hbound x
  have hc : Continuous (flow A x) := continuous_iff_continuousAt.2 (fun s => (hd s).continuousAt)
  have h := norm_le_integrated_gronwall ht (flow A x) (fun s => A s (flow A x s)) hd
    (hA.clm_apply hc) (fun s => ‖A s‖) (fun _ => 0) hA.norm continuous_const
    (fun s _ => norm_nonneg _) (fun _ _ => le_rfl)
    (fun s _ => by simpa only [add_zero] using (A s).le_opNorm (flow A x s))
  simpa only [flow_initial,intervalIntegral.integral_zero,add_zero] using h

lemma norm_integral_mono_upper {F : Type*} [NormedAddCommGroup F]
    {f : ℝ → F} (hf : Continuous f) {s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ u in (0:ℝ)..s,‖f u‖) ≤ ∫ u in (0:ℝ)..t,‖f u‖ := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.norm.intervalIntegrable 0 s) (hf.norm.intervalIntegrable s t)
  have hp : 0 ≤ ∫ u in s..t,‖f u‖ := intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
  linarith

/-- Actual solution stability with a length-independent L1 coefficient error.
Both solutions are constructed, not postulated, and no commutativity is used. -/
theorem flow_L1_difference {A B : ℝ → E →L[ℝ] E}
    (hA : Continuous A) (hB : Continuous B) {MA MB : ℝ} (hMA : 0 ≤ MA) (hMB : 0 ≤ MB)
    (hAb : ∀ s,‖A s‖ ≤ MA) (hBb : ∀ s,‖B s‖ ≤ MB) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖flow A x t-flow B x t‖ ≤
      ‖x‖*Real.exp ((∫ s in (0:ℝ)..t,‖A s‖)+(∫ s in (0:ℝ)..t,‖B s‖)) *
        (∫ s in (0:ℝ)..t,‖A s-B s‖) := by
  let c := ‖x‖*Real.exp (∫ s in (0:ℝ)..t,‖B s‖)
  have hc0 : 0 ≤ c := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hAd := flow_hasDerivAt hA hMA hAb x
  have hBd := flow_hasDerivAt hB hMB hBb x
  have hAc := continuous_iff_continuousAt.2 (fun s => (hAd s).continuousAt)
  have hBc := continuous_iff_continuousAt.2 (fun s => (hBd s).continuousAt)
  have hbound (s : ℝ) (hs : s ∈ Icc 0 t) : ‖flow B x s‖ ≤ c := by
    apply (flow_norm_integral_bound hB hMB hBb x hs.1).trans
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (norm_integral_mono_upper hB hs.1 hs.2)) (norm_nonneg _)
  have h := norm_le_integrated_gronwall ht (fun s => flow A x s-flow B x s)
    (fun s => A s (flow A x s)-B s (flow B x s))
    (fun s => (hAd s).fun_sub (hBd s)) ((hA.clm_apply hAc).sub (hB.clm_apply hBc))
    (fun s => ‖A s‖) (fun s => ‖A s-B s‖*c) hA.norm ((hA.sub hB).norm.mul continuous_const)
    (fun _ _ => norm_nonneg _) (fun _ _ => mul_nonneg (norm_nonneg _) hc0) (fun s hs => by
      have he : A s (flow A x s)-B s (flow B x s) =
          A s (flow A x s-flow B x s)+(A s-B s) (flow B x s) := by
        simp only [map_sub,sub_apply]; abel
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add ((A s).le_opNorm _)
        (((A s-B s).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _)))))
  simp only [flow_initial,sub_self,norm_zero,zero_add,intervalIntegral.integral_mul_const] at h
  apply h.trans_eq
  dsimp [c]
  rw [Real.exp_add]
  ring

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The exact first-jet coefficient on value/parameter-derivative pairs. -/
def jetBlock (A : E →L[ℝ] E) (A' : H →L[ℝ] E →L[ℝ] E) :
    E×(H →L[ℝ] E) →L[ℝ] E×(H →L[ℝ] E) :=
  (A.comp (ContinuousLinearMap.fst ℝ E (H →L[ℝ] E))).prod
    (((ContinuousLinearMap.compL ℝ H E E) A).comp (ContinuousLinearMap.snd ℝ E (H →L[ℝ] E)) +
      A'.flip.comp (ContinuousLinearMap.fst ℝ E (H →L[ℝ] E)))

omit [CompleteSpace E] in
lemma jetBlock_apply (A : E →L[ℝ] E) (A' : H →L[ℝ] E →L[ℝ] E) (v : E×(H →L[ℝ] E)) :
    jetBlock A A' v = (A v.1,A.comp v.2+A'.flip v.1) := rfl

omit [CompleteSpace E] in
lemma jetBlock_continuous (A : ℝ → E →L[ℝ] E)
    (A' : ℝ → H →L[ℝ] E →L[ℝ] E) (hA : Continuous A) (hA' : Continuous A') :
    Continuous (fun t => jetBlock (A t) (A' t)) := by
  unfold jetBlock
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := E×(H →L[ℝ] E)) (F := E) (G := H →L[ℝ] E) ℝ).continuous.comp
    ((hA.clm_comp continuous_const).prodMk
    (((ContinuousLinearMap.compL ℝ H E E).continuous.comp hA).clm_comp continuous_const |>.add
      (((ContinuousLinearMap.flipₗᵢ ℝ H E E).continuous.comp hA').clm_comp continuous_const)))

omit [CompleteSpace E] in
lemma jetBlock_norm (A : E →L[ℝ] E) (A' : H →L[ℝ] E →L[ℝ] E) :
    ‖jetBlock A A'‖ ≤ ‖A‖+‖A'‖ := by
  apply (jetBlock A A').opNorm_le_bound (M := ‖A‖+‖A'‖) (add_nonneg (norm_nonneg A) (norm_nonneg A'))
  intro v
  rw [jetBlock_apply,Prod.norm_def]
  apply max_le
  · calc
      ‖A v.1‖ ≤ ‖A‖*‖v.1‖ := A.le_opNorm _
      _ ≤ (‖A‖+‖A'‖)*‖v‖ := by
        rw [Prod.norm_def]
        exact mul_le_mul (le_add_of_nonneg_right (norm_nonneg A')) (le_max_left _ _)
          (norm_nonneg _) (add_nonneg (norm_nonneg A) (norm_nonneg A'))
  · calc
      _ ≤ ‖A.comp v.2‖+‖A'.flip v.1‖ := norm_add_le _ _
      _ ≤ ‖A‖*‖v.2‖+‖A'‖*‖v.1‖ := by
        apply add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        simpa only [ContinuousLinearMap.opNorm_flip] using A'.flip.le_opNorm v.1
      _ ≤ (‖A‖+‖A'‖)*‖v‖ := by
        rw [Prod.norm_def,add_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg A'))

omit [CompleteSpace E] in
lemma jetBlock_sub (A B : E →L[ℝ] E) (A' B' : H →L[ℝ] E →L[ℝ] E) :
    jetBlock A A'-jetBlock B B'=jetBlock (A-B) (A'-B') := by
  apply ContinuousLinearMap.ext
  intro v
  change (A v.1,A.comp v.2+A'.flip v.1)-(B v.1,B.comp v.2+B'.flip v.1) = _
  rw [jetBlock_apply]
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro h
    simp only [Prod.snd_sub,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,sub_apply,add_apply]
    abel

/-- The actual parameter jet is itself the actual constructed linear flow. -/
lemma flow_jet (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hA' : ∀ p,Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ p s,‖A p s‖ ≤ M) (hb' : ∀ p s,‖A' p s‖ ≤ M)
    (x : E) (p : H) (t : ℝ) :
    (flow (A p) x t,flowD A A' x p t) =
      flow (fun s => jetBlock (A p s) (A' p s)) (x,0) t := by
  have hJ := jetBlock_continuous (A p) (A' p) (hA p) (hA' p)
  have hJb (s : ℝ) : ‖jetBlock (A p s) (A' p s)‖ ≤ 2*M :=
    (jetBlock_norm _ _).trans (by linarith [hb p s,hb' p s])
  have hd (s : ℝ) : HasDerivAt (fun u => (flow (A p) x u,flowD A A' x p u))
      (jetBlock (A p s) (A' p s) (flow (A p) x s,flowD A A' x p s)) s :=
    (flow_hasDerivAt (hA p) hM (hb p) x s).prodMk (flowD_hasDerivAt A A' hA hA' hM hb hb' x p s)
  have he := solution_unique (by positivity : 0 ≤ 2*M) hJb hd
    (flow_hasDerivAt hJ (by positivity) hJb (x,0)) (t₀ := 0)
    (by simp only [flow_initial,flowD_initial])
  exact congrFun he t

/-- A genuine C1-in-parameter endpoint estimate, with an L1 (not duration)
constant, for two actual coefficient families. -/
theorem flow_jet_L1_difference
    (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (hA : ∀ p,Continuous (A p)) (hB : ∀ p,Continuous (B p))
    (hA' : ∀ p,Continuous (A' p)) (hB' : ∀ p,Continuous (B' p))
    {M : ℝ} (hM : 0 ≤ M) (hbA : ∀ p s,‖A p s‖ ≤ M) (hbB : ∀ p s,‖B p s‖ ≤ M)
    (hbA' : ∀ p s,‖A' p s‖ ≤ M) (hbB' : ∀ p s,‖B' p s‖ ≤ M)
    (x : E) (p : H) {t : ℝ} (ht : 0 ≤ t) :
    max ‖flow (A p) x t-flow (B p) x t‖ ‖flowD A A' x p t-flowD B B' x p t‖ ≤
      ‖x‖*Real.exp ((∫ s in (0:ℝ)..t,‖jetBlock (A p s) (A' p s)‖)+
        (∫ s in (0:ℝ)..t,‖jetBlock (B p s) (B' p s)‖)) *
        (∫ s in (0:ℝ)..t,‖jetBlock (A p s-B p s) (A' p s-B' p s)‖) := by
  have hJAb (s : ℝ) : ‖jetBlock (A p s) (A' p s)‖ ≤ 2*M :=
    (jetBlock_norm _ _).trans (by linarith [hbA p s,hbA' p s])
  have hJBb (s : ℝ) : ‖jetBlock (B p s) (B' p s)‖ ≤ 2*M :=
    (jetBlock_norm _ _).trans (by linarith [hbB p s,hbB' p s])
  have h := flow_L1_difference (jetBlock_continuous (A p) (A' p) (hA p) (hA' p))
    (jetBlock_continuous (B p) (B' p) (hB p) (hB' p)) (by positivity : 0 ≤ 2*M)
    (by positivity : 0 ≤ 2*M) hJAb hJBb (x,0) ht
  rw [← flow_jet A A' hA hA' hM hbA hbA' x p t,
    ← flow_jet B B' hB hB' hM hbB hbB' x p t] at h
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,jetBlock_sub,norm_zero,
    max_eq_left (norm_nonneg x)] using h

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The actual time variational equation needs bounds only at the current
parameter, not at the irrelevant parameters outside the admissible ball. -/
lemma flowD_hasDerivAt_pointwise
    (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (p : H) (hA : Continuous (A p)) (hA' : Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s,‖A p s‖ ≤ M) (hb' : ∀ s,‖A' p s‖ ≤ M)
    (x : E) (t : ℝ) :
    HasDerivAt (flowD A A' x p)
      ((A p t).comp (flowD A A' x p t)+(A' p t).flip (flow (A p) x t)) t := by
  have he : flowD (fun _ : H => A p) (fun _ : H => A' p) x p=flowD A A' x p :=
    funext (flowD_frozen A A' x p p)
  simpa only [he,flowD_frozen] using
    (flowD_hasDerivAt (fun _ : H => A p) (fun _ : H => A' p)
      (fun _ => hA) (fun _ => hA') hM (fun _ => hb) (fun _ => hb') x p t)

/-- Local-in-parameter actual jet stability. The parameter universe is not
silently restricted; coefficients outside the admissible set are unused. -/
theorem flow_jet_L1_difference_pointwise
    (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    (p : H) (hA : Continuous (A p)) (hB : Continuous (B p))
    (hA' : Continuous (A' p)) (hB' : Continuous (B' p))
    {M : ℝ} (hM : 0 ≤ M) (hbA : ∀ s,‖A p s‖ ≤ M) (hbB : ∀ s,‖B p s‖ ≤ M)
    (hbA' : ∀ s,‖A' p s‖ ≤ M) (hbB' : ∀ s,‖B' p s‖ ≤ M)
    (x : E) {t : ℝ} (ht : 0 ≤ t) :
    max ‖flow (A p) x t-flow (B p) x t‖ ‖flowD A A' x p t-flowD B B' x p t‖ ≤
      ‖x‖*Real.exp ((∫ s in (0:ℝ)..t,‖jetBlock (A p s) (A' p s)‖)+
        (∫ s in (0:ℝ)..t,‖jetBlock (B p s) (B' p s)‖)) *
        (∫ s in (0:ℝ)..t,‖jetBlock (A p s-B p s) (A' p s-B' p s)‖) := by
  simpa only [flowD_frozen] using flow_jet_L1_difference
    (fun _ : H => A p) (fun _ : H => B p) (fun _ : H => A' p) (fun _ : H => B' p)
    (fun _ => hA) (fun _ => hB) (fun _ => hA') (fun _ => hB') hM
    (fun _ => hbA) (fun _ => hbB) (fun _ => hbA') (fun _ => hbB') x p ht

/-- Quantitative C1 endpoint stability for the genuine Frechet derivatives on
an admissible open connected parameter domain. The right side depends on L1
coefficient and jet norms, so it does not lose a factor equal to pulse duration. -/
theorem flow_fderiv_L1_difference_on
    (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    {S : Set H} (hS : IsOpen S) (hSc : IsPreconnected S)
    (hA : ∀ p ∈ S,Continuous (A p)) (hB : ∀ p ∈ S,Continuous (B p))
    (hA' : ∀ p ∈ S,Continuous (A' p)) (hB' : ∀ p ∈ S,Continuous (B' p))
    (hdA : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => A q t) (A' p t) p)
    (hdB : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => B q t) (B' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hbA : ∀ p ∈ S,∀ s,‖A p s‖ ≤ M)
    (hbB : ∀ p ∈ S,∀ s,‖B p s‖ ≤ M) (hbA' : ∀ p ∈ S,∀ s,‖A' p s‖ ≤ M)
    (hbB' : ∀ p ∈ S,∀ s,‖B' p s‖ ≤ M)
    (x : E) {p : H} (hp : p ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    max ‖flow (A p) x t-flow (B p) x t‖
        ‖fderiv ℝ (fun q => flow (A q) x t) p-fderiv ℝ (fun q => flow (B q) x t) p‖ ≤
      ‖x‖*Real.exp ((∫ s in (0:ℝ)..t,‖jetBlock (A p s) (A' p s)‖)+
        (∫ s in (0:ℝ)..t,‖jetBlock (B p s) (B' p s)‖)) *
        (∫ s in (0:ℝ)..t,‖jetBlock (A p s-B p s) (A' p s-B' p s)‖) := by
  rw [(flow_hasFDerivAt_parameter_on A A' hS hSc hA hA' hdA hM hbA hbA' x hp t).fderiv,
    (flow_hasFDerivAt_parameter_on B B' hS hSc hB hB' hdB hM hbB hbB' x hp t).fderiv]
  exact flow_jet_L1_difference_pointwise A B A' B' p (hA p hp) (hB p hp)
    (hA' p hp) (hB' p hp) hM (hbA p hp) (hbB p hp) (hbA' p hp) (hbB' p hp) x ht

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Rescaling an integrated error introduces NO pulse-duration factor. -/
lemma slow_time_integral_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (X : ℝ → F) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ τ in (0:ℝ)..1,‖T • X (a+T*τ)‖)=(∫ t in a..a+T,‖X t‖) := by
  simp_rw [norm_smul,Real.norm_eq_abs,abs_of_pos hT]
  rw [intervalIntegral.integral_const_mul]
  have he := intervalIntegral.integral_comp_add_mul (f := fun t => ‖X t‖)
    (a := (0:ℝ)) (b := 1) hT.ne' a
  rw [he]
  simp only [mul_zero,add_zero,mul_one,smul_eq_mul]
  field_simp

omit [CompleteSpace E] in
lemma jetBlock_integral_le {A : ℝ → E →L[ℝ] E}
    {A' : ℝ → H →L[ℝ] E →L[ℝ] E}
    (hA : Continuous A) (hA' : Continuous A') {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t,‖jetBlock (A s) (A' s)‖) ≤
      (∫ s in (0:ℝ)..t,‖A s‖)+(∫ s in (0:ℝ)..t,‖A' s‖) := by
  have hc := jetBlock_continuous A A' hA hA'
  have hnc := Continuous.norm (E := E×(H →L[ℝ] E) →L[ℝ] E×(H →L[ℝ] E)) hc
  calc
    _ ≤ ∫ s in (0:ℝ)..t,‖A s‖+‖A' s‖ :=
      intervalIntegral.integral_mono_on (f := fun s => ‖jetBlock (A s) (A' s)‖) ht
        (hnc.intervalIntegrable 0 t)
        ((hA.norm.add (Continuous.norm (E := H →L[ℝ] E →L[ℝ] E) hA')).intervalIntegrable 0 t) (fun _ _ => jetBlock_norm _ _)
    _ = _ := intervalIntegral.integral_add (hA.norm.intervalIntegrable 0 t)
      ((Continuous.norm (E := H →L[ℝ] E →L[ℝ] E) hA').intervalIntegrable 0 t)

/-- The actual flow AND its genuine parameter Frechet derivative converge in
C1 from integrated coefficient errors. All resulting constants are independent
of the (possibly large) global M used only to construct/differentiate PB flow. -/
theorem pulse_endpoint_C1_of_integrated_errors
    (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    {S : Set H} (hS : IsOpen S) (hSc : IsPreconnected S)
    (hA : ∀ p ∈ S,Continuous (A p)) (hB : ∀ p ∈ S,Continuous (B p))
    (hA' : ∀ p ∈ S,Continuous (A' p)) (hB' : ∀ p ∈ S,Continuous (B' p))
    (hdA : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => A q t) (A' p t) p)
    (hdB : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => B q t) (B' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hbA : ∀ p ∈ S,∀ s,‖A p s‖ ≤ M)
    (hbB : ∀ p ∈ S,∀ s,‖B p s‖ ≤ M) (hbA' : ∀ p ∈ S,∀ s,‖A' p s‖ ≤ M)
    (hbB' : ∀ p ∈ S,∀ s,‖B' p s‖ ≤ M)
    (x : E) {p : H} (hp : p ∈ S) {C η : ℝ}
    (hIB : (∫ s in (0:ℝ)..1,‖B p s‖)+(∫ s in (0:ℝ)..1,‖B' p s‖) ≤ C)
    (hIE : (∫ s in (0:ℝ)..1,‖A p s-B p s‖)+
      (∫ s in (0:ℝ)..1,‖A' p s-B' p s‖) ≤ C*η) :
    max ‖flow (A p) x 1-flow (B p) x 1‖
        ‖fderiv ℝ (fun q => flow (A q) x 1) p-fderiv ℝ (fun q => flow (B q) x 1) p‖ ≤
      ‖x‖*Real.exp (2*C+C*η)*(C*η) := by
  have hJ := jetBlock_integral_le (hB p hp) (hB' p hp) (by norm_num : (0:ℝ) ≤ 1)
  have hJE := jetBlock_integral_le ((hA p hp).sub (hB p hp))
    ((hA' p hp).sub (hB' p hp)) (by norm_num : (0:ℝ) ≤ 1)
  have hJA : (∫ s in (0:ℝ)..1,‖jetBlock (A p s) (A' p s)‖) ≤ C+C*η := by
    have he : ∀ s,jetBlock (A p s) (A' p s)=jetBlock (B p s) (B' p s)+
        jetBlock (A p s-B p s) (A' p s-B' p s) := by
      intro s; rw [← jetBlock_sub]; abel
    have hAc0 := jetBlock_continuous _ _ (hA p hp) (hA' p hp)
    have hAc := Continuous.norm (E := E×(H →L[ℝ] E) →L[ℝ] E×(H →L[ℝ] E)) hAc0
    have hBc0 := jetBlock_continuous _ _ (hB p hp) (hB' p hp)
    have hBc := Continuous.norm (E := E×(H →L[ℝ] E) →L[ℝ] E×(H →L[ℝ] E)) hBc0
    have hEc0 := jetBlock_continuous _ _ ((hA p hp).sub (hB p hp))
      ((hA' p hp).sub (hB' p hp))
    have hEc := Continuous.norm (E := E×(H →L[ℝ] E) →L[ℝ] E×(H →L[ℝ] E)) hEc0
    calc
      _ ≤ ∫ s in (0:ℝ)..1,‖jetBlock (B p s) (B' p s)‖+
          ‖jetBlock (A p s-B p s) (A' p s-B' p s)‖ :=
        intervalIntegral.integral_mono_on (by norm_num) (hAc.intervalIntegrable 0 1)
          ((hBc.add hEc).intervalIntegrable 0 1) (fun s _ => by rw [he s]; exact norm_add_le (jetBlock (B p s) (B' p s)) (jetBlock (A p s-B p s) (A' p s-B' p s)))
      _ = (∫ s in (0:ℝ)..1,‖jetBlock (B p s) (B' p s)‖)+
          (∫ s in (0:ℝ)..1,‖jetBlock (A p s-B p s) (A' p s-B' p s)‖) :=
        intervalIntegral.integral_add (hBc.intervalIntegrable 0 1) (hEc.intervalIntegrable 0 1)
      _ ≤ C+C*η := add_le_add (hJ.trans hIB) (hJE.trans hIE)
  have hbound := flow_fderiv_L1_difference_on A B A' B' hS hSc hA hB hA' hB' hdA hdB
    hM hbA hbB hbA' hbB' x hp (by norm_num : (0:ℝ) ≤ 1)
  apply hbound.trans
  apply mul_le_mul
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg x)
    apply Real.exp_le_exp.2
    linarith [hJ.trans hIB]
  · exact hJE.trans hIE
  · exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun s => norm_nonneg (jetBlock (A p s-B p s) (A' p s-B' p s)))
  · positivity

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {H F ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Finite-direction estimates control the genuine derivative operator norm.
No interchange of supremum and integral is used. -/
lemma opNorm_le_sum_basis (b : OrthonormalBasis ι ℝ H) (L : H →L[ℝ] F) :
    ‖L‖ ≤ ∑ i,‖L (b i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _) 
  intro x
  calc
    ‖L x‖ = ‖∑ i,⟪b i,x⟫_ℝ • L (b i)‖ := by
      conv_lhs => rw [← b.sum_repr' x]
      rw [map_sum]; simp only [map_smul]
    _ ≤ ∑ i,‖⟪b i,x⟫_ℝ • L (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i,‖x‖*‖L (b i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      have h : ‖⟪b i,x⟫_ℝ‖ ≤ ‖x‖ := by
        simpa only [b.norm_eq_one i,one_mul] using (norm_inner_le_norm (𝕜 := ℝ) (b i) x)
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = (∑ i,‖L (b i)‖)*‖x‖ := by rw [← Finset.mul_sum, mul_comm]

/-- Turning the integrated raywise Riccati-jet estimates into the C1 operator
estimate costs only the FIXED parameter dimension, never the pulse duration. -/
theorem integrated_opNorm_le_basis_sum (b : OrthonormalBasis ι ℝ H)
    {L : ℝ → H →L[ℝ] F} {a z C : ℝ} (haz : a ≤ z)
    (hL : ContinuousOn L (Set.Icc a z))
    (hI : ∀ i,(∫ t in a..z,‖L t (b i)‖) ≤ C) :
    (∫ t in a..z,‖L t‖) ≤ (Fintype.card ι:ℝ)*C := by
  have hc (i : ι) : ContinuousOn (fun t => ‖L t (b i)‖) (Set.Icc a z) :=
    (hL.clm_apply continuousOn_const).norm
  calc
    _ ≤ ∫ t in a..z,∑ i,‖L t (b i)‖ :=
      intervalIntegral.integral_mono_on haz (hL.norm.intervalIntegrable_of_Icc haz)
        ((continuousOn_finsetSum _ (fun i _ => hc i)).intervalIntegrable_of_Icc haz)
        (fun _ _ => opNorm_le_sum_basis b _)
    _ = ∑ i,∫ t in a..z,‖L t (b i)‖ := by
      rw [intervalIntegral.integral_finsetSum]
      intro i _;exact (hc i).intervalIntegrable_of_Icc haz
    _ ≤ ∑ _i : ι,C := Finset.sum_le_sum fun i _ => hI i
    _ = _ := by simp

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

/-- Passage from finite Frobenius estimates on the actual Riccati value and
parameter basis rays to the genuine C1 endpoint estimate. The parameter and
angular coordinate constants are fixed before every history map. -/
theorem endpoint_C1_of_matrix_ray_errors
    (e : OrthonormalBasis ι ℝ E) (h : OrthonormalBasis κ ℝ H)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ J : ℝ,C ≤ J ∧ 0 ≤ J ∧
    ∀ (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (S : Set H) (p : H) (M η : ℝ) (x : E),
      IsOpen S → IsPreconnected S → p ∈ S →
      (∀ q ∈ S,Continuous (A q)) → (∀ q ∈ S,Continuous (B q)) →
      (∀ q ∈ S,Continuous (A' q)) → (∀ q ∈ S,Continuous (B' q)) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => A r t) (A' q t) q) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => B r t) (B' q t) q) →
      0 ≤ M → 0 ≤ η →
      (∀ q ∈ S,∀ t,‖A q t‖ ≤ M) → (∀ q ∈ S,∀ t,‖B q t‖ ≤ M) →
      (∀ q ∈ S,∀ t,‖A' q t‖ ≤ M) → (∀ q ∈ S,∀ t,‖B' q t‖ ≤ M) →
      (∫ t in (0:ℝ)..1,‖B p t‖)+(∫ t in (0:ℝ)..1,‖B' p t‖) ≤ C →
      (∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A p t)-orthogonalMatrix e (B p t)‖) ≤ η →
      (∀ i,(∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A' p t (h i))-
        orthogonalMatrix e (B' p t (h i))‖) ≤ η) →
      max ‖flow (A p) x 1-flow (B p) x 1‖
        ‖fderiv ℝ (fun q => flow (A q) x 1) p-fderiv ℝ (fun q => flow (B q) x 1) p‖ ≤
        ‖x‖*Real.exp (2*J+J*η)*(J*η) := by
  obtain ⟨K,hK,hk⟩ := orthogonalMatrix_norm_bound e
  let J := C+K*(1+(Fintype.card κ:ℝ))
  have hCJ : C ≤ J := le_add_of_nonneg_right (mul_nonneg hK.le (by positivity))
  have hJ : 0 ≤ J := hC.trans hCJ
  refine ⟨J,hCJ,hJ,?_⟩
  intro A B A' B' S p M η x hS hSc hp hA hB hA' hB' hdA hdB hM hη
    hbA hbB hbA' hbB' hIB hI₀ hI₁
  have hi₀ := integrated_matrix_error_to_operator (by norm_num : (0:ℝ) ≤ 1) e hk
    (hA p hp).continuousOn (hB p hp).continuousOn
  have hi₀' : (∫ t in (0:ℝ)..1,‖A p t-B p t‖) ≤ K*η :=
    hi₀.trans (mul_le_mul_of_nonneg_left hI₀ hK.le)
  have hr (i : κ) : (∫ t in (0:ℝ)..1,‖(A' p t-B' p t) (h i)‖) ≤ K*η := by
    have hii := integrated_matrix_error_to_operator (P := fun t => A' p t (h i))
      (Q := fun t => B' p t (h i)) (by norm_num : (0:ℝ) ≤ 1) e hk
      ((hA' p hp).clm_apply continuous_const).continuousOn
      ((hB' p hp).clm_apply continuous_const).continuousOn
    exact hii.trans (mul_le_mul_of_nonneg_left (hI₁ i) hK.le)
  have hi₁ := integrated_opNorm_le_basis_sum h (by norm_num : (0:ℝ) ≤ 1)
    ((hA' p hp).sub (hB' p hp)).continuousOn hr
  have hi : (∫ t in (0:ℝ)..1,‖A p t-B p t‖)+
      (∫ t in (0:ℝ)..1,‖A' p t-B' p t‖) ≤ J*η := by
    calc
      _ ≤ K*η+(Fintype.card κ:ℝ)*(K*η) := add_le_add hi₀' hi₁
      _ ≤ J*η := by dsimp [J];nlinarith [mul_nonneg hC hη]
  exact pulse_endpoint_C1_of_integrated_errors A B A' B' hS hSc hA hB hA' hB'
    hdA hdB hM hbA hbB hbA' hbB' x hp (hIB.trans hCJ) hi

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
variable {E H V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A fixed contraction lifts value and genuine parameter derivative L1
errors to the endpoint flow, without a dimension- or duration-dependent loss.
Taking L to be left multiplication gives the actual operator endpoint. -/
theorem pulse_endpoint_C1_of_contracted_errors
    (L : V →L[ℝ] E →L[ℝ] E) (hL : ‖L‖ ≤ 1)
    (A B : H → ℝ → V) (A' B' : H → ℝ → H →L[ℝ] V)
    {S : Set H} (hS : IsOpen S) (hSc : IsPreconnected S)
    (hA : ∀ p ∈ S,Continuous (A p)) (hB : ∀ p ∈ S,Continuous (B p))
    (hA' : ∀ p ∈ S,Continuous (A' p)) (hB' : ∀ p ∈ S,Continuous (B' p))
    (hdA : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => A q t) (A' p t) p)
    (hdB : ∀ p ∈ S,∀ t,HasFDerivAt (fun q => B q t) (B' p t) p)
    {M : ℝ} (hM : 0 ≤ M) (hbA : ∀ p ∈ S,∀ s,‖A p s‖ ≤ M)
    (hbB : ∀ p ∈ S,∀ s,‖B p s‖ ≤ M) (hbA' : ∀ p ∈ S,∀ s,‖A' p s‖ ≤ M)
    (hbB' : ∀ p ∈ S,∀ s,‖B' p s‖ ≤ M)
    (x : E) {p : H} (hp : p ∈ S) {C η : ℝ}
    (hIB : (∫ s in (0:ℝ)..1,‖B p s‖)+(∫ s in (0:ℝ)..1,‖B' p s‖) ≤ C)
    (hIE : (∫ s in (0:ℝ)..1,‖A p s-B p s‖)+
      (∫ s in (0:ℝ)..1,‖A' p s-B' p s‖) ≤ C*η) :
    max ‖flow (fun t => L (A p t)) x 1-flow (fun t => L (B p t)) x 1‖
        ‖fderiv ℝ (fun q => flow (fun t => L (A q t)) x 1) p-
          fderiv ℝ (fun q => flow (fun t => L (B q t)) x 1) p‖ ≤
      ‖x‖*Real.exp (2*C+C*η)*(C*η) := by
  have hl (v : V) : ‖L v‖ ≤ ‖v‖ :=
    (L.le_opNorm v).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg v)).trans_eq (one_mul _))
  have hl' (T : H →L[ℝ] V) : ‖L.comp T‖ ≤ ‖T‖ :=
    (L.opNorm_comp_le T).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg T)).trans_eq (one_mul _))
  have hli (f : ℝ → V) (hf : Continuous f) :
      (∫ t in (0:ℝ)..1,‖L (f t)‖) ≤ ∫ t in (0:ℝ)..1,‖f t‖ :=
    intervalIntegral.integral_mono_on (by norm_num) ((L.continuous.comp hf).norm.intervalIntegrable 0 1)
      (hf.norm.intervalIntegrable 0 1) (fun t _ => hl _)
  have hli' (f : ℝ → H →L[ℝ] V) (hf : Continuous f) :
      (∫ t in (0:ℝ)..1,‖L.comp (f t)‖) ≤ ∫ t in (0:ℝ)..1,‖f t‖ :=
    intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_const.clm_comp hf).norm.intervalIntegrable 0 1)
      (hf.norm.intervalIntegrable 0 1) (fun t _ => hl' _)
  apply pulse_endpoint_C1_of_integrated_errors
    (fun q t => L (A q t)) (fun q t => L (B q t))
    (fun q t => L.comp (A' q t)) (fun q t => L.comp (B' q t)) hS hSc
    (fun q hq => L.continuous.comp (hA q hq)) (fun q hq => L.continuous.comp (hB q hq))
    (fun q hq => continuous_const.clm_comp (hA' q hq))
    (fun q hq => continuous_const.clm_comp (hB' q hq))
    (fun q hq t => L.hasFDerivAt.comp q (hdA q hq t))
    (fun q hq t => L.hasFDerivAt.comp q (hdB q hq t))
    hM (fun q hq t => (hl _).trans (hbA q hq t))
    (fun q hq t => (hl _).trans (hbB q hq t))
    (fun q hq t => (hl' _).trans (hbA' q hq t))
    (fun q hq t => (hl' _).trans (hbB' q hq t)) x hp
  · exact (add_le_add (hli _ (hB p hp)) (hli' _ (hB' p hp))).trans hIB
  · have ho := add_le_add (hli _ ((hA p hp).sub (hB p hp)))
      (hli' _ ((hA' p hp).sub (hB' p hp)))
    simpa only [Pi.sub_apply,map_sub,ContinuousLinearMap.comp_sub] using ho.trans hIE

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H F ι κ : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

/-- Passage from finite Frobenius estimates on the actual Riccati value and
parameter basis rays to the genuine C1 endpoint estimate. The parameter and
angular coordinate constants are fixed before every history map. -/
theorem contracted_endpoint_C1_of_matrix_ray_errors
    (L : (E →L[ℝ] E) →L[ℝ] F →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (e : OrthonormalBasis ι ℝ E) (h : OrthonormalBasis κ ℝ H)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ J : ℝ,C ≤ J ∧ 0 ≤ J ∧
    ∀ (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (S : Set H) (p : H) (M η : ℝ) (x : F),
      IsOpen S → IsPreconnected S → p ∈ S →
      (∀ q ∈ S,Continuous (A q)) → (∀ q ∈ S,Continuous (B q)) →
      (∀ q ∈ S,Continuous (A' q)) → (∀ q ∈ S,Continuous (B' q)) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => A r t) (A' q t) q) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => B r t) (B' q t) q) →
      0 ≤ M → 0 ≤ η →
      (∀ q ∈ S,∀ t,‖A q t‖ ≤ M) → (∀ q ∈ S,∀ t,‖B q t‖ ≤ M) →
      (∀ q ∈ S,∀ t,‖A' q t‖ ≤ M) → (∀ q ∈ S,∀ t,‖B' q t‖ ≤ M) →
      (∫ t in (0:ℝ)..1,‖B p t‖)+(∫ t in (0:ℝ)..1,‖B' p t‖) ≤ C →
      (∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A p t)-orthogonalMatrix e (B p t)‖) ≤ η →
      (∀ i,(∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A' p t (h i))-
        orthogonalMatrix e (B' p t (h i))‖) ≤ η) →
      max ‖flow (fun t => L (A p t)) x 1-flow (fun t => L (B p t)) x 1‖
        ‖fderiv ℝ (fun q => flow (fun t => L (A q t)) x 1) p-fderiv ℝ (fun q => flow (fun t => L (B q t)) x 1) p‖ ≤
        ‖x‖*Real.exp (2*J+J*η)*(J*η) := by
  obtain ⟨K,hK,hk⟩ := orthogonalMatrix_norm_bound e
  let J := C+K*(1+(Fintype.card κ:ℝ))
  have hCJ : C ≤ J := le_add_of_nonneg_right (mul_nonneg hK.le (by positivity))
  have hJ : 0 ≤ J := hC.trans hCJ
  refine ⟨J,hCJ,hJ,?_⟩
  intro A B A' B' S p M η x hS hSc hp hA hB hA' hB' hdA hdB hM hη
    hbA hbB hbA' hbB' hIB hI₀ hI₁
  have hi₀ := integrated_matrix_error_to_operator (by norm_num : (0:ℝ) ≤ 1) e hk
    (hA p hp).continuousOn (hB p hp).continuousOn
  have hi₀' : (∫ t in (0:ℝ)..1,‖A p t-B p t‖) ≤ K*η :=
    hi₀.trans (mul_le_mul_of_nonneg_left hI₀ hK.le)
  have hr (i : κ) : (∫ t in (0:ℝ)..1,‖(A' p t-B' p t) (h i)‖) ≤ K*η := by
    have hii := integrated_matrix_error_to_operator (P := fun t => A' p t (h i))
      (Q := fun t => B' p t (h i)) (by norm_num : (0:ℝ) ≤ 1) e hk
      ((hA' p hp).clm_apply continuous_const).continuousOn
      ((hB' p hp).clm_apply continuous_const).continuousOn
    exact hii.trans (mul_le_mul_of_nonneg_left (hI₁ i) hK.le)
  have hi₁ := integrated_opNorm_le_basis_sum h (by norm_num : (0:ℝ) ≤ 1)
    ((hA' p hp).sub (hB' p hp)).continuousOn hr
  have hi : (∫ t in (0:ℝ)..1,‖A p t-B p t‖)+
      (∫ t in (0:ℝ)..1,‖A' p t-B' p t‖) ≤ J*η := by
    calc
      _ ≤ K*η+(Fintype.card κ:ℝ)*(K*η) := add_le_add hi₀' hi₁
      _ ≤ J*η := by dsimp [J];nlinarith [mul_nonneg hC hη]
  exact pulse_endpoint_C1_of_contracted_errors L hL A B A' B' hS hSc hA hB hA' hB'
    hdA hdB hM hbA hbB hbA' hbB' x hp (hIB.trans hCJ) hi

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

/-- Passage from finite Frobenius estimates on the actual Riccati value and
parameter basis rays to the genuine C1 endpoint estimate. The parameter and
angular coordinate constants are fixed before every history map. -/
theorem operator_endpoint_C1_of_matrix_ray_errors
    (e : OrthonormalBasis ι ℝ E) (h : OrthonormalBasis κ ℝ H)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ J : ℝ,C ≤ J ∧ 0 ≤ J ∧
    ∀ (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (S : Set H) (p : H) (M η : ℝ),
      IsOpen S → IsPreconnected S → p ∈ S →
      (∀ q ∈ S,Continuous (A q)) → (∀ q ∈ S,Continuous (B q)) →
      (∀ q ∈ S,Continuous (A' q)) → (∀ q ∈ S,Continuous (B' q)) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => A r t) (A' q t) q) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => B r t) (B' q t) q) →
      0 ≤ M → 0 ≤ η →
      (∀ q ∈ S,∀ t,‖A q t‖ ≤ M) → (∀ q ∈ S,∀ t,‖B q t‖ ≤ M) →
      (∀ q ∈ S,∀ t,‖A' q t‖ ≤ M) → (∀ q ∈ S,∀ t,‖B' q t‖ ≤ M) →
      (∫ t in (0:ℝ)..1,‖B p t‖)+(∫ t in (0:ℝ)..1,‖B' p t‖) ≤ C →
      (∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A p t)-orthogonalMatrix e (B p t)‖) ≤ η →
      (∀ i,(∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A' p t (h i))-
        orthogonalMatrix e (B' p t (h i))‖) ≤ η) →
      max ‖flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (A p t)) 1 1-flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B p t)) 1 1‖
        ‖fderiv ℝ (fun q => flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (A q t)) 1 1) p-fderiv ℝ (fun q => flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q t)) 1 1) p‖ ≤
        Real.exp (2*J+J*η)*(J*η) := by
  obtain ⟨J,hCJ,hJ,h⟩ := contracted_endpoint_C1_of_matrix_ray_errors
    (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)) (ContinuousLinearMap.opNorm_mul_le _ _) e h hC
  refine ⟨J,hCJ,hJ,?_⟩
  intro A B A' B' S p M η hS hSc hp hA hB hA' hB' hdA hdB hM hη hbA hbB hbA' hbB' hIB hI₀ hI₁
  have he := h A B A' B' S p M η 1 hS hSc hp hA hB hA' hB' hdA hdB hM hη hbA hbB hbA' hbB' hIB hI₀ hI₁
  apply he.trans
  calc
    _ ≤ 1*Real.exp (2*J+J*η)*(J*η) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hJ hη)
      exact mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (Real.exp_pos _).le
    _ = _ := by rw [one_mul]

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
/-- Exterior extension is by constant coefficients, never by altering the
actual solution on the pulse. -/
def clip01 (t : ℝ) : ℝ := min 1 (max 0 t)
lemma clip01_continuous : Continuous clip01 :=
  continuous_const.min (continuous_const.max continuous_id)
lemma clip01_mem (t : ℝ) : clip01 t ∈ Set.Icc (0:ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩
lemma clip01_eq {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : clip01 t=t := by
  rw [clip01,max_eq_right ht.1,min_eq_right ht.2]
lemma integral_clip01 (f : ℝ → ℝ) :
    (∫ t in (0:ℝ)..1,f (clip01 t))=∫ t in (0:ℝ)..1,f t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  change f (clip01 t)=f t
  rw [clip01_eq ht]
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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open MeasureTheory
open scoped BigOperators Matrix.Norms.Frobenius
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype κ]

/-- Passage from finite Frobenius estimates on the actual Riccati value and
parameter basis rays to the genuine C1 endpoint estimate. The parameter and
angular coordinate constants are fixed before every history map. -/
theorem clipped_operator_endpoint_C1_of_matrix_ray_errors
    (e : OrthonormalBasis ι ℝ E) (h : OrthonormalBasis κ ℝ H)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ J : ℝ,C ≤ J ∧ 0 ≤ J ∧
    ∀ (A B : H → ℝ → E →L[ℝ] E) (A' B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (S : Set H) (p : H) (M η : ℝ),
      IsOpen S → IsPreconnected S → p ∈ S →
      (∀ q ∈ S,ContinuousOn (A q) (Set.Icc (0:ℝ) 1)) → (∀ q ∈ S,ContinuousOn (B q) (Set.Icc (0:ℝ) 1)) →
      (∀ q ∈ S,ContinuousOn (A' q) (Set.Icc (0:ℝ) 1)) → (∀ q ∈ S,ContinuousOn (B' q) (Set.Icc (0:ℝ) 1)) →
      (∀ q ∈ S,∀ t ∈ Set.Icc (0:ℝ) 1,HasFDerivAt (fun r => A r t) (A' q t) q) →
      (∀ q ∈ S,∀ t ∈ Set.Icc (0:ℝ) 1,HasFDerivAt (fun r => B r t) (B' q t) q) →
      0 ≤ M → 0 ≤ η →
      (∀ q ∈ S,∀ t ∈ Set.Icc (0:ℝ) 1,‖A q t‖ ≤ M) → (∀ q ∈ S,∀ t ∈ Set.Icc (0:ℝ) 1,‖B q t‖ ≤ M) →
      (∀ q ∈ S,∀ t ∈ Set.Icc (0:ℝ) 1,‖A' q t‖ ≤ M) → (∀ q ∈ S,∀ t ∈ Set.Icc (0:ℝ) 1,‖B' q t‖ ≤ M) →
      (∫ t in (0:ℝ)..1,‖B p t‖)+(∫ t in (0:ℝ)..1,‖B' p t‖) ≤ C →
      (∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A p t)-orthogonalMatrix e (B p t)‖) ≤ η →
      (∀ i,(∫ t in (0:ℝ)..1,‖orthogonalMatrix e (A' p t (h i))-
        orthogonalMatrix e (B' p t (h i))‖) ≤ η) →
      max ‖flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (A p (clip01 t))) 1 1-flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B p (clip01 t))) 1 1‖
        ‖fderiv ℝ (fun q => flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (A q (clip01 t))) 1 1) p-fderiv ℝ (fun q => flow (fun t => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q (clip01 t))) 1 1) p‖ ≤
        Real.exp (2*J+J*η)*(J*η) := by
  obtain ⟨J,hCJ,hJ,he⟩ := operator_endpoint_C1_of_matrix_ray_errors e h hC
  refine ⟨J,hCJ,hJ,?_⟩
  intro A B A' B' S p M η hS hSc hp hA hB hA' hB' hdA hdB hM hη hbA hbB hbA' hbB' hIB hI₀ hI₁
  apply he (fun q t => A q (clip01 t)) (fun q t => B q (clip01 t))
    (fun q t => A' q (clip01 t)) (fun q t => B' q (clip01 t)) S p M η hS hSc hp
    (fun q hq => (hA q hq).comp_continuous clip01_continuous clip01_mem)
    (fun q hq => (hB q hq).comp_continuous clip01_continuous clip01_mem)
    (fun q hq => (hA' q hq).comp_continuous clip01_continuous clip01_mem)
    (fun q hq => (hB' q hq).comp_continuous clip01_continuous clip01_mem)
    (fun q hq t => hdA q hq _ (clip01_mem t))
    (fun q hq t => hdB q hq _ (clip01_mem t)) hM hη
    (fun q hq t => hbA q hq _ (clip01_mem t))
    (fun q hq t => hbB q hq _ (clip01_mem t))
    (fun q hq t => hbA' q hq _ (clip01_mem t))
    (fun q hq t => hbB' q hq _ (clip01_mem t))
  · rw [integral_clip01 (fun t => ‖B p t‖),integral_clip01 (fun t => ‖B' p t‖)]
    exact hIB
  · rw [integral_clip01 (fun t => ‖orthogonalMatrix e (A p t)-orthogonalMatrix e (B p t)‖)]
    exact hI₀
  · intro i
    rw [integral_clip01 (fun t => ‖orthogonalMatrix e (A' p t (h i))-orthogonalMatrix e (B' p t (h i))‖)]
    exact hI₁ i

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- PB iteration uses only coefficient values on the actual elapsed interval. -/
lemma term_congr_interval {A B : ℝ → E →L[ℝ] E} {b : ℝ}
    (hAB : EqOn A B (Icc 0 b)) (x : E) (n : ℕ) :
    ∀ t ∈ Icc 0 b,term A x n t=term B x n t := by
  induction n with
  | zero => intro t ht; rfl
  | succ n ih =>
    intro t ht
    simp only [term]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hsb : s ∈ Icc 0 b := ⟨hs.1,hs.2.trans ht.2⟩
    change A s (term A x n s)=B s (term B x n s)
    rw [hAB hsb,ih s hsb]

/-- Exact identity, not an endpoint estimate, under exterior coefficient
extension; this also identifies genuine parameter derivatives by congruence. -/
lemma flow_congr_interval {A B : ℝ → E →L[ℝ] E} {b : ℝ}
    (hAB : EqOn A B (Icc 0 b)) (x : E) {t : ℝ} (ht : t ∈ Icc 0 b) :
    flow A x t=flow B x t := by
  unfold flow
  apply tsum_congr
  intro n
  exact term_congr_interval hAB x n t ht

lemma flow_clip01_endpoint (A : ℝ → E →L[ℝ] E) (x : E) :
    flow (fun t => A (clip01 t)) x 1=flow A x 1 :=
  flow_congr_interval (fun t ht => congrArg A (clip01_eq ht)) x ⟨by norm_num,le_rfl⟩

/-- The Frobenius integrated error of the normalized coefficient is EXACTLY
that of the actual physical-time Riccati comparison. No factor T is lost. -/
lemma normalized_matrix_integral {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (P S : ℝ → F) (v : ℝ → ℝ) (I : F) (a : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ u in (0:ℝ)..1,‖L (T • (P (a+T*u)-v (a+T*u) • I))-L (S u)‖)=
    ∫ t in a..a+T,‖L (P t)-L (v t • I+T⁻¹ • S (T⁻¹*(t-a)))‖ := by
  let X : ℝ → G := fun t => L (P t)-L (v t • I+T⁻¹ • S (T⁻¹*(t-a)))
  have he (u : ℝ) :
      L (T • (P (a+T*u)-v (a+T*u) • I))-L (S u)=T • X (a+T*u) := by
    have hu : T⁻¹*(a+T*u-a)=u := by field_simp;ring
    dsimp [X]
    rw [hu]
    simp only [map_smul,map_sub,map_add,smul_sub,smul_add,smul_smul,mul_inv_cancel₀ hT.ne',one_smul]
    module
  calc
    _ = ∫ u in (0:ℝ)..1,‖T • X (a+T*u)‖ := by
      apply intervalIntegral.integral_congr
      intro u _
      exact congrArg norm (he u)
    _ = _ := slow_time_integral_norm X a hT

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

omit [CompleteSpace E] in
/-- Peano--Baker construction is causal on the positive half line, before any
existence/summability assumption is imposed. -/
lemma term_history_eq {A B : ℝ → E →L[ℝ] E} {T : ℝ}
    (h : Set.EqOn A B (Set.Icc 0 T)) (x : E) (n : ℕ) :
    Set.EqOn (term A x n) (term B x n) (Set.Icc 0 T) := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro t ht
    simp only [term]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht.1] at hs
    have hsT : s ∈ Set.Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
    change A s (term A x n s)=B s (term B x n s)
    rw [h hsT,ih hsT]

omit [CompleteSpace E] in
lemma flow_history_eq {A B : ℝ → E →L[ℝ] E} {T : ℝ}
    (h : Set.EqOn A B (Set.Icc 0 T)) (x : E) :
    Set.EqOn (flow A x) (flow B x) (Set.Icc 0 T) := by
  intro t ht
  exact tsum_congr (fun n => term_history_eq h x n ht)

omit [CompleteSpace E] in
/-- A control parameter not used in the incoming history has identically zero
actual variational flow throughout that history. -/
lemma termD_history_zero {A : H → ℝ → E →L[ℝ] E}
    {A' : H → ℝ → H →L[ℝ] E →L[ℝ] E} {p : H} {T : ℝ}
    (h : ∀ t ∈ Set.Icc 0 T,A' p t=0) (x : E) (n : ℕ) :
    ∀ t ∈ Set.Icc 0 T,termD A A' x p n t=0 := by
  induction n with
  | zero => exact fun _ _ => rfl
  | succ n ih =>
    intro t ht
    simp only [termD]
    have hz : (∫ s in (0:ℝ)..t,
        (A p s).comp (termD A A' x p n s)+(A' p s).flip (term (A p) x n s)) =
        ∫ _ in (0:ℝ)..t,(0:H →L[ℝ] E) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht.1] at hs
      have hsT : s ∈ Set.Icc 0 T := ⟨hs.1,hs.2.trans ht.2⟩
      simp only [h s hsT,ih s hsT,ContinuousLinearMap.comp_zero,
        ContinuousLinearMap.flip_zero,zero_apply,add_zero]
    simpa only [intervalIntegral.integral_zero] using hz

omit [CompleteSpace E] in
lemma flowD_history_zero {A : H → ℝ → E →L[ℝ] E}
    {A' : H → ℝ → H →L[ℝ] E →L[ℝ] E} {p : H} {T : ℝ}
    (h : ∀ t ∈ Set.Icc 0 T,A' p t=0) (x : E) :
    ∀ t ∈ Set.Icc 0 T,flowD A A' x p t=0 := by
  intro t ht
  unfold flowD
  simp only [termD_history_zero h x _ t ht,tsum_zero]

omit [CompleteSpace E] in
/-- Exact restart, independent of earlier coefficients, follows from interval
ODE uniqueness with the actual incoming value, not an artificially reset value. -/
lemma solution_unique_on_Icc {A : ℝ → E →L[ℝ] E} {M a b : ℝ}
    (hM : 0 ≤ M) (hb : ∀ t ∈ Set.Ico a b,‖A t‖ ≤ M) {f g : ℝ → E}
    (hfc : ContinuousOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hf : ∀ t ∈ Set.Ico a b,HasDerivAt f (A t (f t)) t)
    (hg : ∀ t ∈ Set.Ico a b,HasDerivAt g (A t (g t)) t)
    (he : f a=g a) : Set.EqOn f g (Set.Icc a b) := by
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ) (K := ⟨M,hM⟩)
    (fun t ht => ((A t).lipschitzWith.weaken (hb t ht)).lipschitzOnWith)
    hfc (fun t ht => (hf t ht).hasDerivWithinAt) (fun _ _ => Set.mem_univ _)
    hgc (fun t ht => (hg t ht).hasDerivWithinAt) (fun _ _ => Set.mem_univ _) he

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def scalarNormalized (v : ℝ → ℝ) (a : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  Real.exp (-(∫ s in a..t,v s)) • f t

omit [CompleteSpace E] in
/-- Removing the exact scalar baseline, rather than its frozen limit, from an
actual solution is an exact differentiable identity. -/
lemma scalarNormalized_deriv {v : ℝ → ℝ} (hv : Continuous v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E} {a t : ℝ}
    (hf : HasDerivAt f (P t (f t)) t) :
    HasDerivAt (scalarNormalized v a f)
      ((P t-v t • ContinuousLinearMap.id ℝ E) (scalarNormalized v a f t)) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable a t)
    hv.stronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt
  have he := hi.neg.exp
  have hd := he.smul hf
  apply hd.congr_deriv
  simp only [sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,map_smul,scalarNormalized]
  module

omit [CompleteSpace E] in
lemma scalarNormalized_initial (v : ℝ → ℝ) (a : ℝ) (f : ℝ → E) :
    scalarNormalized v a f a=f a := by simp [scalarNormalized]

omit [CompleteSpace E] in
/-- Exact passage to slow pulse time. The factor T belongs inside the
coefficient; scalar phase may grow with T but causes no error amplification. -/
lemma scalarNormalized_rescaled_deriv {v : ℝ → ℝ} (hv : Continuous v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E} {a T τ : ℝ}
    (hf : HasDerivAt f (P (a+T*τ) (f (a+T*τ))) (a+T*τ)) :
    HasDerivAt (fun u => scalarNormalized v a f (a+T*u))
      ((T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E))
        (scalarNormalized v a f (a+T*τ))) τ := by
  have hc : HasDerivAt (fun u : ℝ => a+T*u) T τ := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id τ).const_mul T).const_add a
  simpa only [Function.comp_def,smul_apply] using
    (scalarNormalized_deriv (a := a) hv hf).scomp τ hc

/-- The normalized ACTUAL solution equals the actual constructed first-order
flow on the entire pulse. The incoming value is not replaced or estimated. -/
theorem scalarNormalized_eq_flow {v : ℝ → ℝ} (hv : Continuous v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E} {a T : ℝ}
    (hf : ∀ t,HasDerivAt f (P t (f t)) t)
    {C : ℝ → E →L[ℝ] E}
    (hC : Continuous C) {M : ℝ} (hM : 0 ≤ M) (hCb : ∀ t,‖C t‖ ≤ M)
    (hCe : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      C τ=T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E)) :
    ∀ τ ∈ Set.Icc (0:ℝ) 1,
      scalarNormalized v a f (a+T*τ)=flow C (f a) τ := by
  have hd (τ : ℝ) := scalarNormalized_rescaled_deriv hv (a := a) (T := T) (hf (a+T*τ))
  apply solution_unique_on_Icc hM (fun t _ => hCb t)
    ((continuous_iff_continuousAt.2 fun τ => (hd τ).continuousAt).continuousOn)
    ((continuous_iff_continuousAt.2 fun τ => (flow_hasDerivAt hC hM hCb (f a) τ).continuousAt).continuousOn)
    (fun τ hτ => by rw [hCe τ ⟨hτ.1,hτ.2.le⟩]; exact hd τ)
    (fun τ _ => flow_hasDerivAt hC hM hCb (f a) τ)
  simp only [mul_zero,add_zero,scalarNormalized_initial,flow_initial]

omit [CompleteSpace E] in
/-- The scalar baseline is independent of the current control parameter, so
normalization commutes exactly with its Frechet derivative. -/
lemma scalarNormalized_hasFDerivAt_parameter {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : H → ℝ → E} {f' : H →L[ℝ] E} {p : H} {v : ℝ → ℝ} {a t : ℝ}
    (hf : HasFDerivAt (fun q => f q t) f' p) :
    HasFDerivAt (fun q => scalarNormalized v a (f q) t)
      (Real.exp (-(∫ s in a..t,v s)) • f') p := hf.const_smul _

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Local normalization: only integrability from a to t and continuity at t
are required of the scalar baseline. Irrelevant pre-pulse poles are allowed. -/
lemma scalarNormalized_deriv_local {v : ℝ → ℝ} {a t : ℝ}
    (hvint : IntervalIntegrable v volume a t) (hvmeas : StronglyMeasurableAtFilter v (𝓝 t))
    (hv : ContinuousAt v t) {P : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hf : HasDerivAt f (P t (f t)) t) :
    HasDerivAt (scalarNormalized v a f)
      ((P t-v t • ContinuousLinearMap.id ℝ E) (scalarNormalized v a f t)) t := by
  have hi := intervalIntegral.integral_hasDerivAt_right hvint hvmeas hv
  have hd := hi.neg.exp.smul hf
  apply hd.congr_deriv
  simp only [sub_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,scalarNormalized]
  module

omit [CompleteSpace E] in
lemma scalarNormalized_rescaled_deriv_local {v : ℝ → ℝ} {a T τ : ℝ}
    (hvint : IntervalIntegrable v volume a (a+T*τ))
    (hvmeas : StronglyMeasurableAtFilter v (𝓝 (a+T*τ)))
    (hv : ContinuousAt v (a+T*τ)) {P : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hf : HasDerivAt f (P (a+T*τ) (f (a+T*τ))) (a+T*τ)) :
    HasDerivAt (fun u => scalarNormalized v a f (a+T*u))
      ((T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E))
        (scalarNormalized v a f (a+T*τ))) τ := by
  have hc : HasDerivAt (fun u : ℝ => a+T*u) T τ := by
    simpa only [mul_one,id_eq] using ((hasDerivAt_id τ).const_mul T).const_add a
  simpa only [Function.comp_def,smul_apply] using
    (scalarNormalized_deriv_local hvint hvmeas hv hf).scomp τ hc

/-- Exact identification of the normalized actual solution with PB flow,
using derivatives only on the pulse. The exterior extension is applied only
to its coefficient, never to the unknown solution or its derivative. -/
theorem scalarNormalized_eq_flow_on {v : ℝ → ℝ} {a T : ℝ}
    (hT : 0 ≤ T) (hvc : ∀ t ∈ Icc a (a+T),ContinuousAt v t)
    (hvm : StronglyMeasurable v)
    {P : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hf : ∀ t ∈ Icc a (a+T),HasDerivAt f (P t (f t)) t)
    {C : ℝ → E →L[ℝ] E}
    (hC : Continuous C) {M : ℝ} (hM : 0 ≤ M) (hCb : ∀ t,‖C t‖ ≤ M)
    (hCe : ∀ τ ∈ Icc (0:ℝ) 1,
      C τ=T • (P (a+T*τ)-v (a+T*τ) • ContinuousLinearMap.id ℝ E)) :
    ∀ τ ∈ Icc (0:ℝ) 1,
      scalarNormalized v a f (a+T*τ)=flow C (f a) τ := by
  have hvcOn : ContinuousOn v (Icc a (a+T)) := fun t ht => (hvc t ht).continuousWithinAt
  have hτt (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) : a+T*τ ∈ Icc a (a+T) := by
    constructor <;> nlinarith [mul_nonneg hT hτ.1,mul_le_mul_of_nonneg_left hτ.2 hT]
  have hd (τ : ℝ) (hτ : τ ∈ Icc (0:ℝ) 1) :
      HasDerivAt (fun u => scalarNormalized v a f (a+T*u))
        (C τ (scalarNormalized v a f (a+T*τ))) τ := by
    rw [hCe τ hτ]
    have ht := hτt τ hτ
    apply scalarNormalized_rescaled_deriv_local _ hvm.stronglyMeasurableAtFilter (hvc _ ht) (hf _ ht)
    exact (hvcOn.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  apply solution_unique_on_Icc hM (fun t _ => hCb t)
    (fun τ hτ => (hd τ hτ).continuousAt.continuousWithinAt)
    ((continuous_iff_continuousAt.2 fun τ => (flow_hasDerivAt hC hM hCb (f a) τ).continuousAt).continuousOn)
    (fun τ hτ => hd τ ⟨hτ.1,hτ.2.le⟩)
    (fun τ _ => flow_hasDerivAt hC hM hCb (f a) τ)
  simp only [mul_zero,add_zero,scalarNormalized_initial,flow_initial]

/-- Constant exterior extension of a pulse coefficient. Its boundedness
follows from genuine continuity on the compact pulse, rather than global
invertibility of an irrelevant scalar comparison. -/
def clippedPulse (C : ℝ → E →L[ℝ] E) : ℝ → E →L[ℝ] E :=
  IccExtend (by norm_num : (0:ℝ) ≤ 1) (fun s : Icc (0:ℝ) 1 => C s)

omit [CompleteSpace E] in
lemma clippedPulse_eq (C : ℝ → E →L[ℝ] E) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    clippedPulse C t=C t := IccExtend_of_mem _ _ ht

omit [CompleteSpace E] in
lemma clippedPulse_continuous {C : ℝ → E →L[ℝ] E} (hC : ContinuousOn C (Icc (0:ℝ) 1)) :
    Continuous (clippedPulse C) :=
  continuous_IccExtend_iff.2 (continuousOn_iff_continuous_domRestrict.1 hC)

omit [CompleteSpace E] in
lemma clippedPulse_bounded {C : ℝ → E →L[ℝ] E} (hC : ContinuousOn C (Icc (0:ℝ) 1)) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ t,‖clippedPulse C t‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hC
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro t
  exact (hM _ (projIcc _ _ (by norm_num : (0:ℝ) ≤ 1) t).property).trans (le_max_left _ _)

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- The actual normalized value transmission, not a surrogate first-order
solution, is EXACTLY the clipped slow-time operator PB endpoint. -/
theorem actual_normalized_value_endpoint
    {A : ℝ → E →L[ℝ] E} {b v : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnA : ∀ t,‖A t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hpos : ∀ t w,0 ≤ inner ℝ w (A t w)) {l a T : ℝ}
    (hl : 0 < l) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hvc : ∀ t ∈ Icc a (a+T),ContinuousAt v t) (hvm : StronglyMeasurable v) :
    Real.exp (-(∫ t in a..a+T,v t)) •
      (operatorValue A b l (a+T)*Ring.inverse (operatorValue A b l a)) =
      flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E)
        (T • (slope A b l (a+T*clip01 u)-
          v (a+T*clip01 u) • (1:E →L[ℝ] E)))) 1 1 := by
  let V := operatorValue A b l
  let P := slope A b l
  let f : ℝ → E →L[ℝ] E := fun t => V t*Ring.inverse (V a)
  let F : ℝ → E →L[ℝ] E := fun u => T • (P (a+T*u)-v (a+T*u) • 1)
  let C := fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (F (clip01 u))
  have hunit (t : ℝ) (ht : 0 ≤ t) := operatorValue_isUnit hA hb hMA hMb hnA hnb hpos hl ht
  have hτt (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : a+T*u ∈ Icc a (a+T) := by
    constructor <;> nlinarith [mul_nonneg hT hu.1,mul_le_mul_of_nonneg_left hu.2 hT]
  have hPc : ContinuousOn P (Ici 0) := by
    intro t ht
    exact (slope_deriv hA hb hMA hMb hnA hnb l t (hunit t ht)).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (Icc (0:ℝ) 1) := by
    have hPcomp : ContinuousOn (fun u : ℝ => P (a+T*u)) (Icc (0:ℝ) 1) :=
      hPc.comp (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
        (fun u hu => ha.trans (hτt u hu).1)
    have hvcomp : ContinuousOn (fun u : ℝ => v (a+T*u)) (Icc (0:ℝ) 1) :=
      (show ContinuousOn v (Icc a (a+T)) from fun t ht => (hvc t ht).continuousWithinAt).comp
        (continuous_const.add (continuous_const.mul continuous_id)).continuousOn hτt
    exact (hPcomp.sub (hvcomp.smul (continuousOn_const (c := (1:E →L[ℝ] E))))).const_smul T
  have hFclip : Continuous (fun u => F (clip01 u)) := hFc.comp_continuous clip01_continuous clip01_mem
  have hCc : Continuous C := (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).continuous.comp hFclip
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hFc
  have hCb (u : ℝ) : ‖C u‖ ≤ max M 0 := by
    calc
      ‖C u‖ ≤ ‖ContinuousLinearMap.mul ℝ (E →L[ℝ] E)‖*‖F (clip01 u)‖ :=
        (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).le_opNorm _
      _ ≤ 1*‖F (clip01 u)‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le _ _) (norm_nonneg _)
      _ ≤ max M 0 := by simpa only [one_mul] using (hM _ (clip01_mem u)).trans (le_max_left _ _)
  have hf (t : ℝ) (ht : t ∈ Icc a (a+T)) : HasDerivAt f ((leftAction P t) (f t)) t := by
    have hv := (operatorValue_deriv hA hb hMA hMb hnA hnb l t).mul_const (Ring.inverse (V a))
    apply hv.congr_deriv
    change operatorVelocity A b l t*Ring.inverse (V a) = P t*(V t*Ring.inverse (V a))
    rw [← mul_assoc]
    have he : P t*V t=operatorVelocity A b l t := by
      dsimp [P,V,slope]
      rw [mul_assoc,Ring.inverse_mul_cancel _ (hunit t (ha.trans ht.1)),mul_one]
    rw [he]
  have hCe (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      C u=T • (leftAction P (a+T*u)-v (a+T*u) • ContinuousLinearMap.id ℝ (E →L[ℝ] E)) := by
    dsimp [C]
    rw [clip01_eq hu]
    ext W x
    simp [F,leftAction]
  have he := scalarNormalized_eq_flow_on hT hvc hvm hf hCc (le_max_right M 0) hCb hCe 1 ⟨by norm_num,le_rfl⟩
  have hfa : f a=1 := Ring.mul_inverse_cancel _ (hunit a ha)
  simpa only [scalarNormalized,mul_one,f,hfa,V,C,F,P] using he

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

/-- Positivity produces a contraction bound for the inverse actual value
operator. This is uniform over all positive histories and all t >= 0. -/
theorem actual_value_inverse_norm_le_one
    {A : ℝ → E →L[ℝ] E} {b : ℝ → ℝ}
    (hA : Continuous A) (hb : Continuous b) {MA Mb : ℝ}
    (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnA : ∀ t,‖A t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hpos : ∀ t w,0 ≤ inner ℝ w (A t w)) {l t : ℝ}
    (hl : 0 < l) (ht : 0 ≤ t) :
    ‖Ring.inverse (operatorValue A b l t)‖ ≤ 1 := by
  have hunit (s : ℝ) (hs : 0 ≤ s) := operatorValue_isUnit hA hb hMA hMb hnA hnb hpos hl hs
  have hlower (x : E) : ‖x‖ ≤ ‖operatorValue A b l t x‖ := by
    let y := value A b l x
    let z := velocity A b l x
    have hy (s : ℝ) := value_deriv hA hb hMA hMb hnA hnb l x s
    have hz (s : ℝ) := velocity_deriv hA hb hMA hMb hnA hnb l x s
    have hd (s : ℝ) : HasDerivAt (fun u => inner ℝ (y u) (y u))
        (2*inner ℝ (y s) (z s)) s := by
      convert (hy s).inner ℝ (hy s) using 1; first | rfl |
        (rw [real_inner_comm (z s) (y s)]; ring)
    have hm : MonotoneOn (fun u => inner ℝ (y u) (y u)) (Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
        (fun s _ => (hd s).continuousAt.continuousWithinAt)
        (fun s _ => (hd s).hasDerivWithinAt)
      intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      by_cases hx : x=0
      · subst x
        have hy0 : y s=0 := by
          change value A b l 0 s=0
          exact (value_linear hA hb hMA hMb hnA hnb l s).mk'.map_zero
        rw [hy0,inner_zero_left,mul_zero]
      · exact mul_nonneg (by norm_num)
          (regular_pairing_positive hb hpos hy hz hl
            (by simp only [value_initial,velocity_initial])
            (by simpa only [y,value_initial] using hx) hs0).le
    have h := hm (by simp only [mem_Ici,le_refl]) ht ht
    simp only [y,value_initial,real_inner_self_eq_norm_sq] at h
    have he := operatorValue_apply hA hb hMA hMb hnA hnb l x t
    rw [he]
    nlinarith [norm_nonneg x,norm_nonneg (value A b l x t)]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have h := hlower (Ring.inverse (operatorValue A b l t) x)
  have he : operatorValue A b l t (Ring.inverse (operatorValue A b l t) x)=x := by
    change (operatorValue A b l t*Ring.inverse (operatorValue A b l t)) x=x
    rw [Ring.mul_inverse_cancel _ (hunit t ht)]
    rfl
  simpa only [he,one_mul] using h

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A coarse finite-time bound used ONLY to justify local parameter
 differentiation; it is not the uniform-history C1 error constant. -/
lemma flowD_norm_bound_pointwise
    (A : H → ℝ → E →L[ℝ] E) (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
    {p : H} (hA : Continuous (A p)) (hA' : Continuous (A' p))
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ s,‖A p s‖ ≤ M) (hb' : ∀ s,‖A' p s‖ ≤ M)
    (x : E) (t : ℝ) : ‖flowD A A' x p t‖ ≤ ‖x‖*Real.exp (2*M*|t|) := by
  unfold flowD
  apply tsum_of_norm_bounded
    (show HasSum (fun n : ℕ => ‖x‖*((2*M*|t|)^n/(n.factorial:ℝ)))
      (‖x‖*Real.exp (2*M*|t|)) from by
        simpa only [← Real.exp_eq_exp_ℝ] using
          (NormedSpace.expSeries_div_hasSum_exp (2*M*|t|)).mul_left ‖x‖)
  intro n
  simpa only [mul_pow,mul_div_assoc,mul_assoc] using
    termD_bound_at_parameter A A' hA hA' hM hb hb' x n t

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [NormedSpace ℝ H]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- The finite-time norm bound needed for differentiation under the PB series
is PRODUCED for the actual slope and actual full parameter jet, uniformly on
the admissible parameter set. No unknown-solution bounds are assumptions. -/
theorem actual_slope_jet_uniform_bound_on
    (A : H → ℝ → E →L[ℝ] E) (b : ℝ → ℝ)
    (B' : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
    (S : Set H) (hA : ∀ p ∈ S,Continuous (A p)) (hb : Continuous b)
    (hB' : ∀ p ∈ S,Continuous (B' p))
    {M MA Mb : ℝ} (hM : 0 ≤ M) (hMA : 0 ≤ MA) (hMb : 0 ≤ Mb)
    (hnB : ∀ p ∈ S,∀ t,‖block (leftAction (A p)) b t‖ ≤ M)
    (hnB' : ∀ p ∈ S,∀ t,‖B' p t‖ ≤ M)
    (hnA : ∀ p ∈ S,∀ t,‖A p t‖ ≤ MA) (hnb : ∀ t,|b t| ≤ Mb)
    (hpos : ∀ p ∈ S,∀ t w,0 ≤ inner ℝ w (A p t w)) {l R : ℝ}
    (hl : 0 < l) : ∃ N : ℝ,0 ≤ N ∧ ∀ p ∈ S,∀ t ∈ Icc 0 R,
      ‖slope (A p) b l t‖ ≤ N ∧ ‖slopeJet A b B' l p t‖ ≤ N := by
  let x₀ : OperatorPhase E := (1,l • 1)
  let C : ℝ := ‖x₀‖*Real.exp (M*R)
  let D : ℝ := ‖x₀‖*Real.exp (2*M*R)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨C+(1+C)*D,add_nonneg hC (mul_nonneg (by linarith) hD),?_⟩
  intro p hp t ht
  have hbc := block_continuous (leftAction_continuous (hA p hp)) hb
  let Y := flow (block (leftAction (A p)) b) x₀ t
  have hY : ‖Y‖ ≤ C := by
    apply (flow_norm_integral_bound hbc hM (hnB p hp) x₀ ht.1).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 _) (norm_nonneg x₀)
    have hint : (∫ s in (0:ℝ)..t,‖block (leftAction (A p)) b s‖) ≤ ∫ s in (0:ℝ)..t,M :=
      intervalIntegral.integral_mono_on ht.1 (hbc.norm.intervalIntegrable 0 t)
        (continuous_const.intervalIntegrable 0 t) (fun s _ => hnB p hp s)
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hint
    exact hint.trans (by nlinarith [ht.2])
  have hinv := actual_value_inverse_norm_le_one (hA p hp) hb hMA hMb (hnA p hp) hnb (hpos p hp) hl ht.1
  have hW : ‖operatorVelocity (A p) b l t‖ ≤ C := by
    change ‖Y.2‖ ≤ C
    exact (norm_snd_le Y).trans hY
  have hP : ‖slope (A p) b l t‖ ≤ C := by
    apply (norm_mul_le _ _).trans
    exact (mul_le_mul hW hinv (norm_nonneg _) hC).trans_eq (mul_one C)
  have hJ : ‖phaseJet A b B' l p t‖ ≤ D := by
    apply (flowD_norm_bound_pointwise (fun q => block (leftAction (A q)) b) B'
      hbc (hB' p hp) hM (hnB p hp) (hnB' p hp) x₀ t).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 _) (norm_nonneg x₀)
    rw [abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
  have hVJ (z : H) : ‖valueJet A b B' l p t z‖ ≤ D*‖z‖ := by
    change ‖(phaseJet A b B' l p t z).1‖ ≤ D*‖z‖
    exact (norm_fst_le _).trans (((phaseJet A b B' l p t).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hJ (norm_nonneg z)))
  have hWJ (z : H) : ‖velocityJet A b B' l p t z‖ ≤ D*‖z‖ := by
    change ‖(phaseJet A b B' l p t z).2‖ ≤ D*‖z‖
    exact (norm_snd_le _).trans (((phaseJet A b B' l p t).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hJ (norm_nonneg z)))
  have hPJ : ‖slopeJet A b B' l p t‖ ≤ (1+C)*D := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by linarith) hD)
    intro z
    rw [slopeJet_apply]
    calc
      _ ≤ ‖velocityJet A b B' l p t z-slope (A p) b l t*valueJet A b B' l p t z‖*
          ‖Ring.inverse (operatorValue (A p) b l t)‖ := norm_mul_le _ _
      _ ≤ ‖velocityJet A b B' l p t z-slope (A p) b l t*valueJet A b B' l p t z‖*1 :=
        mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ ≤ D*‖z‖+C*(D*‖z‖) := by
        rw [mul_one]
        exact (norm_sub_le _ _).trans (add_le_add (hWJ z)
          ((norm_mul_le _ _).trans (mul_le_mul hP (hVJ z) (norm_nonneg _) hC)))
      _ = (1+C)*D*‖z‖ := by ring
  exact ⟨hP.trans (le_add_of_nonneg_right (mul_nonneg (by linarith) hD)),hPJ.trans (le_add_of_nonneg_left hC)⟩

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [Fintype ι] [Fintype κ] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Actual regular second-order transmission has the uniform C1 endpoint
estimate. Its full parameter derivative is genuine. The comparison constant
is selected before all histories; finite-time slope/jet bounds needed only
for justified differentiation are produced internally from positivity. -/
theorem actual_normalized_endpoint_C1
    (e : OrthonormalBasis ι ℝ E) (h : OrthonormalBasis κ ℝ H)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ J : ℝ,C ≤ J ∧ 0 ≤ J ∧
    ∀ (A : H → ℝ → E →L[ℝ] E) (b v : ℝ → ℝ)
      (K : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
      (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (B : H → ℝ → E →L[ℝ] E) (B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (S : Set H) (p : H) (M MA Mb M₀ l a T η : ℝ),
      IsOpen S → IsPreconnected S → p ∈ S →
      (∀ q ∈ S,Continuous (A q)) → Continuous b → Continuous v →
      (∀ q ∈ S,Continuous (K q)) →
      (∀ q ∈ S,∀ t z w,K q t z w=(0,A' q t z*w.1)) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => block (leftAction (A r)) b t) (K q t) q) →
      0 ≤ M → 0 ≤ MA → 0 ≤ Mb → 0 ≤ M₀ →
      (∀ q ∈ S,∀ t,‖block (leftAction (A q)) b t‖ ≤ M) →
      (∀ q ∈ S,∀ t,‖K q t‖ ≤ M) →
      (∀ q ∈ S,∀ t,‖A q t‖ ≤ MA) → (∀ t,|b t| ≤ Mb) →
      (∀ q ∈ S,∀ t w,0 ≤ inner ℝ w (A q t w)) →
      0 < l → 0 ≤ a → 0 < T → 0 ≤ η →
      (∀ q ∈ S,ContinuousOn (B q) (Icc (0:ℝ) 1)) →
      (∀ q ∈ S,ContinuousOn (B' q) (Icc (0:ℝ) 1)) →
      (∀ q ∈ S,∀ u ∈ Icc (0:ℝ) 1,HasFDerivAt (fun r => B r u) (B' q u) q) →
      (∀ q ∈ S,∀ u ∈ Icc (0:ℝ) 1,‖B q u‖ ≤ M₀) →
      (∀ q ∈ S,∀ u ∈ Icc (0:ℝ) 1,‖B' q u‖ ≤ M₀) →
      (∫ u in (0:ℝ)..1,‖B p u‖)+(∫ u in (0:ℝ)..1,‖B' p u‖) ≤ C →
      (∫ u in (0:ℝ)..1,‖orthogonalMatrix e
        (T • (slope (A p) b l (a+T*u)-v (a+T*u) • 1))-orthogonalMatrix e (B p u)‖) ≤ η →
      (∀ i,(∫ u in (0:ℝ)..1,‖orthogonalMatrix e (T • (slopeJet A b K l p (a+T*u) (h i)))-
        orthogonalMatrix e (B' p u (h i))‖) ≤ η) →
      let Z := fun q => Real.exp (-(∫ t in a..a+T,v t)) •
        (operatorValue (A q) b l (a+T)*Ring.inverse (operatorValue (A q) b l a))
      let W := fun q => flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q u)) 1 1
      max ‖Z p-W p‖ ‖fderiv ℝ Z p-fderiv ℝ W p‖ ≤ Real.exp (2*J+J*η)*(J*η) := by
  obtain ⟨J,hCJ,hJ,he⟩ := clipped_operator_endpoint_C1_of_matrix_ray_errors e h hC
  refine ⟨J,hCJ,hJ,?_⟩
  intro A b v K A' B B' S p M MA Mb M₀ l a T η hS hSc hp hA hb hv hK hKe hdK
    hM hMA hMb hM₀ hnK₀ hnK₁ hnA hnb hpos hl ha hT hη hB hB' hdB hnB hnB' hIB hI₀ hI₁
  dsimp only
  let F : H → ℝ → E →L[ℝ] E := fun q u => T • (slope (A q) b l (a+T*u)-v (a+T*u) • 1)
  let F' : H → ℝ → H →L[ℝ] E →L[ℝ] E := fun q u => T • slopeJet A b K l q (a+T*u)
  have htime (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : a+T*u ∈ Icc 0 (a+T) := by
    constructor <;> nlinarith [mul_nonneg hT.le hu.1,mul_le_mul_of_nonneg_left hu.2 hT.le]
  obtain ⟨N,hN,hn⟩ := actual_slope_jet_uniform_bound_on A b K S hA hb hK hM hMA hMb
    hnK₀ hnK₁ hnA hnb hpos (R := a+T) hl
  obtain ⟨V,hV⟩ := isCompact_Icc.exists_bound_of_continuousOn (hv.continuousOn (s := Icc (0:ℝ) (a+T)))
  let L := T*(N+max V 0*‖(1:E →L[ℝ] E)‖)+T*N+M₀
  have hV0 : 0 ≤ max V 0 := le_max_right _ _
  have hbaseL : 0 ≤ T*(N+max V 0*‖(1:E →L[ℝ] E)‖) := by positivity
  have hTN : 0 ≤ T*N := mul_nonneg hT.le hN
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcn (q : H) (hq : q ∈ S) := actual_slope_jet_continuousOn A b K A' q
    (hA q hq) hb (hK q hq) (hKe q hq) hM hMA hMb (hnK₀ q hq) (hnK₁ q hq)
    (hnA q hq) hnb (hpos q hq) hl
  have hF (q : H) (hq : q ∈ S) : ContinuousOn (F q) (Icc (0:ℝ) 1) := by
    have hP := (hcn q hq).1.comp
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
      (fun u hu => (htime u hu).1)
    exact (hP.sub ((hv.comp (continuous_const.add (continuous_const.mul continuous_id))).continuousOn.smul
      (continuousOn_const (c := (1:E →L[ℝ] E))))).const_smul T
  have hF' (q : H) (hq : q ∈ S) : ContinuousOn (F' q) (Icc (0:ℝ) 1) :=
    ((hcn q hq).2.comp
      (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
      (fun u hu => (htime u hu).1)).const_smul T
  have hnF (q : H) (hq : q ∈ S) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : ‖F q u‖ ≤ L := by
    have hval := (hn q hq _ (htime u hu)).1
    have hvu : ‖v (a+T*u)‖ ≤ max V 0 := (hV _ (htime u hu)).trans (le_max_left _ _)
    calc
      _ = T*‖slope (A q) b l (a+T*u)-v (a+T*u) • (1:E →L[ℝ] E)‖ := by
        simp only [F,norm_smul,Real.norm_eq_abs,abs_of_pos hT]
      _ ≤ T*(N+max V 0*‖(1:E →L[ℝ] E)‖) := mul_le_mul_of_nonneg_left
        ((norm_sub_le _ _).trans (add_le_add hval (by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right hvu (norm_nonneg _)))) hT.le
      _ ≤ L := by dsimp [L]; linarith
  have hnF' (q : H) (hq : q ∈ S) (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : ‖F' q u‖ ≤ L := by
    calc
      _ = T*‖slopeJet A b K l q (a+T*u)‖ := by simp only [F',norm_smul,Real.norm_eq_abs,abs_of_pos hT]
      _ ≤ T*N := mul_le_mul_of_nonneg_left (hn q hq _ (htime u hu)).2 hT.le
      _ ≤ L := by dsimp [L]; linarith
  have hM₀L : M₀ ≤ L := by dsimp [L]; linarith
  have hh := he F B F' B' S p L η hS hSc hp hF hB hF' hB'
    (fun q hq u hu => actual_normalized_slope_hasFDerivAt A b v K hS hSc hA hb hK hdK
      hM hMA hMb hnK₀ hnK₁ hnA hnb hpos hl hq ha hT.le hu.1)
    hdB hL hη hnF (fun q hq u hu => (hnB q hq u hu).trans hM₀L) hnF'
    (fun q hq u hu => (hnB' q hq u hu).trans hM₀L) hIB hI₀ hI₁
  let Z := fun q => Real.exp (-(∫ t in a..a+T,v t)) •
    (operatorValue (A q) b l (a+T)*Ring.inverse (operatorValue (A q) b l a))
  let Z₀ := fun q => flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (F q (clip01 u))) 1 1
  have hZZ : ∀ q ∈ S,Z q=Z₀ q := fun q hq =>
    actual_normalized_value_endpoint (hA q hq) hb hMA hMb (hnA q hq) hnb (hpos q hq)
      hl ha hT.le (fun _ _ => hv.continuousAt) hv.stronglyMeasurable
  have heq : Z =ᶠ[nhds p] Z₀ := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact hZZ q hq
  have hi : (fun q => flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q (clip01 u))) 1 1)=
      (fun q => flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q u)) 1 1) := by
    funext q
    exact flow_clip01_endpoint (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q u)) 1
  change max ‖Z₀ p-flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B p (clip01 u))) 1 1‖
    ‖fderiv ℝ Z₀ p-fderiv ℝ (fun q => flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q (clip01 u))) 1 1) p‖ ≤ _ at hh
  rw [← hZZ p hp,← heq.fderiv_eq,hi,congrFun hi p] at hh
  exact hh

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
open scoped Matrix.Norms.Frobenius
open MeasureTheory Set
open scoped Matrix.Norms.Frobenius

namespace HarmonicCounterexample.LinearODE
open Set
open scoped InnerProductSpace
variable {E H ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [Fintype ι] [Fintype κ] [DecidableEq ι]
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace

/-- Physical-time Frobenius L1 VALUE and basis-ray JET errors imply the
uniform C1 estimate for the ACTUAL second-order transmission. The complete
scalar baseline is removed; no pulse-duration factor is introduced. -/
theorem actual_physical_endpoint_C1
    (e : OrthonormalBasis ι ℝ E) (h : OrthonormalBasis κ ℝ H)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ J : ℝ,C ≤ J ∧ 0 ≤ J ∧
    ∀ (A : H → ℝ → E →L[ℝ] E) (b v : ℝ → ℝ)
      (K : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E)
      (A' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (B : H → ℝ → E →L[ℝ] E) (B' : H → ℝ → H →L[ℝ] E →L[ℝ] E)
      (S : Set H) (p : H) (M MA Mb M₀ l a T η : ℝ),
      IsOpen S → IsPreconnected S → p ∈ S →
      (∀ q ∈ S,Continuous (A q)) → Continuous b → Continuous v →
      (∀ q ∈ S,Continuous (K q)) →
      (∀ q ∈ S,∀ t z w,K q t z w=(0,A' q t z*w.1)) →
      (∀ q ∈ S,∀ t,HasFDerivAt (fun r => block (leftAction (A r)) b t) (K q t) q) →
      0 ≤ M → 0 ≤ MA → 0 ≤ Mb → 0 ≤ M₀ →
      (∀ q ∈ S,∀ t,‖block (leftAction (A q)) b t‖ ≤ M) →
      (∀ q ∈ S,∀ t,‖K q t‖ ≤ M) →
      (∀ q ∈ S,∀ t,‖A q t‖ ≤ MA) → (∀ t,|b t| ≤ Mb) →
      (∀ q ∈ S,∀ t w,0 ≤ inner ℝ w (A q t w)) →
      0 < l → 0 ≤ a → 0 < T → 0 ≤ η →
      (∀ q ∈ S,ContinuousOn (B q) (Icc (0:ℝ) 1)) →
      (∀ q ∈ S,ContinuousOn (B' q) (Icc (0:ℝ) 1)) →
      (∀ q ∈ S,∀ u ∈ Icc (0:ℝ) 1,HasFDerivAt (fun r => B r u) (B' q u) q) →
      (∀ q ∈ S,∀ u ∈ Icc (0:ℝ) 1,‖B q u‖ ≤ M₀) →
      (∀ q ∈ S,∀ u ∈ Icc (0:ℝ) 1,‖B' q u‖ ≤ M₀) →
      (∫ u in (0:ℝ)..1,‖B p u‖)+(∫ u in (0:ℝ)..1,‖B' p u‖) ≤ C →
      (∫ t in a..a+T,‖orthogonalMatrix e (slope (A p) b l t)-
        orthogonalMatrix e (v t • 1+T⁻¹ • B p (T⁻¹*(t-a)))‖) ≤ η →
      (∀ i,(∫ t in a..a+T,‖orthogonalMatrix e (slopeJet A b K l p t (h i))-
        orthogonalMatrix e (T⁻¹ • B' p (T⁻¹*(t-a)) (h i))‖) ≤ η) →
      let Z := fun q => Real.exp (-(∫ t in a..a+T,v t)) •
        (operatorValue (A q) b l (a+T)*Ring.inverse (operatorValue (A q) b l a))
      let W := fun q => flow (fun u => ContinuousLinearMap.mul ℝ (E →L[ℝ] E) (B q u)) 1 1
      max ‖Z p-W p‖ ‖fderiv ℝ Z p-fderiv ℝ W p‖ ≤ Real.exp (2*J+J*η)*(J*η) := by
  obtain ⟨J,hCJ,hJ,he⟩ := actual_normalized_endpoint_C1 e h hC
  refine ⟨J,hCJ,hJ,?_⟩
  intro A b v K A' B B' S p M MA Mb M₀ l a T η hS hSc hp hA hb hv hK hKe hdK
    hM hMA hMb hM₀ hnK₀ hnK₁ hnA hnb hpos hl ha hT hη hB hB' hdB hnB hnB' hIB hI₀ hI₁
  apply he A b v K A' B B' S p M MA Mb M₀ l a T η hS hSc hp hA hb hv hK hKe hdK
    hM hMA hMb hM₀ hnK₀ hnK₁ hnA hnb hpos hl ha hT hη hB hB' hdB hnB hnB' hIB
  · calc
      _ = ∫ t in a..a+T,‖orthogonalMatrix e (slope (A p) b l t)-
          orthogonalMatrix e (v t • (1:E →L[ℝ] E)+T⁻¹ • B p (T⁻¹*(t-a)))‖ :=
        normalized_matrix_integral (orthogonalMatrix e) (slope (A p) b l) (B p) v 1 a hT
      _ ≤ η := hI₀
  · intro i
    have hi := normalized_matrix_integral (orthogonalMatrix e)
      (fun t => slopeJet A b K l p t (h i)) (fun u => B' p u (h i)) (fun _ => 0) 0 a hT
    simp only [zero_smul,sub_zero,zero_add] at hi
    exact hi.le.trans (hI₁ i)

end HarmonicCounterexample.LinearODE

end

end OAI
