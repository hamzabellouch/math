import Mathlib
import OAI.Probability.SphericalField.Heat.TimeDerivative

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology RealInnerProductSpace
open scoped Pointwise

namespace SphericalPerceptron
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open TopologicalSpace
open scoped Polynomial
open scoped ContDiff

lemma heatLogBCF_moving_hasDerivAt (g : Jet3) (d : ℝ≥0)
    (σ : ℝ → ℝ) (G : ℝ → (ℝ →ᵇ ℝ)) (θ v : ℝ) (h h' : ℝ →ᵇ ℝ)
    (hσ : HasDerivAt σ v θ) (hs : 0 < σ θ)
    (hG : HasDerivAt G h θ) (hGθ : G θ = g.f)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) :
    HasDerivAt (fun t => heatLogBCF (σ t).toNNReal d (G t))
      (v • heatGenerator d (g.heatLog (σ θ).toNNReal d) +
        heatTiltCLM (σ θ).toNNReal d g.f h) θ := by
  let L (t : ℝ) := heatTiltCLM (σ t).toNNReal d g.f
  let A (t : ℝ) := heatLogBCF (σ t).toNNReal d g.f
  let K (t : ℝ) := G t-g.f
  have hK0 : Tendsto K (𝓝 θ) (𝓝 0) := by
    simpa only [hGθ,sub_self] using hG.continuousAt.tendsto.sub_const g.f
  have hKo : (fun t => ‖K t‖) =o[𝓝 θ] (fun _ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr (by simpa only [norm_zero] using hK0.norm)
  have hKb : (fun t => ‖K t‖) =O[𝓝 θ] (fun t => t-θ) := by
    simpa only [hGθ] using hG.isBigO_sub.norm_left
  have hR : (fun t => heatLogBCF (σ t).toNNReal d (G t)-A t-L t (K t))
      =o[𝓝 θ] (fun t => t-θ) := by
    have hb : (fun t => heatLogBCF (σ t).toNNReal d (G t)-A t-L t (K t))
        =O[𝓝 θ] (fun t => ‖K t‖*‖K t‖) := by
      apply Asymptotics.IsBigO.of_bound (2*(d:ℝ))
      apply Filter.Eventually.of_forall
      intro t
      have he := heatLogBCF_terminal_quadratic_error (σ t).toNNReal d g.f (K t)
      simpa only [K,A,L,add_sub_cancel,norm_mul,Real.norm_of_nonneg (norm_nonneg _),pow_two] using he
    exact hb.trans_isLittleO (by simpa only [one_mul] using hKo.mul_isBigO hKb)
  have hE : (fun t => L t (G t-g.f-(t-θ) • h)) =o[𝓝 θ] (fun t => t-θ) := by
    have hb : (fun t => L t (G t-g.f-(t-θ) • h)) =O[𝓝 θ]
        (fun t => G t-g.f-(t-θ) • h) := by
      apply Asymptotics.IsBigO.of_bound'
      exact Filter.Eventually.of_forall (fun t => heatTiltBCF_norm_le (σ t).toNNReal d g.f _)
    apply hb.trans_isLittleO
    simpa only [hGθ] using hG.isLittleO
  have hLc : Tendsto (fun t => L t h-L θ h) (𝓝 θ) (𝓝 0) := by
    have hc := (heatTiltBCF_time_continuous_of_deriv g.f g.d1 h h' g.has1 hh d).continuousAt.comp
      hσ.continuousAt
    have he := hc.tendsto.sub_const (L θ h)
    change Tendsto (fun t => L t h-L θ h) (𝓝 θ) (𝓝 (L θ h-L θ h)) at he
    simpa only [sub_self] using he
  have hLo : (fun t => (t-θ) • (L t h-L θ h)) =o[𝓝 θ] (fun t => t-θ) := by
    have he := (Asymptotics.isBigO_refl (fun t : ℝ => t-θ) (𝓝 θ)).smul_isLittleO
      ((Asymptotics.isLittleO_one_iff ℝ).mpr hLc)
    simpa only [smul_eq_mul,mul_one] using he
  have hA : HasDerivAt A (v • heatGenerator d (g.heatLog (σ θ).toNNReal d)) θ :=
    (heatLogBCF_time_hasDerivAt g d (σ θ) hs).scomp θ hσ
  apply HasDerivAt.of_isLittleO
  apply ((hA.isLittleO.add hR).add hE |>.add hLo).congr_left
  intro t
  simp only [hGθ,K,A,L,map_sub,map_smul,smul_add,smul_sub]
  abel

lemma heatTiltBCF_hasDerivAt (s d : ℝ≥0) (f f' h h' : ℝ →ᵇ ℝ)
    (hf : ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x)
    (hh : ∀ x, HasDerivAt (h:ℝ→ℝ) (h' x) x) (x : ℝ) :
    HasDerivAt (heatTiltBCF s d f h : ℝ→ℝ)
      ((heatTiltBCF s d f h' + (d:ℝ) •
        (heatTiltBCF s d f (f'*h)-heatTiltBCF s d f f'*heatTiltBCF s d f h)) x) x := by
  let A := expBCF d f
  let A' := (d : ℝ) • (A*f')
  have hA y : HasDerivAt (A:ℝ→ℝ) (A' y) y := by
    change HasDerivAt (fun z => Real.exp ((d:ℝ)*f z)) ((d:ℝ)*(A y*f' y)) y
    exact ((hf y).const_mul (d:ℝ)).exp.congr_deriv (by dsimp [A,expBCF]; ring)
  have hB y : HasDerivAt (A*h : ℝ→ᵇ ℝ) ((A'*h+A*h') y) y := by
    simpa only [BoundedContinuousFunction.coe_mul,Pi.mul_apply,
      BoundedContinuousFunction.coe_add,Pi.add_apply] using (hA y).mul (hh y)
  have he := (gaussianAverage_hasDerivAt s (A*h) (A'*h+A*h') hB x).div
    (gaussianAverage_hasDerivAt s A A' hA x) (gaussianAverage_exp_pos s d f x).ne'
  change HasDerivAt (fun y => gaussianAverage s (A*h) y / gaussianAverage s A y) _ x
  apply he.congr_deriv
  have hmul : A'*h = (d:ℝ) • (A*(f'*h)) := by ext y; dsimp [A']; ring
  rw [gaussianAverage_add,hmul,gaussianAverage_smul]
  symm
  change (gaussianAverage s (A*h') x/gaussianAverage s A x) +
    (d:ℝ)*((gaussianAverage s (A*(f'*h)) x/gaussianAverage s A x)-
      (gaussianAverage s (A*f') x/gaussianAverage s A x)*
        (gaussianAverage s (A*h) x/gaussianAverage s A x)) = _
  dsimp only [A']
  rw [gaussianAverage_smul]
  simp only [BoundedContinuousFunction.coe_mul]
  field_simp [show gaussianAverage s A x ≠ 0 from (gaussianAverage_exp_pos s d f x).ne']
  ring

def BoundedC1 (f : ℝ→ᵇ ℝ) : Prop := ∃ f' : ℝ→ᵇ ℝ, ∀ x, HasDerivAt (f:ℝ→ℝ) (f' x) x

lemma BoundedC1.zero : BoundedC1 (0 : ℝ→ᵇ ℝ) := ⟨0,fun x => hasDerivAt_const x 0⟩

lemma BoundedC1.add {f h : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (hh : BoundedC1 h) :
    BoundedC1 (f+h) := by
  obtain ⟨f',hf'⟩ := hf
  obtain ⟨h',hh'⟩ := hh
  exact ⟨f'+h',fun x => (hf' x).add (hh' x)⟩

lemma BoundedC1.smul {f : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (a : ℝ) :
    BoundedC1 (a • f) := by
  obtain ⟨f',hf'⟩ := hf
  exact ⟨a • f',fun x => (hf' x).const_mul a⟩

lemma BoundedC1.heatTilt {f h : ℝ→ᵇ ℝ} (hf : BoundedC1 f) (hh : BoundedC1 h)
    (s d : ℝ≥0) : BoundedC1 (heatTiltCLM s d f h) := by
  obtain ⟨f',hf'⟩ := hf
  obtain ⟨h',hh'⟩ := hh
  exact ⟨_,fun x => heatTiltBCF_hasDerivAt s d f f' h h' hf' hh' x⟩

lemma heatGenerator_boundedC1 (g : Jet3) (d : ℝ≥0) : BoundedC1 (heatGenerator d g) :=
  ⟨_,heatGenerator_hasDerivAt g d⟩

structure HeatIntervalParam where
  duration : ℝ → ℝ
  rate : ℝ
  coefficient : ℝ≥0

def parametricHeatJet (g : Jet3) : List HeatIntervalParam → ℝ → Jet3
  | [], _ => g
  | p::ps, t => (parametricHeatJet g ps t).heatLog (p.duration t).toNNReal p.coefficient

def parametricHeatVelocity (g : Jet3) : List HeatIntervalParam → ℝ → (ℝ→ᵇ ℝ)
  | [], _ => 0
  | p::ps, t => p.rate • heatGenerator p.coefficient (parametricHeatJet g (p::ps) t) +
      heatTiltCLM (p.duration t).toNNReal p.coefficient (parametricHeatJet g ps t).f
        (parametricHeatVelocity g ps t)

lemma parametricHeatVelocity_boundedC1 (g : Jet3) (ps : List HeatIntervalParam) (t : ℝ) :
    BoundedC1 (parametricHeatVelocity g ps t) := by
  induction ps with
  | nil => exact BoundedC1.zero
  | cons p ps ih =>
      exact ((heatGenerator_boundedC1 _ _).smul p.rate).add
        (BoundedC1.heatTilt ⟨_,(parametricHeatJet g ps t).has1⟩ ih _ _)

lemma parametricHeatJet_hasDerivAt (g : Jet3) (ps : List HeatIntervalParam) (θ : ℝ)
    (hp : ∀ p ∈ ps, HasDerivAt p.duration p.rate θ ∧ 0 < p.duration θ) :
    HasDerivAt (fun t => (parametricHeatJet g ps t).f) (parametricHeatVelocity g ps θ) θ := by
  induction ps with
  | nil => exact hasDerivAt_const θ g.f
  | cons p ps ih =>
    have hhead := hp p (List.mem_cons_self ..)
    have htail := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    obtain ⟨h',hh'⟩ := parametricHeatVelocity_boundedC1 g ps θ
    have he := heatLogBCF_moving_hasDerivAt (parametricHeatJet g ps θ) p.coefficient
      p.duration (fun t => (parametricHeatJet g ps t).f) θ p.rate
      (parametricHeatVelocity g ps θ) h' hhead.1 hhead.2 htail rfl hh'
    simpa only [parametricHeatJet,parametricHeatVelocity,Jet3.heatLog_f] using he

end SphericalPerceptron
end
end
end

end OAI
