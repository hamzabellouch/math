import OAI.Combinatorics.Progressions.Estimates.CoefficientAverageL1
import OAI.Combinatorics.Progressions.Estimates.RetainedJointUnitOrder
import OAI.Combinatorics.Progressions.Geometry.AveragedIdealSupport
import OAI.Combinatorics.Progressions.Probability.AveragedJointImageLaw
import OAI.Combinatorics.Progressions.Probability.RetainedGroupedDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

section

variable {W T Q Z X K α : Type*} [MeasurableSpace W] [MeasurableSpace T] [Fintype Q]
  [Fintype α] [DecidableEq α] {I J N : Q → Type*}
  [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
  (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
  (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
  (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
  (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
  (ν : Measure T) (z : W → T → Z → ℝ) (x : W → T → X → ℝ)

noncomputable def flatAffineMixtureDensity (a : W) (v : (Σ q, I q) → ℝ) : ℝ :=
  densityMixture ν (fun t => jointAffineJetDensity s A F e input (z a t) rows c w (x a t))
    (sigmaAxisCoordinates I v)

noncomputable def flatAffineUnitSource
    (p : (W × (∀ q, J q ⊕ N q → ℝ)) × T) : W × ((Σ q, I q) → ℝ) :=
  (p.1.1, (sigmaAxisCoordinates I).symm
    (jointAffineJetUnitMap s A F e input (z p.1.1 p.2) rows c w (x p.1.1 p.2) p.1.2))

variable (hz : ∀ j, Measurable (fun p : W × T => z p.1 p.2 j))
  (hx : ∀ j, Measurable (fun p : W × T => x p.1 p.2 j))

include hz hx in
theorem flatAffineUnitSource_measurable :
    Measurable (flatAffineUnitSource s A F e input rows c w z x) := by
  have hm := jointAffineJetUnitMap_measurable_comp (Ω := (W × (∀ q, J q ⊕ N q → ℝ)) × T)
    s A F e input rows (fun _ => c) (fun _ => w) (fun p => p.1.2)
    (fun _ => measurable_const) (fun _ => measurable_const)
    (fun q => (measurable_pi_apply q).comp (measurable_snd.comp measurable_fst))
    (fun p => z p.1.1 p.2) (fun j => (hz j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (fun p => x p.1.1 p.2) (fun j => (hx j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  exact (measurable_fst.comp measurable_fst).prodMk ((sigmaAxisCoordinates I).symm.continuous.measurable.comp hm)

variable (hw : ∀ q j, 0 < w q j) (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)

include hw hsupport hz hx in
theorem flatAffineMixtureDensity_measurable [SFinite ν] :
    Measurable (Function.uncurry (flatAffineMixtureDensity s A F e input rows c w ν z x)) := by
  have hm := jointAffineJetDensity_measurable_comp (Ω := (W × ((Σ q, I q) → ℝ)) × T)
    s A F e input rows c w hw R hsupport
    (fun p => z p.1.1 p.2) (fun j => (hz j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (fun p => x p.1.1 p.2) (fun j => (hx j).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    (fun p => sigmaAxisCoordinates I p.1.2)
    (fun q i => (measurable_pi_apply (⟨q, i⟩ : Σ q, I q)).comp (measurable_snd.comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

include hw hsupport hz hx in
theorem flatAffineMixtureDensity_image_law (μ : Measure W) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((μ.prod (jointUnitCoefficientSource J N)).prod ν).map
      (flatAffineUnitSource s A F e input rows c w z x) =
      realDensityMeasure (μ.prod volume) (Function.uncurry (flatAffineMixtureDensity s A F e input rows c w ν z x)) := by
  have hlaw := jointAffineJetDensity_retained_conditioned_law s A F e input rows c w hw R hsupport μ ν z hz x hx
  let g := fun p : W × (∀ q, I q → ℝ) => (p.1, (sigmaAxisCoordinates I).symm p.2)
  have hg : Measurable g := measurable_fst.prodMk ((sigmaAxisCoordinates I).symm.continuous.measurable.comp measurable_snd)
  have hm := flatAffineUnitSource_measurable s A F e input rows c w z x hz hx
  have hgroup : Measurable (fun p : (W × (∀ q, J q ⊕ N q → ℝ)) × T =>
      (p.1.1, jointAffineJetUnitMap s A F e input (z p.1.1 p.2) rows c w (x p.1.1 p.2) p.1.2)) := by
    have hback : Measurable (fun p : W × ((Σ q, I q) → ℝ) => (p.1, sigmaAxisCoordinates I p.2)) :=
      measurable_fst.prodMk ((sigmaAxisCoordinates I).continuous.measurable.comp measurable_snd)
    simpa only [Function.comp_def, flatAffineUnitSource, ContinuousLinearEquiv.apply_symm_apply] using hback.comp hm
  have ht := congrArg (Measure.map g) hlaw
  rw [Measure.map_map hg hgroup] at ht
  exact ht.trans (retained_density_flatten I μ _)

end

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

section

variable {W T Q Z X K α : Type*} [MeasurableSpace W] [MeasurableSpace T] [Fintype Q]
  [Fintype α] [DecidableEq α] {I J N : Q → Type*}
  [∀ q, Fintype (I q)] [∀ q, Fintype (J q)] [∀ q, Fintype (N q)]
  (s : ∀ q, I q ↪ J q) (A : ∀ q, (I q → ℝ) ≃L[ℝ] (I q → ℝ))
  (F : ∀ q, (UnselectedColumn (s q) → ℝ) →L[ℝ] (I q → ℝ))
  (e : ∀ q, N q → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
  (rows : ∀ q, I q → Finset α) (c w : ∀ q, J q ⊕ N q → ℝ)
  (ν : Measure T) [IsProbabilityMeasure ν] (z : W → T → Z → ℝ) (x : W → T → X → ℝ)
  (hz : ∀ j, Measurable (fun p : W × T => z p.1 p.2 j))
  (hx : ∀ j, Measurable (fun p : W × T => x p.1 p.2 j))
  (hw : ∀ q j, 0 < w q j) (R : Q → ℝ≥0) (hsupport : ∀ q j, |c q j|+w q j ≤ R q)

include hz hx hw hsupport in
theorem flatAffineMixtureDensity_probability (a : W) :
    (∀ v, 0 ≤ flatAffineMixtureDensity s A F e input rows c w ν z x a v) ∧
      Integrable (flatAffineMixtureDensity s A F e input rows c w ν z x a) ∧
      (∫ v, flatAffineMixtureDensity s A F e input rows c w ν z x a v) = 1 := by
  let D := fun t => jointAffineJetDensity s A F e input (z a t) rows c w (x a t)
  have hm : Measurable (Function.uncurry D) :=
    jointAffineJetDensity_measurable_comp (Ω := T × (∀ q, I q → ℝ)) s A F e input rows c w hw R hsupport
      (fun p => z a p.1) (fun j => (hz j).comp (measurable_const.prodMk measurable_fst))
      (fun p => x a p.1) (fun j => (hx j).comp (measurable_const.prodMk measurable_fst))
      (fun p => p.2) (fun q i => (measurable_pi_apply i).comp ((measurable_pi_apply q).comp measurable_snd))
  have hp := densityMixture_probability_density ν volume D hm (Filter.Eventually.of_forall (fun t => by
    have ht := jointAffineJetDensity_probability_data s A F e input (z a t) rows c w hw R hsupport (x a t)
    exact ⟨ht.2.1, ht.1, ht.2.2⟩))
  refine ⟨fun v => hp.1 _, (sigmaAxisCoordinates_measurePreserving I).integrable_comp_of_integrable hp.2.1, ?_⟩
  exact ((sigmaAxisCoordinates_measurePreserving I).integral_comp
    (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding _).trans hp.2.2

include hz hx hw hsupport in
theorem flatAffineMixtureDensity_bounds (a : W)
    (δ : Q → ℝ≥0) (hδ : ∀ q, 0 < δ q) (hwidth : ∀ q j, (δ q : ℝ) ≤ w q (.inl j))
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ q, pivotKernelCap (UnselectedColumn (s q)) (A q) (R q) ((δ q)⁻¹^Fintype.card (J q)) ≤ Cap)
    (hlip : ∀ q, pivotKernelLip (UnselectedColumn (s q)) (A q) (R q) (affineProductProfileLip (J q) (δ q)) ≤ Lip) :
    (∀ v, flatAffineMixtureDensity s A F e input rows c w ν z x a v ∈ Set.Icc (0 : ℝ) ((Cap : ℝ)^Fintype.card Q)) ∧
      LipschitzWith (Fintype.card Q*Lip*Cap^Fintype.card Q)
        (flatAffineMixtureDensity s A F e input rows c w ν z x a) := by
  have ht := jointAffineJetDensity_mixture_spec s A F e input rows c w hw R hsupport ν
    (z a) (fun j => (hz j).comp (measurable_const.prodMk measurable_id))
    (x a) (fun j => (hx j).comp (measurable_const.prodMk measurable_id)) δ hδ hwidth Cap Lip hCap hcap hlip
  refine ⟨fun v => ht.1 _, ?_⟩
  change LipschitzWith (Fintype.card Q*Lip*Cap^Fintype.card Q)
    ((densityMixture ν (fun t => jointAffineJetDensity s A F e input (z a t) rows c w (x a t))) ∘ sigmaAxisCoordinates I)
  simpa only [mul_one] using ht.2.1.comp (sigmaAxisCoordinates_lipschitz I)

end

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem canonicalAffineRawArray_retained_test {W D G Z α : Type*} [MeasurableSpace W] [Fintype D]
    [Fintype α] [DecidableEq α] {B O J N : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
    (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
    (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
    (Q : D → ℝ) (hQ : ∀ d, 0 < Q d) (T : SamplerTupleIndex G B h → ℝ) (hT : ∀ k, 0 < T k)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (extra : G → Option α → Z) (z : W → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (hkernel : ∀ a x d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
        (normalizedCubeTuple (canonicalTupleInput extra) (z a) x) (sets d))
    (c w : ∀ d, J d ⊕ N d → ℝ) (hw : ∀ d j, 0 < w d j)
    (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (μ : Measure W) [IsProbabilityMeasure μ]
    (φ : W × ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) :
    let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
      (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
    let F := fun d => matrixSupCLM
      (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
    (∫ p, φ (p.1.1, canonicalAffineRawArray h (fun d => Sum.elim (eK d) (eN d)) Q T c w p.1.2 sets
        (rawCanonicalCubeTuple extra T (z p.1.1) p.2))
      ∂(μ.prod (jointUnitCoefficientSource J N)).prod (scaledJointCubeSource h (fun i => T (.inr i)))) =
    ∫ p, flatAffineMixtureDensity s E F eN (canonicalTupleInput extra) sets c w (jointBooleanSource h)
      (fun a _ => z a) (fun _ x => x) p.1 p.2*φ p ∂μ.prod volume := by
  dsimp only
  let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
    (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
  let F := fun d => matrixSupCLM
    (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
  have hz' (j) : Measurable (fun p : W × (JointBlockParameter B h α → ℝ) => z p.1 j) :=
    (hz j).comp measurable_fst
  have hx' (j) : Measurable (fun p : W × (JointBlockParameter B h α → ℝ) => p.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  rw [scaledJointCubeSource_prod_integral h _ (fun i => hT (.inr i))]
  have heval (p : (W × (∀ d, J d ⊕ N d → ℝ)) × (JointBlockParameter B h α → ℝ)) :=
    canonicalAffineRawArray_eq_jointUnitMap h hh sets M s hM S hS Q hQ T (fun k => (hT k).ne') eK eN
      extra (z p.1.1) p.2 (hkernel p.1.1 p.2) c w p.1.2
  simp_rw [heval]
  have hp (a) := flatAffineMixtureDensity_probability s E F eN (canonicalTupleInput extra) sets c w
    (jointBooleanSource h) (fun a _ => z a) (fun _ x => x) hz' hx' hw R hsupport a
  exact mappedTest_eq_density ((μ.prod (jointUnitCoefficientSource J N)).prod (jointBooleanSource h))
    (μ.prod volume) (flatAffineUnitSource s E F eN (canonicalTupleInput extra) sets c w (fun a _ => z a) (fun _ x => x))
    (flatAffineUnitSource_measurable s E F eN (canonicalTupleInput extra) sets c w (fun a _ => z a) (fun _ x => x) hz' hx') _
    (flatAffineMixtureDensity_measurable s E F eN (canonicalTupleInput extra) sets c w
      (jointBooleanSource h) (fun a _ => z a) (fun _ x => x) hz' hx' hw R hsupport)
    (fun p => (hp p.1).1 p.2)
    (flatAffineMixtureDensity_image_law s E F eN (canonicalTupleInput extra) sets c w
      (jointBooleanSource h) (fun a _ => z a) (fun _ x => x) hz' hx' hw R hsupport μ) φ hφ

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

section

variable {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
  {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
  (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
  (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
  (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
  (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
  (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
  (c w : ∀ d, J d ⊕ N d → ℝ) (t : ℝ) (z : W → Z → ℝ)

noncomputable def smallAffineMixtureDensity (a : W) (v : (Σ d, O d) → ℝ) : ℝ :=
  flatAffineMixtureDensity s A F eN (canonicalTupleInput extra) sets
    (fun d j => nonprincipalDilation (Sum.elim (eK d) (eN d)) (canonicalPrincipalExponent h d) t j*c d j)
    (fun d j => nonprincipalDilation (Sum.elim (eK d) (eN d)) (canonicalPrincipalExponent h d) t j*w d j)
    (jointBooleanSource h) (fun a _ => z a) (fun _ x => x) a v

variable (hz : ∀ j, Measurable (fun a => z a j)) (ht : 0 < t) (ht1 : t ≤ 1)
  (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)

include hz ht ht1 hw hsupport in
theorem smallAffineMixtureDensity_measurable :
    Measurable (Function.uncurry (smallAffineMixtureDensity h eK eN s A F sets extra c w t z)) := by
  apply flatAffineMixtureDensity_measurable s A F eN (canonicalTupleInput extra) sets _ _
    (jointBooleanSource h) (fun a _ => z a) (fun _ x => x)
    (fun j => (hz j).comp measurable_fst) (fun j => (measurable_pi_apply j).comp measurable_snd)
    _ R _
  · exact fun d j => nonprincipalDilation_width_pos _ _ ht (w d) (hw d) j
  · exact fun d j => nonprincipalDilation_profile_support _ _ ht ht1 (c d) (w d)
      (fun j => (hw d j).le) (hsupport d) j

include hz ht ht1 hw hsupport in
theorem smallAffineMixtureDensity_probability (a : W) :
    (∀ v, 0 ≤ smallAffineMixtureDensity h eK eN s A F sets extra c w t z a v) ∧
      Integrable (smallAffineMixtureDensity h eK eN s A F sets extra c w t z a) ∧
      (∫ v, smallAffineMixtureDensity h eK eN s A F sets extra c w t z a v) = 1 := by
  apply flatAffineMixtureDensity_probability s A F eN (canonicalTupleInput extra) sets _ _
    (jointBooleanSource h) (fun a _ => z a) (fun _ x => x)
    (fun j => (hz j).comp measurable_fst) (fun j => (measurable_pi_apply j).comp measurable_snd)
    _ R _ a
  · exact fun d j => nonprincipalDilation_width_pos _ _ ht (w d) (hw d) j
  · exact fun d j => nonprincipalDilation_profile_support _ _ ht ht1 (c d) (w d)
      (fun j => (hw d j).le) (hsupport d) j

end

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

section

variable {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
  {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
  (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
  (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
  (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
  (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
  (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
  (c w : ∀ d, J d ⊕ N d → ℝ) (z : W → Z → ℝ)
  (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)

include hw hsupport in
theorem smallAffineMixtureDensity_bounds
    (hz : ∀ j, Measurable (fun a => z a j))
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) (a : W)
    (δ : D → ℝ≥0) (hδ : ∀ d, 0 < δ d) (hwidth : ∀ d j, (δ d : ℝ) ≤ w d j)
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ d, pivotKernelCap (UnselectedColumn (s d)) (A d) (R d)
      ((t*δ d)⁻¹^Fintype.card (J d)) ≤ Cap)
    (hlip : ∀ d, pivotKernelLip (UnselectedColumn (s d)) (A d) (R d)
      (affineProductProfileLip (J d) (t*δ d)) ≤ Lip) :
    (∀ v, smallAffineMixtureDensity h eK eN s A F sets extra c w t z a v ∈
      Set.Icc (0 : ℝ) ((Cap : ℝ)^Fintype.card D)) ∧
      LipschitzWith (Fintype.card D*Lip*Cap^Fintype.card D)
        (smallAffineMixtureDensity h eK eN s A F sets extra c w t z a) := by
  apply flatAffineMixtureDensity_bounds s A F eN (canonicalTupleInput extra) sets _ _
    (jointBooleanSource h) (fun a _ => z a) (fun _ x => x)
    (fun j => (hz j).comp measurable_fst) (fun j => (measurable_pi_apply j).comp measurable_snd)
    _ R _ a (fun d => t*δ d) (fun d => mul_pos ht (hδ d)) _ Cap Lip hCap hcap hlip
  · exact fun d j => nonprincipalDilation_width_pos _ _ ht (w d) (hw d) j
  · exact fun d j => nonprincipalDilation_profile_support _ _ ht ht1 (c d) (w d)
      (fun j => (hw d j).le) (hsupport d) j
  · exact fun d j => nonprincipalDilation_width_lower _ _ ht.le ht1 (w d)
      (fun j => (hw d j).le) (hwidth d) (.inl j)

omit [MeasurableSpace W] in
include hw hsupport in
theorem smallAffineMixtureDensity_support
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (a : W) (hz : ∀ j, |z a j| ≤ 1)
    (degree : D → ℕ) (hd : ∀ d n, (eN d n).sum (fun _ k => k) ≤ degree d)
    (Ro : ℝ≥0) (hRo : ∀ d, normalizedJetOutputRadius α (N d) (A d) (F d)
      (degree d) (R d) (R d) ≤ Ro) :
    ∀ v, (Ro : ℝ) < ‖v‖ → smallAffineMixtureDensity h eK eN s A F sets extra c w t z a v = 0 := by
  intro v hv
  apply jointAffineJetDensity_mixture_support s A F eN (canonicalTupleInput extra) sets _ _
    (fun d j => nonprincipalDilation_width_pos _ _ ht (w d) (hw d) j) R
    (fun d j => nonprincipalDilation_profile_support _ _ ht ht1 (c d) (w d)
      (fun j => (hw d j).le) (hsupport d) j)
    (jointBooleanSource h) (fun _ => z a) (fun x => x) _ degree hd Ro hRo (sigmaAxisCoordinates O v) _
  · filter_upwards [jointBooleanSource_ae_closedBall B h] with x hx
    exact ⟨hz, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx⟩
  · simpa only [sigmaAxisCoordinates_norm] using hv

end

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem smallAffineMixtureDensity_test {W D G Z α : Type*} [MeasurableSpace W] [Fintype D]
    [Fintype α] [DecidableEq α] {B O J N : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
    (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
    (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
    (Q : D → ℝ) (hQ : ∀ d, 0 < Q d) (T : SamplerTupleIndex G B h → ℝ) (hT : ∀ k, 0 < T k)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (extra : G → Option α → Z) (z : W → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (hkernel : ∀ a x d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
      realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
        (normalizedCubeTuple (canonicalTupleInput extra) (z a) x) (sets d))
    (c w : ∀ d, J d ⊕ N d → ℝ) (hw : ∀ d j, 0 < w d j)
    (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (μ : Measure W) [IsProbabilityMeasure μ]
    (φ : W × ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) :
    let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
      (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
    let F := fun d => matrixSupCLM
      (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
    (∫ p, φ (p.1.1, smallAffineSourceOutput h (fun d => Sum.elim (eK d) (eN d)) c w sets extra
        (fun _ => Q) T t (fun a => z a.1) (fun a => a.2) p)
      ∂(μ.prod (jointUnitCoefficientSource J N)).prod (scaledJointCubeSource h (fun i => T (.inr i)))) =
    ∫ p, smallAffineMixtureDensity h eK eN s E F sets extra c w t z p.1 p.2*φ p ∂μ.prod volume := by
  dsimp only
  exact canonicalAffineRawArray_retained_test h hh sets M s hM S hS Q hQ T hT eK eN extra z hz hkernel
    (fun d j => nonprincipalDilation (Sum.elim (eK d) (eN d)) (canonicalPrincipalExponent h d) t j*c d j)
    (fun d j => nonprincipalDilation (Sum.elim (eK d) (eN d)) (canonicalPrincipalExponent h d) t j*w d j)
    (fun d j => nonprincipalDilation_width_pos _ _ ht (w d) (hw d) j) R
    (fun d j => nonprincipalDilation_profile_support _ _ ht ht1 (c d) (w d) (fun j => (hw d j).le) (hsupport d) j)
    μ φ hφ

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem smallAffineMixtureDensity_log_bounds
    {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
    (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
    (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (c w : ∀ d, J d ⊕ N d → ℝ) (z : W → Z → ℝ)
    (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (hz : ∀ j, Measurable (fun a => z a j)) (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (δ : D → ℝ≥0) (hδ : ∀ d, 0 < δ d) (hwidth : ∀ d j, (δ d : ℝ) ≤ w d j)
    {P T : ℝ} (hP : 0 ≤ P) (hT : 0 ≤ T)
    (hA : ∀ d, ‖(A d).symm.toContinuousLinearMap‖ ≤ Real.exp P)
    (hR : ∀ d, (R d : ℝ) ≤ Real.exp P)
    (htT : (t : ℝ)⁻¹ ≤ Real.exp T) (hδP : ∀ d, (δ d : ℝ)⁻¹ ≤ Real.exp P) (a : W) :
    let b := jointPivotProfileLog s P T
    (∀ v, smallAffineMixtureDensity h eK eN s A F sets extra c w t z a v ∈
      Set.Icc (0 : ℝ) (Real.exp (Fintype.card D*b))) ∧
    LipschitzWith ⟨Real.exp (Fintype.card D+(Fintype.card D+1)*b), Real.exp_nonneg _⟩
      (smallAffineMixtureDensity h eK eN s A F sets extra c w t z a) := by
  let b := jointPivotProfileLog s P T
  let C : ℝ≥0 := ⟨Real.exp b, Real.exp_nonneg _⟩
  obtain ⟨hC, hbounds⟩ := jointPivotProfile_regularity s A R δ t ht hδ hP hT hA hR htT hδP
  have hs := smallAffineMixtureDensity_bounds h eK eN s A F sets extra c w z hw R hsupport
    hz t ht ht1 a δ hδ hwidth C C hC (fun d => (hbounds d).1) (fun d => (hbounds d).2)
  dsimp only
  constructor
  · intro v
    refine ⟨(hs.1 v).1, (hs.1 v).2.trans_eq ?_⟩
    exact (Real.exp_nat_mul b (Fintype.card D)).symm
  · apply hs.2.weaken
    change (Fintype.card D : ℝ)*Real.exp b*(Real.exp b)^Fintype.card D ≤ _
    exact jointDensityLip_le_exp _ b

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem exists_averaged_regularized_affine_l1_with_parameters
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (Sum.elim (eK d) (eN d)))
    (index : ∀ d, B d → J d ⊕ N d)
    (hindex : ∀ d b, Sum.elim (eK d) (eN d) (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d ⊕ N d → ℝ) (hw : ∀ d j, 0 < w d j)
    (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (z : W → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A L : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith L Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (Sum.elim (eK d) (eN d) j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B) (O := O) (α := α) h c₀ C A L (ε/2) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t = booleanPerturbationScale (B := B) (O := O) (α := α) (AffineAuxiliaryIndex Z (fun d => J d ⊕ N d)) h c₀ C A L degree Csum Wsum (ε/2) ∧
      ∀ (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
        (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
        (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
        (Q : D → ℝ) (hQ : ∀ d, 0 < Q d)
        (T : SamplerTupleIndex G B h → ℝ), (∀ k, 0 < T k) →
      (∀ a x d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
        realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
          (normalizedCubeTuple (canonicalTupleInput extra) (z a) x) (sets d)) →
      ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
        (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
      let F := fun d => matrixSupCLM
        (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
      (∫ p : W × ((Σ d, O d) → ℝ),
        |averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets δ p.2 -
          smallAffineMixtureDensity h eK eN s E F sets extra c w t z p.1 p.2| ∂μ.prod volume) ≤ ε := by
  let e := fun d => Sum.elim (eK d) (eN d)
  have hr : ∀ d j, Measurable (fun p : W × (∀ d, J d ⊕ N d → ℝ) => p.2 d j) :=
    fun d j => (measurable_pi_apply j).comp ((measurable_pi_apply d).comp measurable_snd)
  obtain ⟨δ, hδ, hδ1, hδeq, t, ht, ht1, hteq, hcomp⟩ := exists_regularized_affine_comparison_with_parameters
    (Ω := W × (∀ d, J d ⊕ N d → ℝ)) (Y := W × ((Σ d, O d) → ℝ))
    h hh e he index hindex c w (fun p => p.2) hr
    (fun p => z p.1) (fun j => (hz j).comp measurable_fst) sets hsets hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A L hLip hTransition extra
    hdegree htaildegree hCsum hWsum hcsum hwsum hε
  refine ⟨δ, hδ, hδ1, hδeq, t, ht, ht1, hteq, ?_⟩
  intro M s hM S hS Q hQ T hT hkernel μ hμ hzb
  let : IsProbabilityMeasure μ := hμ
  dsimp only
  let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
    (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
  let F := fun d => matrixSupCLM
    (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
  let g := smallAffineMixtureDensity h eK eN s E F sets extra c w t z
  have hgm : Measurable (Function.uncurry g) :=
    smallAffineMixtureDensity_measurable h eK eN s E F sets extra c w t z hz ht ht1 hw R hsupport
  have hgp := smallAffineMixtureDensity_probability h eK eN s E F sets extra c w t z hz ht ht1 hw R hsupport
  have hgi : Integrable (Function.uncurry g) (μ.prod volume) :=
    densityMixture_joint_integrable μ volume g hgm (Filter.Eventually.of_forall hgp)
  apply coefficientAverage_density_l1 μ (jointUnitCoefficientSource J N)
    (scaledJointCubeSource h (fun i => T (.inr i))) volume
    (regularizedAffineIdealDensity h e index c w sets δ)
    (regularizedAffineIdealDensity_joint_measurable h e index c w sets δ)
    (regularizedAffineIdealDensity_probability h e index c w sets δ hδ)
    (Function.uncurry g) hgm hgi
    (fun p => (p.1.1, smallAffineSourceOutput h e c w sets extra (fun _ => Q) T t
      (fun a => z a.1) (fun a => a.2) p))
  · intro φ hφ _
    exact smallAffineMixtureDensity_test h hh sets M s hM S hS Q hQ T hT eK eN extra z hz hkernel
      c w hw R hsupport t ht ht1 μ φ hφ
  · intro φ hφ hbound
    exact hcomp (fun _ => Q) T (fun _ d => (hQ d).ne') hT (μ.prod (jointUnitCoefficientSource J N))
      inferInstance (Measure.quasiMeasurePreserving_fst.ae hzb)
      (Measure.quasiMeasurePreserving_snd.ae (jointUnitCoefficientSource_abs_le J N))
      (fun p => (p.1.1, p.2)) (measurable_fst.fst.prodMk measurable_snd) φ hφ hbound

theorem exists_averaged_regularized_affine_l1
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (Sum.elim (eK d) (eN d)))
    (index : ∀ d, B d → J d ⊕ N d)
    (hindex : ∀ d b, Sum.elim (eK d) (eN d) (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d ⊕ N d → ℝ) (hw : ∀ d j, 0 < w d j)
    (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (z : W → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A L : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith L Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (Sum.elim (eK d) (eN d) j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      ∀ (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
        (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
        (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
        (Q : D → ℝ) (hQ : ∀ d, 0 < Q d)
        (T : SamplerTupleIndex G B h → ℝ), (∀ k, 0 < T k) →
      (∀ a x d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
        realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
          (normalizedCubeTuple (canonicalTupleInput extra) (z a) x) (sets d)) →
      ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
        (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
      let F := fun d => matrixSupCLM
        (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
      (∫ p : W × ((Σ d, O d) → ℝ),
        |averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets δ p.2 -
          smallAffineMixtureDensity h eK eN s E F sets extra c w t z p.1 p.2| ∂μ.prod volume) ≤ ε := by
  obtain ⟨δ, hδ, hδ1, _, t, ht, ht1, _, herr⟩ := exists_averaged_regularized_affine_l1_with_parameters h hh eK eN he index hindex c w hw R hsupport z hz sets hsets hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A L hLip hTransition extra
    hdegree htaildegree hCsum hWsum hcsum hwsum hε
  exact ⟨δ, hδ, hδ1, t, ht, ht1, herr⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem averagedAffine_density_data
    {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d)
    (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
    (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
    (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (c w : ∀ d, J d ⊕ N d → ℝ) (z : W → Z → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (δ : D → ℝ≥0) (hδ : ∀ d, 0 < δ d) (hwidth : ∀ d j, (δ d : ℝ) ≤ w d j)
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ d, pivotKernelCap (UnselectedColumn (s d)) (A d) (R d)
      ((t*δ d)⁻¹^Fintype.card (J d)) ≤ Cap)
    (hlip : ∀ d, pivotKernelLip (UnselectedColumn (s d)) (A d) (R d)
      (affineProductProfileLip (J d) (t*δ d)) ≤ Lip)
    (degree : D → ℕ) (hd : ∀ d n, (eN d n).sum (fun _ k => k) ≤ degree d)
    (Ro : ℝ≥0) (hRo : ∀ d, normalizedJetOutputRadius α (N d) (A d) (F d)
      (degree d) (R d) (R d) ≤ Ro)
    (η : ℝ≥0) (hη : 0 < η) {Csum Wsum Ri : ℝ} (hRi : 0 ≤ Ri) (hRiRo : Ri+η ≤ Ro)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, (|c d j|+|w d j|)) ≤ Wsum)
    (hideal : ∀ d o, Wsum+(2 : ℝ)^(sets d o).card*(Csum*((Fintype.card α : ℝ)+1)^h d) ≤ Ri)
    (μ : Measure W) [IsProbabilityMeasure μ] (hzbox : ∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) :
    let f := averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η
    let g := smallAffineMixtureDensity h eK eN s A F sets extra c w t z
    Integrable (fun p : W × ((Σ d, O d) → ℝ) => f p.2-g p.1 p.2) (μ.prod volume) ∧
      (∀ᵐ a ∂μ, LipschitzWith (affineProductProfileLip (Σ d, O d) η) f ∧
        LipschitzWith (Fintype.card D*Lip*Cap^Fintype.card D) (g a) ∧
        (∀ v, (Ro : ℝ) < ‖v‖ → f v = 0) ∧ (∀ v, (Ro : ℝ) < ‖v‖ → g a v = 0)) := by
  dsimp only
  let f := averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η
  let g := smallAffineMixtureDensity h eK eN s A F sets extra c w t z
  have hf := averagedRegularizedIdeal_spec h (fun d => Sum.elim (eK d) (eN d)) index c w sets η hη
  have hg := smallAffineMixtureDensity_bounds h eK eN s A F sets extra c w z hw R hsupport
    hz t ht ht1
  have hfi : Integrable (fun p : W × ((Σ d, O d) → ℝ) => f p.2) (μ.prod volume) := hf.2.2.1.comp_snd μ
  have hgi : Integrable (Function.uncurry g) (μ.prod volume) :=
    densityMixture_joint_integrable μ volume g
      (smallAffineMixtureDensity_measurable h eK eN s A F sets extra c w t z hz ht ht1 hw R hsupport)
      (Filter.Eventually.of_forall
        (smallAffineMixtureDensity_probability h eK eN s A F sets extra c w t z hz ht ht1 hw R hsupport))
  have hfs : ∀ w v, (Ro : ℝ) < ‖v‖ → (fun _ : W => f) w v = 0 := by
    intro _ v hv
    exact averagedRegularizedIdeal_support h (fun d => Sum.elim (eK d) (eN d)) index c w sets η hη
      hRi hcsum hwsum hideal v (lt_of_le_of_lt hRiRo hv)
  have hgood : ∀ᵐ a ∂μ, LipschitzWith (affineProductProfileLip (Σ d, O d) η) f ∧
      LipschitzWith (Fintype.card D*Lip*Cap^Fintype.card D) (g a) ∧
      (∀ v, (Ro : ℝ) < ‖v‖ → f v = 0) ∧ (∀ v, (Ro : ℝ) < ‖v‖ → g a v = 0) := by
    filter_upwards [hzbox] with a ha
    exact ⟨hf.2.1, (hg a δ hδ hwidth Cap Lip hCap hcap hlip).2, hfs a,
      smallAffineMixtureDensity_support h eK eN s A F sets extra c w z hw R hsupport
        t ht ht1 a ha degree hd Ro hRo⟩
  exact ⟨hfi.sub hgi, hgood⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

theorem exists_averaged_affine_l1_with_parameter_bounds
    {W D G Z α : Type*} [MeasurableSpace W]
    [Fintype D] [DecidableEq D] [Fintype Z] [DecidableEq Z] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (he : ∀ d, Function.Injective (Sum.elim (eK d) (eN d)))
    (index : ∀ d, B d → J d ⊕ N d)
    (hindex : ∀ d b, Sum.elim (eK d) (eN d) (index d b) = canonicalPrincipalExponent h d b)
    (c w : ∀ d, J d ⊕ N d → ℝ) (hw : ∀ d j, 0 < w d j)
    (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (z : W → Z → ℝ) (hz : ∀ j, Measurable (fun a => z a j))
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (index d (block d o))|-|w d (index d (block d o))|)
    (hcup : ∀ d o, |c d (index d (block d o))|+|w d (index d (block d o))| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A L : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith L Real.smoothTransition)
    (extra : G → Option α → Z) {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (htaildegree : ∀ d j, (Sum.elim (eK d) (eN d) j).sum (fun _ n => n) ≤ degree)
    {Csum Wsum : ℝ} (hCsum : 0 ≤ Csum) (hWsum : 0 ≤ Wsum)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, affineCoefficientAllowance (c d j) (w d j)) ≤ Wsum)
    {ε : ℝ} (hε : 0 < ε) {P : ℝ} (hP : 0 ≤ P)
    (hNoise : (jointBooleanRegularizationBudget (B := B) (O := O) (α := α) h c₀ C A L
      (fun _ => (ε/2)/(4*((Fintype.card D : ℝ)+1))) : ℝ) ≤ Real.exp P)
    (hm : (Fintype.card (Σ d, O d) : ℝ) ≤ Real.exp P)
    (hK : (jointBooleanInverseBudget (O := O) (α := α) h C
      (booleanToleranceMinor (O := O) (α := α) h c₀ (ε/2)) : ℝ) ≤ Real.exp P)
    (hM : booleanToleranceC2 (B := B) (α := α) (AffineAuxiliaryIndex Z (fun d => J d ⊕ N d))
      h degree Csum Wsum ≤ Real.exp P)
    (hQbudget : booleanToleranceDivergence (B := B) (O := O) (α := α) h c₀ C A L (ε/2) ≤ Real.exp P)
    (hAccuracy : (ε/4)⁻¹ ≤ Real.exp P) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ)⁻¹ ≤ Real.exp (2*P+2) ∧
      ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      t⁻¹ ≤ Real.exp (6*P+8) ∧
      ∀ (M : ∀ d, Matrix (O d) (J d) ℤ) (s : ∀ d, O d ↪ J d)
        (hM : ∀ d, ((M d).submatrix id (s d)).det ≠ 0)
        (S : ∀ d, J d → ℝ) (hS : ∀ d j, 0 < S d j)
        (Q : D → ℝ) (hQ : ∀ d, 0 < Q d)
        (T : SamplerTupleIndex G B h → ℝ), (∀ k, 0 < T k) →
      (∀ a x d, normalizedIntegerColumns (M d) (S d) (fun _ => Q d) =
        realJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1)
          (normalizedCubeTuple (canonicalTupleInput extra) (z a) x) (sets d)) →
      ∀ μ : Measure W, IsProbabilityMeasure μ → (∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) →
      let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hM d)
        (fun j => S d (s d j)) (fun _ => Q d) (fun j => hS d (s d j)) (fun _ => hQ d)
      let F := fun d => matrixSupCLM
        (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
      (∫ p : W × ((Σ d, O d) → ℝ),
        |averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets δ p.2 -
          smallAffineMixtureDensity h eK eN s E F sets extra c w t z p.1 p.2| ∂μ.prod volume) ≤ ε := by
  obtain ⟨δ, hδ, hδ1, hδeq, t, ht, ht1, hteq, herr⟩ :=
    exists_averaged_regularized_affine_l1_with_parameters
      h hh eK eN he index hindex c w hw R hsupport z hz sets hsets hcard block hblock
      c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A L hLip hTransition extra
      hdegree htaildegree hCsum hWsum hcsum hwsum hε
  have hhalf : (ε/2)⁻¹ ≤ Real.exp P := by
    apply le_trans _ hAccuracy
    simpa only [one_div] using
      one_div_le_one_div_of_le (show 0 < ε/4 by positivity) (show ε/4 ≤ ε/2 by linarith)
  have hquarter : ((ε/2)/2)⁻¹ ≤ Real.exp P := by
    have heq : (ε/2)/2 = ε/4 := by ring
    simpa only [heq] using hAccuracy
  refine ⟨δ, hδ, hδ1, ?_, t, ht, ht1, ?_, herr⟩
  · rw [hδeq]
    exact booleanRegularizationRadius_inverse_le_exp h c₀ C A L (half_pos hε) hP hNoise hhalf
  · rw [hteq]
    exact booleanPerturbationScale_inverse_le_exp (AffineAuxiliaryIndex Z (fun d => J d ⊕ N d))
      h hh c₀ C hc₀ hC A L degree hCsum hWsum (half_pos hε) hP hm hK hM hQbudget hquarter

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem averagedAffine_grid_error
    {W D G Z α : Type*} [MeasurableSpace W] [Fintype D] [Fintype α] [DecidableEq α]
    {B O J N : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    [∀ d, Fintype (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (index : ∀ d, B d → J d ⊕ N d)
    (s : ∀ d, O d ↪ J d) (A : ∀ d, (O d → ℝ) ≃L[ℝ] (O d → ℝ))
    (F : ∀ d, (UnselectedColumn (s d) → ℝ) →L[ℝ] (O d → ℝ))
    (sets : ∀ d, O d → Finset α) (extra : G → Option α → Z)
    (c w : ∀ d, J d ⊕ N d → ℝ) (z : W → Z → ℝ)
    (hz : ∀ j, Measurable (fun a => z a j))
    (hw : ∀ d j, 0 < w d j) (R : D → ℝ≥0) (hsupport : ∀ d j, |c d j|+w d j ≤ R d)
    (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (δ : D → ℝ≥0) (hδ : ∀ d, 0 < δ d) (hwidth : ∀ d j, (δ d : ℝ) ≤ w d j)
    (Cap Lip : ℝ≥0) (hCap : 1 ≤ Cap)
    (hcap : ∀ d, pivotKernelCap (UnselectedColumn (s d)) (A d) (R d)
      ((t*δ d)⁻¹^Fintype.card (J d)) ≤ Cap)
    (hlip : ∀ d, pivotKernelLip (UnselectedColumn (s d)) (A d) (R d)
      (affineProductProfileLip (J d) (t*δ d)) ≤ Lip)
    (degree : D → ℕ) (hd : ∀ d n, (eN d n).sum (fun _ k => k) ≤ degree d)
    (Ro : ℝ≥0) (hRo : ∀ d, normalizedJetOutputRadius α (N d) (A d) (F d)
      (degree d) (R d) (R d) ≤ Ro)
    (η : ℝ≥0) (hη : 0 < η) {Csum Wsum Ri : ℝ} (hRi : 0 ≤ Ri) (hRiRo : Ri+η ≤ Ro)
    (hcsum : ∀ d, (∑ b, (|c d (index d b)|+|w d (index d b)|)) ≤ Csum)
    (hwsum : ∀ d, (∑ j, (|c d j|+|w d j|)) ≤ Wsum)
    (hideal : ∀ d o, Wsum+(2 : ℝ)^(sets d o).card*(Csum*((Fintype.card α : ℝ)+1)^h d) ≤ Ri)
    (μ : Measure W) [IsProbabilityMeasure μ] (hzbox : ∀ᵐ a ∂μ, ∀ j, |z a j| ≤ 1) {ε : ℝ}
    (he : (∫ p : W × ((Σ d, O d) → ℝ),
      |averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η p.2 -
        smallAffineMixtureDensity h eK eN s A F sets extra c w t z p.1 p.2| ∂μ.prod volume) ≤ ε)
    (a S : (Σ d, O d) → ℝ) (hS : ∀ j, 0 < S j) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ j, 1/S j ≤ mesh)
    (grid : Finset ((Σ d, O d) → ℤ)) (mask : W → ((Σ d, O d) → ℤ) → ℝ)
    (φ : W → ((Σ d, O d) → ℤ) → ℂ)
    (hM : 0 ≤ M) (hmask : ∀ w k, k ∈ grid → |mask w k| ≤ M)
    (hφ : ∀ w k, k ∈ grid → ‖φ w k‖ ≤ 1) :
    let f := averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η
    let g := smallAffineMixtureDensity h eK eN s A F sets extra c w t z
    ‖∫ w, gridDensityTest f a S grid (mask w) (φ w)-gridDensityTest (g w) a S grid (mask w) (φ w) ∂μ‖ ≤
      M*(ε+(2*(Ro : ℝ)+2)^Fintype.card (Σ d, O d)*
        ((affineProductProfileLip (Σ d, O d) η : ℝ)+(Fintype.card D*Lip*Cap^Fintype.card D : ℝ≥0))*mesh) := by
  dsimp only
  obtain ⟨hi, hgood⟩ := averagedAffine_density_data h eK eN index s A F sets extra c w z hz hw R hsupport
    t ht ht1 δ hδ hwidth Cap Lip hCap hcap hlip degree hd Ro hRo η hη hRi hRiRo
    hcsum hwsum hideal μ hzbox
  simpa only [probReal_univ, one_mul] using
    partial_gridDensityTest_error_ae μ
      (fun _ => averagedRegularizedIdeal h (fun d => Sum.elim (eK d) (eN d)) index c w sets η)
      (smallAffineMixtureDensity h eK eN s A F sets extra c w t z)
      a S hS Ro.coe_nonneg hmesh0 hmesh1 hmesh hgood grid mask φ hM hmask hφ hi he

end Erdos3

end

end OAI
