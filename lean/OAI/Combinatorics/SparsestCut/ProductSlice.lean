import OAI.Combinatorics.SparsestCut.SliceCoefficients

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {K : Type u3} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

def form (B : Z →L[ℝ] ℝ) : (ℝ × Z) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ Z-B.comp (ContinuousLinearMap.snd ℝ ℝ Z)
omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
@[simp] lemma form_apply (B : Z →L[ℝ] ℝ) (x : ℝ × Z) : form B x=x.1-B x.2 := rfl

def cell (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → ℝ) (x : ℝ × Z) : ℝ :=
  F (Finset.univ.filter (fun p => form (B p.1) x+q p.1 p.2<0))
omit [(volume : Measure Z).IsAddHaarMeasure] in
lemma cell_measurable (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → ℝ) :
    Measurable (cell B q F) := by
  unfold cell
  apply InterfaceStep.measurable_filter_apply
  intro p
  exact measurableSet_lt ((form (B p.1)).measurable.add_const (q p.1 p.2)) measurable_const

omit [(volume : Measure Z).IsAddHaarMeasure] in
lemma cell_locallyIntegrable (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ)
    (F : Finset (I × K) → ℝ) {M : ℝ} (hM : ∀ a, |F a|≤M)
    (ν : Measure (ℝ × Z)) [IsLocallyFiniteMeasure ν] : LocallyIntegrable (cell B q F) ν := by
  apply (continuous_const (y := M)).locallyIntegrable.mono (cell_measurable B q F).aestronglyMeasurable
  filter_upwards with x
  exact (show |cell B q F x|≤M from hM _).trans (le_abs_self M)

omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [DecidableEq I] [DecidableEq K] in
lemma cell_translate (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ)
    (F : Finset (I × K) → ℝ) (θ : ℝ × Z) (x : ℝ) (z : Z) :
    cell B q F (θ-(x,z)) =
      F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2<x)) := by
  unfold cell
  congr 1
  apply Finset.filter_congr
  intro p _
  change (θ.1-x-B p.1 (θ.2-z)+q p.1 p.2<0) ↔
    (θ.1-B p.1 θ.2+B p.1 z+q p.1 p.2<x)
  rw [map_sub]
  constructor <;> intro hp <;> linarith

def law (ψ : Z → ℝ) (ν : Measure Z) : Measure Z := ν.withDensity (fun z => ENNReal.ofReal (ψ z))
omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
lemma law_ac (ψ : Z → ℝ) (ν : Measure Z) : law ψ ν ≪ ν := withDensity_absolutelyContinuous _ _
omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
lemma law_integral {ψ : Z → ℝ} (hm : Measurable ψ) (hn : ∀ z, 0≤ψ z)
    (ν : Measure Z) (f : Z → ℝ) :
    (∫ z, f z ∂law ψ ν) = ∫ z, ψ z*f z ∂ν := by
  rw [law,integral_withDensity_eq_integral_toReal_smul (hm.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
lemma law_probability {ψ : Z → ℝ} (_hm : Measurable ψ) (hn : ∀ z, 0≤ψ z)
    (ν : Measure Z) (hi : Integrable ψ ν) (h1 : ∫ z, ψ z ∂ν=1) :
    IsProbabilityMeasure (law ψ ν) := by
  refine ⟨?_⟩
  change (ν.withDensity (fun z => ENNReal.ofReal (ψ z))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn),h1]
  simp

lemma convolution_slice (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ)
    (F : Finset (I × K) → ℝ) {M : ℝ} (_hM0 : 0 ≤ M) (hM : ∀ a, |F a| ≤ M)
    {φ : ℝ → ℝ} {ψ : Z → ℝ} (hmφ : Measurable φ) (hmψ : Measurable ψ)
    (hφ : Integrable φ) (hψ : Integrable ψ) (hnψ : ∀ z, 0≤ψ z) (θ : ℝ × Z) :
    convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell B q F)
        (ContinuousLinearMap.mul ℝ ℝ) volume θ =
      ∫ z, (∫ x, φ x*F (Finset.univ.filter
        (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2<x))) ∂law ψ volume := by
  have hi : Integrable (fun p : ℝ × Z => (φ p.1*ψ p.2)*cell B q F (θ-p)) := by
    apply (((hφ.abs).mul_prod hψ.abs).mul_const M).mono'
      (((hmφ.comp measurable_fst).mul (hmψ.comp measurable_snd)).mul
        ((cell_measurable B q F).comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    filter_upwards with p
    change |φ p.1*ψ p.2*cell B q F (θ-p)| ≤ |φ p.1| * |ψ p.2| * M
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  change (∫ p : ℝ × Z, (φ p.1*ψ p.2)*cell B q F (θ-p) ∂(volume : Measure ℝ).prod (volume : Measure Z)) = _
  rw [integral_prod_symm _ hi,law_integral hmψ hnψ]
  apply integral_congr_ae
  filter_upwards with z
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [cell_translate]
  ring

lemma convolution_derivative (B : I → Z →L[ℝ] ℝ) (hB : Function.Injective B)
    (q : I → K → ℝ) (hq : ∀ i, Function.Injective (q i))
    (F : Finset (I × K) → ℝ) {M C : ℝ} (hM0 : 0≤M) (hC : 0≤C)
    (hM : ∀ a, |F a|≤M) {φ : ℝ → ℝ} {ψ : Z → ℝ}
    (hφ : Integrable φ) (hcφ : Continuous φ) (hφC : ∀ t, |φ t|≤C)
    (hmψ : Measurable ψ) (hnψ : ∀ z, 0≤ψ z) (hψ : Integrable ψ) (hψ1 : ∫ z, ψ z=1)
    (θ : ℝ × Z) :
    HasFDerivAt (convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell B q F)
      (ContinuousLinearMap.mul ℝ ℝ) volume)
      (∑ i, (∑ k, ∫ z, -(φ (form (B i) θ+B i z+q i k)*
        (F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 ≤ form (B i) θ+B i z+q i k))-
          F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 < form (B i) θ+B i z+q i k))))
        ∂law ψ volume) • form (B i)) θ := by
  let := law_probability hmψ hnψ volume hψ hψ1
  have he : convolution (fun p : ℝ × Z => φ p.1*ψ p.2) (cell B q F)
      (ContinuousLinearMap.mul ℝ ℝ) volume =
      (fun θ => ∫ z, (∫ x, φ x*F (Finset.univ.filter
        (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2<x))) ∂law ψ volume) :=
    funext (convolution_slice B q F hM0 hM hcφ.measurable hmψ hφ hψ hnψ)
  rw [he]
  have hi : ∀ᵐ z ∂law ψ volume, Function.Injective
      (fun p : I × K => form (B p.1) θ+(B p.1 z+q p.1 p.2)) := by
    simpa only [add_assoc] using SliceCoefficients.thresholds_injective_ae
      (fun i => form (B i)) B q hq hB volume (law ψ volume) (law_ac ψ volume) θ
  simpa only [add_assoc] using SliceCoefficients.family_derivative (fun i => form (B i))
    (fun p z => B p.1 z+q p.1 p.2) (fun p => (B p.1).measurable.add_const _) F
    hφ hcφ hM0 hC hM hφC (law ψ volume) θ hi
end
end UniformSparsestCut.ProductSlice

end

end OAI
