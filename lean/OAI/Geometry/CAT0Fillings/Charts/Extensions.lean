import Mathlib
import OAI.Geometry.CAT0Fillings.Charts.Differentiability
import OAI.Geometry.CAT0Fillings.Charts.Jacobian
import OAI.Geometry.CAT0Fillings.Charts.Scalar

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
  {k : ℕ} (C : IntegerChart X k)
noncomputable def paramExtended : Euc k → X :=
  by classical exact fun z => if hz : z ∈ C.domain then C.param ⟨z,hz⟩ else Classical.arbitrary X

lemma measurable_paramExtended : Measurable C.paramExtended := by
  classical
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  exact hL.continuous.measurable.dite measurable_const C.borel

omit [MeasurableSpace X] [BorelSpace X] in
lemma scalar_ae_paramExtended (b : X → ℝ) :
    C.scalar b =ᵐ[volume.restrict C.domain] b ∘ C.paramExtended := by
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simp only [scalar,paramExtended,Function.comp_apply,dite_eq_left hz]

variable [CompactSpace X]

omit [Nonempty X] in
lemma measurableEmbedding_param : MeasurableEmbedding C.param := by
  let := C.borel.standardBorel
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  exact hL.continuous.measurable.measurableEmbedding hU.injective

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] [CompactSpace X] in
lemma integrable_weighted_jacobian {π : Fin k → X → ℝ}
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    Integrable (fun z => (C.multiplicity z : ℝ)*C.jacobian π z)
      (volume.restrict C.domain) := by
  obtain ⟨B,hB⟩ := C.exists_jacobian_bound hπ
  exact C.integrable.mul_bdd (C.jacobian_aestronglyMeasurable hπ) hB

lemma weighted_jacobian_le_measure
    (hC : IsMetricCurrent C.action) {ν : Measure X} [IsFiniteMeasure ν]
    (hν : Controls C.action ν) (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hK : ∀ i, LipschitzWith (K i) (π i)) :
    densityPush (volume.restrict C.domain) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) ≤ (∏ i, K i) • ν := by
  have he : MeasurableEmbedding (fun z : C.domain => C.paramExtended (z : Euc k)) := by
    convert C.measurableEmbedding_param using 1
    funext z
    simp [paramExtended,z.property]
  apply signed_chart_control_dominates_on (volume.restrict C.domain) ((∏ i,K i) • ν)
    C.measurable_paramExtended (ae_restrict_mem C.borel) he
    (C.integrable_weighted_jacobian (fun i => ⟨K i,hK i⟩))
  intro b hb
  have heq : (∫ z, (C.multiplicity z : ℝ)*C.jacobian π z*b (C.paramExtended z)
      ∂volume.restrict C.domain) = C.action b π := by
    rw [action,ite_eq_left ⟨hb,fun i => ⟨K i,hK i⟩⟩]
    apply integral_congr_ae
    filter_upwards [C.scalar_ae_paramExtended b] with z hz
    dsimp only [Function.comp_apply] at hz
    rw [hz]
    ring
  rw [heq,integral_smul_nnreal_measure]
  simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul] using hC.mass_bound hν hb K hK

end IntegerChart

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma ae_fderivWithin_scalar_eq_linear {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (ℓ : Euc k →L[ℝ] ℝ)
    (heq : ∀ z ∈ t, C.scalar f z = ℓ z) :
    ∀ᵐ z ∂volume.restrict t, fderivWithin ℝ (C.scalar f) C.domain z = ℓ := by
  have hd := (C.ae_differentiableWithinAt_scalar hf).filter_mono
    (ae_mono (Measure.restrict_mono hts le_rfl))
  filter_upwards [hd,ae_uniqueDiffWithinAt volume t,ae_restrict_mem ht] with z hz hu hzt
  rw [←fderivWithin_subset hts hu hz,fderivWithin_congr' heq hzt,ℓ.fderivWithin hu]

lemma exists_inverse_coordinate_tests {t : Set (Euc k)}
    (ht : MeasurableSet t) (hts : t ⊆ C.domain)
    (ℓ : Fin k → Euc k →L[ℝ] ℝ) (K : ℝ≥0)
    (hrow : ∀ i y (hy : y ∈ t) z (hz : z ∈ t),
      |ℓ i y - ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hts hy⟩) (C.param ⟨z,hts hz⟩)) :
    ∃ π : Fin k → X → ℝ, (∀ i, LipschitzWith K (π i)) ∧
      (∀ i, ∀ z ∈ t, C.scalar (π i) z = ℓ i z) ∧
      ∀ᵐ z ∂volume.restrict t,
        C.jacobian π z = (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)).det := by
  classical
  by_cases hne : t.Nonempty
  · let := hne.to_subtype
    let φ : t → X := fun z => C.param ⟨z,hts z.property⟩
    have hinj : Function.Injective φ := by
      obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z : C.domain => (z : Euc k)) (hU.injective hab)
    let q : Fin k → X → ℝ := fun i x => ℓ i ((Function.invFun φ x : t) : Euc k)
    have hq (i : Fin k) : LipschitzOnWith K (q i) (Set.range φ) := by
      apply lipschitzOnWith_iff_dist_le_mul.mpr
      rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
      simpa only [q,Function.leftInverse_invFun hinj a,
        Function.leftInverse_invFun hinj b,Real.dist_eq] using
        hrow i a a.property b b.property
    choose π hπ heq using fun i => (hq i).extend_real
    have hagree (i : Fin k) (z : Euc k) (hz : z ∈ t) : C.scalar (π i) z = ℓ i z := by
      rw [C.scalar_eq (hts hz)]
      change π i (φ ⟨z,hz⟩) = _
      rw [←heq i (Set.mem_range_self (⟨z,hz⟩ : t))]
      dsimp only [q]
      rw [Function.leftInverse_invFun hinj]
    refine ⟨π,hπ,hagree,?_⟩
    have hae : ∀ᵐ z ∂volume.restrict t, ∀ i,
        fderivWithin ℝ (C.scalar (π i)) C.domain z = ℓ i :=
      ae_all_iff.mpr fun i => C.ae_fderivWithin_scalar_eq_linear ht hts (hπ i) (ℓ i) (hagree i)
    filter_upwards [hae] with z hz
    simp only [jacobian,hz]
    rfl
  · have ht0 : t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst t
    exact ⟨fun _ _ => 0,fun _ => LipschitzWith.const' (0 : ℝ),by simp,by simp⟩

end IntegerChart
end CAT0Fillings

end

end OAI
