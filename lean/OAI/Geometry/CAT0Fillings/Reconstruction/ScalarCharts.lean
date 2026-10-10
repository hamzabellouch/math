import Mathlib
import OAI.Geometry.CAT0Fillings.Slices.WeakApproximation

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations

noncomputable def reindexFactor {k : ℕ} (ρ : Fin k → Fin k) : ℝ :=
  (Matrix.of fun i j => if ρ i = j then (1:ℝ) else 0).det

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma jacobian_reindex (π : Fin k → X → ℝ) (ρ : Fin k → Fin k) (z : Euc k) :
    C.jacobian (π ∘ ρ) z = reindexFactor ρ * C.jacobian π z := by
  classical
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j =>
    fderivWithin ℝ (C.scalar (π i)) C.domain z (EuclideanSpace.single j 1)
  let R : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun i j => if ρ i = j then 1 else 0
  have he : M.submatrix ρ id = R*M := by
    ext i j
    simp [M,R,Matrix.mul_apply]
  change (M.submatrix ρ id).det = R.det*M.det
  rw [he,Matrix.det_mul]

lemma action_reindex [MeasurableSpace X] {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (ρ : Fin k → Fin k) :
    C.action b (π ∘ ρ) = reindexFactor ρ * C.action b π := by
  have hρ : Admissible b (π ∘ ρ) := ⟨h.1,fun i => h.2 (ρ i)⟩
  simp only [action,ite_eq_left h,ite_eq_left hρ,C.jacobian_reindex]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

end IntegerChart
namespace Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]

lemma IntegerRectifiable.apply_reindex {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (h : Admissible b π) (ρ : Fin k → Fin k) :
    T b (π ∘ ρ) = reindexFactor ρ*T b π := by
  obtain ⟨C,_,_,_,hrep⟩ := hT
  rw [hrep,hrep,←tsum_mul_left]
  exact tsum_congr fun j => (C j).action_reindex h ρ

end Foundations
namespace Slicing
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma NormalApprox.apply_reindex {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (ρ : Fin k → Fin k) :
    T b (π ∘ ρ) = reindexFactor ρ*T b π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hl := hlim b (π ∘ ρ)
  have hr := (hlim b π).const_mul (reindexFactor ρ)
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_reindex (hrect j) hab ρ
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

end Slicing
namespace BorelCoefficients
open MassMeasure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma borelAction_reindex {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    {π : Fin k → X → ℝ} (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (ρ : Fin k → Fin k) (hρ : ∀ b, BoundedLip b → T b (π ∘ ρ) = reindexFactor ρ*T b π)
    {f : X → ℝ} (hf : Integrable f μ) :
    borelAction μ hT f (π ∘ ρ) = reindexFactor ρ*borelAction μ hT f π := by
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have hl := borelAction_tendsto μ hT hμ hf
    (fun n => integrable_boundedLip μ (g n).property) hg (π ∘ ρ) (fun i => hπ (ρ i))
  have hr := (borelAction_tendsto μ hT hμ hf
    (fun n => integrable_boundedLip μ (g n).property) hg π hπ).const_mul (reindexFactor ρ)
  have he n : borelAction μ hT (g n).val (π ∘ ρ) =
      reindexFactor ρ*borelAction μ hT (g n).val π := by
    have had : Admissible (g n).val (π ∘ ρ) := ⟨(g n).property,fun i => hπ (ρ i)⟩
    rw [borelAction_eq μ hT hμ had,
      borelAction_eq μ hT hμ ⟨(g n).property,hπ⟩]
    exact hρ (g n).val (g n).property
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

end BorelCoefficients
namespace BorelRestriction
open MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma restrictCurrent_reindex {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {π : Fin k → X → ℝ} (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    (ρ : Fin k → Fin k) (hρ : ∀ b, BoundedLip b → T b (π ∘ ρ) = reindexFactor ρ*T b π)
    {E : Set X} (hE : MeasurableSet E) {b : X → ℝ} (hb : BoundedLip b) :
    restrictCurrent hT E b (π ∘ ρ) = reindexFactor ρ*restrictCurrent hT E b π := by
  have had : Admissible b (π ∘ ρ) := ⟨hb,fun i => hπ (ρ i)⟩
  rw [restrictCurrent_apply hT E had,
    restrictCurrent_apply hT E ⟨hb,hπ⟩]
  exact borelAction_reindex hT _ (currentMassMeasure_controls hT) hπ ρ hρ
    ((integrable_boundedLip _ hb).indicator hE)

end BorelRestriction
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.SliceReconstruction
open Foundations MassMeasure BorelCoefficients BorelRestriction

attribute [local instance] Classical.propDecidable

noncomputable def scalarEquiv : Euc 1 ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)

lemma scalarEquiv_apply (z : Euc 1) : scalarEquiv z = z 0 := rfl

lemma scalarEquiv_volume : MeasurePreserving scalarEquiv volume volume := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

variable {X : Type*} [MetricSpace X]

noncomputable def scalarGraphChart {D : Set ℝ} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ) : IntegerChart X 1 where
  domain := scalarEquiv ⁻¹' D
  borel := scalarEquiv.continuous.measurable hD.measurableSet
  bounded := by
    have he : scalarEquiv ⁻¹' D = scalarEquiv.symm '' D := (scalarEquiv.image_symm_eq_preimage D).symm
    rw [he]
    exact (hD.image scalarEquiv.symm.continuous).isBounded
  param := fun z => γ ⟨scalarEquiv z,z.property⟩
  bilipschitz := by
    obtain ⟨L,U,hL,hU⟩ := hγ
    refine ⟨L * ‖scalarEquiv.toContinuousLinearMap‖₊,
      ‖scalarEquiv.symm.toContinuousLinearMap‖₊*U,?_,?_⟩
    · have he : LipschitzWith ‖scalarEquiv.toContinuousLinearMap‖₊ (fun z : scalarEquiv ⁻¹' D => scalarEquiv z) := by
        apply LipschitzWith.of_dist_le_mul
        intro s t
        exact scalarEquiv.toContinuousLinearMap.lipschitzWith.dist_le_mul s t
      exact hL.comp (he.subtype_mk fun z => z.property)
    · apply AntilipschitzWith.of_le_mul_dist
      intro s t
      have he := scalarEquiv.symm.toContinuousLinearMap.lipschitzWith.dist_le_mul
        (scalarEquiv s) (scalarEquiv t)
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at he
      exact he.trans (by simpa only [NNReal.coe_mul,mul_assoc,Subtype.dist_eq,coe_nnnorm] using
        mul_le_mul_of_nonneg_left (hU.le_mul_dist ⟨scalarEquiv s,s.property⟩
          ⟨scalarEquiv t,t.property⟩) (norm_nonneg scalarEquiv.symm.toContinuousLinearMap))
  multiplicity := fun _ => a
  integrable := by
    have he : scalarEquiv ⁻¹' D = scalarEquiv.symm '' D := (scalarEquiv.image_symm_eq_preimage D).symm
    have hfin := (hD.image scalarEquiv.symm.continuous).measure_lt_top (μ := volume)
    rw [←he] at hfin
    exact integrableOn_const (C := (a : ℝ)) hfin.ne

lemma scalarGraphChart_image {D : Set ℝ} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ) :
    (scalarGraphChart hD γ hγ a).image = Set.range γ := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨⟨scalarEquiv z,z.property⟩,rfl⟩
  · rintro ⟨t,rfl⟩
    refine ⟨⟨scalarEquiv.symm t,by change scalarEquiv (scalarEquiv.symm t) ∈ D; simpa only [ContinuousLinearEquiv.apply_symm_apply] using t.property⟩,?_⟩
    change γ ⟨scalarEquiv (scalarEquiv.symm t),_⟩ = γ t
    congr 1

lemma scalarGraphChart_base_jacobian {D : Set ℝ} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (hbase : ∀ t : D, u (γ t) = t) :
    ∀ᵐ z ∂volume.restrict (scalarGraphChart hD γ hγ a).domain,
      (scalarGraphChart hD γ hγ a).jacobian (fun _ : Fin 1 => u) z = 1 := by
  let C := scalarGraphChart hD γ hγ a
  have he := C.ae_fderivWithin_scalar_eq_linear C.borel (subset_refl _) hu
    scalarEquiv.toContinuousLinearMap (by
      intro z hz
      rw [C.scalar_eq hz]
      exact hbase ⟨scalarEquiv z,hz⟩)
  filter_upwards [he] with z hz
  change C.jacobian (fun _ : Fin 1 => u) z = 1
  change (Matrix.of fun i j : Fin 1 => (fderivWithin ℝ (C.scalar u) C.domain z) (EuclideanSpace.single j 1)).det = 1
  rw [Matrix.det_fin_one,hz]
  rfl

noncomputable def scalarGraphFunction {D : Set ℝ} (γ : D → X) (b : X → ℝ) (t : ℝ) : ℝ :=
  if ht : t ∈ D then b (γ ⟨t,ht⟩) else 0

lemma scalarGraphChart_base_action [MeasurableSpace X] [BorelSpace X]
    {D : Set ℝ} (hD : IsCompact D) (γ : D → X)
    (hγ : ∃ L U : ℝ≥0, LipschitzWith L γ ∧ AntilipschitzWith U γ) (a : ℤ)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) (hbase : ∀ t : D, u (γ t) = t)
    {b : X → ℝ} (hb : BoundedLip b) :
    (scalarGraphChart hD γ hγ a).action b (fun _ : Fin 1 => u) =
      ∫ t in D, (a : ℝ)*scalarGraphFunction γ b t := by
  let C := scalarGraphChart hD γ hγ a
  rw [IntegerChart.action,ite_eq_left ⟨hb,fun _ => ⟨K,hu⟩⟩]
  have he : (∫ z in C.domain, (C.multiplicity z : ℝ)*C.scalar b z*C.jacobian (fun _ => u) z) =
      ∫ z in C.domain, (a : ℝ)*scalarGraphFunction γ b (scalarEquiv z) := by
    apply integral_congr_ae
    filter_upwards [scalarGraphChart_base_jacobian hD γ hγ a hu hbase,ae_restrict_mem C.borel]
      with z hj hz
    rw [hj,mul_one,C.scalar_eq hz]
    have hzd : scalarEquiv z ∈ D := hz
    simp only [scalarGraphFunction,dite_eq_left hzd]
    rfl
  exact he.trans (scalarEquiv_volume.setIntegral_preimage_emb
    scalarEquiv.toHomeomorph.measurableEmbedding (fun t => (a : ℝ)*scalarGraphFunction γ b t) D)

end CAT0Fillings.SliceReconstruction
end

end OAI
