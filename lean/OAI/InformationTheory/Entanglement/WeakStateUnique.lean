import OAI.InformationTheory.Entanglement.WeakStateSupport
import OAI.InformationTheory.Entanglement.PhysicalConditionalUpdate

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder MeasureTheory
open ContinuousLinearMap MeasureTheory Filter
namespace SecretKey
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι X : Type*} [MeasurableSpace X]
omit [CompleteSpace H] in
lemma hilbertBasis_operator_ext (b : HilbertBasis ι ℂ H) {A B : H→L[ℂ]H}
    (h : ∀ i j, inner ℂ (b i) (A (b j))=inner ℂ (b i) (B (b j))) : A=B := by
  have hc (j : ι) : A (b j)=B (b j) := by
    apply b.repr.injective
    ext i
    simpa only [b.repr_apply_apply] using h i j
  ext x
  have ha := (b.hasSum_repr x).mapL A
  have hb := (b.hasSum_repr x).mapL B
  have he : (fun i => A (b.repr x i • b i))=(fun i => B (b.repr x i • b i)) := by
    funext i
    rw [map_smul,map_smul,hc]
  rw [he] at ha
  exact ha.unique hb

theorem weak_density_ae_unique (b : HilbertBasis ι ℂ H) (μ : Measure X) [IsProbabilityMeasure μ]
    (ρ σ : X→DensityOperator b) (T : DensityOperator b)
    (hρ : ∀ x y, Measurable (fun z => inner ℂ x ((ρ z).val.val y)))
    (hσ : ∀ x y, Measurable (fun z => inner ℂ x ((σ z).val.val y)))
    (hmean : ∀ x y, inner ℂ x (T.val.val y)=∫ z, inner ℂ x ((ρ z).val.val y) ∂μ)
    (hsets : ∀ s, MeasurableSet s → ∀ x y,
      ∫ z in s, inner ℂ x ((ρ z).val.val y) ∂μ=∫ z in s, inner ℂ x ((σ z).val.val y) ∂μ) :
    ρ=ᵐ[μ]σ := by
  have hmean' (x y : H) : inner ℂ x (T.val.val y)=∫ z, inner ℂ x ((σ z).val.val y) ∂μ := by
    rw [hmean]
    simpa only [Measure.restrict_univ] using hsets Set.univ MeasurableSet.univ x y
  obtain ⟨hc,hface⟩ := weak_density_countable_support b μ ρ T hρ hmean
  obtain ⟨_,hspace⟩ := weak_density_countable_support b μ σ T hσ hmean'
  let s := Function.support (densityDiag b T)
  let : Countable s := hc.to_subtype
  have hcoeff (i j : s) : (fun z => inner ℂ (b i) ((ρ z).val.val (b j)))=ᵐ[μ]
      (fun z => inner ℂ (b i) ((σ z).val.val (b j))) := by
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    · intro a ha hfin
      exact (density_coefficient_integrable b μ ρ hρ (b i) (b j)).integrableOn
    · intro a ha hfin
      exact (density_coefficient_integrable b μ σ hσ (b i) (b j)).integrableOn
    · intro a ha hfin
      exact hsets a ha (b i) (b j)
  have hall : ∀ᵐ z ∂μ, ∀ i j : s,
      inner ℂ (b i) ((ρ z).val.val (b j))=inner ℂ (b i) ((σ z).val.val (b j)) :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hcoeff i))
  filter_upwards [hface,hspace,hall] with z hz hz' hzc
  apply Subtype.ext
  apply Subtype.ext
  apply hilbertBasis_operator_ext b
  intro i j
  by_cases hj : j∈s
  · by_cases hi : i∈s
    · exact hzc ⟨i,hi⟩ ⟨j,hj⟩
    · have hA := (nonneg_iff_isPositive.mp (ρ z).property.1).isSymmetric
      have hB := (nonneg_iff_isPositive.mp (σ z).property.1).isSymmetric
      erw [← hA (b i) (b j),← hB (b i) (b j),hz i hi,hz' i hi]
  · rw [hz j hj,hz' j hj]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {κ : Type*}
namespace TraceInstrument.ConditionalUpdate
variable {b : HilbertBasis ι ℂ H} {c : HilbertBasis κ ℂ K}
variable {I : TraceInstrument b c X} {ρ : DensityOperator b}

omit [CompleteSpace H] in
theorem ae_unique (U V : I.ConditionalUpdate ρ) : U.state=ᵐ[I.outcome ρ]V.state := by
  let T : DensityOperator c := ⟨I.event Set.univ ρ.val,
    cp_trace_positive b c (I.event_cp Set.univ MeasurableSet.univ) ρ.property.1,by
      rw [I.trace_preserving,ρ.property.2]⟩
  apply weak_density_ae_unique c (I.outcome ρ) U.state V.state T
    U.coefficient_measurable V.coefficient_measurable
  · intro x y
    simpa only [Measure.restrict_univ] using U.disintegration Set.univ MeasurableSet.univ x y
  · intro s hs x y
    rw [← U.disintegration s hs x y,← V.disintegration s hs x y]
end TraceInstrument.ConditionalUpdate

end SecretKey

end

end OAI
