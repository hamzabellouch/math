import OAI.Combinatorics.Progressions.Estimates.WeightedCoefficientSplit

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators

theorem coefficientProductDensity_site_image_le {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [∀ j, MeasurableSpace (SubspaceArrayTorus Unit (U j))]
    [∀ j, BorelSpace (SubspaceArrayTorus Unit (U j))]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ s : CoefficientSlot K m, Measure (SubspaceArrayTorus Unit (U s.1)))
    [∀ s, (ν s).IsAddLeftInvariant] [∀ s, IsProbabilityMeasure (ν s)]
    (f : ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1) → ℝ)
    (hf : ∀ s, Measurable (f s)) (hfi : ∀ s, Integrable (f s) (ν s))
    (hf0 : ∀ s x, 0 ≤ f s x) (hmass : ∀ s, (∫ x, f s x ∂ν s) = 1)
    (C : Fin m → ℝ) (hC : ∀ j x, f (constantCoefficientSlotEquiv K m j).val x ≤ C j)
    (t : K → ℤ) :
    (realDensityMeasure μ (coefficientProductDensity U f)).map
      (coefficientSiteTorusMap U (fun _ : Unit => t)) ≤
      ENNReal.ofReal (∏ j, C j) • Measure.pi (fun j => ν (constantCoefficientSlotEquiv K m j).val) := by
  let _ : ∀ s, SigmaFinite (ν s) := fun s => inferInstance
  let _ : ∀ j, SigmaFinite (ν (constantCoefficientSlotEquiv K m j).val) := fun j => inferInstance
  let _ : ∀ j, IsProbabilityMeasure (ν (constantCoefficientSlotEquiv K m j).val) := fun j => inferInstance
  let _ : ∀ j, (ν (constantCoefficientSlotEquiv K m j).val).IsAddLeftInvariant := fun j => inferInstance
  let ν₀ : ∀ j : Fin m, Measure (SubspaceArrayTorus Unit (U j)) :=
    fun j => ν (constantCoefficientSlotEquiv K m j).val
  let _ : ∀ j, SigmaFinite (ν₀ j) := fun j => inferInstanceAs (SigmaFinite (ν (constantCoefficientSlotEquiv K m j).val))
  let _ : ∀ j, IsProbabilityMeasure (ν₀ j) := fun j => inferInstanceAs (IsProbabilityMeasure (ν (constantCoefficientSlotEquiv K m j).val))
  let _ : ∀ j, (ν₀ j).IsAddLeftInvariant := fun j => inferInstanceAs ((ν (constantCoefficientSlotEquiv K m j).val).IsAddLeftInvariant)
  let μ₀ : Measure (SiteTorus Unit U) := Measure.pi ν₀
  let ω := Measure.pi (fun s : NonconstantCoefficientSlot K m => realDensityMeasure (ν s.val) (f s.val))
  let f₀ : ∀ j : Fin m, SubspaceArrayTorus Unit (U j) → ℝ :=
    fun j x => f (constantCoefficientSlotEquiv K m j).val x
  let F : SiteTorus Unit U → ℝ := fun c => ∏ j, f₀ j (c j)
  let z : NonconstantCoordinateTori (K := K) U → SiteTorus Unit U :=
    fun r => coordinateSiteValue U t (nonconstantCoordinateExtension U r)
  let g : NonconstantCoordinateTori (K := K) U × SiteTorus Unit U → SiteTorus Unit U :=
    fun p => p.2 + z p.1
  let _ : ∀ s, IsProbabilityMeasure (realDensityMeasure (ν s) (f s)) :=
    fun s => realDensityMeasure_probability (ν s) (f s) (hfi s) (hf0 s) (hmass s)
  let _ : ∀ s : NonconstantCoefficientSlot K m,
      IsProbabilityMeasure (realDensityMeasure (ν s.val) (f s.val)) := fun s => inferInstance
  have hz : Measurable z :=
    ((coordinateSiteValue_continuous U t).comp (nonconstantCoordinateExtension_continuous U)).measurable
  have hg : Measurable g := measurable_snd.add (hz.comp measurable_fst)
  have hF : Measurable F := Finset.measurable_prod _ (fun j _ => (hf _).comp (measurable_pi_apply j))
  have hFi : Integrable F μ₀ := Integrable.fintype_prod_dep
    (E := fun j : Fin m => SubspaceArrayTorus Unit (U j))
    (μ := ν₀)
    (f := f₀)
    (fun j => hfi (constantCoefficientSlotEquiv K m j).val)
  have hFm : (∫ c, F c ∂μ₀) = 1 := by
    calc
      _ = ∏ j, ∫ x, f₀ j x ∂ν₀ j := integral_fintype_prod_eq_prod f₀
      _ = 1 := by
        apply Finset.prod_eq_one
        intro j _
        exact hmass (constantCoefficientSlotEquiv K m j).val
  have hFc (c) : F c ∈ Set.Icc (0 : ℝ) (∏ j, C j) :=
    ⟨Finset.prod_nonneg (fun j _ => hf0 _ _),
      Finset.prod_le_prod₀ (fun j _ => hf0 _ _) (fun j _ => hC j (c j))⟩
  have hs : Measurable (coefficientCoordinateSplit U ∘ coefficientCoordinateTorus U) :=
    (coefficientCoordinateSplit_measurePreserving U ν).measurable.comp
      (coefficientCoordinateTorus_continuous U).measurable
  have he : (fun x => coefficientSiteTorusMap U (fun _ : Unit => t) x) =
      g ∘ (coefficientCoordinateSplit U ∘ coefficientCoordinateTorus U) := by
    funext x
    rw [← coordinateSiteValue_coefficientCoordinates, coordinateSiteValue_split]
    rfl
  have hpush : (realDensityMeasure μ (coefficientProductDensity U f)).map
      (coefficientSiteTorusMap U (fun _ : Unit => t)) = (ω.prod (realDensityMeasure μ₀ F)).map g := by
    calc
      _ = ((realDensityMeasure μ (coefficientProductDensity U f)).map
          (coefficientCoordinateSplit U ∘ coefficientCoordinateTorus U)).map g := by
        rw [Measure.map_map hg hs]
        exact congrArg (fun k => (realDensityMeasure μ (coefficientProductDensity U f)).map k) he
      _ = (ω.prod (realDensityMeasure μ₀ F)).map g := congrArg (Measure.map g)
        (coefficientProductDensity_split_law U μ ν f hf hfi hf0 hmass)
  rw [hpush]
  exact haarShiftDensity_image_le μ₀ ω hz hF hFi hFc hFm

end Erdos3.VectorPolynomial

end

end OAI
