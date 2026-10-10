import OAI.Analysis.KadisonKastler.L2MeasurableRestriction

namespace OAI

/-! # Extension by zero from a measurable L² stratum -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H]
  (μ : Measure X) (s : Set X) (hs : MeasurableSet s)

def l2ExtensionFunction (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) (x : X) : H := by
  classical
  exact if hx : x ∈ s then f ⟨x, hx⟩ else 0

@[simp] theorem l2ExtensionFunction_coe
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) (x : s) :
    l2ExtensionFunction μ s f x.val = f x := by
  simp [l2ExtensionFunction, x.property]

 theorem indicator_l2ExtensionFunction
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    s.indicator (l2ExtensionFunction μ s f) = l2ExtensionFunction μ s f := by
  classical
  funext x
  by_cases hx : x ∈ s <;> simp [l2ExtensionFunction, hx]

include hs in
 theorem l2ExtensionMemLp (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    MemLp (l2ExtensionFunction μ s f) 2 μ := by
  have hm : MemLp (l2ExtensionFunction μ s f) 2 (μ.restrict s) := by
    rw [← map_comap_subtype_coe hs]
    apply (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff.mpr
    simpa only [Function.comp_def, l2ExtensionFunction_coe] using Lp.memLp f
  have hi := (memLp_indicator_iff_restrict hs).mpr hm
  rw [indicator_l2ExtensionFunction] at hi
  exact hi

def l2Extend (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) : Lp H 2 μ :=
  (l2ExtensionMemLp μ s hs f).toLp (l2ExtensionFunction μ s f)

 theorem l2Extend_apply_ae (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Extend μ s hs f =ᵐ[μ] l2ExtensionFunction μ s f :=
  MemLp.coeFn_toLp (l2ExtensionMemLp μ s hs f)

 theorem l2Extend_norm (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    ‖l2Extend μ s hs f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (l2Extend_apply_ae μ s hs f)]
  congr 1
  calc
    _ = eLpNorm (s.indicator (l2ExtensionFunction μ s f)) 2 μ := by
      rw [indicator_l2ExtensionFunction]
    _ = eLpNorm (l2ExtensionFunction μ s f) 2 (μ.restrict s) :=
      eLpNorm_indicator_eq_eLpNorm_restrict hs
    _ = eLpNorm ((l2ExtensionFunction μ s f) ∘ ((↑) : s → X)) 2
        (Measure.comap ((↑) : s → X) μ) := by
      rw [← map_comap_subtype_coe hs]
      exact (MeasurableEmbedding.subtype_coe hs).eLpNorm_map_measure
    _ = eLpNorm f 2 (Measure.comap ((↑) : s → X) μ) := by
      congr 1
      funext x
      exact l2ExtensionFunction_coe μ s f x

include hs in
theorem ae_of_subtype_of_outside {p : X → Prop}
    (hin : ∀ᵐ x : s ∂Measure.comap ((↑) : s → X) μ, p x.val)
    (hout : ∀ x, x ∉ s → p x) : ∀ᵐ x ∂μ, p x := by
  have hi := (ae_restrict_iff' hs).mp ((ae_restrict_iff_subtype hs).mpr hin)
  filter_upwards [hi] with x hx
  by_cases hxs : x ∈ s
  · exact hx hxs
  · exact hout x hxs

include hs in
theorem l2ExtensionFunction_add_ae
    (f g : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2ExtensionFunction μ s (f + g) =ᵐ[μ]
      fun x => l2ExtensionFunction μ s f x + l2ExtensionFunction μ s g x := by
  apply ae_of_subtype_of_outside μ s hs
  · filter_upwards [Lp.coeFn_add f g] with x hx
    simpa only [l2ExtensionFunction_coe, Pi.add_apply] using hx
  · intro x hx
    simp [l2ExtensionFunction, hx]

variable [NormedSpace ℂ H]

include hs in
theorem l2ExtensionFunction_smul_ae (c : ℂ)
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2ExtensionFunction μ s (c • f) =ᵐ[μ]
      fun x => c • l2ExtensionFunction μ s f x := by
  apply ae_of_subtype_of_outside μ s hs
  · filter_upwards [Lp.coeFn_smul c f] with x hx
    simpa only [l2ExtensionFunction_coe, Pi.smul_apply] using hx
  · intro x hx
    simp [l2ExtensionFunction, hx]

omit [NormedSpace ℂ H] in
theorem l2Extend_add (f g : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Extend μ s hs (f + g) = l2Extend μ s hs f + l2Extend μ s hs g := by
  apply Lp.ext
  filter_upwards [l2Extend_apply_ae μ s hs (f + g), l2Extend_apply_ae μ s hs f,
    l2Extend_apply_ae μ s hs g,
    Lp.coeFn_add (l2Extend μ s hs f) (l2Extend μ s hs g),
    l2ExtensionFunction_add_ae μ s hs f g] with x hfg hf hg ha he
  simp only [Pi.add_apply] at ha
  rw [hfg, ha, hf, hg]
  exact he

theorem l2Extend_smul (c : ℂ) (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Extend μ s hs (c • f) = c • l2Extend μ s hs f := by
  apply Lp.ext
  filter_upwards [l2Extend_apply_ae μ s hs (c • f), l2Extend_apply_ae μ s hs f,
    Lp.coeFn_smul c (l2Extend μ s hs f),
    l2ExtensionFunction_smul_ae μ s hs c f] with x hcf hf ha he
  simp only [Pi.smul_apply] at ha
  rw [hcf, ha, hf]
  exact he

/-- Extension by zero is an isometric linear inclusion of each stratum. -/
def l2Extension : Lp H 2 (Measure.comap ((↑) : s → X) μ) →ₗᵢ[ℂ] Lp H 2 μ where
  toFun := l2Extend μ s hs
  map_add' := l2Extend_add μ s hs
  map_smul' := l2Extend_smul μ s hs
  norm_map' := l2Extend_norm μ s hs

end

end KadisonKastler

end OAI
