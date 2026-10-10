import OAI.Probability.GammaPassage.BKPathMeasurability

namespace OAI

namespace GammaFPP.BK
open MeasureTheory Set Filter
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Generic outer-measure limit with AE support capture. No measurability of
an uncountable witness-label union or monotonicity of Rounded_t is assumed. -/
lemma ae_eventual_measure_le (P : Measure Ω) (A : Set Ω) (R : ℕ → Set Ω)
    (C : ℝ≥0∞) (hcap : ∀ᵐ ω ∂P, ω ∈ A → ∀ᶠ t in atTop, ω ∈ R t)
    (hbound : ∀ t, P (R t) ≤ C) : P A ≤ C := by
  let E : ℕ → Set Ω := fun N => ⋂ t ≥ N, R t
  have hsubset : A ≤ᵐ[P] ⋃ N, E N := by
    filter_upwards [hcap] with ω hω
    intro ha
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hω ha)
    exact Set.mem_iUnion.mpr ⟨N,Set.mem_iInter.mpr (fun t => Set.mem_iInter.mpr (hN t))⟩
  have hmono : Monotone E := by
    intro N M hNM ω hω
    simp only [E,mem_iInter] at hω ⊢
    exact fun t ht => hω t (hNM.trans ht)
  have hE : ∀ N, P (E N) ≤ C := by
    intro N
    apply (measure_mono ?_).trans (hbound N)
    intro ω hω
    exact mem_iInter.mp (mem_iInter.mp hω N) le_rfl
  calc
    P A ≤ P (⋃ N, E N) := measure_mono_ae hsubset
    _ = ⨆ N, P (E N) := hmono.measure_iUnion
    _ ≤ C := iSup_le hE

end GammaFPP.BK

end OAI
