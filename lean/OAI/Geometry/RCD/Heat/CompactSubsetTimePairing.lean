import OAI.Geometry.RCD.Sobolev.CompactTimeWeakEquation

namespace OAI

/-! # Compact spatial restriction of the weak time equation -/

open Set Filter MeasureTheory
open scoped Interval Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
theorem continuousOn_time_subtype {H : ℝ → X → ℝ}
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ)) (Ω : Set X) :
    ContinuousOn (fun q : ℝ × Ω => H q.1 q.2) (Ioi 0 ×ˢ univ) := by
  have hi : Continuous (fun q : ℝ × Ω => (q.1,(q.2 : X))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hm : MapsTo (fun q : ℝ × Ω => (q.1,(q.2 : X)))
      (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := fun q hq => ⟨hq.1,mem_univ _⟩
  have hh := hH.comp hi.continuousOn hm
  dsimp only [Function.comp_def,Function.uncurry] at hh
  exact hh

theorem compact_subset_time_pairing_hasDerivAt (H D : ℝ → X → ℝ)
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ))
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => H s x) (D t x) t)
    (Ω : Set X) (hΩ : IsCompact Ω) (σ : Measure Ω) (φ : Ω → ℝ)
    (hφ : Integrable φ σ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, φ x * H s x ∂σ) (∫ x, φ x * D t x ∂σ) t := by
  let : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩ
  exact compact_time_pairing_hasDerivAt σ (fun s (x : Ω) => H s x) (fun s (x : Ω) => D s x)
    (continuousOn_time_subtype hH Ω) (continuousOn_time_subtype hD Ω)
    (fun s hs x => hd s hs x) φ hφ ht

theorem compact_subset_time_pairing_weak_equation (H D : ℝ → X → ℝ)
    (hH : ContinuousOn (Function.uncurry H) (Ioi 0 ×ˢ univ))
    (hD : ContinuousOn (Function.uncurry D) (Ioi 0 ×ˢ univ))
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => H s x) (D t x) t)
    (Ω : Set X) (hΩ : IsCompact Ω) (σ : Measure Ω) (φ : Ω → ℝ)
    (hφ : Integrable φ σ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (θ θ' : ℝ → ℝ) (hθ : ContinuousOn θ (Icc a b))
    (hθ' : ContinuousOn θ' (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt θ (θ' t) t)
    (hθa : θ a = 0) (hθb : θ b = 0) :
    (∫ t in a..b, θ t * ∫ x, φ x * D t x ∂σ) =
      -(∫ t in a..b, θ' t * ∫ x, φ x * H t x ∂σ) := by
  let : CompactSpace Ω := isCompact_iff_compactSpace.mp hΩ
  exact compact_time_pairing_weak_equation σ (fun s (x : Ω) => H s x) (fun s (x : Ω) => D s x)
    (continuousOn_time_subtype hH Ω) (continuousOn_time_subtype hD Ω)
    (fun s hs x => hd s hs x) φ hφ ha hab θ θ' hθ hθ' hder hθa hθb

end RegularPointCoordinates

end

end OAI
