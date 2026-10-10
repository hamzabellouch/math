import OAI.Probability.DilutedSpin.Polarization

namespace OAI

section
section
namespace DilutedSpinGlass
open MeasureTheory Filter
open scoped Topology

/-- Countable tags, including the manuscript's pairs (specification, probe),
are selected simultaneously. The error array is not collapsed to finitely
many specifications. -/
theorem countable_tag_parameter_selection
    {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Δ : ℕ → Ω → ℝ) (e : J → ℕ → Ω → ℝ)
    (hΔ : ∀ N, Integrable (Δ N) μ) (he : ∀ j N, Integrable (e j N) μ)
    (hne : ∀ j N x, 0 ≤ e j N x)
    {C v u : ℝ} (hC : 0 ≤ C) (hvu : v < u)
    (hlower : ∀ N x, -C ≤ Δ N x)
    (hlow : ∀ n, ∃ N, n ≤ N ∧ ∫ x, Δ N x ∂μ ≤ v)
    (hlim : ∀ j, Tendsto (fun N => ∫ x, e j N x ∂μ) atTop (𝓝 0)) :
    ∃ (Ns : ℕ → ℕ) (xs : ℕ → Ω), StrictMono Ns ∧
      (∀ n, Δ (Ns n) (xs n) ≤ u) ∧
      (∀ j, Tendsto (fun n => e j (Ns n) (xs n)) atTop (𝓝 0)) := by
  classical
  let : Encodable J := Encodable.ofCountable J
  let e' (k N : ℕ) (x : Ω) : ℝ := match Encodable.decode (α := J) k with
    | none => 0
    | some j => e j N x
  have hei (k N : ℕ) : Integrable (e' k N) μ := by
    cases hk : Encodable.decode (α := J) k with
    | none => simpa only [e',hk] using (integrable_const (0 : ℝ))
    | some j => simpa only [e',hk] using he j N
  have hen (k N : ℕ) (x : Ω) : 0 ≤ e' k N x := by
    cases hk : Encodable.decode (α := J) k with
    | none => simp only [e',hk,le_refl]
    | some j => simpa only [e',hk] using hne j N x
  have hel (k : ℕ) : Tendsto (fun N => ∫ x, e' k N x ∂μ) atTop (𝓝 0) := by
    cases hk : Encodable.decode (α := J) k with
    | none => simpa only [e',hk,integral_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    | some j => simpa only [e',hk] using hlim j
  obtain ⟨Ns,xs,hs,hi,he'⟩ := countable_parameter_selection μ Δ e' hΔ hei hen hC hvu hlower hlow hel
  refine ⟨Ns,xs,hs,hi,fun j => ?_⟩
  simpa only [e',Encodable.encodek] using he' (Encodable.encode j)

end DilutedSpinGlass
end

end

end OAI
