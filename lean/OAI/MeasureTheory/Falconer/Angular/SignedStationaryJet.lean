import OAI.MeasureTheory.Falconer.Angular.NormalizedStationaryJet
import OAI.MeasureTheory.Falconer.Angular.StationaryOppositePhase

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

noncomputable def signedStationaryJet (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ) : ℂ :=
  if plus then normalizedStationaryJet j f θ Λ else
    conj (normalizedStationaryJet j (fun t => conj (f (t+Real.pi))) θ Λ)

 theorem signedStationaryJet_bound {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {C D Λ : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D) (hΛ : 0 < Λ) (hscale : D^2 ≤ Λ)
    (plus : Bool) (j : ℕ) (θ : ℝ)
    (hb : ∀ k ≤ 2*j, ∀ t, ‖iteratedDeriv k f t‖ ≤ C*D^k) :
    ‖signedStationaryJet plus j f θ Λ‖ ≤ (directStationaryExpr j).cost*C := by
  cases plus
  · simp only [signedStationaryJet,Bool.false_eq_true,↓reduceIte,Complex.norm_conj]
    have hfs : ContDiff ℝ ∞ (fun t => f (t+Real.pi)) := hf.comp (contDiff_id.add contDiff_const)
    apply normalizedStationaryJet_bound (Complex.conjCLE.contDiff.comp hfs) hC hD hΛ hscale
    intro k hk
    change ‖iteratedDeriv k (fun t => conj (f (t+Real.pi))) θ‖ ≤ _
    rw [complex_iteratedDeriv_conj hfs,Complex.norm_conj,iteratedDeriv_comp_add_const]
    exact hb k hk _
  · simp only [signedStationaryJet,↓reduceIte]
    exact normalizedStationaryJet_bound hf hC hD hΛ hscale j θ (fun k hk => hb k hk θ)

end PlanarFalconer

end OAI
