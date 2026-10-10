import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalSolutionLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralColumnIdentification

namespace OAI

/-! The constructed common-tail limit is also the limit of every canonical
all-orders column, including the holomorphic columns used in matching. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_allOrders_limit
    (ν m νp νm : ℕ → ℂ) (ν₀ m₀ νp₀ νm₀ η : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (hp : Tendsto νp atTop (𝓝 νp₀)) (hn : Tendsto νm atTop (𝓝 νm₀))
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (c : ℂ × ℂ) (W : ℕ → ℝ → E₄)
    (hW : ∀ᶠ n in atTop, ∀ t, 0 ≤ t → HasDerivAt (W n)
      (circularLeadingField t (W n t)+circularBoundedField (νp n) (νm n) η n
        (radialExteriorCanonical (ν n) n (m n) L t).1 (W n t)) t)
    (heW : ∀ᶠ n in atTop, ∀ J : ℕ, ∃ k : ℕ, J ≤ k ∧ ∃ u : CircularTailSpace,
      ∀ t, 0 ≤ t → W n t=circularPolynomialJet
        (spectralOutgoingPolynomial (νp n) (νm n) η n
          (radialExteriorExpansion (ν n) n (m n) k) c k) t+
            circularUnweight (2*(k : ℝ)) u t) :
    ∃ T : ℝ, 0 ≤ T ∧ L ≤ T ∧ ∃ W₀ : ℝ → E₄,
      TendstoUniformlyOn W W₀ atTop (Ici T) ∧
      Tendsto W₀ atTop (𝓝 ((c.1,0),(c.2,0))) ∧
      ∀ t, T ≤ t → HasDerivAt W₀
        (circularLeadingField t (W₀ t)+circularBoundedField νp₀ νm₀ η 1 0 (W₀ t)) t := by
  obtain ⟨j,hj⟩ := exists_nat_gt (max (radialExteriorMatrixBound ν₀)
    (circularFieldBound νp₀ νm₀ η 1 0))
  have hj₁ : radialExteriorMatrixBound ν₀ < 2*(j : ℝ) := by
    have hh := (le_max_left (radialExteriorMatrixBound ν₀)
      (circularFieldBound νp₀ νm₀ η 1 0)).trans_lt hj
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hj₂ : circularFieldBound νp₀ νm₀ η 1 0 < 2*(j : ℝ) := by
    have hh := (le_max_right (radialExteriorMatrixBound ν₀)
      (circularFieldBound νp₀ νm₀ η 1 0)).trans_lt hj
    linarith [Nat.cast_nonneg (α := ℝ) j]
  obtain ⟨T,ρ,hT,hLT,_hρ,_hρ1,v,w,_hvw,hlim,_hlimn,hlim₀,hactual,hfree⟩ :=
    exists_canonical_circular_solution_limit ν m νp νm ν₀ m₀ νp₀ νm₀ η
      hν hm hp hn δ L hδ hsmall hX j hj₁ hj₂ c
  let U := fun n => spectralOutgoingPolynomial (νp n) (νm n) η n
    (radialExteriorExpansion (ν n) n (m n) j) c j
  let Y := fun n t => circularPolynomialJet (U n) t+circularUnweight (2*(j : ℝ)) (v n) t
  let Y₀ := fun t => circularPolynomialJet (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 c j) t+
    circularUnweight (2*(j : ℝ)) w t
  have heq : ∀ᶠ n in atTop, ∀ t, T ≤ t → Y n t=W n t := by
    filter_upwards [hactual,hW,heW,eventually_ge_atTop 1] with n han hwn hen hnn
    exact circular_expansion_matches_allOrders (ν n) (νp n) (νm n) η (m n) n hnn c j
      (v n) ρ T hT (fun t => (radialExteriorCanonical (ν n) n (m n) L t).1) (Y n) (W n)
      (fun t ht => (han.2 t ht).1) (fun t ht => (han.2 t ht).2)
      (fun t ht => hwn t (hT.trans ht)) (fun _ _ => rfl) hen han.1
  refine ⟨T,hT,hLT,Y₀,?_,hlim₀,hfree⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) ε hε,heq] with n hn he t ht
  rw [← he t ht]
  exact hn t (hT.trans ht)

end DefocusingNLS

end OAI
