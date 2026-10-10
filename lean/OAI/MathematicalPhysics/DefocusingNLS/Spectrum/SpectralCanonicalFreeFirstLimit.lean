import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalColumnLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeSlowIdentification

namespace OAI

/-! The canonical first column converges to the explicit free angular H column. -/

open Filter Topology Set Polynomial
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_first_H_limit
    (ν m νp νm : ℕ → ℂ) (ν₀ m₀ νm₀ q : ℂ) (ell : ℕ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (hp : Tendsto νp atTop (𝓝 ((ell : ℂ)-2*q)))
    (hn : Tendsto νm atTop (𝓝 νm₀)) (hq : -1 < q.re)
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L)
    (W : ℕ → ℝ → E₄)
    (hW : ∀ᶠ n in atTop, ∀ t, 0 ≤ t → HasDerivAt (W n)
      (circularLeadingField t (W n t)+circularBoundedField (νp n) (νm n)
        ((ell*(ell+10) : ℕ) : ℂ) n (radialExteriorCanonical (ν n) n (m n) L t).1
          (W n t)) t)
    (heW : ∀ᶠ n in atTop, ∀ J : ℕ, ∃ k : ℕ, J ≤ k ∧ ∃ u : CircularTailSpace,
      ∀ t, 0 ≤ t → W n t=circularPolynomialJet
        (spectralOutgoingPolynomial (νp n) (νm n) ((ell*(ell+10) : ℕ) : ℂ) n
          (radialExteriorExpansion (ν n) n (m n) k) (1,0) k) t+
            circularUnweight (2*(k : ℝ)) u t) :
    ∃ T : ℝ, 0 ≤ T ∧ L ≤ T ∧
      TendstoUniformlyOn W (spectralFreeFirstColumn ell q) atTop (Ici T) := by
  let η : ℂ := ((ell*(ell+10) : ℕ) : ℂ)
  let νp₀ : ℂ := (ell : ℂ)-2*q
  obtain ⟨j,hj⟩ := exists_nat_gt (max (radialExteriorMatrixBound ν₀)
    (circularFieldBound νp₀ νm₀ η 1 0))
  have hj₁ : radialExteriorMatrixBound ν₀ < 2*((j+1 : ℕ) : ℝ) := by
    have hh := (le_max_left (radialExteriorMatrixBound ν₀)
      (circularFieldBound νp₀ νm₀ η 1 0)).trans_lt hj
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hj₂ : circularFieldBound νp₀ νm₀ η 1 0 < 2*((j+1 : ℕ) : ℝ) := by
    have hh := (le_max_right (radialExteriorMatrixBound ν₀)
      (circularFieldBound νp₀ νm₀ η 1 0)).trans_lt hj
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  obtain ⟨T,ρ,hT,hLT,_hρ,_hρ1,v,w,_hvw,hlim,_hlimn,_hlim₀,hactual,hfree⟩ :=
    exists_canonical_circular_solution_limit ν m νp νm ν₀ m₀ νp₀ νm₀ η
      hν hm hp hn δ L hδ hsmall hX (j+1) hj₁ hj₂ (1,0)
  let U := fun n => spectralOutgoingPolynomial (νp n) (νm n) η n
    (radialExteriorExpansion (ν n) n (m n) (j+1)) (1,0) (j+1)
  let Y := fun n t => circularPolynomialJet (U n) t+
    circularUnweight (2*((j+1 : ℕ) : ℝ)) (v n) t
  let Y₀ := fun t => circularPolynomialJet
    (spectralOutgoingPolynomial νp₀ νm₀ η 1 0 (1,0) (j+1)) t+
      circularUnweight (2*((j+1 : ℕ) : ℝ)) w t
  have heq : ∀ᶠ n in atTop, ∀ t, T ≤ t → Y n t=W n t := by
    filter_upwards [hactual,hW,heW,eventually_ge_atTop 1] with n han hwn hen hnn
    exact circular_expansion_matches_allOrders (ν n) (νp n) (νm n) η (m n) n hnn
      (1,0) (j+1) (v n) ρ T hT
      (fun t => (radialExteriorCanonical (ν n) n (m n) L t).1) (Y n) (W n)
      (fun t ht => (han.2 t ht).1) (fun t ht => (han.2 t ht).2)
      (fun t ht => hwn t (hT.trans ht)) (fun _ _ => rfl) hen han.1
  let S := max T (max 0 (Real.log 4/2))
  have hH : ∀ t, S ≤ t → Y₀ t=spectralFreeFirstColumn ell q t :=
    spectralFreeFirstColumn_eq_correction ell q νm₀ hq j w T hj₂ hfree
  refine ⟨S,(le_max_left 0 _).trans (le_max_right T _),
    hLT.trans (le_max_left T _),?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) ε hε,heq] with n hn he t ht
  have htT : T ≤ t := (le_max_left T _).trans ht
  rw [← he t htT,← hH t ht]
  exact hn t (hT.trans htT)

end DefocusingNLS

end OAI
