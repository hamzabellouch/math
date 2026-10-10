import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalColumnLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalOutgoing

namespace OAI

/-! The holomorphic outgoing columns used in matching have the singular
limit constructed from the actual canonical profile. -/

open Filter Topology Set Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

def IsCanonicalHolomorphicColumn (ν η b : ℂ) (n : ℕ) (L : ℝ) (c : ℂ × ℂ)
    (Y : ℂ → ℝ → E₄) : Prop :=
  (∀ lam t, 0 ≤ t → HasDerivAt (Y lam)
    (circularLeadingField t (Y lam t)+circularBoundedField (ν-2*lam) (star ν-2*lam) η n
      (radialExteriorCanonical ν n b L t).1 (Y lam t)) t) ∧
  (∀ lam, Tendsto (Y lam) atTop (𝓝 ((c.1,0),(c.2,0)))) ∧
  (∀ z t, 0 ≤ t → AnalyticAt ℂ (fun lam => Y lam t) z) ∧
  ∀ lam J, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
    Y lam t=circularPolynomialJet
      (spectralOutgoingPolynomial (ν-2*lam) (star ν-2*lam) η n
        (radialExteriorExpansion ν n b j) c j) t+circularUnweight (2*(j : ℝ)) v t

theorem exists_canonical_holomorphic_singular_limit
    (ν m lam : ℕ → ℂ) (ν₀ m₀ lam₀ η : ℂ)
    (hν : Tendsto ν atTop (𝓝 ν₀)) (hm : Tendsto m atTop (𝓝 m₀))
    (hlam : Tendsto lam atTop (𝓝 lam₀)) (hm₀ : m₀ ≠ 0)
    (δ L : ℝ) (hδ : 0 < δ) (hsmall : ‖m₀‖+2*δ < 1)
    (hX : ∀ᶠ n in atTop, HasRadialExterior (ν n) n (m n) L) (c : ℂ × ℂ) :
    ∃ Y : ℕ → ℂ → ℝ → E₄,
      (∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (ν n) η (m n) n L c (Y n)) ∧
      ∃ T : ℝ, 0 ≤ T ∧ L ≤ T ∧ ∃ Y₀ : ℝ → E₄,
        TendstoUniformlyOn (fun n => Y n (lam n)) Y₀ atTop (Ici T) ∧
        Tendsto Y₀ atTop (𝓝 ((c.1,0),(c.2,0))) ∧
        ∀ t, T ≤ t → HasDerivAt Y₀
          (circularLeadingField t (Y₀ t)+
            circularBoundedField (ν₀-2*lam₀) (star ν₀-2*lam₀) η 1 0 (Y₀ t)) t := by
  classical
  have hex (n : ℕ) : ∃ Y : ℂ → ℝ → E₄,
      (1 ≤ n ∧ HasRadialExterior (ν n) n (m n) L ∧ m n ≠ 0) →
        IsCanonicalHolomorphicColumn (ν n) η (m n) n L c Y := by
    by_cases h : 1 ≤ n ∧ HasRadialExterior (ν n) n (m n) L ∧ m n ≠ 0
    · obtain ⟨Y,hY⟩ := canonical_holomorphic_circular_allOrders
        (ν n) (ν n) (star (ν n)) η (m n) n h.1 L h.2.1 h.2.2 c
      exact ⟨Y,fun _ => hY⟩
    · exact ⟨fun _ _ => 0,fun hh => (h hh).elim⟩
  choose Y hY using hex
  have hgood : ∀ᶠ n in atTop, 1 ≤ n ∧ HasRadialExterior (ν n) n (m n) L ∧ m n ≠ 0 :=
    (eventually_ge_atTop 1).and (hX.and (hm.eventually (eventually_ne_nhds hm₀)))
  have hspec : ∀ᶠ n in atTop, IsCanonicalHolomorphicColumn (ν n) η (m n) n L c (Y n) :=
    hgood.mono (fun n hn => hY n hn)
  have hW : ∀ᶠ n in atTop, ∀ t, 0 ≤ t → HasDerivAt (Y n (lam n))
      (circularLeadingField t (Y n (lam n) t)+
        circularBoundedField (ν n-2*lam n) (star (ν n)-2*lam n) η n
          (radialExteriorCanonical (ν n) n (m n) L t).1 (Y n (lam n) t)) t :=
    hspec.mono (fun n hn => hn.1 (lam n))
  have heW : ∀ᶠ n in atTop, ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace,
      ∀ t, 0 ≤ t → Y n (lam n) t=circularPolynomialJet
        (spectralOutgoingPolynomial (ν n-2*lam n) (star (ν n)-2*lam n) η n
          (radialExteriorExpansion (ν n) n (m n) j) c j) t+
            circularUnweight (2*(j : ℝ)) v t :=
    hspec.mono (fun n hn => hn.2.2.2 (lam n))
  have hsν := continuous_star.continuousAt.tendsto.comp hν
  obtain ⟨T,hT,hLT,Y₀,hlim,hlim₀,hfree⟩ := canonical_circular_allOrders_limit
    ν m (fun n => ν n-2*lam n) (fun n => star (ν n)-2*lam n)
    ν₀ m₀ (ν₀-2*lam₀) (star ν₀-2*lam₀) η hν hm
    (hν.sub (hlam.const_mul 2)) (hsν.sub (hlam.const_mul 2))
    δ L hδ hsmall hX c (fun n => Y n (lam n)) hW heW
  exact ⟨Y,hspec,T,hT,hLT,Y₀,hlim,hlim₀,hfree⟩

end DefocusingNLS

end OAI
