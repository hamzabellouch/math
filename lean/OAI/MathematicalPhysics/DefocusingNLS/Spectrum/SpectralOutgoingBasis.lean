import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCanonicalOutgoing
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralColumnRank

namespace OAI

/-! Two canonical normalized slow columns form a rank-two subspace at every exterior point. -/

open Filter
namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem canonical_circular_outgoing_basis (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0) :
    ∃ Yp Ym : ℝ → E₄,
      (∀ t, 0 ≤ t → HasDerivAt Yp (circularLeadingField t (Yp t)+
        circularBoundedField νp νm η n (radialExteriorCanonical ν n b L t).1 (Yp t)) t) ∧
      (∀ t, 0 ≤ t → HasDerivAt Ym (circularLeadingField t (Ym t)+
        circularBoundedField νp νm η n (radialExteriorCanonical ν n b L t).1 (Ym t)) t) ∧
      Tendsto Yp atTop (nhds ((1,0),(0,0))) ∧
      Tendsto Ym atTop (nhds ((0,0),(1,0))) ∧
      (∀ t, 0 ≤ t → LinearIndependent ℂ ![Yp t,Ym t]) ∧
      (∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
        Yp t=circularPolynomialJet (spectralOutgoingPolynomial νp νm η n
          (radialExteriorExpansion ν n b j) (1,0) j) t+circularUnweight (2*(j : ℝ)) v t) ∧
      (∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ ∃ v : CircularTailSpace, ∀ t, 0 ≤ t →
        Ym t=circularPolynomialJet (spectralOutgoingPolynomial νp νm η n
          (radialExteriorExpansion ν n b j) (0,1) j) t+circularUnweight (2*(j : ℝ)) v t) := by
  obtain ⟨Yp,hp,hplim,hpe⟩ := canonical_circular_allOrders ν νp νm η b n hn L hX hb (1,0)
  obtain ⟨Ym,hm,hmlim,hme⟩ := canonical_circular_allOrders ν νp νm η b n hn L hX hb (0,1)
  obtain ⟨q,hq,_⟩ := canonical_circular_expansion_data ν b n L hX hb
  refine ⟨Yp,Ym,hp,hm,hplim,hmlim,?_,hpe,hme⟩
  intro t ht
  apply circular_columns_at_linearIndependent νp νm η n hn ‖q‖
    (fun s => (radialExteriorCanonical ν n b L s).1) Yp Ym _ hp hm hplim hmlim t ht
  intro s hs
  rw [← hq s hs]
  exact q.norm_coe_le_norm s

theorem canonical_holomorphic_circular_basis (ν νp νm η b : ℂ) (n : ℕ) (hn : 1 ≤ n)
    (L : ℝ) (hX : HasRadialExterior ν n b L) (hb : b ≠ 0) :
    ∃ Yp Ym : ℂ → ℝ → E₄,
      (∀ lam t, 0 ≤ t → HasDerivAt (Yp lam)
        (circularLeadingField t (Yp lam t)+circularBoundedField (νp-2*lam) (νm-2*lam) η n
          (radialExteriorCanonical ν n b L t).1 (Yp lam t)) t) ∧
      (∀ lam t, 0 ≤ t → HasDerivAt (Ym lam)
        (circularLeadingField t (Ym lam t)+circularBoundedField (νp-2*lam) (νm-2*lam) η n
          (radialExteriorCanonical ν n b L t).1 (Ym lam t)) t) ∧
      (∀ lam, Tendsto (Yp lam) atTop (nhds ((1,0),(0,0)))) ∧
      (∀ lam, Tendsto (Ym lam) atTop (nhds ((0,0),(1,0)))) ∧
      (∀ lam t, 0 ≤ t → LinearIndependent ℂ ![Yp lam t,Ym lam t]) ∧
      (∀ z t, 0 ≤ t → AnalyticAt ℂ (fun lam => Yp lam t) z ∧
        AnalyticAt ℂ (fun lam => Ym lam t) z) := by
  obtain ⟨Yp,hp,hplim,hpa,_⟩ :=
    canonical_holomorphic_circular_allOrders ν νp νm η b n hn L hX hb (1,0)
  obtain ⟨Ym,hm,hmlim,hma,_⟩ :=
    canonical_holomorphic_circular_allOrders ν νp νm η b n hn L hX hb (0,1)
  obtain ⟨q,hq,_⟩ := canonical_circular_expansion_data ν b n L hX hb
  refine ⟨Yp,Ym,hp,hm,hplim,hmlim,?_,fun z t ht => ⟨hpa z t ht,hma z t ht⟩⟩
  intro lam t ht
  apply circular_columns_at_linearIndependent (νp-2*lam) (νm-2*lam) η n hn ‖q‖
    (fun s => (radialExteriorCanonical ν n b L s).1) (Yp lam) (Ym lam) _
    (hp lam) (hm lam) (hplim lam) (hmlim lam) t ht
  intro s hs
  rw [← hq s hs]
  exact q.norm_coe_le_norm s

end DefocusingNLS

end OAI
