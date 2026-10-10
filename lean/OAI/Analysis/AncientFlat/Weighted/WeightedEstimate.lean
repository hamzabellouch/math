import OAI.Analysis.AncientFlat.Regularity.ReferenceEstimate
import OAI.Analysis.AncientFlat.Regularity.NormalizedJets
import OAI.Analysis.AncientFlat.Evolution.ScaledEquation

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicInterior ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem weighted_estimate (G H : ℝ → ℝ) (c κ α δ a : ℝ)
    (hc : 0<c) (hκ : 0<κ) (hα : 0<α) (hα1 : α<1)
    (hδ : 0<δ) (hδ1 : δ<1) (ha : 0<a) (ha1 : a≤1/16)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hH0 : H 0=c) (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ∃ C : ℝ, 0<C ∧ ∀ (u ut : ℝ → V → ℂ) (f : V × ℝ → ℂ) (F M : ℝ),
      0≤F → 0≤M →
      (∀ t : ℝ, ContDiff ℝ 4 (u t)) →
      (∀ p : V × ℝ, p.2<0 → HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      LocallyFiniteJets α u ut → YBound α (-2+2*δ) a F f →
      (∀ p : V × ℝ, p.2<0 → ‖u p.2 p.1‖≤M*(-p.2)^((-1+δ)/2)) →
      (∀ p : V × ℝ, p.2<0 → ut p.2 p.1+(profilePrincipal G p : ℂ)*
        Δ (Δ (u p.2)) p.1+(profilePotential G p : ℂ)*u p.2 p.1=f p) →
      XBound α (-2+2*δ) a (C*(F+M)) u ut := by
  obtain ⟨C,hC,HC⟩ := reference_estimate (V := V) G H c κ α δ a hc hκ hα hα1 hδ hδ1 ha hG hH hH0 hmatch hpos
  refine ⟨256*C,by positivity,?_⟩
  intro u ut f F M hF hM hs hd hj hf hu he p hp
  obtain ⟨r,hr,q,heq,hq⟩ := normalized_center p hp
  have hqt : q.2<0 := (normalized_sigma hq).1
  have hs' := scaleU_contDiff (-2+2*δ) r u hs
  have hd' : ∀ p : V × ℝ, p.2<0 →
      HasDerivAt (fun t => scaleU (-2+2*δ) r u t p.1) (scaleUT (-2+2*δ) r ut p.2 p.1) p.2 := by
    intro z hz
    exact scaleU_hasDerivAt (-2+2*δ) r u ut z (hd _ ((scale_time_neg r hr z).mpr hz))
  have he' : ∀ p : V × ℝ, p.2<0 →
      scaleUT (-2+2*δ) r ut p.2 p.1+(profilePrincipal G p:ℂ)*Δ (Δ (scaleU (-2+2*δ) r u p.2)) p.1+
      (profilePotential G p:ℂ)*scaleU (-2+2*δ) r u p.2 p.1=scaleValue ((-2+2*δ)-4) r f p := by
    intro z hz
    exact scale_equation G (-2+2*δ) r hr u ut f hs z (he _ ((scale_time_neg r hr z).mpr hz))
  have hRef := HC (scaleU (-2+2*δ) r u) (scaleUT (-2+2*δ) r ut)
    (scaleValue ((-2+2*δ)-4) r f) F M hF hM hs' hd'
    (hj.scale hr hs) (hf.scale r hr) (scale_growth δ r M hr hM u hu) he'
  have hjq := normalized_jet_bound hα hα1 hδ hδ1 ha ha1 (show 0≤C*(F+M) by positivity)
    q hq (scaleU (-2+2*δ) r u) (scaleUT (-2+2*δ) r ut) hs' hRef.1 hRef.2
  rw [weightedValue_scale (-2+2*δ) r hr q hqt,
    weightedTime_scale (-2+2*δ) r hr q hqt,heq] at hjq
  have hDom : localDomain a q=localDomain a p := by rw [←heq,localDomain_scale a r hr q]
  rw [hDom] at hjq
  convert hjq using 1; ring
end FlatWeighted

end

end OAI
