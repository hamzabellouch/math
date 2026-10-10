import OAI.Analysis.AncientFlat.Geometry.NormalizedGeometry
import OAI.Analysis.AncientFlat.Regularity.ScaledJets

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatWeighted
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
lemma normalized_jet_bound {α δ a N : ℝ} (_ : 0<α) (hα1 : α<1) (hδ : 0<δ) (_ : δ<1)
    (ha : 0<a) (ha1 : a≤1/16) (hN : 0≤N) (p : V × ℝ)
    (hp : CoreCenter p ∨ AnnularCenter p) (u ut : ℝ → V → ℂ)
    (hs : ∀ t, ContDiff ℝ 4 (u t))
    (hjC : JetBound α ParabolicCore.inner u ut N) (hjA : JetBound α ParabolicAnnular.inner u ut N) :
    JetBound α (localDomain a p) (weightedValue (-2+2*δ) p u) (weightedTime (-2+2*δ) p ut) (256*N) := by
  obtain ⟨ht,hs1,hs2⟩ := normalized_sigma hp
  have hsig := sigma_pos p ht
  have hsa : sigma p^α≤2 := (Real.rpow_le_rpow_of_exponent_le hs1 hα1.le).trans (by simpa using hs2)
  have hs4 : sigma p^4≤16 := by have hh := pow_le_pow_left₀ hsig.le hs2 4; norm_num at hh; exact hh
  have hsw : sigma p^(-(-2+2*δ))≤4 := by
    apply (Real.rpow_le_rpow_of_exponent_le hs1 (show -(-2+2*δ)≤2 by linarith)).trans
    have hh := pow_le_pow_left₀ hsig.le hs2 2
    norm_num at hh ⊢
    exact hh
  have hChart : JetBound α (localDomain a p) (windowValue p (sigma p) u) (windowTime p (sigma p) ut)
      ((1+sigma p^4)*(1+sigma p^α)*N) := by
    rcases hp with hc|hc
    · exact window_jet_bound_general hN hsig p u ut hs hjC ((normalized_chart_maps ha ha1 p (Or.inl hc)).1 hc)
    · exact window_jet_bound_general hN hsig p u ut hs hjA ((normalized_chart_maps ha ha1 p (Or.inr hc)).2 hc)
  have hC := hChart.const_smul (windowValue_contDiff p (sigma p) u hs) (sigma p^(-(-2+2*δ)))
  rw [abs_of_pos (Real.rpow_pos_of_pos hsig _)] at hC
  have hb : sigma p^(-(-2+2*δ))*((1+sigma p^4)*(1+sigma p^α)*N)≤256*N := by
    have h1 : (1+sigma p^4)*(1+sigma p^α)≤51 := by nlinarith [Real.rpow_nonneg hsig.le α,pow_nonneg hsig.le 4]
    have h2 : sigma p^(-(-2+2*δ))*((1+sigma p^4)*(1+sigma p^α))≤204 := by nlinarith [Real.rpow_nonneg hsig.le (-(-2+2*δ))]
    nlinarith [mul_le_mul_of_nonneg_right h2 hN]
  have heV : (fun t x => sigma p^(-(-2+2*δ)) • windowValue p (sigma p) u t x)=weightedValue (-2+2*δ) p u := rfl
  have heT : (fun t x => sigma p^(-(-2+2*δ)) • windowTime p (sigma p) ut t x)=weightedTime (-2+2*δ) p ut := by
    funext t x
    simp only [windowTime,weightedTime,chart,smul_smul]
  rw [heV,heT] at hC
  exact ⟨fun n hn => (hC.1 n hn).mono hb,hC.2.mono hb⟩
end FlatWeighted

end

end OAI
