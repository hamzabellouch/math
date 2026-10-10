import OAI.Analysis.AncientFlat.Evolution.CoreProfile
import OAI.Analysis.AncientFlat.Evolution.GeneralWindows
import OAI.Analysis.AncientFlat.Geometry.InteriorSchauder
import OAI.Analysis.AncientFlat.Weighted.WeightedEstimateCore

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicCore
open ParabolicInterior ParabolicLocalization FlatWeighted
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
lemma outer_window : MapsTo (window ((0:V),-1/2) 2) (ParabolicInterior.cylinder 2) outer := by
  intro p hp
  simp only [window,zero_add,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2),outer,mem_ofPred_eq]
  norm_num only [show (2:ℝ)^4=16 by norm_num]
  rcases hp with ⟨hx,ht,he⟩
  norm_num at ht
  exact ⟨by linarith,by linarith,by linarith⟩
lemma inner_window : MapsTo (window ((0:V),1/32) (1/2)) inner (ParabolicInterior.cylinder 1) := by
  intro p hp
  simp only [window,zero_add,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2),ParabolicInterior.cylinder,mem_ofPred_eq]
  norm_num only [show ((1:ℝ)/2)^4=1/16 by norm_num,one_pow]
  exact ⟨by linarith [hp.1],by linarith [hp.2.1],by linarith [hp.2.2]⟩
lemma windows_cancel (u ut : ℝ → V → ℂ) :
    windowValue ((0:V),1/32) (1/2) (windowValue (0,-1/2) 2 u)=u ∧
    windowTime ((0:V),1/32) (1/2) (windowTime (0,-1/2) 2 ut)=ut := by
  constructor <;> funext t x <;> simp only [windowValue,windowTime,zero_add,smul_smul] <;> norm_num
  · congr 1
    ring
  · congr 1
    ring
variable [FiniteDimensional ℝ V]
lemma core_schauder (α κ K : ℝ) (hα : 0<α) (hα1 : α<1) (hκ : 0<κ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ),
      HolderBound α outer a K → HolderBound α outer b K → (∀ p∈outer, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U : ℝ), 0≤F → 0≤U →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈outer, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      LocallyFiniteJets α u ut → HolderBound α outer (fun p => f p.2 p.1) F →
      (∀ p∈outer, ‖u p.2 p.1‖≤U) →
      (∀ p∈outer, ut p.2 p.1+(a p:ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1=f p.2 p.1) →
      JetBound α inner u ut (C*(F+U)) := by
  have hq : 0<(2:ℝ) := by norm_num
  have hqa : (2:ℝ)^α≤2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hα1.le
  obtain ⟨C,hC,H⟩ := interior_schauder (V := V) α κ (64*K) hα hα1 hκ (by positivity)
  refine ⟨48*C,by positivity,?_⟩
  intro a b ha hb hell u ut f F U hF hU hs hd hj hf hu he
  let p0 : V × ℝ := (0,-1/2)
  have hm : MapsTo (window p0 2) (ParabolicInterior.cylinder 2) outer := outer_window
  have ha' := (holder_window_general hK hq p0 ha hm).mono
    (show (1+(2:ℝ)^α)*K≤64*K by nlinarith)
  have hb' := ((holder_window_general hK hq p0 hb hm).const_smul ((2:ℝ)^4)).mono
    (show |(2:ℝ)^4| * ((1+(2:ℝ)^α)*K)≤64*K by norm_num; nlinarith)
  have hf' := ((holder_window_general hF hq p0 hf hm).const_smul ((2:ℝ)^4)).mono
    (show |(2:ℝ)^4| * ((1+(2:ℝ)^α)*F)≤48*F by norm_num; nlinarith)
  obtain ⟨N,hN,hjN⟩ := hj 258 (by norm_num) (-1/2) (by norm_num)
  have hmN : MapsTo (window p0 2) (ParabolicInterior.cylinder 2)
      {p : V × ℝ | ‖p.1‖≤258 ∧ -258≤p.2 ∧ p.2≤-1/2} := by
    intro p hp
    have hh := hm hp
    exact ⟨by linarith [hh.1],by linarith [hh.2.1],hh.2.2⟩
  have Hres := H (fun p => a (window p0 2 p)) (fun p => (2:ℝ)^4 • b (window p0 2 p))
    ha' hb' (fun p hp => hell _ (hm hp))
    (windowValue p0 2 u) (windowTime p0 2 ut) (windowTime p0 2 f) (48*F) U (by positivity) hU
    (windowValue_contDiff p0 2 u hs)
    (fun p hp => window_hasDerivAt p0 2 u ut p (hd _ (hm hp)))
    ⟨(1+(2:ℝ)^4)*(1+(2:ℝ)^α)*N,by positivity,window_jet_bound_general hN hq p0 u ut hs hjN hmN⟩
    hf' (fun p hp => hu _ (hm hp)) (fun p hp => window_equation p0 2 a b u ut f hs p (he _ (hm hp)))
  have Hback := window_jet_bound hα.le (show 0≤C*(48*F+U) by positivity)
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (1:ℝ)/2≤1) ((0:V),1/32)
    (windowValue p0 2 u) (windowTime p0 2 ut) (windowValue_contDiff p0 2 u hs) Hres inner_window
  change JetBound α inner (windowValue ((0:V),1/32) (1/2) (windowValue (0,-1/2) 2 u))
    (windowTime ((0:V),1/32) (1/2) (windowTime (0,-1/2) 2 ut)) (C*(48*F+U)) at Hback
  rw [(windows_cancel u ut).1,(windows_cancel u ut).2] at Hback
  have hbnd : C*(48*F+U)≤(48*C)*(F+U) := by nlinarith
  exact ⟨fun n hn => (Hback.1 n hn).mono hbnd,Hback.2.mono hbnd⟩
end ParabolicCore

end

end OAI
