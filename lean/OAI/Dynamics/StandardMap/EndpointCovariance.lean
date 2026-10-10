import OAI.Dynamics.StandardMap.EndpointShapes

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory
open scoped Topology Classical
namespace StandardMapEntropy
noncomputable def erealOrderIso (e : ℝ ≃o ℝ) : EReal ≃o EReal := e.withTopCongr.withBotCongr
@[simp] lemma erealOrderIso_coe (e : ℝ ≃o ℝ) (r : ℝ) : erealOrderIso e (r:EReal)=(e r:ℝ) := rfl
@[simp] lemma erealOrderIso_top (e : ℝ ≃o ℝ) : erealOrderIso e ⊤=⊤ := rfl
@[simp] lemma erealOrderIso_bot (e : ℝ ≃o ℝ) : erealOrderIso e ⊥=⊥ := rfl
lemma endpoints_reindex (d d' : DistanceArray) (e : ℝ ≃o ℝ) (b : DyadicTime ≃ DyadicTime)
    (hb : ∀s:DyadicTime,(b s:ℝ)=e (s:ℝ))
    (he : ∀s t:DyadicTime,d'.val (b s) (b t)≠|(b t:ℝ)-(b s:ℝ)| ↔ d.val s t≠|(t:ℝ)-(s:ℝ)|) :
    leftEndpoint d'=erealOrderIso e (leftEndpoint d) ∧ rightEndpoint d'=erealOrderIso e (rightEndpoint d) := by
  constructor
  · unfold leftEndpoint
    rw [←b.iInf_comp]
    simp_rw [←b.iInf_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((max (b _:ℝ) (t:ℝ)):EReal) else ⊤)]
    simp only [OrderIso.map_iInf]
    apply iInf_congr; intro s
    apply iInf_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [max_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact max_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
  · unfold rightEndpoint
    rw [←b.iSup_comp]
    simp_rw [←b.iSup_comp (g := fun t => if d'.val (b _) t≠|(t:ℝ)-(b _:ℝ)| then ((min (b _:ℝ) (t:ℝ)):EReal) else ⊥)]
    simp only [OrderIso.map_iSup]
    apply iSup_congr; intro s
    apply iSup_congr; intro t
    simp only [he s t]
    split_ifs
    · rcases le_total (s:ℝ) (t:ℝ) with h|h
      · rw [min_eq_left (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_left (EReal.coe_le_coe_iff.mpr (e.monotone h))
      · rw [min_eq_right (EReal.coe_le_coe_iff.mpr h)]
        simp only [erealOrderIso_coe,hb]
        exact min_eq_right (EReal.coe_le_coe_iff.mpr (e.monotone h))
    · rfl
lemma endpoints_translate (r : DyadicTime) (d : DistanceArray) :
    leftEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (leftEndpoint d) ∧
    rightEndpoint (arrayTranslate r d)=erealOrderIso (OrderIso.addRight (-(r:ℝ))) (rightEndpoint d) := by
  apply endpoints_reindex d _ _ (Equiv.addRight (-r))
  · intro s; rfl
  · intro s t
    change d.val (s+-r+r) (t+-r+r)≠|((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))| ↔ _
    rw [show s+-r+r=s by abel,show t+-r+r=t by abel]
    rw [show ((t:ℝ)+-(r:ℝ))-((s:ℝ)+-(r:ℝ))=(t:ℝ)-(s:ℝ) by ring]
noncomputable def dyadicHalfEquiv : DyadicTime ≃ DyadicTime where
  toFun := dyadicHalf
  invFun := fun s => s+s
  left_inv := dyadicHalf_add_self
  right_inv := dyadicHalf_double
lemma endpoints_dilate (d : DistanceArray) :
    leftEndpoint (arrayDilate d)=erealOrderIso (OrderIso.mulRight₀ (1/2:ℝ) (by norm_num)) (leftEndpoint d) ∧
    rightEndpoint (arrayDilate d)=erealOrderIso (OrderIso.mulRight₀ (1/2:ℝ) (by norm_num)) (rightEndpoint d) := by
  apply endpoints_reindex d _ _ dyadicHalfEquiv
  · intro s; change (s:ℝ)/2=(s:ℝ)*(1/2); ring
  · intro s t
    change (d.val (dyadicHalf s+dyadicHalf s) (dyadicHalf t+dyadicHalf t)/2≠|(t:ℝ)/2-(s:ℝ)/2|) ↔ _
    rw [dyadicHalf_add_self,dyadicHalf_add_self,←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact not_congr (div_left_inj' (by norm_num))
end StandardMapEntropy

end OAI
