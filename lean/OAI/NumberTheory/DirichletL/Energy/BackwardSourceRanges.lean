import OAI.NumberTheory.DirichletL.Energy.WidthRanges
import OAI.NumberTheory.DirichletL.Energy.StageReserveBounded

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBackwardSourceRanges
open CenteredMomentEnergyWidthRanges CenteredMomentEnergyProfiles
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyState
open CenteredMomentNaturalRowSource CenteredMomentEnergyStageReserveBounded

def lengthAt (M B L:ℝ)(depth k:ℕ):ℝ:=range M B L (depth-k)
def lowerAt (a b:ℝ)(depth k:ℕ):ℝ:=lower a b (depth-k)

lemma previous_length (M B L:ℝ)(depth k:ℕ)(hk:k<depth):
    lengthAt M B L depth k=CenteredMomentEnergyWidthRanges.step M B
      (lengthAt M B L depth (k+1)):=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lengthAt,hn,range]

lemma previous_lower (a b:ℝ)(depth k:ℕ)(hk:k<depth):
    lowerAt a b depth k=lowerAt a b depth (k+1)/max 1 b:=by
  have hn:depth-k=(depth-(k+1))+1:=by omega
  simp only [lowerAt,hn,lower]

lemma length_nonneg (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    0≤lengthAt M B L depth k:=range_nonneg M B L hM hB _

lemma original_length (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    L≤lengthAt M B L depth k:=range_original M B L hM hB _

lemma lower_positive (a b:ℝ)(ha:0<a)(depth k:ℕ):0<lowerAt a b depth k:=
  lower_pos a b ha _

theorem profile_step_support (a b:ℝ)(ha:0<a)(depth k:ℕ)(hk:k<depth)
    (W:Test (lowerAt a b depth (k+1)) b)(U:ℝ)(hU:0<U)(t:ℝ)(j:Fin 2):
    Function.support
      ((CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).profile:ℝ→ℂ)
      ⊆Set.Icc (lowerAt a b depth k) b:=by
  rw [previous_lower a b depth k hk]
  exact (CenteredMomentEnergyProfiles.step _ b (lower_positive a b ha depth (k+1)) W U hU t j).support

theorem previous_admits (M B L stageCap rho d e Lref:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)(hd:d≤1)(he:e≤1)
    (depth k:ℕ)(hk:k<depth)(hLref:Lref≤stageCap+B+rho/100):
    lengthAt M B L depth (k+1)≤lengthAt M B L depth k ∧
    Lref≤lengthAt M B L depth k ∧
    max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1≤lengthAt M B L depth k ∧
    2*lengthAt M B L depth (k+1)+e≤lengthAt M B L depth k ∧
    2*(max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)+1)+e≤lengthAt M B L depth k:=by
  have h:=step_admits M B (lengthAt M B L depth (k+1)) rho d e hM hB
    (length_nonneg M B L hM hB depth (k+1)) hrho hd he
  rw [previous_length M B L depth k hk]
  refine ⟨h.1,?_,?_,h.2.2.2.1,?_⟩
  · exact (show Lref≤M+B+rho/100+1 by linarith).trans h.2.1
  · have hm:max (lengthAt M B L depth (k+1)) (stageCap+B+2*d)≤
        max (lengthAt M B L depth (k+1)) (M+B+2*d):=max_le_max_left _ (by linarith)
    linarith only [hm,h.2.2.1]
  · apply le_trans _ h.2.2.2.2
    gcongr

lemma paired_contours (M B L stageCap rho L₁ L₂:ℝ)
    (hM:0≤M)(hB:0≤B)(hstage:stageCap≤M)(hrho:rho≤1)
    (depth k:ℕ)(hk:k<depth)
    (h₁:L₁≤stageCap+B+rho/100)(h₂:L₂≤stageCap+B+rho/100):
    max L₁ L₂≤lengthAt M B L depth k:=
  (previous_admits M B L stageCap rho 0 0 (max L₁ L₂) hM hB hstage hrho
    (by norm_num) (by norm_num) depth k hk (max_le h₁ h₂)).2.1

lemma source_cap_uniform (M B L:ℝ)(hM:0≤M)(hB:0≤B)(depth k:ℕ):
    sourceCap M B L (depth-k)≤sourceCap M B L depth:=by
  have h:=range_mono M B L hM hB (Nat.sub_le depth k)
  unfold sourceCap
  linarith

lemma scheduled_source_cap (M B L ε:ℝ)(hM:0≤M)(hB:0≤B)(k:ℕ):
    sourceCap M B L (count M ε-k)≤finalSourceCap M B L ε:=
  source_cap_uniform M B L hM hB _ _

theorem actual_reference_reserve_previous
    (M B L stageCap rho ε bΦ:ℝ)(hM:0≤M)(hB:0≤B)(hstage0:0≤stageCap)
    (hstage:stageCap≤M)(hrho:0<rho)(hrho1:rho≤1)(hε:0<ε)
    (depth k:ℕ)(hk:k<depth):
    ∃d xi saving Lref C:ℝ,0<d ∧ 0<xi ∧ 0<saving ∧ 0<C ∧
      xi≤rho/100 ∧ stageCap+B+xi≤Lref ∧ Lref≤stageCap+B+rho/100 ∧
      Lref≤lengthAt M B L depth k ∧
      ∀e:ℝ,0≤e → ∀Z:ℝ,1≤Z → ∀s:NaturalState Z B bΦ,s.width≤stageCap →
      ∀(α:Type*)[Fintype α](w:α→ℝ),(∑i,w i)≤stageCap →
      (s.puncture.radical.absNorm:ℝ)^d*(Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^d*
          (1+2*(Lref*Real.log Z))*Z^(s.width+e)+
        (max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*d)*Z^(-2*saving)*
          max 1 s.radial.scale*Z^(s.width/4)*(∏i,Z^(w i)))≤C*Z^(s.width+e+ε):=by
  obtain ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,hledger⟩:=
    exists_bounded_separated_reference_reserve rho ε stageCap B bΦ hrho hε hstage0 hB
  refine ⟨d,xi,saving,Lref,C,hd,hxi,hs,hC,hxr,hL,hLu,?_,hledger⟩
  exact (previous_admits M B L stageCap rho 0 0 Lref hM hB hstage hrho1
    (by norm_num) (by norm_num) depth k hk hLu).2.1

end SevenEighths.CenteredMomentEnergyBackwardSourceRanges

end

end OAI
