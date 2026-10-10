import OAI.Probability.GaussianPropeller.SmallCell

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Reduction
open FourCertificates ProbabilityBounds
open scoped RealInnerProductSpace
variable {d:ℕ}

lemma triangle_gram (u v w : Space d) (hs:u+v+w=0) :
    let D:=‖u‖^2*‖v‖^2-⟪u,v⟫^2
    D=‖u‖^2*‖w‖^2-⟪u,w⟫^2 ∧ D=‖v‖^2*‖w‖^2-⟪v,w⟫^2 ∧
    4*D=(‖u‖^2+‖v‖^2+‖w‖^2)^2-2*(‖u‖^4+‖v‖^4+‖w‖^4) := by
  have hw:w=-(u+v) := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs)
  subst w
  simp only [norm_neg,norm_add_sq_real,inner_neg_right,inner_add_right,real_inner_self_eq_norm_sq,
    real_inner_comm u v]
  constructor
  · ring
  constructor
  · ring
  · have h4:‖u+v‖^4=(‖u‖^2+‖v‖^2+2*⟪u,v⟫)^2 := by rw [show (4:ℕ)=2*2 by rfl,pow_mul,norm_add_sq_real]; ring
    rw [h4]
    ring

lemma residual_fourth_le (x y:Space d) (hx:x≠0) :
    ‖residualVector x y‖^4≤‖y‖^4 := by
  have h:=residual_norm_sq (z:=x) (y:=y) hx
  have hle:‖residualVector x y‖^2≤‖y‖^2 := by nlinarith only [h,mul_nonneg (sq_nonneg (residualCoefficient x y)) (sq_nonneg ‖x‖)]
  have hh: (‖residualVector x y‖^2)^2≤(‖y‖^2)^2 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hle
  simpa only [←pow_mul] using hh

lemma four_incompatibility (z:Fin 4→Space d) (P:Fin 4→ℝ)
    (hsum:∑ j,z j=0) (hnorm:∑ j,‖z j‖^2=1)
    (hpos:∀ j,z j≠0) (horder:Antitone (fun j=>‖z j‖))
    (hneg:Pairwise (fun j l=>⟪z j,z l⟫<0)) (hcap:∀ j,‖z j‖≤2/3)
    (hprob:∑ j,P j=1) (hPh:∀ j,P j≤1/2)
    (hcap3:∀ j,‖z j‖≤(8/3:ℝ)*P j*(1-P j))
    (hlin:∀ j,0.415*‖z j‖+0.15*‖z j‖^2≤P j)
    (hloss:∀ j,∃ x≥(0:ℝ),p x=P j ∧
      (9/(8*Real.pi))*‖z j‖^2/(1+Real.sqrt (1-(4/3:ℝ)*‖z j‖^2))≤loss x)
    (hpair:∀ i j l, i≠j → i≠l →
      ‖residualVector (z i) (z j)‖^2*‖residualVector (z i) (z l)‖^2-
      ⟪residualVector (z i) (z j),residualVector (z i) (z l)⟫^2≤
      (3/Real.pi)^2*‖z i‖^2*(1+residualCoefficient (z i) (z j))^2*
      (1+residualCoefficient (z i) (z l))^2) : False := by
  have hn:‖z 0‖^2+‖z 1‖^2+‖z 2‖^2+‖z 3‖^2=1 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hnorm
  have hp:P 0+P 1+P 2+P 3=1 := by simpa [Fin.sum_univ_succ,add_assoc] using hprob
  have hq:∀ j,‖z j‖^2≤(2/3:ℝ)^2 := fun j=>(sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hcap j)
  have hquartic:∀ j, (147/500:ℝ)≤‖z j‖ → quartic ‖z j‖≤P j := by
    intro j hj
    by_cases ht:‖z j‖≤79/200
    · obtain ⟨x,hx,hpx,hl⟩:=hloss j
      rw [←hpx]
      exact (quartic_of_loss ⟨hj,ht⟩ hx hl).le
    · exact quartic_from_cap ⟨(le_of_not_ge ht),(hcap j)⟩ (hPh j) (hcap3 j)
  by_cases ht:‖z 3‖≤39/250
  · have ht2:‖z 3‖^2≤(39/250:ℝ)^2 := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr ht
    have h0:(147/500:ℝ)≤‖z 0‖ := by nlinarith only [hn,hq 1,hq 2,ht2,norm_nonneg (z 0)]
    have h1:(147/500:ℝ)≤‖z 1‖ := by nlinarith only [hn,hq 0,hq 2,ht2,norm_nonneg (z 1)]
    have h2:(147/500:ℝ)≤‖z 2‖ := by nlinarith only [hn,hq 0,hq 1,ht2,norm_nonneg (z 2)]
    let a:=residualCoefficient (z 3) (z 0)
    let b:=residualCoefficient (z 3) (z 1)
    let c:=residualCoefficient (z 3) (z 2)
    let u:=residualVector (z 3) (z 0)
    let v:=residualVector (z 3) (z 1)
    let w:=residualVector (z 3) (z 2)
    have ha:0≤a := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠0))).le
    have hb:0≤b := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠1))).le
    have hc:0≤c := (residualCoefficient_pos (hneg (by decide : (3:Fin 4)≠2))).le
    have habc:a+b+c=1 := by
      have hh:=residual_coefficient_sum z hsum 3 (hpos 3)
      have he:(Finset.univ.erase (3:Fin 4))={0,1,2} := by decide
      rw [he] at hh
      simpa [a,b,c,Finset.sum_insert,add_assoc] using hh
    have hs:u+v+w=0 := by
      have hh:=residual_sum z hsum 3 (hpos 3)
      have he:(Finset.univ.erase (3:Fin 4))={0,1,2} := by decide
      rw [he] at hh
      simpa [u,v,w,Finset.sum_insert,add_assoc] using hh
    obtain ⟨hD1,hD2,hD3⟩:=triangle_gram u v w hs
    have hu:‖u‖^2=‖z 0‖^2-a^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hv:‖v‖^2=‖z 1‖^2-b^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hw:‖w‖^2=‖z 2‖^2-c^2*‖z 3‖^2 := residual_norm_sq (hpos 3)
    have hH:‖u‖^2+‖v‖^2+‖w‖^2=1-‖z 3‖^2-(a^2+b^2+c^2)*‖z 3‖^2 := by
      nlinarith only [hu,hv,hw,hn]
    have he0:=hquartic 0 h0
    have he1:=hquartic 1 h1
    have he2:=hquartic 2 h2
    unfold quartic at he0 he1 he2
    have hV:(3/5:ℝ)*(‖u‖^4+‖v‖^4+‖w‖^4)≤(10003/40000:ℝ)-(83/200:ℝ)*‖z 3‖+(81/250:ℝ)*‖z 3‖^2 := by
      nlinarith only [he0,he1,he2,hlin 3,hn,hp,
        residual_fourth_le (z 3) (z 0) (hpos 3),residual_fourth_le (z 3) (z 1) (hpos 3),residual_fourth_le (z 3) (z 2) (hpos 3)]
    apply FourAlgebra.small_exclusion ⟨norm_nonneg _,ht⟩ ha hb hc habc hH hV hD3
    · exact hpair 3 0 1 (by decide) (by decide)
    · rw [hD1]; exact hpair 3 0 2 (by decide) (by decide)
    · rw [hD2]; exact hpair 3 1 2 (by decide) (by decide)
  have htlo:(39/250:ℝ)≤‖z 3‖ := (lt_of_not_ge ht).le
  have hmin:∀ j, ‖z 3‖≤‖z j‖ := fun j=>horder (show j≤3 by omega)
  have haff:∀ j,affine ‖z j‖≤P j := fun j=> affine_from_cap ⟨htlo.trans (hmin j),hcap j⟩ (hPh j) (hcap3 j)
  have ha0:=haff 0; have ha1:=haff 1; have ha2:=haff 2
  unfold affine at ha0 ha1 ha2
  by_cases ht18:‖z 3‖≤9/50
  · obtain ⟨x,hx,hpx,hl⟩:=hloss 3
    have hsmall:=small_of_loss ⟨htlo,ht18⟩ hx hl
    rw [hpx] at hsmall
    unfold small at hsmall
    have hprod:=mul_nonneg (sub_nonneg.mpr htlo) (sub_nonneg.mpr ht18)
    nlinarith only [ha0,ha1,ha2,hsmall,hn,hp,hprod,htlo,ht18]
  by_cases ht40:‖z 3‖≤2/5
  · have hlo:(9/50:ℝ)≤‖z 3‖ := (lt_of_not_ge ht18).le
    have hprod:=mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr ht40)
    nlinarith only [ha0,ha1,ha2,hlin 3,hn,hp,hprod,hlo,ht40]
  have hlarge:∀ j,large ‖z j‖≤P j := by
    intro j
    have hj:(2/5:ℝ)≤‖z j‖ := (le_of_not_ge ht40).trans (hmin j)
    by_cases hj525:‖z j‖≤21/40
    · obtain ⟨x,hx,hpx,hl⟩:=hloss j
      rw [←hpx]
      exact (large_of_loss ⟨hj,hj525⟩ hx hl).le
    · exact large_from_cap ⟨le_of_not_ge hj525,hcap j⟩ (hPh j) (hcap3 j)
  have hl0:=hlarge 0; have hl1:=hlarge 1; have hl2:=hlarge 2; have hl3:=hlarge 3
  unfold large at hl0 hl1 hl2 hl3
  nlinarith only [hl0,hl1,hl2,hl3,hn,hp]

end GaussianPropeller.Reduction

end OAI
