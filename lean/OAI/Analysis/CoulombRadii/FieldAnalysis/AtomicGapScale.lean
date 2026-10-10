import Mathlib
import OAI.Analysis.CoulombRadii.Screening.UniformCountConsequences
import OAI.Analysis.CoulombRadii.ThomasFermi.AtomicRefinedGap
import OAI.Analysis.CoulombRadii.RandomFields.ObservationSmallScale

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace Coulomb

def atomicRefinedFormula (δ P m a b : ℝ) : ℝ :=
  (δ+thinReserveFactor*(Real.sqrt P*m/b^2))+
    12*a*unitWindowKinetic/b^2*Real.sqrt (atomicPhysicalCapConstant*P*m^2/a^2)+
    Real.sqrt ((atomicPhysicalCapConstant*P*m^2/a^2)*
      (18*atomicPatchCountFactor*(b/a)*P*m^2))+
    (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(atomicPatchCountFactor*P*m^2)^(2/3:ℝ)+
    ((2*Real.pi+1)/(2*b))*Real.sqrt (atomicPatchCountFactor*P*m^2)

lemma atomicRefinedFormula_mono {δ δ' P P' m m' a b : ℝ}
    (hd : δ ≤ δ') (hP : 0 ≤ P) (hPP : P ≤ P') (hm : 0 ≤ m) (hmm : m ≤ m')
    (ha : 0<a) (hb : 0<b) :
    atomicRefinedFormula δ P m a b ≤ atomicRefinedFormula δ' P' m' a b := by
  have hP' := hP.trans hPP
  have hm' := hm.trans hmm
  have hA := atomicPhysicalCapConstant_nonneg
  have hB := atomicPatchCountFactor_nonneg
  have hT := thinReserveFactor_nonneg
  have hU := unitWindowKinetic_nonneg
  have hN := neumannBoundary_nonneg
  unfold atomicRefinedFormula
  gcongr

lemma atomicRefinedError_eq_formula (δ P a b : ℝ) :
    atomicRefinedError δ P a b=atomicRefinedFormula δ P (screenMass δ a) a b := rfl

lemma atomicRefinedError_small_bound {δ P a : ℝ} (hδ : 0 ≤ δ)
    (hP : 0 ≤ P) (hPP : P ≤ atomicCountConstant) (ha : 0<a) (ha1 : a ≤ 1)
    (hd : δ ≤ a^(-349/50:ℝ)) :
    atomicRefinedError δ P a (a^(6/5:ℝ)) ≤
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) := by
  have hsmall : δ*a^7 ≤ 1 := by
    calc
      δ*a^7 ≤ a^(-349/50:ℝ)*a^7 := mul_le_mul_of_nonneg_right hd (pow_nonneg ha.le _)
      _ = a^(1/50:ℝ) := by rw [←Real.rpow_natCast a 7,←Real.rpow_add ha]; norm_num
      _ ≤ 1 := Real.rpow_le_one ha.le ha1 (by norm_num)
  have hm := NeutralAtom.screenMass_small_offset ha ha1 hδ hsmall
  have hm' : screenMass δ a ≤ 2*a^(-3:ℝ) := by
    simpa only [Real.rpow_neg ha.le,Real.rpow_ofNat,div_eq_mul_inv] using hm
  rw [atomicRefinedError_eq_formula]
  exact atomicRefinedFormula_mono hd hP hPP (screenMass_pos _ _).le hm' ha (Real.rpow_pos_of_pos ha _)

lemma mul_rpow_monomials {a : ℝ} (ha : 0<a) (c d x y : ℝ) :
    (c*a^x)*(d*a^y)=(c*d)*a^(x+y) := by rw [Real.rpow_add ha]; ring

lemma sqrt_rpow_monomial {a : ℝ} (ha : 0<a) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    Real.sqrt (c*a^x)=Real.sqrt c*a^(x/2) := by
  rw [Real.sqrt_mul hc]
  simp only [Real.sqrt_eq_rpow]
  rw [←Real.rpow_mul ha.le]
  congr 2
  ring

lemma div_rpow_monomial {a : ℝ} (ha : 0<a) (c x y : ℝ) :
    (c*a^x)/a^y=c*a^(x-y) := by rw [Real.rpow_sub ha]; ring

lemma atomicRefinedFormula_power_expansion {a P : ℝ} (ha : 0<a) (hP : 0 ≤ P) :
    atomicRefinedFormula (a^(-349/50:ℝ)) P (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) =
      a^(-349/50:ℝ)+
      (2*thinReserveFactor*Real.sqrt P)*a^(-27/5:ℝ)+
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*a^(-27/5:ℝ)+
      Real.sqrt (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)*a^(-69/10:ℝ)+
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*a^(-32/5:ℝ)+
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-21/5:ℝ) := by
  have hm2 : (2*a^(-3:ℝ))^2=4*a^(-6:ℝ) := by
    rw [mul_pow,←Real.rpow_mul_natCast ha.le]
    norm_num
  have hb2 : (a^(6/5:ℝ))^2=a^(12/5:ℝ) := by
    rw [←Real.rpow_mul_natCast ha.le]
    norm_num
  have hq : atomicPhysicalCapConstant*P*(2*a^(-3:ℝ))^2/a^2=
      (4*atomicPhysicalCapConstant*P)*a^(-8:ℝ) := by
    rw [hm2]
    calc
      _ = ((4*atomicPhysicalCapConstant*P)*a^(-6:ℝ))/a^2 := by ring
      _ = _ := by rw [←Real.rpow_natCast a 2,div_rpow_monomial ha]; norm_num
  have hn : atomicPatchCountFactor*P*(2*a^(-3:ℝ))^2=
      (4*atomicPatchCountFactor*P)*a^(-6:ℝ) := by rw [hm2]; ring
  have hd : 18*atomicPatchCountFactor*(a^(6/5:ℝ)/a)*P*(2*a^(-3:ℝ))^2=
      (72*atomicPatchCountFactor*P)*a^(-29/5:ℝ) := by
    rw [hm2]
    calc
      _ = ((72*atomicPatchCountFactor*P)*(a^(6/5:ℝ)*a^(-6:ℝ)))/a^1 := by ring
      _ = _ := by rw [←Real.rpow_add ha,←Real.rpow_natCast a 1,div_rpow_monomial ha]; norm_num
  have hqd : ((4*atomicPhysicalCapConstant*P)*a^(-8:ℝ))*
      ((72*atomicPatchCountFactor*P)*a^(-29/5:ℝ))=
      (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)*a^(-69/5:ℝ) := by
    rw [mul_rpow_monomials ha]
    congr 1 <;> ring_nf
  have hN0 : 0 ≤ 4*atomicPatchCountFactor*P := by positivity [atomicPatchCountFactor_nonneg]
  have hQ0 : 0 ≤ 4*atomicPhysicalCapConstant*P := by positivity [atomicPhysicalCapConstant_nonneg]
  have hQD0 : 0 ≤ 288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2 := by
    positivity [atomicPhysicalCapConstant_nonneg,atomicPatchCountFactor_nonneg]
  have hn23 : ((4*atomicPatchCountFactor*P)*a^(-6:ℝ))^(2/3:ℝ)=
      (4*atomicPatchCountFactor*P)^(2/3:ℝ)*a^(-4:ℝ) := by
    rw [Real.mul_rpow hN0 (Real.rpow_nonneg ha.le _),←Real.rpow_mul ha.le]
    norm_num
  have hsi : ((a^(6/5:ℝ))⁻¹)^2=a^(-12/5:ℝ) := by
    rw [←Real.rpow_neg ha.le,←Real.rpow_mul_natCast ha.le]
    norm_num
  unfold atomicRefinedFormula
  rw [hq,hn,hd,hqd,hb2,hsi,hn23,sqrt_rpow_monomial ha hQ0,
    sqrt_rpow_monomial ha hN0,sqrt_rpow_monomial ha hQD0]
  norm_num only
  have h1 : thinReserveFactor*(Real.sqrt P*(2*a^(-3:ℝ))/a^(12/5:ℝ))=
      (2*thinReserveFactor*Real.sqrt P)*a^(-27/5:ℝ) := by
    calc
      _ = (2*thinReserveFactor*Real.sqrt P)*a^(-3:ℝ)/a^(12/5:ℝ) := by ring
      _ = _ := by rw [div_rpow_monomial ha]; norm_num
  have h2 : 12*a*unitWindowKinetic/a^(12/5:ℝ)*
      (Real.sqrt (4*atomicPhysicalCapConstant*P)*a^(-4:ℝ))=
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*a^(-27/5:ℝ) := by
    calc
      _ = (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P))*(a^1*a^(-4:ℝ))/a^(12/5:ℝ) := by ring
      _ = _ := by rw [←Real.rpow_natCast a 1,←Real.rpow_add ha,div_rpow_monomial ha]; norm_num
  have h4 : a^(-12/5:ℝ)*((Real.pi^2/2)*neumannBoundary)*
      ((4*atomicPatchCountFactor*P)^(2/3:ℝ)*a^(-4:ℝ))=
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*a^(-32/5:ℝ) := by
    calc
      _ = (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ))*(a^(-12/5:ℝ)*a^(-4:ℝ)) := by ring
      _ = _ := by rw [←Real.rpow_add ha]; norm_num
  have h5 : ((2*Real.pi+1)/(2*a^(6/5:ℝ)))*(Real.sqrt (4*atomicPatchCountFactor*P)*a^(-3:ℝ))=
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-21/5:ℝ) := by
    calc
      _ = ((((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P))*a^(-3:ℝ))/a^(6/5:ℝ) := by ring
      _ = _ := by rw [div_rpow_monomial ha]; norm_num
  norm_num at h1 h2 h4 h5 ⊢
  rw [h1,h2,h4,h5]

lemma atomicRefinedFormula_scaled_tendsto {P : ℝ} (hP : 0 ≤ P) :
    Tendsto (fun a : ℝ => atomicRefinedFormula (a^(-349/50:ℝ)) P
      (2*a^(-3:ℝ)) a (a^(6/5:ℝ))*a^(349/50:ℝ)) (𝓝[>] 0) (𝓝 1) := by
  have ht := (((((tendsto_const_nhds (x := (1:ℝ))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<79/50)).const_mul
      (2*thinReserveFactor*Real.sqrt P))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<79/50)).const_mul
      (12*unitWindowKinetic*Real.sqrt (4*atomicPhysicalCapConstant*P)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<2/25)).const_mul
      (Real.sqrt (288*atomicPhysicalCapConstant*atomicPatchCountFactor*P^2)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<29/50)).const_mul
      (((Real.pi^2/2)*neumannBoundary)*(4*atomicPatchCountFactor*P)^(2/3:ℝ)))).add
    ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<139/50)).const_mul
      (((2*Real.pi+1)/2)*Real.sqrt (4*atomicPatchCountFactor*P)))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha : 0<a := ha
  rw [atomicRefinedFormula_power_expansion ha hP]
  simp only [add_mul,mul_assoc,←Real.rpow_add ha]
  norm_num

lemma exists_atomic_refined_small_scale : ∃ s : ℝ, 0<s ∧ s≤1 ∧
    ∀ a : ℝ, 0<a → a<s →
      18*a^(6/5:ℝ)≤a ∧
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant
        (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) ≤ 2*a^(-349/50:ℝ) := by
  have hP : 0 ≤ atomicCountConstant := le_trans (by norm_num) atomicCountConstant_ge_two
  have he := (atomicRefinedFormula_scaled_tendsto hP).eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2))
  have hs := ((NeutralAtom.tendsto_positive_rpow_zero (by norm_num : (0:ℝ)<1/5)).const_mul 18).eventually
    (gt_mem_nhds (by norm_num : (18:ℝ)*0<1))
  have hh : ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 ∧
      atomicRefinedFormula (a^(-349/50:ℝ)) atomicCountConstant
        (2*a^(-3:ℝ)) a (a^(6/5:ℝ))*a^(349/50:ℝ)<2 ∧ 18*a^(1/5:ℝ)<1 := by
    filter_upwards [he,hs, (show ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 from
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds)] with a ha hb hc
    exact ⟨hc,ha,hb⟩
  obtain ⟨s,hs0,hprop⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hh
  refine ⟨min s 1, lt_min hs0 (by norm_num), min_le_right _ _, ?_⟩
  intro a ha has
  have hp := hprop ⟨ha, has.trans_le (min_le_left s 1)⟩
  constructor
  · have hx : a^(6/5:ℝ)=a^(1/5:ℝ)*a := by
      rw [show (6/5:ℝ)=1/5+1 by norm_num,Real.rpow_add ha,Real.rpow_one]
    rw [hx]
    nlinarith [mul_lt_mul_of_pos_right hp.2.2 ha]
  · have hx : a^(-349/50:ℝ)*a^(349/50:ℝ)=1 := by rw [←Real.rpow_add ha]; norm_num
    apply le_of_mul_le_mul_right (a := a^(349/50:ℝ)) _ (Real.rpow_pos_of_pos ha (349/50:ℝ))
    rw [mul_assoc,hx,mul_one]
    exact hp.2.1.le

end Coulomb
end

end
end

end OAI
