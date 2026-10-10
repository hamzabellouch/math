import OAI.NumberTheory.DirichletL.Energy.ZeroBalancedDictionary
import OAI.NumberTheory.DirichletL.Energy.NaturalSourceAdmission

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyZeroBalancedAdmission
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyReferenceState CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentSourceInputTailUniform
open CenteredMomentEnergyOriginalProfileControl CenteredMomentFirstReferenceEnergy
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstPhysicalSource
variable {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(p:Profiles a b)(ha:0<a)
variable (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)
local notation "inp"=>CenteredMomentEnergyZeroReferencePhysical.balancedInput s p ha t X₁ X₂ hX₁ hX₂

theorem fixed_fields :
    (inp).lower=1 ∧ (inp).upper=1 ∧
    (inp).b₁=b ∧ (inp).b₂=b ∧
    (inp).W₁=p.profile 0 ∧ (inp).W₂=p.profile 1 ∧
    (∀i,(inp).lo i=1) ∧ (∀i,(inp).hi i=1) ∧
    (∀i,(inp).M i≤1) ∧ Fintype.card (Fin 0)=0 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_,by simp⟩
  all_goals intro i; exact Fin.elim0 i

lemma lower_product : 0<a*a ∧ (∏i,(inp).lo i)*a*a=a*a := by
  exact ⟨mul_pos ha ha,by simp⟩

lemma profile_control (S:Finset (ℕ×ℕ)) :
    (plainControl inp (p.profile 0) (p.profile 1))^2≤
      (p.control (insert (0,0) S))^2 := by
  simpa using plain_control_sq_le inp p S 0 1 (by norm_num)
    (by simp) (fun i=>Fin.elim0 i)

lemma source_factor (hZ:1<Z) :
    sourceFactor inp a a s.radial.scale≤
      (Real.exp (Real.log 4)*fixedPresentationCost/(a*a))*Z^s.width := by
  have hK:0<s.radial.scale:=s.radial.scale_pos
  have hh:=source_factor_le inp 0 1 a s.radial.scale (by norm_num) ha hK
    (by simp) (fun i=>Fin.elim0 i)
  simp only [pow_zero,one_mul] at hh
  have hcap:=CenteredMomentEnergyPositiveHighParameters.actual_conductor_scale s hZ
  have hc:0≤Real.exp (Real.log 4)*fixedPresentationCost/(a*a):=by
    exact div_nonneg (mul_nonneg (Real.exp_pos _).le fixedPresentationCost_pos.le)
      (mul_pos ha ha).le
  apply hh.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hcap hc

theorem four_upper_scales (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    (inp).X₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).X₂≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₁≤Z^(max Mcap (2*Lgoal)) ∧
    (inp).Y₂≤Z^(max Mcap (2*Lgoal)) := by
  have hLg:Lgoal≤max Mcap (2*Lgoal):=by linarith [le_max_right Mcap (2*Lgoal)]
  have hp:0<Z:=zero_lt_one.trans hZ
  have hquarter:0≤s.width/4:=div_nonneg s.width_nonneg (by norm_num)
  have hY₁:1≤comparisonFirst Z s.width:=Real.one_le_rpow hZ.le hquarter
  refine ⟨hc₁.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),
    hc₂.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hLg),?_,?_⟩
  · change Z^(s.width/4)≤_
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [s.width_nonneg,le_max_left Mcap (2*Lgoal)]
  · change X₁*X₂/comparisonFirst Z s.width≤_
    calc
      _≤X₁*X₂:=div_le_self (mul_pos hX₁ hX₂).le hY₁
      _≤Z^Lgoal*Z^Lgoal:=mul_le_mul hc₁ hc₂ hX₂.le (Real.rpow_pos_of_pos hp _).le
      _=Z^(2*Lgoal):=by rw [←Real.rpow_add hp];congr 1;ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (le_max_right _ _)

theorem capacity_packet (Mcap Lgoal:ℝ)(hZ:1<Z)(hL:0≤Lgoal)
    (hs:s.width≤Mcap)(hc₁:X₁≤Z^Lgoal)(hc₂:X₂≤Z^Lgoal) :
    let Mdecl:=max s.width (length Z X₁+length Z X₂)
    0≤Mdecl ∧ Mdecl≤max Mcap (2*Lgoal) ∧
    volume inp≤Z^Mdecl ∧ volume inp≤Z^(max Mcap (2*Lgoal)) ∧
    1≤s.radial.scale ∧ s.radial.scale⁻¹≤1 ∧
    Real.logb Z s.radial.scale+Real.logb Z (s.character.modulus.absNorm:ℝ)≤s.width ∧
    s.radial.scale*(s.character.modulus.absNorm:ℝ)≤Z^s.width := by
  have hd:=CenteredMomentEnergyZeroBalancedDictionary.declared_capacity s p ha t X₁ X₂ hX₁ hX₂ hZ
  have hu:=CenteredMomentEnergyZeroBalancedDictionary.declared_capacity_upper s X₁ X₂ Mcap Lgoal hZ hL hs hc₁ hc₂
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission s
  exact ⟨s.width_nonneg.trans (le_max_left _ _),hu,hd.2.2.2,
    hd.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hu),hr.1,hr.2.1,hd.2.1,hd.2.2.1⟩

end SevenEighths.CenteredMomentEnergyZeroBalancedAdmission

end

end OAI
