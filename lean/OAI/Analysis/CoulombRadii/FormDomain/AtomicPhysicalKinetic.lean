import Mathlib
import OAI.Analysis.CoulombRadii.Packets.AtomicSmallPatch
import OAI.Analysis.CoulombRadii.LimitTheory.AtomicOutKinetic

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

theorem RecordedEnsemble.atomic_outerKinetic_le {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (T : RecordedEnsemble n) (ha : T.CoreFermionic)
    {y : Space} (hy : y≠0) (hs : T.OutSupported (Metric.closedBall y (80*atomicCellScale y)))
    {E : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) :
    (∑ p,outerKinetic (T.vector p))≤T.totalForm S-E*T.totalMass+
      (atomicCellScale y/2)*(∑ p,sliceExpectation (T.vector p) (fun s x => (atomicPatchCap S ((T.vector p).coreSlice s x).normalized x y)^2))+
      (∑ p,(T.out p:ℝ)^2*mass (T.vector p))/(2*atomicCellScale y) := by
  have H := Finset.sum_le_sum (fun (p : T.index) (_ : p∈Finset.univ) =>
    Coulomb.atomic_outerKinetic_le S hatom (T.vector p) (ha p).coreSlice hy (hs p) hE)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at H
  apply H.trans_eq
  unfold totalForm totalMass
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem exists_atomic_physical_kinetic {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ j,S.position j=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      (∑ p,outerKinetic (T.ensemble.vector p))≤
        δ+thinReserveFactor*(Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)/b^2)+
          (atomicPhysicalCapConstant+atomicPatchCountFactor)*screenCountParameter ψ δ*
            (screenMass δ (atomicCellScale y))^2/(2*atomicCellScale y) := by
  let a := atomicCellScale y
  let P := screenCountParameter ψ δ
  let m := screenMass δ a
  have ha : 0<a := atomicCellScale_pos hy
  have hP : 0≤P := le_trans zero_le_one (screenCountParameter_ge_one ψ δ)
  obtain ⟨t,ht,T,hEt,ho,hcs,hos,hD,hN,hraw⟩ :=
    exists_atomic_thin_screened_sharp S hatom ψ hψ hm hE hstate hδ hy hb hsmall hcond
  let Q := ∑ p,sliceExpectation (T.ensemble.vector p) (fun s x => (atomicPatchCap S ((T.ensemble.vector p).coreSlice s x).normalized x y)^2)
  let N := ∑ p,(T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p)
  have hwidth : t+b≤80*a := by dsimp only [a] at *; linarith [ht.2]
  have hQ : Q≤atomicPhysicalCapConstant*P*m^2/a^2 := by
    have HQ := atomicPatchCap_ensemble_square S hatom T.ensemble hy
      (H := (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2)
      (fun v hv => (Real.sqrt_le_iff.mp (hraw v hv)).2)
    change Q≤_ at HQ
    calc
      Q≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+8*N/(9*a^2) := HQ
      _≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+
        8*(atomicPatchCountFactor*P*m^2)/(9*a^2) := add_le_add le_rfl
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (by positivity))
      _=atomicPhysicalCapConstant*P*m^2/a^2 := by
        dsimp only [atomicPhysicalCapConstant,screenFieldUnit,m]
        simp only [mul_pow,div_pow,Real.sq_sqrt hP]
        ring
  have hs : T.ensemble.OutSupported (Metric.closedBall y (80*a)) := by
    intro p s
    filter_upwards [hos p s] with x hx
    intro i hi hn
    exact hx i hi (fun hh => hn (Metric.closedBall_subset_closedBall hwidth hh))
  have HK := RecordedEnsemble.atomic_outerKinetic_le S hatom T.ensemble T.fermionic hy hs hE
  rw [T.mass_eq,hm,mul_one] at HK
  have hB := thinIMS_sharp_budget ψ hm hδ hP
    (fun z hz => screenCountParameter_controls ψ hm δ hz) hy hb hwidth
  have hq := mul_le_mul_of_nonneg_left hQ (show 0≤a/2 by positivity)
  have hn := div_le_div_of_nonneg_right hN (show 0≤2*a by positivity)
  refine ⟨t,ht,T,hEt,ho,hcs,hos,?_⟩
  change _≤δ+thinReserveFactor*(Real.sqrt P*m/b^2)+(atomicPhysicalCapConstant+atomicPatchCountFactor)*P*m^2/(2*a)
  have hident : (a/2)*(atomicPhysicalCapConstant*P*m^2/a^2)+atomicPatchCountFactor*P*m^2/(2*a)=
      (atomicPhysicalCapConstant+atomicPatchCountFactor)*P*m^2/(2*a) := by field_simp
  change _≤T.ensemble.totalForm S-E+(a/2)*Q+N/(2*a) at HK
  dsimp only [m,P,a] at hq hn hident hB HK ⊢
  linarith

end Coulomb

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

def atomicKineticFormula (δ P m a b : ℝ) : ℝ :=
  δ+thinReserveFactor*(Real.sqrt P*m/b^2)+
    (atomicPhysicalCapConstant+atomicPatchCountFactor)*P*m^2/(2*a)

def atomicKineticConstant : ℝ := 1+2*thinReserveFactor*Real.sqrt atomicCountConstant+
  2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant

lemma atomicKineticFormula_small {δ P a : ℝ} (hδ : 0≤δ)
    (hP : 0≤P) (hPP : P≤atomicCountConstant) (ha : 0<a) (ha1 : a≤1)
    (hd : δ≤a^(-349/50:ℝ)) :
    atomicKineticFormula δ P (screenMass δ a) a (a^(6/5:ℝ))≤atomicKineticConstant*a^(-7:ℝ) := by
  have hsmall : δ*a^7≤1 := by
    calc
      δ*a^7≤a^(-349/50:ℝ)*a^7 := mul_le_mul_of_nonneg_right hd (pow_nonneg ha.le _)
      _=a^(1/50:ℝ) := by rw [←Real.rpow_natCast a 7,←Real.rpow_add ha]; norm_num
      _≤1 := Real.rpow_le_one ha.le ha1 (by norm_num)
  have hm : screenMass δ a≤2*a^(-3:ℝ) := by
    simpa only [Real.rpow_neg ha.le,Real.rpow_ofNat,div_eq_mul_inv] using
      NeutralAtom.screenMass_small_offset ha ha1 hδ hsmall
  have hmn := (screenMass_pos δ a).le
  have hA := atomicPhysicalCapConstant_nonneg
  have hB := atomicPatchCountFactor_nonneg
  have hT := thinReserveFactor_nonneg
  have hC := hP.trans hPP
  have hbound : atomicKineticFormula δ P (screenMass δ a) a (a^(6/5:ℝ))≤
      atomicKineticFormula (a^(-349/50:ℝ)) atomicCountConstant (2*a^(-3:ℝ)) a (a^(6/5:ℝ)) := by
    unfold atomicKineticFormula
    gcongr
  have he : atomicKineticFormula (a^(-349/50:ℝ)) atomicCountConstant (2*a^(-3:ℝ)) a (a^(6/5:ℝ))=
      a^(-349/50:ℝ)+(2*thinReserveFactor*Real.sqrt atomicCountConstant)*a^(-27/5:ℝ)+
        (2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant)*a^(-7:ℝ) := by
    have hm2 : (2*a^(-3:ℝ))^2=4*a^(-6:ℝ) := by
      rw [mul_pow,←Real.rpow_mul_natCast ha.le]; norm_num
    have hb2 : (a^(6/5:ℝ))^2=a^(12/5:ℝ) := by rw [←Real.rpow_mul_natCast ha.le]; norm_num
    unfold atomicKineticFormula
    rw [hm2,hb2]
    have h1 : Real.sqrt atomicCountConstant*(2*a^(-3:ℝ))/a^(12/5:ℝ)=
        (2*Real.sqrt atomicCountConstant)*a^(-27/5:ℝ) := by
      rw [show Real.sqrt atomicCountConstant*(2*a^(-3:ℝ))=(2*Real.sqrt atomicCountConstant)*a^(-3:ℝ) by ring,
        div_rpow_monomial ha]
      norm_num
    rw [h1]
    have h2 : (atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant*(4*a^(-6:ℝ))/(2*a)=
        (2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant)*a^(-7:ℝ) := by
      calc
        _=((2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant)*a^(-6:ℝ))/a := by ring
        _=_ := by
          have H := div_rpow_monomial ha (2*(atomicPhysicalCapConstant+atomicPatchCountFactor)*atomicCountConstant) (-6) 1
          simp only [Real.rpow_one] at H
          convert H using 1
          norm_num
    rw [h2]
    ring
  rw [he] at hbound
  have h1 : a^(-349/50:ℝ)≤a^(-7:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)
  have h2 : a^(-27/5:ℝ)≤a^(-7:ℝ) := Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num)
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0≤2*thinReserveFactor*Real.sqrt atomicCountConstant by positivity)
  unfold atomicKineticConstant
  nlinarith

theorem exists_atomic_small_kinetic : ∃ s : ℝ, 0<s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i,S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ (y : Space), y≠0 → atomicCellScale y<s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(atomicCellScale y)^(6/5:ℝ))) ∧
      (∑ p,outerKinetic (T.ensemble.vector p))≤atomicKineticConstant*(atomicCellScale y)^(-7:ℝ) := by
  obtain ⟨s,hs,hs1,hbound⟩ := exists_atomic_refined_small_scale
  refine ⟨s,hs,hs1,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have ha1 : a≤1 := hys.le.trans hs1
  obtain ⟨hsmall,_⟩ := hbound a ha hys
  obtain ⟨t,ht,T,hEt,ho,hcs,hos,hK⟩ := exists_atomic_physical_kinetic S hatom ψ hψ hm hE hstate hδ
    hy (Real.rpow_pos_of_pos ha (6/5:ℝ)) hsmall
    (source_patch_scale_condition ha ha1 (screenCountParameter_ge_one ψ δ))
  refine ⟨t,ht,T,ho,hcs,hos,hK.trans ?_⟩
  exact atomicKineticFormula_small hδ (le_trans zero_le_one (screenCountParameter_ge_one ψ δ))
    (screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ) ha ha1 hd
end Coulomb

end

end OAI
