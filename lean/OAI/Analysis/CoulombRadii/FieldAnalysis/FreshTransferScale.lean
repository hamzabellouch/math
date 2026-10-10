import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicNear
import OAI.Analysis.CoulombRadii.FieldAnalysis.FreshFieldTransfer
import OAI.Analysis.CoulombRadii.Localization.AtomicRetainedGap

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma transfer_radius_le {a : ℝ} (ha : 0<a) (ha1 : a≤1) :
    a^(6/5:ℝ)≤a^(101/100:ℝ) ∧ a^(101/100:ℝ)≤a := by
  exact ⟨Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num),
    by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (1:ℝ)≤101/100)⟩

lemma transfer_near_power {a : ℝ} (ha : 0<a) {R : ℝ}
    (hR : 0≤R) (hRb : R≤3*a^(101/100:ℝ)) (C : ℝ) (hC : 0≤C) :
    C*a^(-21/5:ℝ)*R^(1/5:ℝ)≤(C*3^(1/5:ℝ))*a^(-1999/500:ℝ) := by
  calc
    _≤C*a^(-21/5:ℝ)*(3*a^(101/100:ℝ))^(1/5:ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR hRb (by norm_num)) (by positivity)
    _=(C*3^(1/5:ℝ))*a^(-1999/500:ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3) (Real.rpow_nonneg ha.le _),←Real.rpow_mul ha.le]
      calc
        _=(C*3^(1/5:ℝ))*(a^(-21/5:ℝ)*a^((101/100)*(1/5):ℝ)) := by ring
        _=_ := by rw [←Real.rpow_add ha]; norm_num

lemma transfer_gap_power {a : ℝ} (ha : 0<a) :
    a^(-799/200:ℝ)+(5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*(2*a^(-349/50:ℝ))=
      (7/2:ℝ)*a^(-799/200:ℝ) := by
  have he : (5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*(2*a^(-349/50:ℝ))=
      (5/2:ℝ)*a^(-799/200:ℝ) := by
    calc
      _=((5/2:ℝ)*a^(-349/50:ℝ))/(a^(101/100:ℝ)*a^(-799/200:ℝ)) := by ring
      _=_ := by rw [←Real.rpow_add ha,div_rpow_monomial ha]; norm_num
  rw [he]
  ring

lemma transfer_deleted_power {a C : ℝ} (ha : 0<a) (hC : 0≤C) :
    Real.sqrt (C*a^(-29/5:ℝ))/a=Real.sqrt C*a^(-39/10:ℝ) := by
  rw [sqrt_rpow_monomial ha hC]
  conv_lhs => arg 2; rw [←Real.rpow_one a]
  rw [div_rpow_monomial ha]
  norm_num

lemma transfer_tfnear_power {a : ℝ} (ha : 0<a) (K : ℝ) :
    (K/a^6)*(2*Real.pi*(a^(101/100:ℝ))^2)=(2*Real.pi*K)*a^(-199/50:ℝ) := by
  rw [←Real.rpow_mul_natCast ha.le]
  calc
    _=((2*Real.pi*K)*a^((101/100)*2:ℝ))/a^6 := by ring_nf
    _=_ := by rw [←Real.rpow_natCast a 6,div_rpow_monomial ha]; norm_num

lemma transfer_power_budget {a C D K : ℝ} (ha : 0<a) (ha1 : a≤1)
    (hC : 0≤C) (hD : 0≤D) (hK : 0≤K) :
    a^(-799/200:ℝ)+(5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*(2*a^(-349/50:ℝ))+
      C*a^(-21/5:ℝ)*(a^(101/100:ℝ)+2*a^(6/5:ℝ))^(1/5:ℝ)+
      C*a^(-21/5:ℝ)*(2*a^(6/5:ℝ))^(1/5:ℝ)+
      Real.sqrt (D*a^(-29/5:ℝ))/a+(K/a^6)*(2*Real.pi*(a^(101/100:ℝ))^2)≤
      (7/2+2*C*3^(1/5:ℝ)+Real.sqrt D+2*Real.pi*K)*a^(-1999/500:ℝ) := by
  obtain ⟨hbr,hra⟩ := transfer_radius_le ha ha1
  have hN₁ := transfer_near_power ha (by positivity : 0≤a^(101/100:ℝ)+2*a^(6/5:ℝ))
    (by linarith : a^(101/100:ℝ)+2*a^(6/5:ℝ)≤3*a^(101/100:ℝ)) C hC
  have hN₂ := transfer_near_power ha (by positivity : 0≤2*a^(6/5:ℝ))
    (by linarith [Real.rpow_nonneg ha.le (101/100:ℝ)] : 2*a^(6/5:ℝ)≤3*a^(101/100:ℝ)) C hC
  have h1 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (-1999/500:ℝ)≤-799/200)) (by norm_num : (0:ℝ)≤7/2)
  have h2 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (-1999/500:ℝ)≤-39/10)) (Real.sqrt_nonneg D)
  have h3 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge ha ha1 (by norm_num : (-1999/500:ℝ)≤-199/50)) (by positivity : 0≤2*Real.pi*K)
  rw [transfer_gap_power ha,transfer_deleted_power ha hD,transfer_tfnear_power ha]
  nlinarith
end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

def atomicPatchMeanField {J n : ℕ} (S : Nuclei J) (hatom : ∀ i,S.position i=0)
    (T : RecordedEnsemble n) (y : Space) (hy : y≠0) (b : ℝ) (hb : 0<b)
    (t : ℝ) (ht : t≤6*atomicCellScale y) : ℝ :=
  ∑ p,sliceExpectation (T.vector p) (fun s x =>
    patchTFScreenedField S ((T.vector p).coreSlice s x).normalized
      (atomicCellScale_pos hy) hb ht y (atomic_patch_nucleus_distance S hatom y) y)

def atomicTransferConstant : ℝ := 7/2+2*atomicNearConstant*3^(1/5:ℝ)+
  Real.sqrt (72*atomicPatchCountFactor*atomicCountConstant)+
  2*Real.pi*(tfInteriorConstant thomasFermiKineticConstant/
    (thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)

lemma atomicTransferConstant_nonneg : 0≤atomicTransferConstant := by
  unfold atomicTransferConstant
  positivity [atomicNearConstant_nonneg,atomicPatchCountFactor_nonneg,atomicCountConstant_ge_two,
    tfInteriorConstant_nonneg thomasFermiKineticConstant,thomasFermiKineticConstant_pos]

theorem exists_atomic_fresh_field_transfer : ∃ s : ℝ, 0<s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J) (hatom : ∀ i,S.position i=0)
    (u : H1Vector n), Antisymmetric u → mass u=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S u≤E+δ → 0≤δ →
    ∀ (y : Space) (hy : y≠0), atomicCellScale y<s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S u (thinIMS u y t ((atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤form S u+thinIMS u y t ((atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(atomicCellScale y)^(6/5:ℝ))) ∧
      atomicPatchTFGap S hatom T.ensemble y hy ((atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (atomicCellScale_pos hy) _) t ht.2≤2*(atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((atomicCellScale y)^(6/5:ℝ))≤
        (72*atomicPatchCountFactor*atomicCountConstant)*(atomicCellScale y)^(-29/5:ℝ) ∧
      |coreScreenedField S u y-atomicPatchMeanField S hatom T.ensemble y hy
        ((atomicCellScale y)^(6/5:ℝ)) (Real.rpow_pos_of_pos (atomicCellScale_pos hy) _) t ht.2|≤
        atomicTransferConstant*(atomicCellScale y)^(-1999/500:ℝ) := by
  obtain ⟨s₀,hs₀,hs₀1,Hpatch⟩ := exists_atomic_small_gap_with_deleted
  obtain ⟨s₁,hs₁,hs₁1,Hnear⟩ := exists_atomic_near_scale
  obtain ⟨s₂,hs₂,hs₂1,Hscale⟩ := exists_atomic_refined_small_scale
  refine ⟨min s₀ (min s₁ s₂),lt_min hs₀ (lt_min hs₁ hs₂),
    (min_le_left _ _).trans hs₀1,?_⟩
  intro J n S hatom u hu hm E δ hE he hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have ha₀ : a<s₀ := hys.trans_le (min_le_left _ _)
  have ha₁ : a<s₁ := hys.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have ha₂ : a<s₂ := hys.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ha1 : a≤1 := ha₀.le.trans hs₀1
  have hsmall := (Hscale a ha ha₂).1
  have hb : 0<a^(6/5:ℝ) := Real.rpow_pos_of_pos ha _
  have hr : 0<a^(101/100:ℝ) := Real.rpow_pos_of_pos ha _
  have hε : 0<a^(-799/200:ℝ) := Real.rpow_pos_of_pos ha _
  obtain ⟨hbr,hra⟩ := transfer_radius_le ha ha1
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hgap,hdel⟩ := Hpatch S hatom u hu hm hE he hδ y hy ha₀ hd
  refine ⟨t,ht,T,hT,ho,hcs,hos,hgap,hdel,?_⟩
  have HF := fresh_patch_field_transfer S T.ensemble u T.law (T.mass_eq.trans hm)
    ha hb hsmall ht y (atomic_patch_nucleus_distance S hatom y) hr hra hε hcs
  change |coreScreenedField S u y-atomicPatchMeanField S hatom T.ensemble y hy
      (a^(6/5:ℝ)) hb t ht.2|≤
    a^(-799/200:ℝ)+(5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)))*
      atomicPatchTFGap S hatom T.ensemble y hy (a^(6/5:ℝ)) hb t ht.2+
    potentialForm (nearPotential y (a^(101/100:ℝ)+2*a^(6/5:ℝ))) u+
    potentialForm (nearPotential y (2*a^(6/5:ℝ))) u+Real.sqrt (T.ensemble.deletedSquare y t (a^(6/5:ℝ)))/a+
    ((tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ)/a^6)*
      (2*Real.pi*(a^(101/100:ℝ))^2) at HF
  have HN₁ := Hnear S hatom u hu hm hE he hδ y hy ha₁ hd
    (R := a^(101/100:ℝ)+2*a^(6/5:ℝ)) (by positivity) (by change _≤4*a; linarith)
  have HN₂ := Hnear S hatom u hu hm hE he hδ y hy ha₁ hd
    (R := 2*a^(6/5:ℝ)) (by positivity) (by change _≤4*a; linarith)
  have HG := mul_le_mul_of_nonneg_left hgap (show 0≤5/(4*a^(101/100:ℝ)*a^(-799/200:ℝ)) by positivity)
  have HD := div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hdel) ha.le
  have Hpower := transfer_power_budget ha ha1 atomicNearConstant_nonneg
    (show 0≤72*atomicPatchCountFactor*atomicCountConstant by positivity [atomicPatchCountFactor_nonneg,atomicCountConstant_ge_two])
    (show 0≤(tfInteriorConstant thomasFermiKineticConstant/(thomasFermiKineticConstant*(5/3:ℝ)))^(3/2:ℝ) by
      positivity [tfInteriorConstant_nonneg thomasFermiKineticConstant,thomasFermiKineticConstant_pos])
  change _≤atomicTransferConstant*a^(-1999/500:ℝ)
  unfold atomicTransferConstant
  dsimp only [a] at HF HN₁ HN₂ HG HD Hpower ⊢
  linarith
end Coulomb

end

end OAI
