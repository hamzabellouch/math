import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralAnchor
import OAI.Analysis.Conductivity.Geometry.CollarVolumeBound
import OAI.Analysis.Conductivity.Fourier.AngularSignedTrace

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus

def physicalRayConstant : ℝ :=
  1600*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi))

lemma physicalRayConstant_pos : 0<physicalRayConstant := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  unfold physicalRayConstant
  positivity

lemma sourceAngular_volume_in {g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (hn : ∀ y,0≤g y) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    {l r : ℝ} (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hsub : ∀ i j,sourceCollarPiece i j '' sourceExtendedBox l r⊆K) :
    (∫ t in l..r,∫ x : UnitAddTorus (Fin 2),g (sourceAngularCollar t x))≤
      physicalRayConstant*(∫ y in K,g y) := by
  have hh := sourceAngular_volume_bound hg hn hlr hl hr
  have hc : 0≤100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi)) := by
    have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
    positivity
  have hi : IntegrableOn g K := hg.continuousOn.integrableOn_compact hK
  have hm := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => Finset.sum_le_sum (s:=Finset.univ)
    (fun j _ => setIntegral_mono_set hi (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall (hsub i j))))
  have hsum : (∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      16*(∫ y in K,g y) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hm
    change (∑ i : Fin 4,∑ j : Fin 4,∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)≤
      4*(4*(∫ y in K,g y)) at hm
    linarith
  apply hh.trans
  calc
    _≤(100*((1/sourceRadialWidth)/(2*Real.pi))*((1:ℝ)/(2*Real.pi)))*(16*(∫ y in K,g y)) :=
      mul_le_mul_of_nonneg_left hsum hc
    _=_ := by unfold physicalRayConstant; ring

theorem sourceAngular_physical_trace_forward {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (t : ℝ) {η : ℝ} (hη : 0<η) (hl : -(1:ℝ)/100≤t) (hr : t+η≤1/100)
    (hsub : ∀ i j,sourceCollarPiece i j '' sourceExtendedBox t (t+η)⊆K) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      ((1+1/η)*physicalRayConstant)*(∫ y in K,sourcePhysicalEnergy f y) := by
  have ht := sourceAngular_integrated_trace hf t hη
  have he := intervalIntegral.integral_comp_add_left
    (fun a => ∫ x : UnitAddTorus (Fin 2),sourcePhysicalEnergy f (sourceAngularCollar a x))
    (a:=0) (b:=η) t
  rw [he,add_zero] at ht
  have hv := sourceAngular_volume_in (continuous_sourcePhysicalEnergy hf)
    (sourcePhysicalEnergy_nonneg f) hK (by linarith : t≤t+η) hl hr hsub
  exact ht.trans (by have hh := mul_le_mul_of_nonneg_left hv (show 0≤1+1/η by positivity); nlinarith [hh])

theorem sourceAngular_physical_trace_backward {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {K : Set (Fin 3 → ℝ)} (hK : IsCompact K)
    (t : ℝ) {η : ℝ} (hη : 0<η) (hl : -(1:ℝ)/100≤t-η) (hr : t≤1/100)
    (hsub : ∀ i j,sourceCollarPiece i j '' sourceExtendedBox (t-η) t⊆K) :
    (∫ x : UnitAddTorus (Fin 2),(f (sourceAngularCollar t x))^2)≤
      ((1+1/η)*physicalRayConstant)*(∫ y in K,sourcePhysicalEnergy f y) := by
  have ht := sourceAngular_signed_trace hf t (-1) (by norm_num) hη
  simp only [neg_one_mul,←sub_eq_add_neg] at ht
  have he := intervalIntegral.integral_comp_sub_left
    (fun a => ∫ x : UnitAddTorus (Fin 2),sourcePhysicalEnergy f (sourceAngularCollar a x))
    (a:=0) (b:=η) t
  rw [he,sub_zero] at ht
  have hv := sourceAngular_volume_in (continuous_sourcePhysicalEnergy hf)
    (sourcePhysicalEnergy_nonneg f) hK (by linarith : t-η≤t) hl hr hsub
  exact ht.trans (by have hh := mul_le_mul_of_nonneg_left hv (show 0≤1+1/η by positivity); nlinarith [hh])

end

open Set MeasureTheory

def sourcePairEquiv : (Fin 3 → ℝ) ≃ₗ[ℝ] Box3 where
  toFun := sourcePairCoordinates
  invFun := fun z => ![z.1.1,z.1.2,z.2]
  left_inv := by intro x; ext i; fin_cases i <;> rfl
  right_inv := by intro z; rfl
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def sourcePairCLE : (Fin 3 → ℝ) ≃L[ℝ] Box3 := sourcePairEquiv.toContinuousLinearEquiv

def sourcePairMeasurable : (Fin 3 → ℝ) ≃ᵐ Box3 :=
  threeArrow.trans (MeasurableEquiv.prodAssoc (α:=ℝ) (β:=ℝ) (γ:=ℝ)).symm

lemma sourcePairMeasurable_apply (x : Fin 3 → ℝ) : sourcePairMeasurable x=sourcePairCoordinates x := rfl

lemma sourcePair_volume : MeasurePreserving sourcePairMeasurable :=
  (volume_preserving_prodAssoc (α₁:=ℝ) (β₁:=ℝ) (γ₁:=ℝ)).symm.comp threeArrow_volume

def centralPhysical : Set (Fin 3 → ℝ) := sourcePairCoordinates ⁻¹' centralClosed

lemma centralPhysical_compact : IsCompact centralPhysical := by
  exact sourcePairCLE.toHomeomorph.isCompact_preimage.mpr centralClosed_compact

lemma sourcePair_central_image : sourcePairMeasurable '' centralPhysical=centralClosed := by
  exact sourcePairMeasurable.image_preimage centralClosed

lemma integral_centralPhysical (g : Box3 → ℝ) :
    (∫ x in centralPhysical,g (sourcePairCoordinates x))=(∫ z in centralClosed,g z) := by
  have h := sourcePair_volume.setIntegral_image_emb sourcePairMeasurable.measurableEmbedding g centralPhysical
  rw [sourcePair_central_image] at h
  exact h.symm

lemma linear_three_bound (A : (Fin 3 → ℝ) →L[ℝ] ℝ) :
    ‖A‖^2≤3*((A ![1,0,0])^2+(A ![0,1,0])^2+(A ![0,0,1])^2) := by
  have hn : ‖A‖≤|A ![1,0,0]|+|A ![0,1,0]|+|A ![0,0,1]| := by
    apply A.opNorm_le_bound (by positivity)
    intro v
    have he : v=v 0 • ![1,0,0]+v 1 • ![0,1,0]+v 2 • ![0,0,1] := by
      ext i; fin_cases i <;> simp
    have hh := abs_add_le (A (v 0 • ![1,0,0]+v 1 • ![0,1,0])) (A (v 2 • ![0,0,1]))
    have hh' := abs_add_le (A (v 0 • ![1,0,0])) (A (v 1 • ![0,1,0]))
    have hv (i : Fin 3) : |v i|≤‖v‖ := norm_le_pi_norm v i
    conv_lhs => rw [he]
    rw [map_add,map_add,map_smul,map_smul,map_smul]
    change |v 0 * A ![1,0,0]+v 1*A ![0,1,0]+v 2*A ![0,0,1]|≤_
    have ha := abs_add_le (v 0 * A ![1,0,0]+v 1*A ![0,1,0]) (v 2*A ![0,0,1])
    have hb := abs_add_le (v 0 * A ![1,0,0]) (v 1*A ![0,1,0])
    simp only [abs_mul] at ha hb
    have h0 := mul_le_mul_of_nonneg_right (hv 0) (abs_nonneg (A ![1,0,0]))
    have h1 := mul_le_mul_of_nonneg_right (hv 1) (abs_nonneg (A ![0,1,0]))
    have h2 := mul_le_mul_of_nonneg_right (hv 2) (abs_nonneg (A ![0,0,1]))
    nlinarith
  have hs := mul_self_le_mul_self (norm_nonneg A) hn
  nlinarith [sq_abs (A ![1,0,0]),sq_abs (A ![0,1,0]),sq_abs (A ![0,0,1]),
    sq_nonneg (|A ![1,0,0]|-|A ![0,1,0]|),sq_nonneg (|A ![1,0,0]|-|A ![0,0,1]|),
    sq_nonneg (|A ![0,1,0]|-|A ![0,0,1]|)]

lemma sourcePair_energy {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Fin 3 → ℝ) :
    sourcePhysicalEnergy (f ∘ sourcePairCoordinates) x≤
      192*cubeEnergyDensity f (sourcePairCoordinates x)+2*(f (sourcePairCoordinates x))^2 := by
  have he : fderiv ℝ (f ∘ sourcePairCoordinates) x=
      (fderiv ℝ f (sourcePairCoordinates x)).comp sourcePairCLE.toContinuousLinearMap := by
    exact ((hf.differentiable (by simp) _).hasFDerivAt.comp x sourcePairCLE.hasFDerivAt).fderiv
  have hb := linear_three_bound (fderiv ℝ (f ∘ sourcePairCoordinates) x)
  rw [he] at hb
  change ‖(fderiv ℝ f (sourcePairCoordinates x)).comp sourcePairCLE.toContinuousLinearMap‖^2≤
    3*(cubeEnergyDensity f (sourcePairCoordinates x)) at hb
  dsimp [sourcePhysicalEnergy]
  rw [he]
  linarith

end ScalarConductivity

end

end OAI
