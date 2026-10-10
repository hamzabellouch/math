import Mathlib
import OAI.Analysis.Conductivity.Branching.AlignedEndingRegularity

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

def axialFluxBlend (χ : ℝ → ℝ) (F G : Coord3 → Coord3) (x : Coord3) : Coord3 :=
  fun i => (1-χ (x 0))*F x i+χ (x 0)*G x i

lemma axialFluxBlend_C1 {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {F G : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) : ContDiff ℝ 1 (axialFluxBlend χ F G) := by
  apply contDiff_pi.mpr
  intro i
  exact ((contDiff_const.sub (hχ.comp (contDiff_apply ℝ ℝ 0))).mul (contDiff_pi.mp hF i)).add
    ((hχ.comp (contDiff_apply ℝ ℝ 0)).mul (contDiff_pi.mp hG i))

lemma axialFluxBlend_divergence {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {F G : Coord3 → Coord3}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) (x : Coord3) :
    coordinateDivergence (axialFluxBlend χ F G) x=
      (1-χ (x 0))*coordinateDivergence F x+χ (x 0)*coordinateDivergence G x+
        deriv χ (x 0)*(G x 0-F x 0) := by
  have hf (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x := differentiableAt_pi.mp (hF x) i
  have hg (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x := differentiableAt_pi.mp (hG x) i
  have hc : DifferentiableAt ℝ (fun y : Coord3 => χ (y 0)) x :=
    (hχ (x 0)).comp x (differentiableAt_apply 0 x)
  have hd (i : Fin 3) : direction (Pi.single i 1) (fun y => axialFluxBlend χ F G y i) x=
      (1-χ (x 0))*direction (Pi.single i 1) (fun y => F y i) x+
      χ (x 0)*direction (Pi.single i 1) (fun y => G y i) x+
      deriv χ (x 0)*(if (0:Fin 3)=i then 1 else 0)*(G x i-F x i) := by
    have h1 : DifferentiableAt ℝ (fun y => 1-χ (y 0)) x := differentiableAt_const (1:ℝ) |>.sub hc
    have h2 : DifferentiableAt ℝ (fun y => (1-χ (y 0))*F y i) x := h1.mul (hf i)
    have h3 : DifferentiableAt ℝ (fun y => χ (y 0)*G y i) x := hc.mul (hg i)
    change direction (Pi.single i 1) (fun y => (1-χ (y 0))*F y i+χ (y 0)*G y i) x=_
    rw [direction_add h2 h3,direction_mul h1 (hf i),direction_mul hc (hg i),
      direction_sub (differentiableAt_const (1:ℝ)) hc,direction_scalar_coord hχ i 0,direction_const]
    ring
  change (∑ i,direction (Pi.single i 1) (fun y => axialFluxBlend χ F G y i) x)=_
  simp_rw [hd]
  simp only [Fin.sum_univ_three,coordinateDivergence,show (0:Fin 3)≠1 by decide,
    show (0:Fin 3)≠2 by decide,ite_true,ite_false,mul_one,mul_zero,zero_mul,add_zero]
  change _=(1-χ (x 0))*(direction (Pi.single 0 1) (fun y => F y 0) x+
    direction (Pi.single 1 1) (fun y => F y 1) x+direction (Pi.single 2 1) (fun y => F y 2) x)+
    χ (x 0)*(direction (Pi.single 0 1) (fun y => G y 0) x+
    direction (Pi.single 1 1) (fun y => G y 1) x+direction (Pi.single 2 1) (fun y => G y 2) x)+_
  ring

lemma axialFluxBlend_divergence_zero {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) {F G : Coord3 → Coord3}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G) {x : Coord3}
    (hFd : coordinateDivergence F x=0) (hGd : coordinateDivergence G x=0)
    (hn : deriv χ (x 0)=0 ∨ F x 0=G x 0) :
    coordinateDivergence (axialFluxBlend χ F G) x=0 := by
  rw [axialFluxBlend_divergence hχ hF hG,hFd,hGd,mul_zero,mul_zero,zero_add,zero_add]
  rcases hn with hn|hn
  · rw [hn,zero_mul]
  · rw [hn,sub_self,mul_zero]

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology MeasureTheory

theorem C1_divergence_zero_on_test
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure E) [μ.IsAddHaarMeasure] (v : ι → E) (F : ι → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i))
    (ψ : SmoothScalar E) (hc : HasCompactSupport ψ.val)
    (hdiv : ∀ x, x∈Function.support ψ.val → ∑ i, direction (v i) (F i) x = 0) :
    (∫ x, ∑ i, F i x*(smoothDirection (v i) ψ).val x ∂μ) = 0 := by
  have hp := smoothScalar_contDiff ψ
  have hI (i : ι) : Integrable (fun x => F i x*(smoothDirection (v i) ψ).val x) μ :=
    ((hF i).continuous.mul (smoothScalar_contDiff (smoothDirection (v i) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (v i) hc).mul_left
  have hI' (i : ι) : Integrable (fun x => ψ.val x*direction (v i) (F i) x) μ :=
    (hp.continuous.mul (direction_continuous (hF i) _)).integrable_of_hasCompactSupport hc.mul_right
  have hibp (i : ι) : (∫ x, F i x*(smoothDirection (v i) ψ).val x ∂μ) =
      -(∫ x, ψ.val x*direction (v i) (F i) x ∂μ) := by
    have hh := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ)
      (f := F i) (g := ψ.val) (v := v i)
      (show Integrable (fun x => direction (v i) (F i) x*ψ.val x) μ by
        simpa only [mul_comm] using hI' i)
      (hI i)
      (((hF i).continuous.mul hp.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun x _ => ((hF i).differentiable (by norm_num) x).hasFDerivAt)
      (fun x _ => (hp.differentiable (by simp) x).hasFDerivAt)
    change (∫ x, F i x * (fderiv ℝ ψ.val x) (v i) ∂μ) =
      -(∫ x, (fderiv ℝ (F i) x) (v i) * ψ.val x ∂μ) at hh
    simpa only [direction,smoothDirection_apply,mul_comm] using hh
  rw [integral_finsetSum _ (fun i _ => hI i)]
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib,←integral_finsetSum _ (fun i _ => hI' i)]
  have hz : (fun x => ∑ i, ψ.val x*direction (v i) (F i) x) = fun _ => (0:ℝ) := by
    funext x
    rw [←Finset.mul_sum]
    by_cases hx : x∈Function.support ψ.val
    · rw [hdiv x hx,mul_zero]
    · rw [Function.notMem_support.mp hx,zero_mul]
  rw [hz,integral_zero,neg_zero]

theorem axialFluxBlend_weak {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) {F G : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) {U : Set Coord3}
    (hFd : ∀ x∈U,coordinateDivergence F x=0)
    (hGd : ∀ x∈U,coordinateDivergence G x=0)
    (hn : ∀ x∈U,deriv χ (x 0)=0 ∨ F x 0=G x 0)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val⊆U) :
    (∫ x, ∑ i, axialFluxBlend χ F G x i*(smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  apply C1_divergence_zero_on_test volume (fun i => Pi.single i 1)
    (fun i x => axialFluxBlend χ F G x i)
    (fun i => contDiff_pi.mp (axialFluxBlend_C1 hχ hF hG) i) ψ hc
  intro x hx
  have hxU := hs (subset_tsupport _ hx)
  exact axialFluxBlend_divergence_zero (hχ.differentiable (by norm_num))
    (hF.differentiable (by norm_num)) (hG.differentiable (by norm_num))
    (hFd x hxU) (hGd x hxU) (hn x hxU)

end ScalarConductivity



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def delayedEndingTensor (lam k J L K R : ℝ) (x : Coord3) : Mat3 :=
  alignedEndingTensor lam k J L K (x-Pi.single 0 R)

def delayedEndingPotential (lam k J L K R : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  exp (-lam*R)*alignedEndingPotential lam k J L K i j (x-Pi.single 0 R)

lemma delayedEndingPotential_C2 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (i j : Fin 3) :
    ContDiff ℝ 2 (delayedEndingPotential lam k J L K R i j) :=
  contDiff_const.mul ((alignedEndingPotential_C2 hJ hL hK i j).comp (contDiff_id.sub contDiff_const))

lemma delayedEndingPotential_antisymm (lam k J L K R : ℝ) (i j : Fin 3) :
    delayedEndingPotential lam k J L K R i j=fun x => -delayedEndingPotential lam k J L K R j i x := by
  funext x
  rw [delayedEndingPotential,alignedEndingPotential_antisymm]
  simp [delayedEndingPotential]

lemma delayedEnding_direction {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (v x : Coord3) :
    direction v (delayedEndingValue lam k J L K R) x=
      exp (-lam*R)*direction v (alignedEndingValue lam k J L K) (x-Pi.single 0 R) := by
  unfold delayedEndingValue
  simpa only [one_smul,mul_one] using (direction_dilation
    ((alignedEndingValue_C2 (lam:=lam) (k:=k) hJ hL hK).differentiable (by norm_num))
    (exp (-lam*R)) 1 (Pi.single 0 R) v x)

lemma delayedEnding_curl {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3) (i : Fin 3) :
    potentialCurl (delayedEndingPotential lam k J L K R) x i=
      exp (-lam*R)*potentialCurl (alignedEndingPotential lam k J L K) (x-Pi.single 0 R) i := by
  unfold delayedEndingPotential
  simpa only [one_smul,mul_one] using (potentialCurl_dilation
    (fun i j => (alignedEndingPotential_C2 (lam:=lam) (k:=k) hJ hL hK i j).differentiable (by norm_num))
    (exp (-lam*R)) 1 (Pi.single 0 R) x i)

lemma delayedEnding_constitution_ae {lam k J L K R : ℝ} (hk : k≠0) (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3,delayedEndingTensor lam k J L K R x*ᵥ
      (fun i => direction (Pi.single i 1) (delayedEndingValue lam k J L K R) x)=
      potentialCurl (delayedEndingPotential lam k J L K R) x := by
  have hh := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 R)).quasiMeasurePreserving.ae
    (alignedEnding_constitution_ae (lam:=lam) hk hJ hL hK)
  filter_upwards [hh] with x hx
  simp only [←sub_eq_add_neg] at hx
  ext i
  simp only [delayedEnding_direction hJ hL hK,delayedEnding_curl hJ hL hK]
  change (delayedEndingTensor lam k J L K R x*ᵥ(exp (-lam*R) •
    (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) (x-Pi.single 0 R)))) i=_
  rw [Matrix.mulVec_smul,delayedEndingTensor,hx]
  rfl

lemma delayedEndingFlux_C1 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ContDiff ℝ 1 (potentialCurl (delayedEndingPotential lam k J L K R)) := by
  apply contDiff_pi.mpr
  intro i
  apply ContDiff.sum
  intro j _
  exact direction_C1 (delayedEndingPotential_C2 hJ hL hK i j) _

lemma delayedEndingFlux_divergence {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3) :
    coordinateDivergence (potentialCurl (delayedEndingPotential lam k J L K R)) x=0 :=
  antisymmetric_potential_divergence (fun i => Pi.single i 1) (delayedEndingPotential lam k J L K R)
    (delayedEndingPotential_C2 hJ hL hK) (delayedEndingPotential_antisymm lam k J L K R) x

end ScalarConductivity

end

end OAI
