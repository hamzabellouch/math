import Mathlib
import OAI.Analysis.Conductivity.Branching.Ending

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

def permutedDilation (e : Equiv.Perm (Fin 3)) (r : ℝ) (x : Coord3) : Coord3 :=
  fun i => r*x (e i)

lemma permutedDilation_smooth (e : Equiv.Perm (Fin 3)) (r : ℝ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (permutedDilation e r) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (e i))

lemma direction_permutedDilation {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    (e : Equiv.Perm (Fin 3)) (r : ℝ) (i : Fin 3) (x : Coord3) :
    direction (Pi.single i 1) (fun y => f (permutedDilation e r y)) x =
      r*direction (Pi.single (e.symm i) 1) f (permutedDilation e r x) := by
  let P : Coord3 →L[ℝ] Coord3 :=
    ContinuousLinearMap.pi (fun j => r • ContinuousLinearMap.proj (e j))
  have hP : (P : Coord3 → Coord3)=permutedDilation e r := rfl
  have he : P (Pi.single i 1)=r • Pi.single (e.symm i) 1 := by
    ext j
    simp only [P,ContinuousLinearMap.pi_apply,_root_.smul_apply,
      ContinuousLinearMap.proj_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp only [show e j=i ↔ j=e.symm i from e.eq_symm_apply.symm]
  have hd := (hf (P x)).hasFDerivAt.comp x P.hasFDerivAt
  change fderiv ℝ (f ∘ P) x (Pi.single i 1)=_
  rw [hd.fderiv,ContinuousLinearMap.comp_apply,he,map_smul,smul_eq_mul]
  rfl

lemma potentialCurl_permutedDilation {S : Fin 3 → Fin 3 → Coord3 → ℝ}
    (hS : ∀ i j,Differentiable ℝ (S i j))
    (e : Equiv.Perm (Fin 3)) (r : ℝ) (x : Coord3) (i : Fin 3) :
    potentialCurl (fun i j y => S (e.symm i) (e.symm j) (permutedDilation e r y)) x i =
      r*potentialCurl S (permutedDilation e r x) (e.symm i) := by
  simp only [potentialCurl,direction_permutedDilation (hS _ _),Finset.mul_sum]
  exact e.symm.sum_comp (fun j => r*direction (Pi.single j 1) (S (e.symm i) j) (permutedDilation e r x))

lemma permutedTensor_quadratic (e : Equiv.Perm (Fin 3)) (A : Mat3) (v : Coord3) :
    v ⬝ᵥ ((fun i j => A (e.symm i) (e.symm j))*ᵥv) =
      (fun i => v (e i)) ⬝ᵥ (A*ᵥ(fun i => v (e i))) := by
  simp only [Matrix.mulVec,dotProduct]
  have hi := Equiv.sum_comp e (fun i => v i*∑ j,A (e.symm i) (e.symm j)*v j)
  rw [←hi]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.symm_apply_apply]
  congr 1
  have hj := Equiv.sum_comp e (fun j => A i (e.symm j)*v j)
  simpa only [Equiv.symm_apply_apply] using hj.symm

lemma permutedTensor_constitution {f : Coord3 → ℝ} (hf : Differentiable ℝ f)
    {S : Fin 3 → Fin 3 → Coord3 → ℝ} (hS : ∀ i j,Differentiable ℝ (S i j))
    (A : Coord3 → Mat3) (e : Equiv.Perm (Fin 3)) (r : ℝ) (x : Coord3)
    (h : A (permutedDilation e r x)*ᵥ(fun j => direction (Pi.single j 1) f (permutedDilation e r x))=
      potentialCurl S (permutedDilation e r x)) :
    (fun i j => A (permutedDilation e r x) (e.symm i) (e.symm j))*ᵥ
      (fun j => direction (Pi.single j 1) (fun y => f (permutedDilation e r y)) x)=
      potentialCurl (fun i j y => S (e.symm i) (e.symm j) (permutedDilation e r y)) x := by
  ext i
  rw [potentialCurl_permutedDilation hS]
  simp only [Matrix.mulVec,dotProduct,direction_permutedDilation hf]
  have hh := congrFun h (e.symm i)
  change (∑ j,A (permutedDilation e r x) (e.symm i) j*direction (Pi.single j 1) f (permutedDilation e r x))=
    potentialCurl S (permutedDilation e r x) (e.symm i) at hh
  rw [←hh,Finset.mul_sum]
  calc
    _ = ∑ j,r*(A (permutedDilation e r x) (e.symm i) (e.symm j)*
        direction (Pi.single (e.symm j) 1) f (permutedDilation e r x)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := Equiv.sum_comp e.symm (fun j => r*(A (permutedDilation e r x) (e.symm i) j*
      direction (Pi.single j 1) f (permutedDilation e r x)))

lemma permutedDilation_quasiMeasurePreserving (e : Equiv.Perm (Fin 3)) {r : ℝ} (hr : r≠0) :
    Measure.QuasiMeasurePreserving (permutedDilation e r) volume volume := by
  have hp := (volume_measurePreserving_piCongrLeft (fun _ : Fin 3 => ℝ) e.symm).quasiMeasurePreserving
  have hs := Measure.quasiMeasurePreserving_smul (volume : Measure Coord3) hr
  convert hs.comp hp using 1
  funext x i
  simp [permutedDilation,MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]

end ScalarConductivity



namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

local instance endingCoordinateTransportMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance endingCoordinateTransportBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

def angularAxisSwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

lemma angularAxisSwap_apply (i : Fin 3) : angularAxisSwap i=![0,2,1] i := by
  fin_cases i <;> decide

lemma angularAxisSwap_symm : angularAxisSwap.symm=angularAxisSwap := rfl

def alignedEndingValue (lam k J L K : ℝ) (x : Coord3) : ℝ :=
  finiteEndingValue (lam/k) J L K (permutedDilation angularAxisSwap k x)

def alignedEndingTensor (lam k J L K : ℝ) (x : Coord3) : Mat3 :=
  fun i j => finiteEndingTensor (lam/k) J L K (permutedDilation angularAxisSwap k x)
    (angularAxisSwap i) (angularAxisSwap j)

def alignedEndingPotential (lam k J L K : ℝ) (i j : Fin 3) (x : Coord3) : ℝ :=
  finiteEndingPotential (lam/k) J L K (angularAxisSwap i) (angularAxisSwap j)
    (permutedDilation angularAxisSwap k x)

lemma alignedEndingValue_C2 {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ContDiff ℝ 2 (alignedEndingValue lam k J L K) :=
  (finiteEndingValue_C2 hJ hL hK).comp ((permutedDilation_smooth angularAxisSwap k).of_le (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast))

lemma alignedEndingPotential_C2 {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (i j : Fin 3) :
    ContDiff ℝ 2 (alignedEndingPotential lam k J L K i j) :=
  (finiteEndingPotential_C2 hJ hL hK _ _).comp ((permutedDilation_smooth angularAxisSwap k).of_le (show (2:WithTop ℕ∞) ≤ ↑(⊤:ℕ∞) by norm_cast))

lemma alignedEndingPotential_antisymm (lam k J L K : ℝ) (i j : Fin 3) :
    alignedEndingPotential lam k J L K i j = fun x => -alignedEndingPotential lam k J L K j i x := by
  funext x
  exact congrFun (finiteEndingPotential_antisymm _ _ _ _ _ _) _

lemma alignedEndingTensor_measurable (lam k J L K : ℝ) : Measurable (alignedEndingTensor lam k J L K) := by
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp
    ((finiteEndingTensor_measurable _ _ _ _).comp (permutedDilation_smooth _ _).continuous.measurable))

lemma alignedEndingTensor_symm (lam k J L K : ℝ) (x : Coord3) :
    (alignedEndingTensor lam k J L K x).IsSymm := by
  ext i j
  exact congrFun (congrFun (finiteEndingTensor_symm (lam/k) J L K (permutedDilation angularAxisSwap k x))
    (angularAxisSwap i)) (angularAxisSwap j)

lemma alignedEndingTensor_normal (lam k J L K : ℝ) (x : Coord3) :
    alignedEndingTensor lam k J L K x*ᵥPi.single 0 1=Pi.single 0 1 := by
  ext i
  have hh := congrFun (finiteEndingTensor_normal (lam/k) J L K (permutedDilation angularAxisSwap k x)) (angularAxisSwap i)
  fin_cases i <;> simpa [alignedEndingTensor, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    angularAxisSwap_apply, Pi.single_apply] using hh

lemma alignedEnding_initial {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (x : Coord3) (ht : k*x 0≤1) :
    alignedEndingValue lam k J L K x=exp (-lam*x 0)*cos (k*x 2) := by
  have h0 : permutedDilation angularAxisSwap k x 0=k*x 0 := by simp [permutedDilation,angularAxisSwap_apply]
  have h1 : permutedDilation angularAxisSwap k x 1=k*x 2 := by simp [permutedDilation,angularAxisSwap_apply]
  rw [alignedEndingValue,finiteEndingValue_initial hJ _ (by simpa only [h0] using ht),h0,h1]
  congr 2
  field_simp

lemma alignedEnding_terminal {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (x : Coord3) (ht : J+2+2*cascadeLength L K≤k*x 0) :
    alignedEndingValue lam k J L K x=0 := by
  apply finiteEndingValue_terminal hJ hL hK
  simpa only [permutedDilation,angularAxisSwap_apply,Matrix.cons_val_zero] using ht

lemma alignedEnding_constitution_ae {lam k J L K : ℝ} (hk : k≠0) (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ∀ᵐ x : Coord3,alignedEndingTensor lam k J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) x)=
      potentialCurl (alignedEndingPotential lam k J L K) x := by
  have hh := (permutedDilation_quasiMeasurePreserving angularAxisSwap hk).ae
    (finiteEnding_constitution_ae (a:=lam/k) hJ hL hK)
  filter_upwards [hh] with x hx
  exact permutedTensor_constitution ((finiteEndingValue_C2 hJ hL hK).differentiable (by norm_num))
    (fun i j => (finiteEndingPotential_C2 hJ hL hK i j).differentiable (by norm_num))
    (finiteEndingTensor (lam/k) J L K) angularAxisSwap k x hx

lemma alignedEndingFlux_C1 {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => potentialCurl (alignedEndingPotential lam k J L K) x i) := by
  apply ContDiff.sum
  intro j _
  exact direction_C1 (alignedEndingPotential_C2 hJ hL hK i j) _

lemma alignedEndingFlux_divergence {lam k J L K : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3) :
    ∑ i,direction (Pi.single i 1) (fun y => potentialCurl (alignedEndingPotential lam k J L K) y i) x=0 :=
  antisymmetric_potential_divergence (fun i => Pi.single i 1) (alignedEndingPotential lam k J L K)
    (alignedEndingPotential_C2 hJ hL hK) (alignedEndingPotential_antisymm lam k J L K) x

theorem alignedEnding_weak_equation {lam k J L K : ℝ} (hk : k≠0) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val) :
    Integrable (fun x => ∑ i, (alignedEndingTensor lam k J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) x)) i*
        (smoothDirection (Pi.single i 1) ψ).val x) ∧
    (∫ x, ∑ i, (alignedEndingTensor lam k J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) x)) i*
        (smoothDirection (Pi.single i 1) ψ).val x)=0 := by
  have he : (fun x => ∑ i, (alignedEndingTensor lam k J L K x*ᵥ
      (fun j => direction (Pi.single j 1) (alignedEndingValue lam k J L K) x)) i*
        (smoothDirection (Pi.single i 1) ψ).val x)=ᵐ[volume]
      (fun x => ∑ i, potentialCurl (alignedEndingPotential lam k J L K) x i*
        (smoothDirection (Pi.single i 1) ψ).val x) := by
    filter_upwards [alignedEnding_constitution_ae hk hJ hL hK] with x hx
    rw [hx]
  constructor
  · apply Integrable.congr _ he.symm
    apply integrable_finsetSum
    intro i _
    exact ((alignedEndingFlux_C1 hJ hL hK i).continuous.mul
      (smoothScalar_contDiff (smoothDirection (Pi.single i 1) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (Pi.single i 1) hc).mul_left
  · rw [integral_congr_ae he]
    exact C1_divergence_zero_test volume (fun i : Fin 3 => Pi.single i 1)
      (fun i x => potentialCurl (alignedEndingPotential lam k J L K) x i) (alignedEndingFlux_C1 hJ hL hK)
      (alignedEndingFlux_divergence hJ hL hK) ψ hc

end ScalarConductivity

end

end OAI
