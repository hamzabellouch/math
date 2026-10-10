import Mathlib
import OAI.Analysis.Conductivity.Branching.FiniteEndingRegularity
import OAI.Analysis.Conductivity.Branching.AlignedEndingData
import OAI.Analysis.Conductivity.Geometry.RegularPatchLinear

namespace OAI


noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def permutedDilationEquiv (e : Equiv.Perm (Fin 3)) {k : ℝ} (hk : k≠0) : Coord3 ≃L[ℝ] Coord3 :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 3 => ℝ) e.symm).trans
    (LinearEquiv.smulOfNeZero ℝ Coord3 k hk).toContinuousLinearEquiv

lemma permutedDilationEquiv_apply (e : Equiv.Perm (Fin 3)) {k : ℝ} (hk : k≠0) (x : Coord3) :
    permutedDilationEquiv e hk x=permutedDilation e k x := by
  ext i
  simp [permutedDilationEquiv,permutedDilation,ContinuousLinearEquiv.piCongrLeft,
    Homeomorph.piCongrLeft,Equiv.piCongrLeft]

def axialPairScaling {k : ℝ} (hk : k≠0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ (if i=0 then k⁻¹ else 1) (by split_ifs <;> simp_all)).toContinuousLinearEquiv)

lemma axialPairScaling_apply {k : ℝ} (hk : k≠0) (v : Fin 2 → ℝ) (i : Fin 2) :
    axialPairScaling hk v i=(if i=0 then k⁻¹ else 1)*v i := rfl

lemma alignedEnding_axialPair {lam k J L K : ℝ} (hk : k≠0) (x : Coord3) :
    axialPairScaling hk (axialPair (finiteEndingValue (lam/k) J L K)
      (permutedDilationEquiv angularAxisSwap hk x))=axialPair (alignedEndingValue lam k J L K) x := by
  ext i
  fin_cases i <;> simp [axialPairScaling_apply,permutedDilationEquiv_apply,axialPair,
    permutedDilation,angularAxisSwap_apply,alignedEndingValue,hk]

def alignedEndingSymmetricTensor (lam k J L K : ℝ) (x : Coord3) : Symmetric3 :=
  ⟨alignedEndingTensor lam k J L K x,alignedEndingTensor_symm lam k J L K x⟩

lemma RegularPatch.alignedEnding {lam k J L K : ℝ} (hk : k≠0) {O : Set Coord3}
    (h : RegularPatch (axialPair (finiteEndingValue (lam/k) J L K))
      (finiteEndingSymmetricTensor (lam/k) J L K) O) :
    RegularPatch (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K)
      ((permutedDilationEquiv angularAxisSwap hk) ⁻¹' O) := by
  let P := permutedDilationEquiv angularAxisSwap hk
  let Q := axialPairScaling hk
  have he : (fun x => Q (axialPair (finiteEndingValue (lam/k) J L K) (P x)))=
      axialPair (alignedEndingValue lam k J L K) := funext (alignedEnding_axialPair hk)
  refine ⟨h.1.preimage P.continuous,?_,?_,?_⟩
  · rw [←he]
    exact Q.contDiff.contDiffOn.comp (h.2.1.comp P.contDiff.contDiffOn (fun _ hx => hx))
      (fun _ _ => mem_univ _)
  · apply contDiffOn_pi.mpr; intro i
    apply contDiffOn_pi.mpr; intro j
    have hh := h.2.2.1.comp P.contDiff.contDiffOn (fun _ hx => hx)
    have hi := (contDiff_apply ℝ (Fin 3 → ℝ) (angularAxisSwap i)).contDiffOn.comp hh (fun _ _ => mem_univ _)
    have hj := (contDiff_apply ℝ ℝ (angularAxisSwap j)).contDiffOn.comp hi (fun _ _ => mem_univ _)
    change ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x =>
      finiteEndingTensor (lam/k) J L K (P x) (angularAxisSwap i) (angularAxisSwap j)) (P ⁻¹' O) at hj
    convert hj using 1
    funext x
    simp only [alignedEndingSymmetricTensor,alignedEndingTensor,
      P,permutedDilationEquiv_apply]
  · rw [←he]
    exact TwoFieldRankRegular.linearCoordinates h.1 h.2.1 h.2.2.2 P Q

theorem alignedEnding_regularRegion_ae {lam k J L K : ℝ} (hk : k≠0) (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K) U := by
  have he := (permutedDilation_quasiMeasurePreserving angularAxisSwap hk).ae
    (finiteEnding_regularRegion_ae (a:=lam/k) (J:=J) hL hK isOpen_univ)
  filter_upwards [he] with x hx
  intro hxU
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp (hx (mem_univ _))
  have hh : x∈regularRegion (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K) univ := by
    apply mem_regularRegion_iff.mpr
    refine ⟨(permutedDilationEquiv angularAxisSwap hk) ⁻¹' O,subset_univ _,hO.alignedEnding hk,?_⟩
    simpa only [mem_preimage,permutedDilationEquiv_apply] using hxO
  exact mem_regularRegion_congr_nhds hh (Filter.EventuallyEq.rfl) (Filter.EventuallyEq.rfl) hU hxU

lemma alignedEnding_regularRegion_conull {lam k J L K : ℝ} (hk : k≠0) (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    volume (U \ regularRegion (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K) U)=0 := by
  classical
  have hh := ae_iff.mp (alignedEnding_regularRegion_ae (lam:=lam) (J:=J) hk hL hK hU)
  convert hh using 2
  ext x
  simp only [Set.mem_sdiff,mem_ofPred_eq]
  tauto

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

def delayedEndingValue (lam k J L K R : ℝ) (x : Coord3) : ℝ :=
  exp (-lam*R)*alignedEndingValue lam k J L K (x-Pi.single 0 R)

lemma delayedEndingValue_C2 {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K) :
    ContDiff ℝ 2 (delayedEndingValue lam k J L K R) :=
  contDiff_const.mul ((alignedEndingValue_C2 hJ hL hK).comp (contDiff_id.sub contDiff_const))

lemma delayedEndingValue_initial_of_bound {lam k J L K R : ℝ} (hk : 0<k) (hJ : 0<J)
    (x : Coord3) (hx : k*(x 0-R)≤1) :
    delayedEndingValue lam k J L K R x=exp (-lam*x 0)*cos (k*x 2) := by
  rw [delayedEndingValue,alignedEnding_initial hk hJ _ (by simpa using hx)]
  simp only [Pi.sub_apply,Pi.single_eq_same,Pi.single_eq_of_ne (show (2:Fin 3)≠0 by decide),sub_zero]
  rw [←mul_assoc,←exp_add]
  congr 2
  ring

lemma delayedEndingValue_initial {lam k J L K R : ℝ} (hk : 0<k) (hJ : 0<J)
    (x : Coord3) (hx : x 0≤R) :
    delayedEndingValue lam k J L K R x=exp (-lam*x 0)*cos (k*x 2) := by
  apply delayedEndingValue_initial_of_bound hk hJ
  have hh := mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hx)
  linarith

lemma delayedEndingValue_terminal {lam k J L K R : ℝ} (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (x : Coord3) (hx : J+2+2*cascadeLength L K≤k*(x 0-R)) :
    delayedEndingValue lam k J L K R x=0 := by
  rw [delayedEndingValue,alignedEnding_terminal hJ hL hK _ (by simpa using hx),mul_zero]

lemma delayedEndingValue_periodic (lam J L K R : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (delayedEndingValue lam k J L K R) := by
  intro n x
  change exp (-lam*R)*alignedEndingValue lam k J L K (x+angularShift (2*Real.pi) n-Pi.single 0 R)=_
  rw [add_sub_right_comm,alignedEndingValue_angularPeriodic]
  rfl

def matchedEndingPair (u : Coord3 → Fin 2 → ℝ) (lam k J L K : ℝ) (x : Coord3) : Fin 2 → ℝ :=
  if x 0<13/2 then u x else ![x 0,delayedEndingValue lam k J L K 7 x]

lemma matchedEndingPair_C2 {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ 2 u)
    {lam k J L K : ℝ} (hk : 0<k) (hJ : 0<J) (hL : 1≤L) (hK : 0<K)
    (he : ∀ x : Coord3,4≤x 0 → u x=![x 0,exp (-lam*x 0)*cos (k*x 2)]) :
    ContDiff ℝ 2 (matchedEndingPair u lam k J L K) := by
  have hv : ContDiff ℝ 2 (fun x : Coord3 => ![x 0,delayedEndingValue lam k J L K 7 x]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact contDiff_apply ℝ ℝ 0
    · exact delayedEndingValue_C2 hJ hL hK
  apply contDiff_axial_paste hu hv (continuous_apply 0) (δ:=1/4) (by norm_num)
  intro x hx
  rw [he x (by linarith [hx.1]),delayedEndingValue_initial hk hJ x (by linarith [hx.2])]

lemma matchedEndingPair_periodic {u : Coord3 → Fin 2 → ℝ}
    (hu : AngularPeriodic (2*Real.pi) u) (lam J L K : ℝ) (k : ℤ) :
    AngularPeriodic (2*Real.pi) (matchedEndingPair u lam k J L K) := by
  intro n x
  have ht : (x+angularShift (2*Real.pi) n) 0=x 0 := by simp [angularShift]
  simp only [matchedEndingPair,ht,hu n x,delayedEndingValue_periodic _ _ _ _ _ _ n x]

lemma matchedEndingPair_terminal {u : Coord3 → Fin 2 → ℝ} {lam k J L K : ℝ}
    (hJ : 0<J) (hL : 1≤L) (hK : 0<K) (x : Coord3)
    (hx : 13/2≤x 0) (hterm : J+2+2*cascadeLength L K≤k*(x 0-7)) :
    matchedEndingPair u lam k J L K x=![x 0,0] := by
  rw [matchedEndingPair,ite_eq_right (not_lt.mpr hx),delayedEndingValue_terminal hJ hL hK _ hterm]

end ScalarConductivity

end

end OAI
