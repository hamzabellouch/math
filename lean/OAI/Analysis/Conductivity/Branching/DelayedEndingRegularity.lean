import Mathlib
import OAI.Analysis.Conductivity.Branching.AlignedEndingRegularity

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

def delayedEndingSymmetricTensor (lam k J L K R : ℝ) (x : Coord3) : Symmetric3 :=
  alignedEndingSymmetricTensor lam k J L K (x-Pi.single 0 R)

def axialAmplitudeEquiv (a : ℝ) (ha : a≠0) : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearEquiv.piCongrRight (fun i : Fin 2 =>
    (LinearEquiv.smulOfNeZero ℝ ℝ (if i=0 then 1 else a) (by split_ifs <;> simp_all)).toContinuousLinearEquiv)

lemma axialAmplitudeEquiv_apply (a : ℝ) (ha : a≠0) (v : Fin 2 → ℝ) (i : Fin 2) :
    axialAmplitudeEquiv a ha v i=(if i=0 then 1 else a)*v i := rfl

lemma RegularPatch.amplitude {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (a : ℝ) (ha : a≠0) :
    RegularPatch (fun x => axialAmplitudeEquiv a ha (u x)) A O := by
  refine ⟨h.1,(axialAmplitudeEquiv a ha).contDiff.contDiffOn.comp h.2.1 (fun _ _ => mem_univ _),h.2.2.1,?_⟩
  exact h.2.2.2.linearCoordinates h.1 h.2.1 (ContinuousLinearEquiv.refl ℝ Coord3) (axialAmplitudeEquiv a ha)

lemma delayedEnding_axialPair (lam k J L K R : ℝ) (x : Coord3) :
    axialAmplitudeEquiv (exp (-lam*R)) (exp_pos _).ne'
      (axialPair (alignedEndingValue lam k J L K) (x-Pi.single 0 R))+![R,0]=
        axialPair (delayedEndingValue lam k J L K R) x := by
  ext i
  fin_cases i <;> simp [axialAmplitudeEquiv_apply,axialPair,delayedEndingValue]

lemma RegularPatch.delayedEnding {lam k J L K R : ℝ} {O : Set Coord3}
    (h : RegularPatch (axialPair (alignedEndingValue lam k J L K))
      (alignedEndingSymmetricTensor lam k J L K) O) :
    RegularPatch (axialPair (delayedEndingValue lam k J L K R))
      (delayedEndingSymmetricTensor lam k J L K R) ((fun x : Coord3 => x-Pi.single 0 R) ⁻¹' O) := by
  have hh := (h.amplitude (exp (-lam*R)) (exp_pos _).ne').translate (Pi.single 0 R) ![R,0]
  convert hh using 1
  · funext x
    exact (delayedEnding_axialPair _ _ _ _ _ _ _).symm
  · rfl

lemma delayedEnding_regularRegion_ae {lam k J L K R : ℝ} (hk : k≠0) (hL : 0<L) (hK : 0<K)
    {U : Set Coord3} (hU : IsOpen U) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion (axialPair (delayedEndingValue lam k J L K R))
      (delayedEndingSymmetricTensor lam k J L K R) U := by
  have he := (measurePreserving_add_right (volume : Measure Coord3) (-Pi.single 0 R)).quasiMeasurePreserving.ae
    (alignedEnding_regularRegion_ae (lam:=lam) (J:=J) hk hL hK isOpen_univ)
  simp only [←sub_eq_add_neg] at he
  filter_upwards [he] with x hx
  intro hxU
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp (hx (mem_univ _))
  have hh : x∈regularRegion (axialPair (delayedEndingValue lam k J L K R))
      (delayedEndingSymmetricTensor lam k J L K R) univ := by
    apply mem_regularRegion_iff.mpr
    refine ⟨(fun y : Coord3 => y-Pi.single 0 R) ⁻¹' O,subset_univ _,?_,?_⟩
    · exact hO.delayedEnding (R:=R)
    · exact hxO
  exact mem_regularRegion_congr_nhds hh (Filter.EventuallyEq.rfl) (Filter.EventuallyEq.rfl) hU hxU

end ScalarConductivity

end

end OAI
