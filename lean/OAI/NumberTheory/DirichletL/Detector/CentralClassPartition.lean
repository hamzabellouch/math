import OAI.NumberTheory.DirichletL.Detector.CentralClassArithmetic
import OAI.NumberTheory.DirichletL.Hecke.DetectorAmplitudeFirst
import OAI.NumberTheory.DirichletL.Hecke.DetectorClassBudget

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

lemma sum_amplitudeRows {Slot : Type*} (rows : Finset FreeRow) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (f : FreeRow→ℂ) :
    (∑u∈rows,f u)=∑bin : BinLabel slots cap mesh,
      ∑u∈amplitudeRows rows slots U cap mesh hm widths Q bin,f u := by
  have hmap : ∀u∈rows,amplitudeLabel slots U cap mesh hm widths Q u∈
      (Finset.univ : Finset (BinLabel slots cap mesh)) := by simp
  exact (Finset.sum_fiberwise_of_maps_to hmap f).symm

lemma cubeArithmeticSum_amplitude_partition {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) :
    cubeArithmeticSum S hS hmax η rows T hT W Yp a e t=
      ∑bin : BinLabel slots cap mesh,cubeArithmeticSum S hS hmax η
        (amplitudeRows rows slots U cap mesh hm widths Q bin) T hT W Yp a e t := by
  unfold cubeArithmeticSum
  exact sum_amplitudeRows rows slots U cap mesh hm widths Q _

theorem cubeArithmeticSum_class_uniform {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (hcap : cap≤1/2) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (A : ℝ) (hA : 0≤A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty →
      ‖cubeArithmeticSum S hS hmax η (amplitudeRows rows slots U cap mesh hm widths Q bin)
        T hT W Yp a e t‖≤A) :
    ‖cubeArithmeticSum S hS hmax η rows T hT W Yp a e t‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [cubeArithmeticSum_amplitude_partition S hS hmax η rows T hT W Yp a e t slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,cubeArithmeticSum,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm
end SevenEighths.ProbeHighRowFamily

end

end OAI
