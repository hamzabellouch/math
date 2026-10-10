import OAI.NumberTheory.DirichletL.Detector.GaussianSubset

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem compensatedPhysicalProbe_common_gaussian {K : ℕ}
    (W : Fin K→ℝ→ℂ) (M : Fin K→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : Finset (Fin K)→SchwartzMap ℝ ℂ,
    ∃hV : ∀A,HasCompactSupport (V A:ℝ→ℂ),
      (∀N : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧
        ∀A : Finset (Fin K),∀Z : ℝ,0<Z→
          Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z)) ∧
          (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀slotPrimes : Fin K→Finset O,(∀i a,a∈slotPrimes i→a≠0)→
        ∀P : Fin K→ℝ,(∀i,0<P i)→∀X Y Z : ℝ,0<X→0<Y→0<Z→
          compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
          ∑A∈(Finset.univ : Finset (Fin K)).powerset,
            ∑'j : ℕ,∫t : ℝ,
              (∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
                compensationSubsetWeight η W P (fun i=>(p i).val) A*
                  compensationRowTest η C W0 W1 (fun i=>(p i).val) A X Y ((2:ℝ)^j) t*
                    selectedSlotFactor W P (fun i=>(p i).val) A t)*
                      gaussianJointDensity (V A) (hV A) ((2:ℝ)^j/(Z*∏i∈Finset.univ\A,P i)) t) := by
  choose V hV hsep hbound using fun A : Finset (Fin K)=>
    gaussian_selected_slot_family (fun i : SelectedSlot A=>W i.val)
      (fun i : SelectedSlot A=>M i.val) (fun i=>hM i.val) (fun i=>hwindow i.val)
  refine ⟨V,hV,?_,?_⟩
  · intro N s hs
    choose B hB hb using fun A : Finset (Fin K)=>gaussianJointMoment_summed (V A) (hV A) N s hs
    let B0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,B A)+1
    have hB0 : 0<B0 := by
      have hh : 0≤∑A∈(Finset.univ : Finset (Fin K)).powerset,B A :=
        Finset.sum_nonneg (fun A _=>(hB A).le)
      dsimp only [B0]
      linarith
    refine ⟨B0,hB0,?_⟩
    intro A Z hZ
    obtain ⟨hsm,hbd⟩ := hb A Z hZ
    refine ⟨hsm,hbd.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le s)
    have hm : A∈(Finset.univ : Finset (Fin K)).powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
    have hh := Finset.single_le_sum (fun A _=>(hB A).le) hm
    dsimp only [B0]
    linarith
  · intro η C W0 W1 hW0 hW1 slotPrimes hp P hP X Y Z hX hY hZ
    rw [compensatedPhysicalProbe_eq_subsets]
    apply Finset.sum_congr rfl
    intro A hA
    exact compensation_subset_common A W (V A) (hV A) (hsep A) η C W0 W1 hW0 hW1 Finset.univ
      (fun p : ((i : Fin K)→{a : O // a∈slotPrimes i})=>fun i=>(p i).val)
      (fun p _ i=>hp i (p i).val (p i).property) P hP X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI
