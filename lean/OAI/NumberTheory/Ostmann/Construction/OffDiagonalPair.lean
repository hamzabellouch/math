import OAI.NumberTheory.Ostmann.Construction.OffDiagonalParent
import OAI.NumberTheory.Ostmann.Construction.OffDiagonalReindex

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Construction

theorem pivotPairWeight_mem_integerCell (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l) (p : ℕ)
    (hF : pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p≠0) :
    p∈integerPivotCell G := by
  have hf := pivotPairWeight_nonzero d P sources seed V giant X G bins outside l u x y v w p hF
  have hroot := remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u x v hf.2.1
  have hp : 0<p := hroot.1 p (by simp [remainingState,State.values])
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hs := Ostmann.smoothPartition_support_subset hf.1
  have hlog : Real.log p<G+1 := by linarith [hs.2]
  have he : (p:ℝ)<Real.exp (G+1) := (Real.log_lt_iff_lt_exp hpR).mp hlog
  exact Finset.mem_Ioc.mpr ⟨hp,by exact_mod_cast he.le.trans (Nat.le_ceil _)⟩

theorem pivotPairWeight_reversal (d : Decomposition) (P : Finset ℕ) (sources : SourceFamily)
    (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource) (X G : ℝ)
    (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (x y : RemainingSample sources (Template.remainder (l+1) (Template.current seed l)) giant)
    (v w : AllowedFrequency V l) (s : ℤ) (hs : s≠0)
    (hgiant : s.natAbs<x.1.val)
    (hlarge : ∀q∈assignedSlots sources (Template.remainder (l+1) (Template.current seed l)) x.2,
      s.natAbs<q.value)
    (heq : joinedNumerator sources (Template.remainder (l+1) (Template.current seed l)) giant x y v.val w.val=
      s*((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod*(p:ℤ)) :
    pivotPairWeight d P sources seed V giant X G bins outside l u x y v w p=
      regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside
        (joinedRemainingState sources (Template.remainder (l+1) (Template.current seed l)) giant x y s)*
      ((((assignedSlots sources (Template.extracted (l+1) (Template.current seed l)) u).map SmallSlot.value).prod:ℂ)*
        (Ostmann.smoothPartition (Real.log p-G):ℂ)*
        actualCoefficient sources seed V X G (residueTransform d) bins outside l
          (remainingState sources (Template.current seed l) (l+1) giant p u x v.val)*
        conj (actualCoefficient sources seed V X G (residueTransform d) bins outside l
          (remainingState sources (Template.current seed l) (l+1) giant p u y w.val))) := by
  let T := Template.current seed l
  let R := Template.remainder (l+1) T
  let us := assignedSlots sources (Template.extracted (l+1) T) u
  let xs := assignedSlots sources R x.2
  let ys := assignedSlots sources R y.2
  let ax := remainingState sources T (l+1) giant p u x v.val
  let ay := remainingState sources T (l+1) giant p u y w.val
  by_cases hx : actualCoefficient sources seed V X G (residueTransform d) bins outside l ax=0
  · dsimp only [ax,T] at hx
    simp only [pivotPairWeight,remainingIntegrand,hx,mul_zero,zero_mul]
  by_cases hy : actualCoefficient sources seed V X G (residueTransform d) bins outside l ay=0
  · dsimp only [ay,T] at hy
    simp only [pivotPairWeight,remainingIntegrand,hy,mul_zero,map_zero]
  have hxroot := actualCoefficient_root_support sources seed V X G (residueTransform d) bins outside l ax hx
  have hyroot := actualCoefficient_root_support sources seed V X G (residueTransform d) bins outside l ay hy
  have hxp := (state_coprime_halves ax us xs outside
    (Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)) hxroot.2.2.2.1).2.2
  have hyp := (state_coprime_halves ay us ys outside
    (Template.reinsert_perm _ _ _ _ (assignedSlots_length _ _ _) (assignedSlots_length _ _ _)) hyroot.2.2.2.1).2.2
  have hr : Arithmetic.reversalNumerator v.val w.val (halfProduct x.1.val xs:ℤ)
      (halfProduct y.1.val ys:ℤ)=s*(halfProduct p us:ℤ) := by
    change joinedNumerator sources R giant x y v.val w.val=_
    rw [heq]
    simp only [halfProduct,Nat.cast_mul]
    ring
  have hcross := reversal_sample_halves_coprime (halfProduct p us) x.1.val y.1.val xs ys
    v.val w.val s hs (giant.prime _ x.1.property) (assignedSlots_prime sources R x.2)
    hxp ⟨hgiant,hlarge⟩ hr
  have htransform := halfTransforms_reversal d P outside (halfProduct p us) x.1.val y.1.val xs ys
    v.val w.val s (giant.prime _ x.1.property) (giant.prime _ y.1.property)
    (assignedSlots_prime sources R x.2) (assignedSlots_prime sources R y.2)
    hxp.symm hyp.symm hcross hr
  unfold pivotPairWeight remainingIntegrand
  dsimp only
  rw [map_mul]
  calc
    _ = (halfTransform (residueTransform d) (favorableGiantResidueTransform d P)
          (outsideProduct outside*halfProduct p us) v.val x.1.val xs*
        conj (halfTransform (residueTransform d) (favorableGiantResidueTransform d P)
          (outsideProduct outside*halfProduct p us) w.val y.1.val ys))*
        (((us.map SmallSlot.value).prod:ℂ)*(Ostmann.smoothPartition (Real.log p-G):ℂ)*
          actualCoefficient sources seed V X G (residueTransform d) bins outside l ax*
          conj (actualCoefficient sources seed V X G (residueTransform d) bins outside l ay)) := by ring
    _ = _ := by rw [htransform]; rfl

end Ostmann.Construction

end

end OAI
