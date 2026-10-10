import OAI.NumberTheory.DirichletL.Descent.WholePriorityPhysical
import OAI.NumberTheory.DirichletL.Descent.SecondDeletedModeEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMomentWholeRetainedSource
open ActualEisensteinCubic SecondPassArithmetic InverseMoment InverseInitialArithmetic
open InverseFirstPriorityParents InversePrioritySecondSource InverseMomentWholePriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def deleted (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (x : MarkedSecondSource ι Jo 0) : Finset ι :=
  extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x))

theorem retained_conditions (hp : ∀ i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
        R label residual j) := by
  apply whole_assigned_family_conditions p hp (fun x=>extra x.cube) source hs hextra negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

theorem retained_deleted_support
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (hextra : ∀ x∈source,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedPool p pool (wholeAssignedParents p (fun x=>extra x.cube) source negative J lists)
      R label residual j) :
    ∀ i∈deleted p extra negative x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient := by
  have hy := ((mem_retainedPool p pool _ R label residual j x).mp hx).1
  obtain ⟨s,hs₀,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists _).mp hy
  have hc : x.cube=s.cube := (congrArg SecondParentSource.cube he).symm
  have hC : x.firstCommon=s.firstCommon := (congrArg SecondParentSource.firstCommon he).symm
  have ht : x.quotient=sourceIdeal p s.quotientSupport := (congrArg SecondParentSource.quotient he).symm
  have hqs : quotientSupport p (secondParentOf x)=s.quotientSupport := by
    rw [←he,quotientSupport_attach p hinj]
  intro i hi
  change i∈extra x.cube∪(((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪
    quotientSupport p (secondParentOf x)) at hi
  rw [hc,hC,hqs] at hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Or.inl (Finset.mem_union_left _ (hc.symm ▸ hextra s hs₀ hi))
  · rcases Finset.mem_union.mp hi with hi|hi
    · left
      rw [hc,hC]
      rcases Finset.mem_union.mp hi with hi|hi
      · apply Finset.mem_union_left
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact (hs s hs₀).admissible.1 hi
        · exact (hs s hs₀).admissible.2 hi
      · exact Finset.mem_union_right _ hi
    · right
      rw [ht]
      exact source_prime_dvd p _ i hi

theorem whole_coefficient_norm
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈wholeAssignedParents p extra source negative J lists) :
    ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

end SevenEighths.InverseMomentWholeRetainedSource

end

end OAI
