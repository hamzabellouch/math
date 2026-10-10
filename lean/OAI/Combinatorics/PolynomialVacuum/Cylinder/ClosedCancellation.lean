import OAI.Combinatorics.PolynomialVacuum.Cylinder.FinitePartition

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ} [NeZero M]

noncomputable def emptyBoundedSystem (E : Finset (Edge M)) : BoundedSystem E :=
  ⟨⟨∅,by simp⟩,by simp⟩

omit [NeZero M] in
@[simp] theorem not_separates_self [NeZero M] (P : Polygon M) (a : Face M) : ¬Separates P a a :=
  fun h => h Relation.ReflTransGen.refl

 

theorem closed_partition_one (E : Finset (Edge M)) (a : Face M) (κ : ℂ) (hκ : κ≠0) :
    (∑r : BoundedFlow E,currentWeight r.val.val a a κ)=1 := by
  rw [finite_current_partition E a a κ hκ]
  have hz (S : BoundedSystem E) : (∀P∈S.val.val,Separates P a a) ↔ S=emptyBoundedSystem E := by
    constructor
    · intro h
      have he : S.val.val=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun P hP => not_separates_self P a (h P hP))
      exact Subtype.ext (Subtype.ext he)
    · rintro rfl
      simp [emptyBoundedSystem]
  simp_rw [hz]
  rw [Finset.sum_eq_single (emptyBoundedSystem E)]
  · simp [emptyBoundedSystem]
  · intro S _ hS
    simp [hS]
  · simp

noncomputable def uniformSeamWeight (r : Edge M →₀ ℤ) : ℂ :=
  xStar^(activeSites r).card * loopTurnPhase (flowTurn r) * zeta^(columnTotal r 1)

 

omit [NeZero M] in
theorem currentWeight_above [NeZero M] (r : Edge M →₀ ℤ) (j : ℤ) (hj : (flowRadius r : ℤ)<j) (κ : ℂ) :
    currentWeight r (0,j) (0,j) κ=uniformSeamWeight r := by
  have hp : potentialHom (0,j) r=topHom r := by
    change potential r (0,j)= -columnTotal r 1
    simpa only [zero_add] using potential_top_eq r 0 j hj
  simp only [currentWeight,currentPhase,hp,threeSeamFactor,sub_self,zpow_zero,mul_one,
    uniformSeamWeight,mul_assoc]
  change _ * (_ * zeta^(-(-columnTotal r 1)))=_
  rw [neg_neg]

 

theorem uniform_closed_partition_one (E : Finset (Edge M)) :
    (∑r : BoundedFlow E,uniformSeamWeight r.val.val)=1 := by
  let j : ℤ := (E.sup (fun e => e.1.2.natAbs) : ℕ)+1
  have hj (r : BoundedFlow E) : (flowRadius r.val.val : ℤ)<j := by
    have hh : flowRadius r.val.val≤E.sup (fun e => e.1.2.natAbs) :=
      Finset.sup_mono r.property
    dsimp [j]
    omega
  simpa only [currentWeight_above _ j (hj _) (1 : ℂ)] using
    closed_partition_one E (0,j) (1 : ℂ) one_ne_zero

end PolynomialVacuumCylinder

end OAI
