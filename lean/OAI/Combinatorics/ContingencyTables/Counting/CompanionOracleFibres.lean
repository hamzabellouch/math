import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleCorrection

namespace OAI

/-! # The actual integer bins have the manuscript's Cartesian populations -/

namespace ContingencyTables.CompanionOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def freeRange (A : Instance I J) (t : FreeCell A.small A.T) : ℕ := A.b t.val.1 t.val.2+1

def naturalBin (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (t : FreeCell A.small A.T) : ℕ := ((v ((index A).symm t)).val).toNat

lemma naturalBin_cast (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (t : FreeCell A.small A.T) : (naturalBin A v t:ℤ)=(v ((index A).symm t)).val :=
  Int.toNat_of_nonneg (v ((index A).symm t)).property.1

lemma naturalBin_lt (A : Instance I J) {K : ℕ} (v : Grid (I := Fin (dimension A)) K)
    (t : FreeCell A.small A.T) : naturalBin A v t<K := by
  have hh := (v ((index A).symm t)).property.2
  have hc := naturalBin_cast A v t
  omega

lemma integerBin_eq_iff (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) (f : FreeIndex A.small A.T A.b) :
    integerBin A K hK f=v ↔ ∀ t,FairBits.scale K (freeRange A t) (f t).val=naturalBin A v t := by
  constructor
  · intro h t
    have hh := congrArg (fun w : Grid (I := Fin (dimension A)) K =>
      (w ((index A).symm t)).val) h
    change (FairBits.scale K (freeRange A (index A ((index A).symm t)))
      (f (index A ((index A).symm t))).val:ℤ)=(v ((index A).symm t)).val at hh
    rw [Equiv.apply_symm_apply,←naturalBin_cast A v t] at hh
    exact_mod_cast hh
  · intro h
    funext i
    apply Subtype.ext
    have hh := congrArg (fun n : ℕ => (n:ℤ)) (h (index A i))
    rw [naturalBin_cast,Equiv.symm_apply_apply] at hh
    exact hh

def integerFiberEquiv (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    {f // f∈integerFiber A K hK v} ≃
      CompanionBinPopulation.Assignments K (freeRange A) (naturalBin A v) where
  toFun f t := ⟨(f.val t).val,by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (f.val t).isLt,?_⟩
    exact (integerBin_eq_iff A K hK v f.val).mp (Finset.mem_filter.mp f.property).2 t⟩
  invFun x := ⟨(fun t => ⟨(x t).val,by
    exact Finset.mem_range.mp (Finset.mem_filter.mp (x t).property).1⟩),by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply (integerBin_eq_iff A K hK v _).mpr
    intro t
    exact (Finset.mem_filter.mp (x t).property).2⟩
  left_inv f := by
    apply Subtype.ext
    funext t
    exact Fin.ext rfl
  right_inv x := by
    funext t
    exact Subtype.ext rfl

theorem integerFiber_card (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    (integerFiber A K hK v).card=
      ∏ t : FreeCell A.small A.T,(FairBits.fiber K (freeRange A t) (naturalBin A v t)).card := by
  let : DecidableEq (FreeCell A.small A.T) := Classical.decEq _
  calc
    _ = Fintype.card {f // f∈integerFiber A K hK v} := (Fintype.card_coe _).symm
    _ = _ := Fintype.card_congr (integerFiberEquiv A K hK v)
    _ = _ := CompanionBinPopulation.assignment_card K (freeRange A) (naturalBin A v)

theorem integerFiber_nonempty (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) :
    (integerFiber A K hK v).Nonempty := by
  have hpop (t : FreeCell A.small A.T) :
      (FairBits.fiber K (freeRange A t) (naturalBin A v t)).Nonempty := by
    apply CompanionBinPopulation.coordinate_nonempty K (freeRange A t) A.d _ hK A.hd
    · have hh := (A.hlarge t.val.1 t.val.2 t.property.1).1
      unfold freeRange
      omega
    · exact naturalBin_lt A v t
  let x : CompanionBinPopulation.Assignments K (freeRange A) (naturalBin A v) :=
    fun t => ⟨(hpop t).choose,(hpop t).choose_spec⟩
  exact ⟨((integerFiberEquiv A K hK v).symm x).val,
    ((integerFiberEquiv A K hK v).symm x).property⟩

lemma assignmentCount_eq_prod (A : Instance I J) :
    assignmentCount A=∏ t : FreeCell A.small A.T,freeRange A t := by
  simp only [assignmentCount,FreeIndex,Fintype.card_pi,Fintype.card_fin,freeRange]

theorem population_eq_integerFiber (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (v : Grid (I := Fin (dimension A)) K) :
    CompanionBinPopulation.population K (freeRange A) (naturalBin A v)=
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A := by
  rw [CompanionBinPopulation.population_eq_card,CompanionBinPopulation.assignment_card,
    ←integerFiber_card A K hK,
    assignmentCount_eq_prod]
  simp only [dimension,Nat.cast_prod]

theorem actual_population_bounds (A : Instance I J) (K : ℕ) (hK : 0 < K)
    (hW : 100*A.d*K ≤ A.W) (v : Grid (I := Fin (dimension A)) K) :
    1/2 ≤ (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ∧
      (K:ℚ)^dimension A*(integerFiber A K hK v).card/assignmentCount A ≤ 2 := by
  have hh := CompanionBinPopulation.population_bounds K A.d (freeRange A) (naturalBin A v)
    hK A.hd (ForestScaledPenalty.free_card_le A)
    (by
      intro t
      have hb := (A.hlarge t.val.1 t.val.2 t.property.1).1
      unfold freeRange
      omega)
    (naturalBin_lt A v)
  simpa only [population_eq_integerFiber A K hK] using hh

end

end ContingencyTables.CompanionOracleDensity

end OAI
