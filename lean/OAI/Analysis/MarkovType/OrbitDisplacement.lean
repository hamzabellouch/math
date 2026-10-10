import OAI.Analysis.MarkovType.MarkedChains
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

def OrbitRep (C : FiniteMarkedChain S E) :=
  {e : E // (Fintype.equivFin E) e < (Fintype.equivFin E) (C.rev e)}

instance (C : FiniteMarkedChain S E) : Fintype (OrbitRep C) := by
  classical
  unfold OrbitRep
  infer_instance

theorem orbitRep_rev_ne (C : FiniteMarkedChain S E) (j : OrbitRep C) :
    C.rev j.val ≠ j.val := by
  intro h
  have hj := j.property
  rw [h] at hj
  exact (lt_irrefl _) hj

theorem orbitRep_rev_ne_rep (C : FiniteMarkedChain S E)
    (j k : OrbitRep C) : C.rev j.val ≠ k.val := by
  intro h
  have hk := k.property
  rw [← h, C.rev_rev] at hk
  exact (lt_asymm j.property hk)

def orbitDisplacement (C : FiniteMarkedChain S E) (e : E)
    (j : OrbitRep C) : ℤ := by
  classical
  exact (if e = j.val then 1 else 0) -
    (if C.rev e = j.val then 1 else 0)

@[simp] theorem orbitDisplacement_rev (C : FiniteMarkedChain S E) (e : E) :
    orbitDisplacement C (C.rev e) = -orbitDisplacement C e := by
  classical
  funext j
  change ((if C.rev e = j.val then 1 else 0) -
    (if C.rev (C.rev e) = j.val then 1 else 0) : ℤ) =
      -((if e = j.val then 1 else 0) - (if C.rev e = j.val then 1 else 0))
  rw [C.rev_rev e]
  exact (neg_sub _ _).symm

theorem orbitDisplacement_bounds (C : FiniteMarkedChain S E)
    (e : E) (j : OrbitRep C) :
    -1 ≤ orbitDisplacement C e j ∧ orbitDisplacement C e j ≤ 1 := by
  classical
  unfold orbitDisplacement
  split_ifs <;> norm_num

@[simp] theorem orbitDisplacement_fixed (C : FiniteMarkedChain S E)
    {e : E} (he : C.rev e = e) : orbitDisplacement C e = 0 := by
  classical
  funext j
  simp [orbitDisplacement, he]

@[simp] theorem orbitDisplacement_rep_self (C : FiniteMarkedChain S E)
    (j : OrbitRep C) : orbitDisplacement C j.val j = 1 := by
  classical
  simp [orbitDisplacement, orbitRep_rev_ne C j]

theorem orbitDisplacement_rep_other (C : FiniteMarkedChain S E)
    {j k : OrbitRep C} (hjk : j ≠ k) :
    orbitDisplacement C j.val k = 0 := by
  classical
  have hval : j.val ≠ k.val := fun h => hjk (Subtype.ext h)
  simp [orbitDisplacement, hval, orbitRep_rev_ne_rep C j k]

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def labelLinear (C : FiniteMarkedChain S E) (g : E → V)
    (a : OrbitRep C → ℤ) : V :=
  ∑ j, (a j : ℝ) • g j.val

@[simp] theorem labelLinear_zero (C : FiniteMarkedChain S E) (g : E → V) :
    labelLinear C g 0 = 0 := by
  simp [labelLinear]

theorem labelLinear_add (C : FiniteMarkedChain S E) (g : E → V)
    (a b : OrbitRep C → ℤ) :
    labelLinear C g (a + b) = labelLinear C g a + labelLinear C g b := by
  simp [labelLinear, Int.cast_add, add_smul, Finset.sum_add_distrib]

@[simp] theorem labelLinear_neg (C : FiniteMarkedChain S E) (g : E → V)
    (a : OrbitRep C → ℤ) :
    labelLinear C g (-a) = -labelLinear C g a := by
  simp [labelLinear, Int.cast_neg, neg_smul, Finset.sum_neg_distrib]

theorem oddLabel_eq_zero_of_fixed (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) {e : E} (he : C.rev e = e) :
    g e = 0 := by
  have hneg : g e = -g e := by simpa [he] using hg e
  have htwo : (2 : ℝ) • g e = 0 := by
    rw [two_smul]
    calc
      g e + g e = -g e + g e := congrArg (fun v => v + g e) hneg
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem labelLinear_displacement_rep (C : FiniteMarkedChain S E)
    (g : E → V) (j : OrbitRep C) :
    labelLinear C g (orbitDisplacement C j.val) = g j.val := by
  classical
  unfold labelLinear
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [orbitDisplacement_rep_other C (Ne.symm hkj)]
    simp
  · simp

theorem labelLinear_displacement (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (e : E) :
    labelLinear C g (orbitDisplacement C e) = g e := by
  classical
  by_cases he : C.rev e = e
  · rw [orbitDisplacement_fixed C he, labelLinear_zero,
      oddLabel_eq_zero_of_fixed C hg he]
  · have hidx : (Fintype.equivFin E) e ≠ (Fintype.equivFin E) (C.rev e) :=
      fun h => he ((Fintype.equivFin E).injective h).symm
    rcases lt_or_gt_of_ne hidx with hpos | hneg
    · exact labelLinear_displacement_rep C g ⟨e, hpos⟩
    · let j : OrbitRep C := ⟨C.rev e, by rw [C.rev_rev e]; exact hneg⟩
      have hj := labelLinear_displacement_rep C g j
      change labelLinear C g (orbitDisplacement C (C.rev e)) = g (C.rev e) at hj
      rw [orbitDisplacement_rev, labelLinear_neg, hg e] at hj
      exact neg_injective hj

theorem oddLabel_zero_of_no_orbits (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (hJ : IsEmpty (OrbitRep C)) :
    ∀ e, g e = 0 := by
  let := hJ
  intro e
  rw [← labelLinear_displacement C hg e]
  simp [labelLinear]

end MarkovSuperreflexivity

end

end OAI
