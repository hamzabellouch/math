import OAI.Analysis.MarkovType.LatticeLift
import OAI.Analysis.MarkovType.MarkedPaths
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

def prefixDisplacement (C : FiniteMarkedChain S E) {n : ℕ} (w : Fin n → E) :
    ℕ → (OrbitRep C → ℤ)
  | 0 => 0
  | k + 1 => prefixDisplacement C w k +
      if h : k < n then orbitDisplacement C (w ⟨k, h⟩) else 0

@[simp] theorem prefixDisplacement_zero (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) : prefixDisplacement C w 0 = 0 := rfl

theorem prefixDisplacement_succ (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) (i : Fin n) :
    prefixDisplacement C w (i.val + 1) =
      prefixDisplacement C w i.val + orbitDisplacement C (w i) := by
  simp [prefixDisplacement, i.isLt]

theorem prefixDisplacement_bounds (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) (k : ℕ) (j : OrbitRep C) :
    -(k : ℤ) ≤ prefixDisplacement C w k j ∧
      prefixDisplacement C w k j ≤ (k : ℤ) := by
  induction k with
  | zero => simp [prefixDisplacement]
  | succ k ih =>
      by_cases hk : k < n
      · have hd := orbitDisplacement_bounds C (w ⟨k, hk⟩) j
        simp only [prefixDisplacement, hk, dite_true, Pi.add_apply]
        constructor <;> omega
      · simp only [prefixDisplacement, hk, dite_false, add_zero]
        constructor <;> omega

theorem prefixDisplacement_total (C : FiniteMarkedChain S E)
    {n : ℕ} (w : Fin n → E) :
    prefixDisplacement C w n = ∑ i : Fin n, orbitDisplacement C (w i) := by
  classical
  have hsum (k : ℕ) : prefixDisplacement C w k =
      ∑ t ∈ Finset.range k, if h : t < n then orbitDisplacement C (w ⟨t, h⟩) else 0 := by
    induction k with
    | zero => simp [prefixDisplacement]
    | succ k ih => simp only [prefixDisplacement, Finset.sum_range_succ, ih]
  rw [hsum, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [i.isLt]

def centralPosition (C : FiniteMarkedChain S E) {n R : ℕ} (hnR : n ≤ R)
    (a : LatticeCube (OrbitRep C) (R - n)) (w : Fin n → E)
    (i : Fin (n + 1)) : LiftCube C R := fun j =>
  ⟨latticeCubeVal a j + prefixDisplacement C w i.val j, by
    have ha := latticeCube_coordinate_bounds a j
    have hd := prefixDisplacement_bounds C w i.val j
    have hi := i.isLt
    constructor <;> omega⟩

@[simp] theorem centralPosition_zero (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (w : Fin n → E) :
    centralPosition C hnR a w 0 = latticeCubeInclusion (Nat.sub_le R n) a := by
  apply latticeCubeVal_injective
  funext j
  simp [centralPosition, latticeCubeVal, latticeCubeInclusion]

theorem centralPosition_accept (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (w : Fin n → E) (i : Fin n) :
    liftAccept C R (w i) (centralPosition C hnR a w i.castSucc) := by
  intro j
  have hnext := latticeCube_coordinate_bounds (centralPosition C hnR a w i.succ) j
  simpa only [centralPosition, latticeCubeVal, Fin.val_succ, Fin.val_castSucc,
    prefixDisplacement_succ, Pi.add_apply, add_assoc] using hnext

theorem centralPosition_move (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (w : Fin n → E) (i : Fin n)
    (h : liftAccept C R (w i) (centralPosition C hnR a w i.castSucc)) :
    liftMove C R (w i) (centralPosition C hnR a w i.castSucc) h =
      centralPosition C hnR a w i.succ := by
  apply latticeCubeVal_injective
  funext j
  simp [liftMove, centralPosition, latticeCubeVal, prefixDisplacement_succ, add_assoc]

def centralLiftPath (C : FiniteMarkedChain S E) {n R : ℕ} (hnR : n ≤ R)
    (a : LatticeCube (OrbitRep C) (R - n)) (ω : MarkedPath S E n) :
    MarkedPath (S × LiftCube C R) (E × LiftCube C R) n :=
  ((ω.1, centralPosition C hnR a ω.2 0),
    fun i => (ω.2 i, centralPosition C hnR a ω.2 i.castSucc))

theorem centralLiftPath_state (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (ω : MarkedPath S E n) (i : Fin (n + 1)) :
    markedState (latticeLift C R) (centralLiftPath C hnR a ω) i =
      (markedState C ω i, centralPosition C hnR a ω.2 i) := by
  classical
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [centralLiftPath]
  · rw [markedState_succ, markedState_succ]
    change liftTarget C R (ω.2 j, centralPosition C hnR a ω.2 j.castSucc) = _
    have h := centralPosition_accept C hnR a ω.2 j
    simp only [liftTarget, h, dite_true]
    rw [centralPosition_move]

theorem centralLiftPath_valid_iff (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (ω : MarkedPath S E n) :
    markedValid (latticeLift C R) (centralLiftPath C hnR a ω) ↔ markedValid C ω := by
  constructor
  · intro h i
    have hi := h i
    rw [centralLiftPath_state] at hi
    exact congrArg Prod.fst hi
  · intro h i
    rw [centralLiftPath_state]
    exact Prod.ext (h i) rfl

theorem centralLiftPath_weight (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (a : LatticeCube (OrbitRep C) (R - n))
    (ω : MarkedPath S E n) :
    markedPathWeight (latticeLift C R) n (centralLiftPath C hnR a ω) =
      markedPathWeight C n ω / (Fintype.card (LiftCube C R) : ℝ) := by
  classical
  by_cases hv : markedValid C ω
  · rw [markedPathWeight_of_valid _ _ ((centralLiftPath_valid_iff C hnR a ω).2 hv),
      markedPathWeight_of_valid C ω hv]
    simp only [latticeLift, liftMass, centralLiftPath]
    ring
  · have hl : ¬markedValid (latticeLift C R) (centralLiftPath C hnR a ω) :=
      fun h => hv ((centralLiftPath_valid_iff C hnR a ω).1 h)
    rw [markedPathWeight_eq_zero_of_not_valid _ _ hl,
      markedPathWeight_eq_zero_of_not_valid C ω hv, zero_div]

theorem centralLiftPath_injective (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) :
    Function.Injective (fun x : LatticeCube (OrbitRep C) (R - n) × MarkedPath S E n =>
      centralLiftPath C hnR x.1 x.2) := by
  intro x y h
  have ha : x.1 = y.1 := by
    apply latticeCubeVal_injective
    funext j
    have hj := congrArg (fun ρ => latticeCubeVal ρ.1.2 j) h
    simpa [centralLiftPath, centralPosition, latticeCubeVal, latticeCubeInclusion] using hj
  have hs : x.2.1 = y.2.1 := congrArg (fun ρ => ρ.1.1) h
  have hw : x.2.2 = y.2.2 := congrArg (fun ρ => fun i => (ρ.2 i).1) h
  exact Prod.ext ha (Prod.ext hs hw)

theorem centralLiftPath_factorization (C : FiniteMarkedChain S E)
    {n R : ℕ} (hnR : n ≤ R) (F : MarkedPath S E n → ℝ) :
    (∑ x : LatticeCube (OrbitRep C) (R - n) × MarkedPath S E n,
      markedPathWeight (latticeLift C R) n (centralLiftPath C hnR x.1 x.2) * F x.2) =
      latticeDensity (OrbitRep C) n R * markedExpect C n F := by
  classical
  have hrow : (∑ ω : MarkedPath S E n,
      markedPathWeight C n ω / (Fintype.card (LiftCube C R) : ℝ) * F ω) =
      markedExpect C n F / (Fintype.card (LiftCube C R) : ℝ) := by
    unfold markedExpect
    simp only [div_mul_eq_mul_div, Finset.sum_div]
  simp only [Fintype.sum_prod_type, centralLiftPath_weight, hrow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold latticeDensity
  ring

section Potential

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem labelLinear_finSum (C : FiniteMarkedChain S E) (g : E → V)
    {ι : Type*} [Fintype ι] (f : ι → OrbitRep C → ℤ) :
    labelLinear C g (∑ i, f i) = ∑ i, labelLinear C g (f i) := by
  classical
  simp only [labelLinear, Finset.sum_apply, Int.cast_sum, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem centralLiftPath_potential (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) {n R : ℕ} (hnR : n ≤ R)
    (a : LatticeCube (OrbitRep C) (R - n)) (ω : MarkedPath S E n) :
    liftPotential C g R
        (markedState (latticeLift C R) (centralLiftPath C hnR a ω) (Fin.last n)) -
      liftPotential C g R
        (markedState (latticeLift C R) (centralLiftPath C hnR a ω) 0) = edgeSum g ω := by
  rw [centralLiftPath_state, centralLiftPath_state]
  change labelLinear C g
      (latticeCubeVal a + prefixDisplacement C ω.2 n) -
      labelLinear C g (latticeCubeVal a + prefixDisplacement C ω.2 0) = _
  rw [prefixDisplacement_zero, add_zero, labelLinear_add, prefixDisplacement_total,
    labelLinear_finSum]
  simp_rw [labelLinear_displacement C hg]
  unfold edgeSum
  abel

end Potential

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem lattice_central_cost_le (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) (p : ℝ) {n R : ℕ} (hnR : n ≤ R) :
    latticeDensity (OrbitRep C) n R * markedSumCost C g p n ≤
      stateCost (latticeLift C R).toStateChain (liftPotential C g R) p n := by
  classical
  let f : LatticeCube (OrbitRep C) (R - n) × MarkedPath S E n →
      MarkedPath (S × LiftCube C R) (E × LiftCube C R) n :=
    fun x => centralLiftPath C hnR x.1 x.2
  let H : StatePath (S × LiftCube C R) n → ℝ :=
    fun η => Real.rpow (‖liftPotential C g R (η (Fin.last n)) -
      liftPotential C g R (η 0)‖) p
  let G : MarkedPath (S × LiftCube C R) (E × LiftCube C R) n → ℝ :=
    fun ω => markedPathWeight (latticeLift C R) n ω *
      H (markedState (latticeLift C R) ω)
  have hG (ω) : 0 ≤ G ω :=
    mul_nonneg (markedPathWeight_nonneg _ _ _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hsum : (∑ x, G (f x)) =
      latticeDensity (OrbitRep C) n R * markedSumCost C g p n := by
    have hfact := centralLiftPath_factorization C hnR
      (fun ω => Real.rpow (‖edgeSum g ω‖) p)
    simpa only [G, H, f, centralLiftPath_potential C hg, markedSumCost] using hfact
  rw [← hsum]
  calc
    (∑ x, G (f x)) = ∑ ω ∈ Finset.univ.image f, G ω := by
      rw [Finset.sum_image]
      exact fun x _ y _ h => centralLiftPath_injective C hnR h
    _ ≤ ∑ ω, G ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun ω _ _ => hG ω)
    _ = stateCost (latticeLift C R).toStateChain (liftPotential C g R) p n := by
      change markedExpect (latticeLift C R) n
        (fun ω => H (markedState (latticeLift C R) ω)) = _
      rw [markedExpect_state]
      rfl

end MarkovSuperreflexivity

end

end OAI
