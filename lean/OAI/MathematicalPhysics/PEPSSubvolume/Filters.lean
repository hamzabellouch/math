import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.UnitaryGauge

namespace OAI

/-! Positive filter families and one-factor global optimization. -/

noncomputable section
open scoped BigOperators ComplexOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume

abbrev LocalPositiveFilter {L : ℕ} (q : ℕ) (X : Finset (Vertex L)) :=
  PolynomialPEPS.PinnedEntropy.NestedFilter.PositiveFilter q X

abbrev filterTracePower {L q : ℕ} {X : Finset (Vertex L)}
    (F : LocalPositiveFilter q X) (p : ℝ) :=
  PolynomialPEPS.PinnedEntropy.NestedFilter.tracePower F p

abbrev FilterFamily {L : ℕ} (q m : ℕ) (X : Fin m → Finset (Vertex L)) :=
  PolynomialPEPS.PinnedEntropy.NestedFilter.FilterFamily q m X

abbrev FilterFeasible {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (a : Fin m → ℝ) (F : FilterFamily q m X) :=
  PolynomialPEPS.PinnedEntropy.NestedFilter.Admissible a F

def orderedFilterProduct {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (F : FilterFamily q m X) : Operator L q :=
  (List.finRange m).foldl
    (fun P j => liftLocal (X j) (F j).matrix * P) 1

def filteredVector {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (F : FilterFamily q m X) (Ω : State L q) : State L q :=
  asMap (orderedFilterProduct F) Ω

def IsFilterOptimizer {L q m : ℕ} {X : Fin m → Finset (Vertex L)}
    (Ω : State L q) (a : Fin m → ℝ) (F : FilterFamily q m X) : Prop :=
  FilterFeasible a F ∧
  ∀ G : FilterFamily q m X,
    FilterFeasible a G → ‖filteredVector G Ω‖ ≤ ‖filteredVector F Ω‖

end PolynomialPEPS.Subvolume

namespace PolynomialPEPS.Subvolume.PhysicalCurve
open scoped Matrix.Norms.L2Operator BigOperators ComplexOrder
variable {L q : ℕ}

theorem orderedPrefix_eq_finRange (A : ℕ → Operator L q) (n : ℕ) :
    orderedPrefix A n =
      (List.finRange n).foldl (fun P j => A j.val * P) 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orderedPrefix_succ, List.finRange_succ_last, List.foldl_append,
      List.foldl_map]
    simpa only [List.foldl_cons, List.foldl_nil, Fin.val_last, Fin.val_castSucc] using
      congrArg (fun P => A n * P) ih

theorem orderedFilterProduct_eq_prefix (X : ℕ → Finset (Vertex L))
    (G : (j : ℕ) → LocalPositiveFilter q (X j)) (n : ℕ) :
    orderedFilterProduct (L := L) (q := q) (X := fun j : Fin n => X j.val)
      (fun j : Fin n => G j.val) =
      orderedPrefix (fun j => liftLocal (X j) (G j).matrix) n := by
  unfold orderedFilterProduct
  exact (orderedPrefix_eq_finRange (fun j => liftLocal (X j) (G j).matrix) n).symm

end PolynomialPEPS.Subvolume.PhysicalCurve

namespace PolynomialPEPS.Subvolume.OptimizerGauge
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {L q : ℕ}

theorem unitary_positive_family_bound (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : FilterFamily q n (fun j => X j.val))
    (hF : IsFilterOptimizer ψ (fun j => a j.val) F)
    (U : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
      (RegionConfiguration q (X j)) ℂ))
    (P : (j : ℕ) → LocalPositiveFilter q (X j))
    (hP : ∀ j < n, filterTracePower (P j) (2/a j) = 1) :
    ‖asMap (orderedPrefix (fun j => liftLocal (X j)
      ((U j : Matrix _ _ ℂ) * (P j).matrix)) n) ψ‖ ≤ ‖filteredVector F ψ‖ := by
  let G : (j : ℕ) → LocalPositiveFilter q (X j) := fun j =>
    ⟨gaugedMatrix hq X hX U (fun k => (P k).matrix) j,
      gaugedMatrix_posSemidef hq X hX U (fun k => (P k).matrix) (fun k => (P k).positive) j⟩
  have hG : FilterFeasible (fun j : Fin n => a j.val) (fun j : Fin n => G j.val) := by
    intro j
    change (∑ i, Real.rpow
      ((gaugedMatrix_posSemidef hq X hX U (fun k => (P k).matrix)
        (fun k => (P k).positive) j.val).isHermitian.eigenvalues i) (2/a j.val)) = 1
    rw [gaugedMatrix_eigenvalues hq X hX U (fun k => (P k).matrix) (fun k => (P k).positive)]
    exact hP j.val j.isLt
  have heq : ‖asMap (orderedPrefix (fun j => liftLocal (X j)
      ((U j : Matrix _ _ ℂ) * (P j).matrix)) n) ψ‖ =
      ‖filteredVector (fun j : Fin n => G j.val) ψ‖ := by
    rw [norm_orderedPrefix_gauge hq X hX U (fun j => (P j).matrix)]
    change _ = ‖asMap (orderedFilterProduct (fun j : Fin n => G j.val)) ψ‖
    rw [PhysicalCurve.orderedFilterProduct_eq_prefix]
  rw [heq]
  exact hF.2 _ hG

theorem prefix_update_outside (A : ℕ → Operator L q) (k n : ℕ) (B : Operator L q)
    (hnk : n ≤ k) : orderedPrefix (Function.update A k B) n = orderedPrefix A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [orderedPrefix_succ, orderedPrefix_succ, ih (by omega)]
    rw [Function.update_of_ne (show n ≠ k by omega)]

theorem prefix_update_add (A : ℕ → Operator L q) (k n : ℕ) (hk : k < n)
    (B C : Operator L q) :
    orderedPrefix (Function.update A k (B+C)) n =
      orderedPrefix (Function.update A k B) n + orderedPrefix (Function.update A k C) n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k=n
    · subst k
      simp only [orderedPrefix_succ, Function.update_self,
        prefix_update_outside A n n _ le_rfl, add_mul]
    · have hkn' : n ≠ k := Ne.symm hkn
      simp only [orderedPrefix_succ, Function.update_of_ne hkn']
      rw [ih (by omega), mul_add]

theorem prefix_update_smul (A : ℕ → Operator L q) (k n : ℕ) (hk : k < n)
    (c : ℂ) (B : Operator L q) :
    orderedPrefix (Function.update A k (c • B)) n =
      c • orderedPrefix (Function.update A k B) n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k=n
    · subst k
      simp only [orderedPrefix_succ, Function.update_self,
        prefix_update_outside A n n _ le_rfl, smul_mul_assoc]
    · have hkn' : n ≠ k := Ne.symm hkn
      simp only [orderedPrefix_succ, Function.update_of_ne hkn']
      rw [ih (by omega), mul_smul_comm]

end PolynomialPEPS.Subvolume.OptimizerGauge

namespace PolynomialPEPS.Subvolume.OptimizerGauge
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {L q : ℕ}

theorem one_replacement_bound (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (_hk : k < n)
    (V : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (G : LocalPositiveFilter q (X k)) (hG : filterTracePower G (2/a k) = 1) :
    ‖asMap (orderedPrefix (Function.update (fun j => liftLocal (X j) (F j).matrix)
      k (liftLocal (X k) ((V : Matrix _ _ ℂ) * G.matrix))) n) ψ‖ ≤
      ‖filteredVector (fun j : Fin n => F j.val) ψ‖ := by
  let U : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
      (RegionConfiguration q (X j)) ℂ) := Function.update (fun _ => 1) k V
  let P : (j : ℕ) → LocalPositiveFilter q (X j) := Function.update F k G
  have hp : ∀ j < n, filterTracePower (P j) (2/a j) = 1 := by
    intro j hj
    by_cases hjk : j=k
    · subst j
      simpa [P] using hG
    · simpa [P,Function.update_of_ne hjk] using hF.1 ⟨j,hj⟩
  have heq : (fun j => liftLocal (X j) ((U j : Matrix _ _ ℂ)*(P j).matrix)) =
      Function.update (fun j => liftLocal (X j) (F j).matrix) k
        (liftLocal (X k) ((V : Matrix _ _ ℂ)*G.matrix)) := by
    funext j
    by_cases hjk : j=k
    · subst j
      simp [U,P]
    · simp [U,P,Function.update_of_ne hjk]
  simpa only [heq] using unitary_positive_family_bound hq X hX a ψ n
    (fun j : Fin n => F j.val) hF U P hp

end PolynomialPEPS.Subvolume.OptimizerGauge

end

end OAI
