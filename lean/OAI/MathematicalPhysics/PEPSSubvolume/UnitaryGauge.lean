import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.LocalOperators

namespace OAI

/-! Outward unitary gauges for nested physical filters. -/

noncomputable section
open scoped BigOperators ComplexOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume
open scoped Matrix.Norms.L2Operator

variable {L q : ℕ}

theorem SupportedOn.mono {A B : Finset (Vertex L)} (h : A ⊆ B)
    {M : Operator L q} (hM : SupportedOn M A) : SupportedOn M B :=
  PolynomialPEPS.PinnedEntropy.SupportedOn.mono hM h

theorem exists_local_unitary (hq : 0 < q) (A : Finset (Vertex L))
    (U : unitary (Operator L q)) (hU : SupportedOn (U : Operator L q) A) :
    ∃ V : unitary (Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ),
      liftLocal A (V : Matrix _ _ ℂ) = (U : Operator L q) := by
  obtain ⟨a, ha⟩ := hU
  have hu : a ∈ unitary (Matrix _ _ ℂ) := by
    constructor
    · apply liftLocal_injective hq A
      rw [liftLocal_mul, liftLocal_star, liftLocal_one, ← ha]
      exact U.property.1
    · apply liftLocal_injective hq A
      rw [liftLocal_mul, liftLocal_star, liftLocal_one, ← ha]
      exact U.property.2
  exact ⟨⟨a,hu⟩,ha.symm⟩

theorem posSemidef_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.PosSemidef) (V : unitary (Matrix n n ℂ)) :
    (star (V : Matrix n n ℂ) * P * (V : Matrix n n ℂ)).PosSemidef := by
  exact hP.conjTranspose_mul_mul_same (V : Matrix n n ℂ)

theorem eigenvalues_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) (hP : P.PosSemidef) (V : unitary (Matrix n n ℂ)) :
    (posSemidef_unitary_conj P hP V).isHermitian.eigenvalues =
      hP.isHermitian.eigenvalues := by
  apply ((posSemidef_unitary_conj P hP V).isHermitian.eigenvalues_eq_eigenvalues_iff
    hP.isHermitian).mpr
  rw [Matrix.charpoly_mul_comm, ← mul_assoc]
  simp

def orderedPrefix (A : ℕ → Operator L q) : ℕ → Operator L q
  | 0 => 1
  | n+1 => A n * orderedPrefix A n

@[simp] theorem orderedPrefix_zero (A : ℕ → Operator L q) : orderedPrefix A 0 = 1 := rfl
@[simp] theorem orderedPrefix_succ (A : ℕ → Operator L q) (n : ℕ) :
    orderedPrefix A (n+1) = A n * orderedPrefix A n := rfl

theorem orderedPrefix_unitary (U : ℕ → unitary (Operator L q)) (n : ℕ) :
    orderedPrefix (fun j => (U j : Operator L q)) n ∈ unitary (Operator L q) := by
  induction n with
  | zero => exact (unitary _).one_mem
  | succ n ih => exact (unitary _).mul_mem (U n).property ih

theorem orderedPrefix_supported (X : ℕ → Finset (Vertex L))
    (hX : Monotone X) (A : ℕ → Operator L q) (hA : ∀ j, SupportedOn (A j) (X j))
    (n k : ℕ) (hnk : n ≤ k) : SupportedOn (orderedPrefix A n) (X k) := by
  induction n with
  | zero => exact SupportedOn.one _
  | succ n ih =>
    exact ((hA n).mono (hX (Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self n) hnk)))).mul
      (ih (Nat.le_trans (Nat.le_succ n) hnk))

def liftUnitary (A : Finset (Vertex L))
    (U : unitary (Matrix (RegionConfiguration q A) (RegionConfiguration q A) ℂ)) :
    unitary (Operator L q) :=
  ⟨liftLocal A (U : Matrix _ _ ℂ), by
    constructor
    · rw [← liftLocal_star, ← liftLocal_mul, U.property.1, liftLocal_one]
    · rw [← liftLocal_star, ← liftLocal_mul, U.property.2, liftLocal_one]⟩

variable (hq : 0 < q) (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
  (U : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
    (RegionConfiguration q (X j)) ℂ))

def outwardPrefix (j : ℕ) :
    unitary (Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ) :=
  Classical.choose <| exists_local_unitary hq (X j)
    ⟨orderedPrefix (fun k => (liftUnitary (X k) (U k) : Operator L q)) j,
      orderedPrefix_unitary (fun k => liftUnitary (X k) (U k)) j⟩
    (orderedPrefix_supported X hX
      (fun k => (liftUnitary (X k) (U k) : Operator L q))
      (fun k => ⟨(U k : Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ),rfl⟩)
      j j le_rfl)

theorem outwardPrefix_spec (j : ℕ) :
    liftLocal (X j) (outwardPrefix hq X hX U j : Matrix _ _ ℂ) =
      orderedPrefix (fun k => (liftUnitary (X k) (U k) : Operator L q)) j :=
  Classical.choose_spec <| exists_local_unitary hq (X j)
    ⟨orderedPrefix (fun k => (liftUnitary (X k) (U k) : Operator L q)) j,
      orderedPrefix_unitary (fun k => liftUnitary (X k) (U k)) j⟩
    (orderedPrefix_supported X hX
      (fun k => (liftUnitary (X k) (U k) : Operator L q))
      (fun k => ⟨(U k : Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ),rfl⟩)
      j j le_rfl)

variable (P : (j : ℕ) → Matrix (RegionConfiguration q (X j))
    (RegionConfiguration q (X j)) ℂ)

def gaugedMatrix (j : ℕ) :
    Matrix (RegionConfiguration q (X j)) (RegionConfiguration q (X j)) ℂ :=
  star (outwardPrefix hq X hX U j : Matrix _ _ ℂ) * P j *
    (outwardPrefix hq X hX U j : Matrix _ _ ℂ)

theorem gaugedMatrix_posSemidef (hP : ∀ j, (P j).PosSemidef) (j : ℕ) :
    (gaugedMatrix hq X hX U P j).PosSemidef :=
  posSemidef_unitary_conj (P j) (hP j) (outwardPrefix hq X hX U j)

theorem gaugedMatrix_eigenvalues (hP : ∀ j, (P j).PosSemidef) (j : ℕ) :
    (gaugedMatrix_posSemidef hq X hX U P hP j).isHermitian.eigenvalues =
      (hP j).isHermitian.eigenvalues :=
  eigenvalues_unitary_conj (P j) (hP j) (outwardPrefix hq X hX U j)

theorem liftLocal_gaugedMatrix (j : ℕ) :
    liftLocal (X j) (gaugedMatrix hq X hX U P j) =
      star (orderedPrefix (fun k => (liftUnitary (X k) (U k) : Operator L q)) j) *
      liftLocal (X j) (P j) *
      orderedPrefix (fun k => (liftUnitary (X k) (U k) : Operator L q)) j := by
  simp only [gaugedMatrix, liftLocal_mul, liftLocal_star, outwardPrefix_spec]

theorem gaugeStep_eq {R : Type*} [Monoid R] [Star R]
    (A B V P : R) (hV : V * star V = 1) :
    (A * B) * (V * P) = (A * V) * (star V * B * V * P) := by
  simp only [mul_assoc]
  rw [← mul_assoc V (star V), hV, one_mul]

theorem orderedPrefix_gauge (n : ℕ) :
    orderedPrefix (fun j => liftLocal (X j) ((U j : Matrix _ _ ℂ) * P j)) n =
      orderedPrefix (fun j => (liftUnitary (X j) (U j) : Operator L q)) n *
      orderedPrefix (fun j => liftLocal (X j) (gaugedMatrix hq X hX U P j)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orderedPrefix_succ, ih, orderedPrefix_succ, orderedPrefix_succ,
      liftLocal_gaugedMatrix, liftLocal_mul]
    have hu := (orderedPrefix_unitary (fun k => liftUnitary (X k) (U k)) n).2
    exact gaugeStep_eq _ _ _ _ hu

theorem norm_asMap_unitary (V : unitary (Operator L q)) (ψ : State L q) :
    ‖asMap (V : Operator L q) ψ‖ = ‖ψ‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    (Unitary.map_mem Matrix.toEuclideanCLM V.property) ψ

theorem norm_asMap_mul_of_unitary (V A : Operator L q)
    (hV : V ∈ unitary (Operator L q)) (ψ : State L q) :
    ‖asMap (V * A) ψ‖ = ‖asMap A ψ‖ := by
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Configuration L q) (V * A) ψ‖ = _
  rw [map_mul]
  exact norm_asMap_unitary (L := L) (q := q) ⟨V,hV⟩ (asMap A ψ)

theorem norm_orderedPrefix_gauge (n : ℕ) (ψ : State L q) :
    ‖asMap (orderedPrefix (fun j => liftLocal (X j) ((U j : Matrix _ _ ℂ) * P j)) n) ψ‖ =
      ‖asMap (orderedPrefix (fun j => liftLocal (X j) (gaugedMatrix hq X hX U P j)) n) ψ‖ := by
  rw [orderedPrefix_gauge]
  exact norm_asMap_mul_of_unitary
    (L := L) (q := q)
    (orderedPrefix (fun j => (liftUnitary (X j) (U j) : Operator L q)) n)
    (orderedPrefix (fun j => liftLocal (X j) (gaugedMatrix hq X hX U P j)) n)
    (orderedPrefix_unitary (fun j => liftUnitary (X j) (U j)) n) ψ

end PolynomialPEPS.Subvolume

end

end OAI
