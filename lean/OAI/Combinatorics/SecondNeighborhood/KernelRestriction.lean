import OAI.Combinatorics.SecondNeighborhood.MatrixMaps

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

open Matrix
open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev PairFiber (P : Finset (X × X)) (p : X) := {j : X // (p, j) ∈ P}

def fiberIndex (P : Finset (X × X)) (p : X) (j : PairFiber P p) : ↥P :=
  ⟨(p, j.1), j.2⟩

omit [Fintype X] [DecidableEq X] in
theorem fiberIndex_injective (P : Finset (X × X)) (p : X) :
    Function.Injective (fiberIndex P p) := by
  intro j k h
  apply Subtype.ext
  exact congrArg (fun q : ↥P => q.1.2) h

omit [Fintype X] [DecidableEq X] in
theorem mem_range_fiberIndex (P : Finset (X × X)) (p : X) (q : ↥P) :
    q ∈ Set.range (fiberIndex P p) ↔ q.1.1 = p := by
  constructor
  · rintro ⟨j, rfl⟩
    rfl
  · rcases q with ⟨⟨q₁, q₂⟩, hq⟩
    intro h
    change q₁ = p at h
    subst q₁
    exact ⟨⟨q₂, hq⟩, rfl⟩

def restrictFiber (P : Finset (X × X)) (p : X) (u : ↥P → ℝ) :
    PairFiber P p → ℝ :=
  fun j => u (fiberIndex P p j)

def matrixD (R C : Finset (X × X)) (b : X → X → ℝ) (p i : X) :
    Matrix (PairFiber C i) (PairFiber R p) ℝ :=
  fun s j => b s.1 j.1

def localSupport (r : X → X → Prop) (R C : Finset (X × X)) (p i : X) :
    Set (PairFiber C i × PairFiber R p) :=
  {q | r q.1.1 q.2.1}

theorem matrixB_mulVec_fiber (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) (u : ↥R → ℝ) (p s : X)
    (hps : (p, s) ∈ H r R C) :
    (matrixB r R C b *ᵥ u) ⟨(p, s), hps⟩ =
      ∑ j : PairFiber R p, b s j.1 * u (fiberIndex R p j) := by
  classical
  change (∑ q : ↥R, matrixB r R C b ⟨(p, s), hps⟩ q * u q) = _
  symm
  apply Fintype.sum_of_injective (fiberIndex R p) (fiberIndex_injective R p)
  · intro q hq
    have hfirst : p ≠ q.1.1 := by
      intro heq
      exact hq ((mem_range_fiberIndex R p q).mpr heq.symm)
    simp [matrixB, hfirst]
  · intro j
    simp [matrixB, fiberIndex]

theorem matrixN_transpose_mulVec_fiber (r : X → X → Prop)
    (R C : Finset (X × X)) (b : X → X → ℝ) (v : ↥C → ℝ) (i j : X)
    (hij : (i, j) ∈ Z r R C) :
    ((matrixN r R C b)ᵀ *ᵥ v) ⟨(i, j), hij⟩ =
      ∑ s : PairFiber C i, b s.1 j * v (fiberIndex C i s) := by
  classical
  change (∑ q : ↥C, matrixN r R C b q ⟨(i, j), hij⟩ * v q) = _
  symm
  apply Fintype.sum_of_injective (fiberIndex C i) (fiberIndex_injective C i)
  · intro q hq
    have hfirst : q.1.1 ≠ i := by
      intro heq
      exact hq ((mem_range_fiberIndex C i q).mpr heq)
    simp [matrixN, hfirst]
  · intro s
    simp [matrixN, fiberIndex]

theorem restrictFiber_mem_kernelD (r : X → X → Prop) (R C : Finset (X × X))
    (b : X → X → ℝ) (hb : SupportedCoefficients r b) (p i : X)
    (hpi : r p i) (u : ↥R → ℝ) (hu : matrixB r R C b *ᵥ u = 0) :
    matrixD R C b p i *ᵥ restrictFiber R p u = 0 := by
  classical
  funext s
  change (∑ j : PairFiber R p, b s.1 j.1 * u (fiberIndex R p j)) = 0
  by_cases hrow : ∃ j : PairFiber R p, r s.1 j.1
  · obtain ⟨j, hj⟩ := hrow
    have hps : (p, s.1) ∈ H r R C := by
      apply mem_H.mpr
      exact ⟨i, j.1, j.2, s.2, hpi, hj⟩
    rw [← matrixB_mulVec_fiber r R C b u p s.1 hps]
    exact congrFun hu ⟨(p, s.1), hps⟩
  · apply Finset.sum_eq_zero
    intro j _
    have hzero : b s.1 j.1 = 0 := hb s.1 j.1 (fun h => hrow ⟨j, h⟩)
    rw [hzero, zero_mul]

theorem restrictFiber_mem_kernelD_transpose (r : X → X → Prop)
    (R C : Finset (X × X)) (b : X → X → ℝ) (hb : SupportedCoefficients r b)
    (p i : X) (hpi : r p i) (v : ↥C → ℝ)
    (hv : (matrixN r R C b)ᵀ *ᵥ v = 0) :
    (matrixD R C b p i)ᵀ *ᵥ restrictFiber C i v = 0 := by
  classical
  funext j
  change (∑ s : PairFiber C i, b s.1 j.1 * v (fiberIndex C i s)) = 0
  by_cases hcol : ∃ s : PairFiber C i, r s.1 j.1
  · obtain ⟨s, hs⟩ := hcol
    have hij : (i, j.1) ∈ Z r R C := by
      apply mem_Z.mpr
      exact ⟨p, s.1, j.2, s.2, hpi, hs⟩
    rw [← matrixN_transpose_mulVec_fiber r R C b v i j.1 hij]
    exact congrFun hv ⟨(i, j.1), hij⟩
  · apply Finset.sum_eq_zero
    intro s _
    have hzero : b s.1 j.1 = 0 := hb s.1 j.1 (fun h => hcol ⟨s, h⟩)
    rw [hzero, zero_mul]

end SeymourSecondNeighborhood.Pruning

end OAI
