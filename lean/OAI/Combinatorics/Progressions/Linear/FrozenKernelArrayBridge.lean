import OAI.Combinatorics.Progressions.Lattices.RegularizedAffineComparison

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem canonicalAffineRawArray_frozen_kernel {D G Z α : Type*} [Fintype D]
    [Fintype α] [DecidableEq α] {B O J N : D → Type*}
    [∀ d, Fintype (B d)] [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    [∀ d, Fintype (J d)] [∀ d, DecidableEq (J d)] [∀ d, Fintype (N d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (sets : ∀ d, O d → Finset α)
    (Q : D → ℝ) (hQ : ∀ d, 0 < Q d) (T : SamplerTupleIndex G B h → ℝ) (hT : ∀ k, 0 < T k)
    (eK : ∀ d, J d → SamplerTupleIndex G B h →₀ ℕ)
    (eN : ∀ d, N d → SamplerTupleIndex G B h →₀ ℕ)
    (extra : G → Option α → Z) (z : Z → ℝ)
    (v : ∀ _d : D, Finset α → SamplerTupleIndex G B h → ℤ)
    (hcoords : ∀ d j t k, k ∈ (eK d j).support →
      (v d t k : ℝ)/T k = normalizedCubeTuple (canonicalTupleInput extra) z 0 t k)
    (hfrozen : ∀ d j k, k ∈ (eK d j).support → ∃ g, k = Sum.inl g)
    (s : ∀ d, O d ↪ J d)
    (hminor : ∀ d, ((integerJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1) (v d) (sets d)).submatrix
      id (s d)).det ≠ 0)
    (x : JointBlockParameter B h α → ℝ) (c w r : ∀ d, J d ⊕ N d → ℝ) :
    let M := fun d => integerJetMatrix (fun j => MvPolynomial.monomial (eK d j) 1) (v d) (sets d)
    let S := fun d j => Q d/monomialScale T (eK d j)
    let E := fun d => normalizedPivotEquiv ((M d).submatrix id (s d)) (hminor d)
      (fun j => S d (s d j)) (fun _ => Q d)
      (fun j => div_pos (hQ d) (monomialScale_pos T hT (eK d (s d j)))) (fun _ => hQ d)
    let F := fun d => matrixSupCLM
      (normalizedIntegerColumns (remainingMatrixColumns (M d) (s d)) (fun j => S d j.val) (fun _ => Q d))
    canonicalAffineRawArray h (fun d => Sum.elim (eK d) (eN d)) Q T c w r sets
      (rawCanonicalCubeTuple extra T z (jointCubeScale h (fun i => T (.inr i)) x)) =
      fun o => jointAffineJetUnitMap s E F eN (canonicalTupleInput extra) z sets c w x r o.1 o.2 := by
  dsimp only
  apply canonicalAffineRawArray_eq_jointUnitMap h hh sets _ s hminor _
    (fun d j => div_pos (hQ d) (monomialScale_pos T hT (eK d j))) Q hQ T
    (fun k => (hT k).ne') eK eN extra z x _ c w r
  intro d
  apply normalized_frozenKernelJetMatrix (eK d) (canonicalTupleInput extra) z (sets d) (v d) T
    (hQ d).ne' (hcoords d) _ x
  intro j k hk a
  obtain ⟨g, rfl⟩ := hfrozen d j k hk
  exact ⟨extra g a, rfl⟩

end Erdos3

end

end OAI
