import OAI.Probability.InvariantIsing.Magnetic.RestrictedKernelFactorization
import OAI.Probability.InvariantIsing.Magnetic.RestrictedEndpointKernel

namespace OAI

/-! The full-spin constrained endpoint law is the product scalar-field endpoint law. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal
namespace InvariantIsing

lemma restrictedTailEndpointKernel_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) :
    restrictedTailEndpointKernel hN Finset.univ Finset.univ_nonempty n b v hb =
    fieldVectorTailEndpointKernel N (List.ofFn (fun i : Fin n => (b i,v i)))
      (finiteFieldIncrements_positive n b v hb) := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    let bs := fun j => b (j+1)
    let vs := fun j => v (j+1)
    have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j+1) (by omega)
    simp only [List.ofFn_succ,fieldVectorTailEndpointKernel]
    change restrictedTailEndpointKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs ∘ₖ
      vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion Finset.univ n bs vs)
        (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs).1 = _
    rw [ih bs vs hbs,vectorGaussianTransition_univ hN n bs vs hbs]
    rfl

lemma fieldVectorPairEndpointKernel_zero (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    fieldVectorPairEndpointKernel N L hL 0 =
      fieldVectorTailEndpointKernel N L hL ×ₖ fieldVectorTailEndpointKernel N L hL := by
  cases L <;> rfl

lemma fieldVectorPairEndpointKernel_transport (N : ℕ) {L L' : List (ℝ × ℝ≥0)}
    (he : L = L') (hL : ∀ av ∈ L, 0 < av.1) (hL' : ∀ av ∈ L', 0 < av.1)
    (i : Fin (L.length+1)) (i' : Fin (L'.length+1)) (hi : i.val = i'.val) :
    fieldVectorPairEndpointKernel N L hL i = fieldVectorPairEndpointKernel N L' hL' i' := by
  subst L'
  have hii : i = i' := Fin.ext hi
  subst i'
  rfl

theorem restrictedPairEndpointKernel_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ j < n, 0 < b j) (i : Fin (n+1)) :
    restrictedPairEndpointKernel hN Finset.univ Finset.univ_nonempty n b v hb i =
    fieldVectorPairEndpointKernel N (List.ofFn (fun j : Fin n => (b j,v j)))
      (finiteFieldIncrements_positive n b v hb) (Fin.cast (by simp) i) := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [restrictedPairEndpointKernel,Fin.cases_zero]
      rw [restrictedTailEndpointKernel_univ,Fin.cast_zero,fieldVectorPairEndpointKernel_zero]
    · let bs := fun j => b (j+1)
      let vs := fun j => v (j+1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j+1) (by omega)
      let L := List.ofFn (fun k : Fin n => (bs k,vs k))
      have hlist : List.ofFn (fun k : Fin (n+1) => (b k,v k)) = (b 0,v 0)::L := by
        rw [List.ofFn_succ]
        rfl
      have hL : ∀ av ∈ (b 0,v 0)::L, 0 < av.1 := by
        rw [← hlist]
        exact finiteFieldIncrements_positive (n+1) b v hb
      let j' : Fin (L.length+1) := Fin.cast (by simp [L]) j
      have he := fieldVectorPairEndpointKernel_transport N hlist
        (finiteFieldIncrements_positive (n+1) b v hb) hL
        (Fin.cast (by simp) j.succ) j'.succ rfl
      rw [he]
      simp only [restrictedPairEndpointKernel,Fin.cases_succ]
      change restrictedPairEndpointKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs j ∘ₖ
        vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion Finset.univ n bs vs)
          (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs).1 = _
      rw [ih bs vs hbs,vectorGaussianTransition_univ hN n bs vs hbs]
      rfl

end InvariantIsing

end

end OAI
