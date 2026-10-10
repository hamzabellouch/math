import OAI.Probability.InvariantIsing.Magnetic.RestrictedKernelFactorization

namespace OAI

/-! Identification of the canonical member of the branching-pair family. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldVectorPairSpinKernel_zero (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    fieldVectorPairSpinKernel N L hL 0 =
      fieldVectorTailSpinKernel N L hL ×ₖ fieldVectorTailSpinKernel N L hL := by
  cases L <;> rfl

lemma fieldVectorPairSpinKernel_transport (N : ℕ) {L L' : List (ℝ × ℝ≥0)}
    (he : L = L') (hL : ∀ av ∈ L, 0 < av.1) (hL' : ∀ av ∈ L', 0 < av.1)
    (i : Fin (L.length + 1)) (i' : Fin (L'.length + 1)) (hi : i.val = i'.val) :
    fieldVectorPairSpinKernel N L hL i = fieldVectorPairSpinKernel N L' hL' i' := by
  subst L'
  have hii : i = i' := Fin.ext hi
  subst i'
  rfl

theorem restrictedPairSpinKernel_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ j < n, 0 < b j) (i : Fin (n + 1)) :
    restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb i =
      fieldVectorPairSpinKernel N (List.ofFn (fun j : Fin n => (b j, v j)))
        (finiteFieldIncrements_positive n b v hb) (Fin.cast (by simp) i) := by
  induction n generalizing b v with
  | zero =>
    change restrictedSpinKernel Finset.univ ×ₖ restrictedSpinKernel Finset.univ = _
    rw [restrictedSpinKernel_univ]
    rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [restrictedPairSpinKernel, Fin.cases_zero]
      rw [restrictedTailSpinKernel_univ, Fin.cast_zero, fieldVectorPairSpinKernel_zero]
    · let bs := fun j => b (j + 1)
      let vs := fun j => v (j + 1)
      have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
      let L := List.ofFn (fun k : Fin n => (bs k, vs k))
      have hlist : List.ofFn (fun k : Fin (n + 1) => (b k, v k)) = (b 0, v 0) :: L := by
        rw [List.ofFn_succ]
        rfl
      have hL : ∀ av ∈ (b 0, v 0) :: L, 0 < av.1 := by
        rw [← hlist]
        exact finiteFieldIncrements_positive (n + 1) b v hb
      let j' : Fin (L.length + 1) := Fin.cast (by simp [L]) j
      have he := fieldVectorPairSpinKernel_transport N hlist
        (finiteFieldIncrements_positive (n + 1) b v hb) hL
        (Fin.cast (by simp) j.succ) j'.succ rfl
      rw [he]
      simp only [restrictedPairSpinKernel, Fin.cases_succ]
      change restrictedPairSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs j ∘ₖ
        vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion Finset.univ n bs vs)
          (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs).1 = _
      rw [ih bs vs hbs, vectorGaussianTransition_univ hN n bs vs hbs]
      rfl

end InvariantIsing

end

end OAI
