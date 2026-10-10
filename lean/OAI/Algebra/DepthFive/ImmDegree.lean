import OAI.Algebra.DepthFive.Basic

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

variable {K : Type*} [CommSemiring K]

/-- A product of matrices whose entries are linear is homogeneous in its length. -/
theorem matrix_list_prod_isHomogeneous {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix ι ι (MvPolynomial σ K)))
    (hL : ∀ A ∈ L, ∀ i j, (A i j).IsHomogeneous 1) (i j : ι) :
    (L.prod i j).IsHomogeneous L.length := by
  induction L generalizing i j with
  | nil =>
      simp only [List.prod_nil, List.length_nil, Matrix.one_apply]
      split_ifs
      · exact MvPolynomial.isHomogeneous_one σ K
      · exact MvPolynomial.isHomogeneous_zero σ K 0
  | cons A L ih =>
      simp only [List.prod_cons, List.length_cons, Matrix.mul_apply]
      apply MvPolynomial.IsHomogeneous.sum
      intro k hk
      simpa only [Nat.add_comm] using
        (hL A (List.mem_cons_self) i k).mul
          (ih (fun B hB => hL B (List.mem_cons_of_mem A hB)) k j)

/-- The iterated matrix multiplication polynomial has its expected degree. -/
theorem imm_isHomogeneous (K : Type*) [CommSemiring K] (n : ℕ) :
    (imm K n).IsHomogeneous n := by
  classical
  unfold imm
  split_ifs with hn
  · simpa only [List.length_ofFn] using
      matrix_list_prod_isHomogeneous (List.ofFn (fun t : Fin n => immLayer K n t))
        (by
          intro A hA i j
          obtain ⟨t, rfl⟩ := List.mem_ofFn.mp hA
          exact MvPolynomial.isHomogeneous_X K (t, i, j))
        (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  · exact MvPolynomial.isHomogeneous_zero _ _ _

/-- Matrix multiplication adds weighted degrees, including repeated layer occurrences. -/
theorem matrix_list_map_prod_isWeightedHomogeneous {σ ι τ M : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (w : σ → M) (A : τ → Matrix ι ι (MvPolynomial σ K)) (d : τ → M)
    (L : List τ) (hA : ∀ t ∈ L, ∀ i j, (A t i j).IsWeightedHomogeneous w (d t))
    (i j : ι) :
    ((L.map A).prod i j).IsWeightedHomogeneous w (L.map d).sum := by
  induction L generalizing i j with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil, Matrix.one_apply]
      split_ifs
      · exact MvPolynomial.isWeightedHomogeneous_one K w
      · exact MvPolynomial.isWeightedHomogeneous_zero K w 0
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, Matrix.mul_apply]
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro k hk
      exact (hA t List.mem_cons_self i k).mul
        (ih (fun s hs => hA s (List.mem_cons_of_mem t hs)) k j)

/-- Every monomial of IMM uses each matrix layer once, expressed with arbitrary additive weights. -/
theorem imm_isWeightedHomogeneous (K : Type*) [CommSemiring K] (n : ℕ)
    {M : Type*} [AddCommMonoid M] (w : Fin n → M) :
    (imm K n).IsWeightedHomogeneous (fun x => w x.1) (∑ t, w t) := by
  classical
  unfold imm
  split_ifs with hn
  · simpa only [← List.ofFn_eq_map, List.sum_ofFn] using
      matrix_list_map_prod_isWeightedHomogeneous
        (fun x : Fin n × Fin n × Fin n => w x.1) (immLayer K n) w (List.finRange n)
        (fun t ht i j => MvPolynomial.isWeightedHomogeneous_X K _ (t, i, j))
        (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n)
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

/-- The degree in any selected collection of matrix layers is its cardinality. -/
theorem imm_layers_isWeightedHomogeneous (K : Type*) [CommSemiring K] (n : ℕ)
    (s : Finset (Fin n)) :
    (imm K n).IsWeightedHomogeneous (fun x => if x.1 ∈ s then 1 else 0) s.card := by
  classical
  simpa using imm_isWeightedHomogeneous K n (fun t => if t ∈ s then (1 : ℕ) else 0)

/-- A support monomial has degree exactly one in each individual matrix layer. -/
theorem imm_support_layer_weight (K : Type*) [CommSemiring K] (n : ℕ)
    (t : Fin n) {d : (Fin n × Fin n × Fin n) →₀ ℕ} (hd : d ∈ (imm K n).support) :
    Finsupp.weight (fun x : Fin n × Fin n × Fin n => if x.1 = t then (1 : ℕ) else 0) d = 1 := by
  classical
  simpa using
    (imm_isWeightedHomogeneous K n (fun s => if s = t then (1 : ℕ) else 0))
      (MvPolynomial.mem_support_iff.mp hd)

/-- IMM is multilinear in every matrix-entry variable. -/
theorem imm_degreeOf_le_one (K : Type*) [CommSemiring K] (n : ℕ)
    (x : Fin n × Fin n × Fin n) : (imm K n).degreeOf x ≤ 1 := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hdeg := imm_support_layer_weight K n x.1 hd
  rw [Finsupp.weight_apply, Finsupp.sum] at hdeg
  by_cases hx : d x = 0
  · simp [hx]
  · calc
      d x = d x • (if x.1 = x.1 then (1 : ℕ) else 0) := by simp
      _ ≤ ∑ y ∈ d.support, d y • (if y.1 = x.1 then (1 : ℕ) else 0) :=
        Finset.single_le_sum (f := fun y => d y • (if y.1 = x.1 then (1 : ℕ) else 0))
          (fun y hy => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hx)
      _ = 1 := hdeg

/-- Evaluation assigning every matrix layer the identity matrix. -/
def immIdentityEvaluation (K : Type*) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n × Fin n) K →+* K :=
  MvPolynomial.eval (fun x => if x.2.1 = x.2.2 then 1 else 0)

@[simp] theorem immIdentityEvaluation_layer (n : ℕ) (t : Fin n) :
    (immIdentityEvaluation K n).mapMatrix (immLayer K n t) = 1 := by
  classical
  ext i j
  simp [immIdentityEvaluation, immLayer, Matrix.one_apply]

/-- Evaluation at identity matrices sends any product of variable layers to the identity. -/
theorem immIdentityEvaluation_layers (n : ℕ) (L : List (Fin n)) :
    (immIdentityEvaluation K n).mapMatrix ((L.map (immLayer K n)).prod) = 1 := by
  classical
  rw [map_list_prod, List.map_map]
  simp only [Function.comp_def, immIdentityEvaluation_layer]
  simp

@[simp] theorem immIdentityEvaluation_imm (n : ℕ) (hn : 0 < n) :
    immIdentityEvaluation K n (imm K n) = 1 := by
  classical
  unfold imm
  simp only [dite_eq_left hn]
  have h : (immIdentityEvaluation K n).mapMatrix
      (List.ofFn (fun t : Fin n => immLayer K n t)).prod = 1 := by
    rw [map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, immIdentityEvaluation_layer]
    simp
  exact congrArg (fun A : Matrix (Fin n) (Fin n) K =>
    A ⟨0, hn⟩ ⟨0, hn⟩) h

/-- IMM does not vanish over any nontrivial coefficient semiring when its size is positive. -/
theorem imm_ne_zero (K : Type*) [CommSemiring K] [Nontrivial K] (n : ℕ) (hn : 0 < n) :
    imm K n ≠ 0 := by
  intro h
  have he := immIdentityEvaluation_imm (K := K) n hn
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- The total degree of IMM is the number of matrix layers. -/
theorem imm_totalDegree (K : Type*) [CommSemiring K] [Nontrivial K] (n : ℕ) :
    (imm K n).totalDegree = n := by
  by_cases hn : 0 < n
  · exact (imm_isHomogeneous K n).totalDegree (imm_ne_zero K n hn)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp [imm]

end Problem335

end

end OAI
