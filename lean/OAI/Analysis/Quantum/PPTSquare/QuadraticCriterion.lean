import OAI.Analysis.Quantum.PPTSquare.SymmetricVectors

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

def symExponent (t : Fin 10) : Fin 4 →₀ ℕ :=
  Finsupp.single (symPair t).1 1 + Finsupp.single (symPair t).2 1

lemma symExponent_injective : Function.Injective symExponent := by
  have hi : Function.Injective (fun t : Fin 10 => fun i : Fin 4 =>
      (if (symPair t).1 = i then 1 else 0 : ℕ) +
      (if (symPair t).2 = i then 1 else 0 : ℕ)) := by decide
  intro a b h
  apply hi
  funext i
  simpa only [symExponent, Finsupp.add_apply, Finsupp.single_apply] using
    congrArg (fun f : Fin 4 →₀ ℕ => f i) h

lemma symExponent_degree (t : Fin 10) : (symExponent t).degree = 2 := by
  simp [symExponent]

def quadratic (u : Fin 10 → ℂ) : MvPolynomial (Fin 4) ℂ :=
  ∑ t, MvPolynomial.monomial (symExponent t) (star (u t) * symWeight t)

lemma quadratic_homogeneous (u : Fin 10 → ℂ) : (quadratic u).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro t _
  exact MvPolynomial.isHomogeneous_monomial _ (symExponent_degree t)

lemma quadratic_coeff (u : Fin 10 → ℂ) (t : Fin 10) :
    (quadratic u).coeff (symExponent t) = star (u t) * symWeight t := by
  simp [quadratic, symExponent_injective.eq_iff]

lemma quadratic_ne {u : Fin 10 → ℂ} (hu : u ≠ 0) : quadratic u ≠ 0 := by
  intro h
  apply hu
  funext t
  have hc := congrArg (fun polynomial : MvPolynomial (Fin 4) ℂ =>
    polynomial.coeff (symExponent t)) h
  rw [quadratic_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
  simpa only [mul_eq_zero, symWeight_ne, or_false, star_eq_zero, Pi.zero_apply] using hc

lemma quadratic_eval (u : Fin 10 → ℂ) (x : Fin 4 → ℂ) :
    MvPolynomial.eval x (quadratic u) = star u ⬝ᵥ xhat x := by
  simp only [quadratic, map_sum, MvPolynomial.eval_monomial, symExponent,
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index, pow_zero, pow_one, dotProduct, xhat, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro t _
  ring

variable {n m : Type} [Fintype n] [Fintype m]

lemma product_dot_product (u a : n → ℂ) (v b : m → ℂ) :
    star (product u v) ⬝ᵥ product a b = (star u ⬝ᵥ a) * (star v ⬝ᵥ b) := by
  simp only [dotProduct, product, Pi.star_apply, star_mul, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype n] [Fintype m] in
lemma product_ne_factors {u : n → ℂ} {v : m → ℂ} (h : product u v ≠ 0) :
    u ≠ 0 ∧ v ≠ 0 := by
  constructor
  · intro hu; apply h; ext ⟨i,j⟩; simp [product, hu]
  · intro hv; apply h; ext ⟨i,j⟩; simp [product, hv]

lemma range_product_quadratic {L : Map (Fin 4) (Fin 4)} (hL : PPT L)
    (u v : Fin 10 → ℂ) (hrange : ∃ w, (Z L).mulVec w = product u v)
    (x : Fin 4 → ℂ) (hrank : (L (projector x)).rank < 4) :
    MvPolynomial.eval x (quadratic u) * MvPolynomial.eval x (quadratic v) = 0 := by
  obtain ⟨w, hw⟩ := hrange
  rw [quadratic_eval, quadratic_eval, ← product_dot_product, ← hw,
    Matrix.star_mulVec, (Z_psd hL).isHermitian.eq, ← Matrix.dotProduct_mulVec,
    rank_loss_kernel hL x hrank, dotProduct_zero]

lemma no_product_in_range {L : Map (Fin 4) (Fin 4)} (hL : PPT L)
    (X : Fin 20 → Fin 4 → ℂ)
    (hRank : ∀ i, (L (projector (X i))).rank < 4)
    (hQuad : QuadraticEvaluations X)
    (u v : Fin 10 → ℂ) (hrange : ∃ w, (Z L).mulVec w = product u v) :
    product u v = 0 := by
  classical
  by_contra hne
  obtain ⟨hu, hv⟩ := product_ne_factors hne
  have huc := hQuad (quadratic u) (quadratic_homogeneous u) (quadratic_ne hu)
  have hvc := hQuad (quadratic v) (quadratic_homogeneous v) (quadratic_ne hv)
  have hc : (Finset.univ : Finset (Fin 20)) ⊆
      (Finset.univ.filter (fun i => MvPolynomial.eval (X i) (quadratic u) = 0)) ∪
      (Finset.univ.filter (fun i => MvPolynomial.eval (X i) (quadratic v) = 0)) := by
    intro i _
    have hp := range_product_quadratic hL u v hrange (X i) (hRank i)
    simpa only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      mul_eq_zero] using hp
  have hcard := (Finset.card_le_card hc).trans (Finset.card_union_le _ _)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

end TensorCriterion

namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

lemma range_mul_self_conjTranspose (Q : Matrix n m ℂ) :
    LinearMap.range (Q * Qᴴ).mulVecLin = LinearMap.range Q.mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro x ⟨w, rfl⟩
    refine ⟨Qᴴ.mulVec w, ?_⟩
    exact Matrix.mulVec_mulVec w Q Qᴴ
  · exact Matrix.rank_self_mul_conjTranspose Q

def concatenate (C : p → Matrix n m ℂ) : Matrix n (p × m) ℂ :=
  Matrix.of fun a t => C t.1 a t.2

omit [Fintype n] in
lemma concatenate_mul (C : p → Matrix n m ℂ) :
    concatenate C * (concatenate C)ᴴ = ∑ i, C i * (C i)ᴴ := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, concatenate, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.sum_apply]

lemma sqrt_mul_conjTranspose [DecidableEq n] (A : Mat n) (hA : A.PosSemidef) :
    CFC.sqrt A * (CFC.sqrt A)ᴴ = A := by
  rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self A hA.nonneg

lemma separable_nonzero_product [DecidableEq n] [DecidableEq m]
    {A : Mat (n × m)} (hA : Separable A) (hne : A ≠ 0) :
    ∃ (u : n → ℂ) (v : m → ℂ), product u v ≠ 0 ∧
      ∃ w, A.mulVec w = product u v := by
  classical
  obtain ⟨r, B, C, hB, hC, hAeq⟩ := hA
  let D (i : Fin r) : Mat (n × m) := CFC.sqrt (B i) ⊗ₖ CFC.sqrt (C i)
  let Q : Matrix (n × m) (Fin r × (n × m)) ℂ := concatenate D
  have hQ : Q * Qᴴ = A := by
    rw [show Q = concatenate D from rfl, concatenate_mul, hAeq]
    apply Finset.sum_congr rfl
    intro i _
    simp only [D, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      sqrt_mul_conjTranspose (B i) (hB i), sqrt_mul_conjTranspose (C i) (hC i)]
  have hQne : Q ≠ 0 := by
    intro hh
    apply hne
    rw [← hQ, hh, Matrix.zero_mul]
  obtain ⟨a, t, hat⟩ : ∃ a t, Q a t ≠ 0 := by
    by_contra! h
    apply hQne
    ext a t
    exact h a t
  let u : n → ℂ := fun b => CFC.sqrt (B t.1) b t.2.1
  let v : m → ℂ := fun b => CFC.sqrt (C t.1) b t.2.2
  have hv : product u v = Q.col t := rfl
  refine ⟨u, v, ?_, ?_⟩
  · intro hp
    apply hat
    exact congrFun (hv.symm.trans hp) a
  · have hm : Q.col t ∈ LinearMap.range Q.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨t, rfl⟩
    rw [← range_mul_self_conjTranspose Q, hQ] at hm
    rw [hv]
    exact hm

theorem tensor_criterion (L : Map (Fin 4) (Fin 4)) (hL : PPT L)
    (X : Fin 20 → Fin 4 → ℂ) (_hX : DistinctDirections X)
    (hRank : ∀ i, (L (projector (X i))).rank < 4)
    (hQuad : QuadraticEvaluations X)
    (hDef : ∃ y : Fin 4 → ℂ, (L (projector y)).PosDef) :
    PPT (Phi1 L) ∧ PPT (Phi2 L) ∧ Z L ≠ 0 ∧
    (∀ u v : Fin 10 → ℂ, (∃ w, (Z L).mulVec w = product u v) → product u v = 0) ∧
    ¬ EntanglementBreaking ((Phi2 L).comp (Phi1 L)) := by
  have hn := Z_ne_zero hL hDef
  have hp := no_product_in_range hL X hRank hQuad
  refine ⟨Phi1_ppt hL, Phi2_ppt hL, hn, hp, ?_⟩
  intro heb
  obtain ⟨u, v, hne, w, hw⟩ := separable_nonzero_product (eb_choi heb) hn
  exact hne (hp u v ⟨w, hw⟩)

end TensorCriterion

end

end OAI
