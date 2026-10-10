import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeMatrixFactorAction
import OAI.Analysis.KadisonSimilarity.FreeProduct.GeneratedWordDensity

namespace OAI

/-! Centering the first two letters proves covariance for the base factor. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : ReducedWordGenerated G A D)

local notation "W" => G.freeMatrixConjugationIsometry A D ι u hτ hf hgen
local notation "θ" => matrixConjugateLetter D ι u

private theorem freeMatrix_base_product (n : ℕ) (x : A) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    W (G.vector ((x : P) * (d : P) *
      (alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)))) =
    G.vector ((x : P) * (θ d : P) *
      (alternatingProduct (fun i => (a i : P)) (fun i => (θ (c i) : P)) * (b : P))) := by
  induction n using Nat.strong_induction_on generalizing x d b with
  | h n ih =>
    let x₀ : A := x - G.trace (x : P) • 1
    let d₀ : D := d - G.trace (d : P) • 1
    have hx₀ : G.trace (x₀ : P) = 0 := by
      change G.trace ((x : P) - G.trace (x : P) • (1 : P)) = 0
      simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]
    have hd₀ : G.trace (d₀ : P) = 0 := by
      change G.trace ((d : P) - G.trace (d : P) • (1 : P)) = 0
      simp only [map_sub, map_smul, hτ, smul_eq_mul, mul_one, sub_self]
    let w := alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)
    let w' := alternatingProduct (fun i => (a i : P)) (fun i => (θ (c i) : P)) * (b : P)
    have hxd : W (G.vector ((x₀ : P) * (d₀ : P) * w)) =
        G.vector ((x₀ : P) * (θ d₀ : P) * w') := by
      simpa only [alternatingProduct_cons, OneMemClass.coe_one, one_mul,
        matrixConjugateLetter_one_letter, Fin.cons_zero, Fin.cons_succ, w, w', mul_assoc] using
        G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen (n + 1) 1 b
          (Fin.cons x₀ a) (Fin.cons d₀ c)
          (fun i => Fin.cases hx₀ ha i) (fun i => Fin.cases hd₀ hc i)
    have hdw : W (G.vector ((d₀ : P) * w)) = G.vector ((θ d₀ : P) * w') := by
      simpa only [w, w', mul_assoc] using
        G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen n d₀ b a c ha hc
    have hxw : W (G.vector ((x : P) * w)) = G.vector ((x : P) * w') := by
      cases n with
      | zero =>
        simpa only [w, w', alternatingProduct_zero, one_mul, MulMemClass.coe_mul] using
          G.freeMatrixConjugationIsometry_base A D ι u hτ hf hgen (x * b)
      | succ m =>
        have h := ih m (Nat.lt_succ_self m) (x * a 0) (c 0) b
          (fun i => a i.succ) (fun i => c i.succ)
          (fun i => ha i.succ) (fun i => hc i.succ)
        simpa only [w, w', alternatingProduct_cons, MulMemClass.coe_mul, mul_assoc] using h
    have heq : (x : P) * (d : P) * w =
        (x₀ : P) * (d₀ : P) * w + G.trace (x : P) • ((d₀ : P) * w) +
          G.trace (d : P) • ((x : P) * w) := by
      change (x : P) * (d : P) * w =
        ((x : P) - G.trace (x : P) • 1) * ((d : P) - G.trace (d : P) • 1) * w +
        G.trace (x : P) • (((d : P) - G.trace (d : P) • 1) * w) +
        G.trace (d : P) • ((x : P) * w)
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    have hd₀eq : (θ d₀ : P) = (θ d : P) - G.trace (d : P) • 1 := by
      dsimp only [d₀]
      rw [matrixConjugateLetter_sub, matrixConjugateLetter_smul,
        matrixConjugateLetter_one_letter]
      rfl
    have heq' : (x : P) * (θ d : P) * w' =
        (x₀ : P) * (θ d₀ : P) * w' + G.trace (x : P) • ((θ d₀ : P) * w') +
          G.trace (d : P) • ((x : P) * w') := by
      rw [hd₀eq]
      change (x : P) * (θ d : P) * w' =
        ((x : P) - G.trace (x : P) • 1) * ((θ d : P) - G.trace (d : P) • 1) * w' +
        G.trace (x : P) • (((θ d : P) - G.trace (d : P) • 1) * w') +
        G.trace (d : P) • ((x : P) * w')
      simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    change W (G.vector ((x : P) * (d : P) * w)) = G.vector ((x : P) * (θ d : P) * w')
    rw [heq, map_add, map_add, map_smul, map_smul, map_add, map_add, map_smul, map_smul,
      hxd, hdw, hxw]
    rw [heq', map_add, map_add, map_smul, map_smul]

theorem freeMatrixConjugationIsometry_base_left (x : A) :
    (W).toContinuousLinearMap.comp (G.left (x : P)) =
      (G.left (x : P)).comp (W).toContinuousLinearMap := by
  apply sub_eq_zero.mp
  apply continuousLinearMap_eq_zero_of_total (G.freeWordFamily A D)
    (G.freeWordFamily_total A D hgen)
  rintro ⟨n, p⟩
  change W (G.left (x : P) (G.freeWordFamily A D ⟨n, p⟩)) -
    G.left (x : P) (W (G.freeWordFamily A D ⟨n, p⟩)) = 0
  apply sub_eq_zero.mpr
  change W (G.left (x : P) (tracialAlgebraFamily G A D n p)) =
    G.left (x : P) (W (tracialAlgebraFamily G A D n p))
  unfold tracialAlgebraFamily
  rw [G.left_vector, G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen
    n p.2.1 p.1.2 (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2), G.left_vector]
  simpa only [mul_assoc] using
    G.freeMatrix_base_product A D ι u hτ hf hgen n x p.2.1 p.1.2
      (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
      (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2)

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
