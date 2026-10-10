import OAI.Combinatorics.Progressions.Linear.MixedPairPartitionKernel

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def cubicExchangeSwap {X : Type*} (x : Fin 2 → X) : Fin 2 → X := fun i => x i.rev

theorem expect_cubicExchangeSwap {X : Type*} [Fintype X] (f : (Fin 2 → X) → ℝ) :
    (𝔼 x, f (cubicExchangeSwap x)) = 𝔼 x, f x := by
  let e : (Fin 2 → X) ≃ (Fin 2 → X) :=
    { toFun := cubicExchangeSwap
      invFun := cubicExchangeSwap
      left_inv := fun x => by funext i; simp [cubicExchangeSwap]
      right_inv := fun x => by funext i; simp [cubicExchangeSwap] }
  exact Fintype.expect_equiv e _ f (fun _ => rfl)

def cubicReducedCorner (i : Fin 7) (x : Fin 2 → ℤ) : CubicReplicatedIndex → ℤ :=
  ![cubicTrilinearInput (x 1) (x 0) (x 1),
    cubicTrilinearInput (x 1) (x 0) (x 1),
    cubicTrilinearInput (x 1) (x 0) (x 0),
    cubicTrilinearInput (x 0) (x 1) (x 1),
    cubicTrilinearInput (x 0) (x 0) (x 1),
    cubicTrilinearInput (x 0) (x 0) (x 1),
    cubicTrilinearInput (x 0) (x 0) (x 0)] i

def cubicSymmetricCorner (i : Fin 7) (x : Fin 2 → ℤ) : CubicReplicatedIndex → ℤ :=
  ![cubicTrilinearInput (x 0) (x 1) (x 1),
    cubicTrilinearInput (x 0) (x 1) (x 1),
    cubicTrilinearInput (x 0) (x 0) (x 1),
    cubicTrilinearInput (x 0) (x 1) (x 1),
    cubicTrilinearInput (x 0) (x 0) (x 1),
    cubicTrilinearInput (x 0) (x 0) (x 1),
    cubicTrilinearInput (x 0) (x 0) (x 0)] i

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicSymmetricSeven (a : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ i, W.eval (a i) (cubicSymmetricCorner i x))

theorem cubicSymmetricSeven_norm (a : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.cubicSymmetricSeven a x‖ ≤ 1 := by
  rw [cubicSymmetricSeven, norm_star, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem cubicSymmetricSeven_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin 7 → Fin W.outputDim, ‖W.cubicSymmetricSeven a x‖ ^ 2 = 1 := by
  simp only [cubicSymmetricSeven, norm_star, norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ i : Fin 7, ∑ a : Fin W.outputDim, ‖W.eval a (cubicSymmetricCorner i x)‖ ^ 2 :=
      (Fintype.prod_sum _).symm
    _ = 1 := by simp only [W.unit_eval, Finset.prod_const_one]

theorem cubicSymmetricSeven_explicit (a : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.cubicSymmetricSeven a x = star
      ((W.eval (a 0) (cubicTrilinearInput (x 0) (x 1) (x 1)) *
        W.eval (a 1) (cubicTrilinearInput (x 0) (x 1) (x 1)) *
        W.eval (a 3) (cubicTrilinearInput (x 0) (x 1) (x 1))) *
       (W.eval (a 2) (cubicTrilinearInput (x 0) (x 0) (x 1)) *
        W.eval (a 4) (cubicTrilinearInput (x 0) (x 0) (x 1)) *
        W.eval (a 5) (cubicTrilinearInput (x 0) (x 0) (x 1))) *
        W.eval (a 6) (cubicTrilinearInput (x 0) (x 0) (x 0))) := by
  rw [cubicSymmetricSeven, Fin.prod_univ_seven]
  dsimp [cubicSymmetricCorner]
  congr 1
  ring

noncomputable def cubicSevenOriginalFactor (a b : Fin 7 → Fin W.outputDim)
    (k : Fin 7) (x : Fin 2 → ℤ) : ℂ :=
  W.eval (a k) (cubicReducedCorner k x) * star (W.eval (b k) (cubicSymmetricCorner k x))

theorem cubicSevenOriginalFactor_norm (a b : Fin 7 → Fin W.outputDim)
    (k : Fin 7) (x : Fin 2 → ℤ) : ‖W.cubicSevenOriginalFactor a b k x‖ ≤ 1 := by
  rw [cubicSevenOriginalFactor, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

noncomputable def cubicSevenExchangeFactor
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin 7 → Fin W.outputDim) (k : Fin 7) (x : Fin 2 → ℤ) : ℂ :=
  ![star (G (b 0) (a 0) x), star (G (b 1) (a 1) x), G (a 2) (b 2) (cubicExchangeSwap x),
    W.cubicSevenOriginalFactor a b 3 x, W.cubicSevenOriginalFactor a b 4 x,
    W.cubicSevenOriginalFactor a b 5 x, W.cubicSevenOriginalFactor a b 6 x] k

noncomputable def cubicSevenExchangeProduct
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ k, W.cubicSevenExchangeFactor G a b k x)

theorem cubicMixedSeven_cross_symmetric
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
      W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
        W.eval i x)
    (a b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.cubicMixedSeven a x * star (W.cubicSymmetricSeven b x) =
      star (∏ k, W.cubicSevenOriginalFactor a b k x) := by
  have hred : W.cubicMixedSeven a x = star (∏ k, W.eval (a k) (cubicReducedCorner k x)) := by
    rw [W.cubicMixedSeven_replica_reduction hsymm, Fin.prod_univ_seven]
    rfl
  rw [hred, cubicSymmetricSeven]
  simp only [cubicSevenOriginalFactor, Finset.prod_mul_distrib, star_prod, star_mul, star_star]
  ring

theorem cubicSevenExchangeFactor_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1)
    (a b : Fin 7 → Fin W.outputDim) (k : Fin 7) (x : Fin 2 → ZMod N) :
    ‖W.cubicSevenExchangeFactor G a b k (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
  fin_cases k
  · exact (norm_star _).le.trans (hG _ _ x)
  · exact (norm_star _).le.trans (hG _ _ x)
  · exact hG _ _ (cubicExchangeSwap x)
  all_goals exact W.cubicSevenOriginalFactor_norm _ _ _ _

theorem cubicSevenExchangeProduct_norm {N : ℕ} [NeZero N]
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1)
    (a b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicSevenExchangeProduct G a b (fun z => ((x z).val : ℤ))‖ ≤ 1 := by
  rw [cubicSevenExchangeProduct, norm_star, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun k _ => W.cubicSevenExchangeFactor_norm G hG a b k x)

theorem cubicSevenExchangeFactor_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
      W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
        W.eval i x)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a b : Fin 7 → Fin W.outputDim) (k : Fin 7) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicSevenOriginalFactor a b k (fun z => ((x z).val : ℤ)) -
        W.cubicSevenExchangeFactor G a b k (fun z => ((x z).val : ℤ))‖) ≤
      ![ε, ε, ε, 0, 0, 0, 0] k := by
  have hstar (u v g : ℂ) : ‖v * star u - star g‖ = ‖u * star v - g‖ := by
    calc
      _ = ‖star (u * star v - g)‖ := by
        congr 1
        simp only [star_sub, star_mul, star_star]
      _ = _ := norm_star _
  fin_cases k
  · change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval (a 0) (cubicTrilinearInput (x 1).val (x 0).val (x 1).val) *
          star (W.eval (b 0) (cubicTrilinearInput (x 0).val (x 1).val (x 1).val)) -
        star (G (b 0) (a 0) (fun z => ((x z).val : ℤ)))‖) ≤ ε
    simpa only [hstar] using herr (b 0) (a 0)
  · change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval (a 1) (cubicTrilinearInput (x 1).val (x 0).val (x 1).val) *
          star (W.eval (b 1) (cubicTrilinearInput (x 0).val (x 1).val (x 1).val)) -
        star (G (b 1) (a 1) (fun z => ((x z).val : ℤ)))‖) ≤ ε
    simpa only [hstar] using herr (b 1) (a 1)
  · let e : (Fin 2 → ZMod N) → ℝ := fun x =>
      ‖W.eval (a 2) (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval (b 2) (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G (a 2) (b 2) (fun z => ((x z).val : ℤ))‖
    have hs : (𝔼 x, e (cubicExchangeSwap x)) ≤ ε :=
      (expect_cubicExchangeSwap e).le.trans (herr (a 2) (b 2))
    apply le_trans _ hs
    apply le_of_eq
    apply Finset.expect_congr rfl
    intro x _
    change ‖W.eval (a 2) (cubicTrilinearInput (x 1).val (x 0).val (x 0).val) *
        star (W.eval (b 2) (cubicTrilinearInput (x 0).val (x 0).val (x 1).val)) -
      G (a 2) (b 2) (fun z => ((x z.rev).val : ℤ))‖ =
      ‖W.eval (a 2) (cubicTrilinearInput (x 1).val (x 0).val (x 0).val) *
        star (W.eval (b 2) (cubicTrilinearInput (x 0).val (x 1).val (x 0).val)) -
      G (a 2) (b 2) (fun z => ((x z.rev).val : ℤ))‖
    rw [W.eval_cubicTrilinearInput_swap hsymm (b 2) (x 0).val (x 0).val (x 1).val]
  all_goals simp [cubicSevenExchangeFactor]

theorem cubicSevenExchangeProduct_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (hsymm : ∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) i x,
      W.eval i (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
        W.eval i x)
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ 1)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a b : Fin 7 → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicMixedSeven a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicSevenExchangeProduct G a b (fun z => ((x z).val : ℤ))‖) ≤ 3 * ε := by
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ∑ k : Fin 7,
        ‖W.cubicSevenOriginalFactor a b k (fun z => ((x z).val : ℤ)) -
          W.cubicSevenExchangeFactor G a b k (fun z => ((x z).val : ℤ))‖ := by
      apply Finset.expect_le_expect
      intro x _
      rw [W.cubicMixedSeven_cross_symmetric hsymm, cubicSevenExchangeProduct, ← star_sub, norm_star]
      exact norm_unit_prod_sub_prod_le_sum Finset.univ _ _
        (fun k _ => W.cubicSevenOriginalFactor_norm _ _ k _)
        (fun k _ => W.cubicSevenExchangeFactor_norm G hG _ _ k x)
    _ = ∑ k : Fin 7, 𝔼 x : Fin 2 → ZMod N,
        ‖W.cubicSevenOriginalFactor a b k (fun z => ((x z).val : ℤ)) -
          W.cubicSevenExchangeFactor G a b k (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_sum_comm _ _ _
    _ ≤ ∑ k : Fin 7, ![ε, ε, ε, 0, 0, 0, 0] k :=
      Finset.sum_le_sum (fun k _ => W.cubicSevenExchangeFactor_mean_error hsymm G herr a b k)
    _ = _ := by rw [Fin.sum_univ_seven]; dsimp; ring

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators NNReal

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicWrappedDiagonalCorrection (N : ℕ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin 7 → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  ∑ k, W.cubicDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x

noncomputable def cubicCyclicDiagonalCorrection (N : ℕ) (δ : ℝ≥0)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin 7 → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  (1 - (smoothCyclicCarry N δ x : ℂ)) * F a b x +
    (smoothCyclicCarry N δ x : ℂ) * W.cubicWrappedDiagonalCorrection N F a b x

theorem cubicWrappedDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin 7 → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin 7 → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ))‖) ≤ W.outputDim * ε := by
  have hpoint (x : Fin 2 → ℤ) :
      ‖W.cubicWrappedDiagonalDerivative N a x * star (W.cubicSymmetricSeven b x) -
        W.cubicWrappedDiagonalCorrection N F a b x‖ ≤
      ∑ k, ‖W.cubicDiagonalDerivative (a.1, k) x * star (W.cubicSymmetricSeven b x) -
        F (a.1, k) b x‖ := by
    have heq : W.cubicWrappedDiagonalDerivative N a x * star (W.cubicSymmetricSeven b x) -
        W.cubicWrappedDiagonalCorrection N F a b x =
        ∑ k, W.cubicDiagonalWrapCoefficient N a.2 k x *
          (W.cubicDiagonalDerivative (a.1, k) x * star (W.cubicSymmetricSeven b x) -
            F (a.1, k) b x) := by
      rw [W.cubicWrappedDiagonalDerivative_resolution, Finset.sum_mul]
      simp only [cubicWrappedDiagonalCorrection, mul_sub, Finset.sum_sub_distrib, mul_assoc]
    rw [heq]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (W.cubicDiagonalWrapCoefficient_norm N a.2 k x)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N,
        ∑ k, ‖W.cubicDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ :=
      Finset.expect_le_expect (fun x _ => hpoint _)
    _ = ∑ k, 𝔼 x : Fin 2 → ZMod N,
        ‖W.cubicDiagonalDerivative (a.1, k) (fun z => ((x z).val : ℤ)) *
            star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
          F (a.1, k) b (fun z => ((x z).val : ℤ))‖ := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _k : Fin W.outputDim, ε := Finset.sum_le_sum (fun k _ => herr (a.1, k) b)
    _ = _ := by simp

theorem cubicCyclicDiagonalCorrection_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (δ : ℝ≥0) (hδ : 0 < δ)
    (F : (Fin W.outputDim × Fin W.outputDim) →
      (Fin 7 → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        F a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a : Fin W.outputDim × Fin W.outputDim)
    (b : Fin 7 → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicCyclicDiagonalDerivative a x * star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicCyclicDiagonalCorrection N δ F a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim + 1) * ε + 12 * (δ : ℝ) + 2 / N := by
  have hpoint (x : Fin 2 → ZMod N) := norm_smoothed_branch_error
    (cyclicCarry (x 0) (x 1)) (smoothCyclicCarry N δ (fun z => ((x z).val : ℤ)))
    (circleCarryCutoff_range δ _)
    (W.cubicDiagonalDerivative a (fun z => ((x z).val : ℤ)) *
      star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))))
    (W.cubicWrappedDiagonalDerivative N a (fun z => ((x z).val : ℤ)) *
      star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))))
    (F a b (fun z => ((x z).val : ℤ)))
    (W.cubicWrappedDiagonalCorrection N F a b (fun z => ((x z).val : ℤ)))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (W.cubicDiagonalDerivative_norm a _)).trans
        (W.cubicSymmetricSeven_norm b _))
    (by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (W.cubicWrappedDiagonalDerivative_norm N a _)).trans (W.cubicSymmetricSeven_norm b _))
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Complex.ofReal_sub, Complex.ofReal_one, ← mul_assoc, ← add_mul,
    ← W.cubicCyclicDiagonalDerivative_branches] at hm
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at hm
  have hi := herr a b
  have hw := W.cubicWrappedDiagonalCorrection_mean_error F herr a b
  have hc := smoothCyclicCarry_mean_error (N := N) δ hδ
  dsimp only [cubicCyclicDiagonalCorrection]
  exact hm.trans ((add_le_add (add_le_add hi hw)
    (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

theorem exists_cubicCyclicDiagonalCorrection_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q e : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (N : ℕ)
      (δ : ℝ≥0), 0 < δ → 0 ≤ q → 0 ≤ e → (δ : ℝ)⁻¹ ≤ Real.exp e →
      ∀ F : (Fin W.outputDim × Fin W.outputDim) →
          (Fin 7 → Fin W.outputDim) → (Fin 2 → ℤ) → ℂ,
        (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 q (F a b))) →
        ∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
          ((p + q + e + C) ^ C) (W.cubicCyclicDiagonalCorrection N δ F a b)) := by
  obtain ⟨A, _, hwrap⟩ := exists_cubicDiagonalWrapCoefficient_expansion
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + Polynomial.C A) ^ A + X + (X + 6) ^ 2 + 13
  let T := (R + Polynomial.C B) ^ B + X + R + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C B) ^ B + T + 2)
  refine ⟨C, hC, ?_⟩
  intro p q e W N δ hδ hq he hinv F hF a b
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let v := p + q + e
  let r := (v + A) ^ A + v + (v + 6) ^ 2 + 13
  let t := (r + B) ^ B + v + r + 2
  let d := (t + B) ^ B + t
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have har : (p + A) ^ A ≤ r := by
    calc
      _ ≤ (v + A) ^ A := pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
      _ ≤ r := by dsimp [r]; nlinarith [sq_nonneg (v + 6)]
  have hqr : q ≤ r := by
    have : 0 ≤ (v + A) ^ A := by positivity
    have hs : 0 ≤ (v + 6) ^ 2 := sq_nonneg _
    dsimp [r, v] at *
    linarith
  have her : raisedNiltestBudget (e + 4) ≤ r := by
    have hpow : (e + 6) ^ 2 ≤ (v + 6) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) 2
    have hA : 0 ≤ (v + A) ^ A := by positivity
    have hev : e ≤ v := by dsimp [v]; linarith
    dsimp [raisedNiltestBudget, r]
    nlinarith
  have hrt : r ≤ t := by
    have : 0 ≤ (r + B) ^ B := by positivity
    dsimp [t]
    linarith
  have hwt : (r + B) ^ B + p ≤ t := by dsimp [t, v]; linarith
  have htd : t ≤ d := le_add_of_nonneg_left (by positivity)
  have hpd : (t + B) ^ B ≤ d := le_add_of_nonneg_right ht
  have hcost : d + 2 ≤ (p + q + e + C) ^ C := by
    simpa [X, R, T, r, t, d, v, Polynomial.eval₂_pow] using hbudget v hv
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp p := by
    simpa only [Fintype.card_fin] using W.output_bound
  have hcoeff : (∑ _k : Fin W.outputDim, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hdim
  have hterms (k : Fin W.outputDim) := hmul hr
    ((Classical.choice (hwrap W N a.2 k)).mono har) ((Classical.choice (hF (a.1, k) b)).mono hqr)
  have EW : NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 t
      (W.cubicWrappedDiagonalCorrection N F a b) := by
    have E := (NativeIntegerExpansion.weightedSum (fun k => Classical.choice (hterms k))
      (fun _ => (1 : ℂ)) hp hdim hcoeff).mono hwt
    change NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 t
      (fun x => ∑ k, W.cubicDiagonalWrapCoefficient N a.2 k x * F (a.1, k) b x)
    simpa only [one_mul] using E
  let w := fun x => (smoothCyclicCarry N δ x : ℂ)
  have EC := ((Classical.choice (exists_smoothCyclicCarry_expansion N δ hδ he hinv)).raiseStep
    (by norm_num : 1 ≤ 2) (by positivity : 0 ≤ e + 4)).mono (her.trans hrt)
  have E₀ := (Classical.choice (hF a b)).mono (hqr.trans (hrt.trans htd))
  have E₁ := (Classical.choice (hmul ht EC EW)).mono hpd
  have E₂ := (Classical.choice (hmul ht EC ((Classical.choice (hF a b)).mono (hqr.trans hrt)))).mono hpd
  let fs : Fin 3 → (Fin 2 → ℤ) → ℂ := ![F a b,
    (fun x => w x * W.cubicWrappedDiagonalCorrection N F a b x), (fun x => w x * F a b x)]
  have Efs (j : Fin 3) : Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2 d (fs j)) := by
    fin_cases j
    · exact ⟨E₀⟩
    · exact ⟨E₁⟩
    · exact ⟨E₂⟩
  let cs : Fin 3 → ℂ := ![1, 1, -1]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have E := (NativeIntegerExpansion.weightedSum (fun j => Classical.choice (Efs j)) cs
    (by norm_num : (0 : ℝ) ≤ 2) (by simpa using hthree)
    (by convert hthree using 1; norm_num [cs, Fin.sum_univ_succ])).mono hcost
  have heq : (fun x => ∑ j, cs j * fs j x) = W.cubicCyclicDiagonalCorrection N δ F a b := by
    funext x
    simp [cs, fs, Fin.sum_univ_succ, w, cubicCyclicDiagonalCorrection]
    ring
  exact ⟨heq ▸ E⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicPermutedExchangeLeft
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  complexCrossContraction
    (W.eval a (cubicTrilinearInput (x 1) (x 1) (x 0)))
    (W.eval b (cubicTrilinearInput (x 0) (x 1) (x 1)))
    (fun i => W.eval i (cubicTrilinearInput (x 1) (x 0) (x 1)))
    (fun j => W.eval j (cubicTrilinearInput (x 0) (x 1) (x 1)))
    (fun i j => star (G j i x))

noncomputable def cubicPermutedExchangeRight
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  complexCrossContraction
    (W.eval a (cubicTrilinearInput (x 1) (x 0) (x 0)))
    (W.eval b (cubicTrilinearInput (x 0) (x 0) (x 1)))
    (fun i => W.eval i (cubicTrilinearInput (x 1) (x 0) (x 0)))
    (fun j => W.eval j (cubicTrilinearInput (x 0) (x 1) (x 0)))
    (fun i j => G i j (cubicExchangeSwap x))

theorem cubicPermutedExchangeLeft_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicPermutedExchangeLeft G a b (fun z => ((x z).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  have h := norm_complexCrossContraction_le_card
    (W.eval a (cubicTrilinearInput (x 1).val (x 1).val (x 0).val))
    (W.eval b (cubicTrilinearInput (x 0).val (x 1).val (x 1).val))
    (fun i => W.eval i (cubicTrilinearInput (x 1).val (x 0).val (x 1).val))
    (fun j => W.eval j (cubicTrilinearInput (x 0).val (x 1).val (x 1).val))
    (fun i j => star (G j i (fun z => ((x z).val : ℤ))))
    (W.norm_eval a _) (W.norm_eval b _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)
    (fun i j => (norm_star _).le.trans (hG j i x))
  convert h using 1 <;> first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

theorem cubicPermutedExchangeRight_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (a b : Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicPermutedExchangeRight G a b (fun z => ((x z).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  have h := norm_complexCrossContraction_le_card
    (W.eval a (cubicTrilinearInput (x 1).val (x 0).val (x 0).val))
    (W.eval b (cubicTrilinearInput (x 0).val (x 0).val (x 1).val))
    (fun i => W.eval i (cubicTrilinearInput (x 1).val (x 0).val (x 0).val))
    (fun j => W.eval j (cubicTrilinearInput (x 0).val (x 1).val (x 0).val))
    (fun i j => G i j (fun z => ((x z.rev).val : ℤ)))
    (W.norm_eval a _) (W.norm_eval b _) (fun i => W.norm_eval i _) (fun j => W.norm_eval j _)
    (fun i j => hG i j (cubicExchangeSwap x))
  convert h using 1 <;> first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

theorem cubicPermutedExchangeLeft_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 1).val (x 1).val (x 0).val) *
          star (W.eval b (cubicTrilinearInput (x 0).val (x 1).val (x 1).val)) -
        W.cubicPermutedExchangeLeft G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 2 * ε := by
  have hstar (u v g : ℂ) : ‖v * star u - star g‖ = ‖u * star v - g‖ := by
    rw [← norm_star (u * star v - g)]
    simp only [star_sub, star_mul, star_star]
  have h := mean_complexCrossContraction_error_le_card
    (fun x : Fin 2 → ZMod N => W.eval a (cubicTrilinearInput (x 1).val (x 1).val (x 0).val))
    (fun x => W.eval b (cubicTrilinearInput (x 0).val (x 1).val (x 1).val))
    (fun i x => W.eval i (cubicTrilinearInput (x 1).val (x 0).val (x 1).val))
    (fun j x => W.eval j (cubicTrilinearInput (x 0).val (x 1).val (x 1).val))
    (fun i j x => star (G j i (fun z => ((x z).val : ℤ))))
    (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
    (fun _ => W.unit_eval _) (fun _ => W.unit_eval _)
    (fun _ _ => W.norm_eval _ _) (fun _ _ => W.norm_eval _ _)
    (fun i j => by simpa only [hstar] using herr j i)
  convert h using 1 <;> first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

theorem cubicPermutedExchangeRight_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a b : Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 1).val (x 0).val (x 0).val) *
          star (W.eval b (cubicTrilinearInput (x 0).val (x 0).val (x 1).val)) -
        W.cubicPermutedExchangeRight G a b (fun z => ((x z).val : ℤ))‖) ≤
      (W.outputDim : ℝ) ^ 2 * ε := by
  have hswap (i j : Fin W.outputDim) :
      (𝔼 x : Fin 2 → ZMod N,
        ‖W.eval i (cubicTrilinearInput (x 1).val (x 0).val (x 0).val) *
            star (W.eval j (cubicTrilinearInput (x 0).val (x 1).val (x 0).val)) -
          G i j (fun z => ((x z.rev).val : ℤ))‖) ≤ ε :=
    (expect_cubicExchangeSwap (fun x : Fin 2 → ZMod N =>
      ‖W.eval i (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval j (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G i j (fun z => ((x z).val : ℤ))‖)).le.trans (herr i j)
  have h := mean_complexCrossContraction_error_le_card
    (fun x : Fin 2 → ZMod N => W.eval a (cubicTrilinearInput (x 1).val (x 0).val (x 0).val))
    (fun x => W.eval b (cubicTrilinearInput (x 0).val (x 0).val (x 1).val))
    (fun i x => W.eval i (cubicTrilinearInput (x 1).val (x 0).val (x 0).val))
    (fun j x => W.eval j (cubicTrilinearInput (x 0).val (x 1).val (x 0).val))
    (fun i j x => G i j (fun z => ((x z.rev).val : ℤ)))
    (fun _ => W.norm_eval _ _) (fun _ => W.norm_eval _ _)
    (fun _ => W.unit_eval _) (fun _ => W.unit_eval _)
    (fun _ _ => W.norm_eval _ _) (fun _ _ => W.norm_eval _ _) hswap
  convert h using 1 <;> first | rfl | simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

def cubicSevenMerge {I : Type*} (a b : Fin 3 → I) (c : I) : Fin 7 → I :=
  ![a 0, a 1, b 0, a 2, b 1, b 2, c]

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicHnnTensor (a : Fin 3 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval 3 a (cubicTrilinearInput (x 0) (x 1) (x 1))

noncomputable def cubicHhnTensor (a : Fin 3 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  tensorVector W.eval 3 a (cubicTrilinearInput (x 0) (x 0) (x 1))

theorem cubicHnnTensor_norm (a : Fin 3 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.cubicHnnTensor a x‖ ≤ 1 := by
  rw [cubicHnnTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem cubicHhnTensor_norm (a : Fin 3 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    ‖W.cubicHhnTensor a x‖ ≤ 1 := by
  rw [cubicHhnTensor, tensorVector, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => W.norm_eval _ _)

theorem cubicHnnTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin 3 → Fin W.outputDim, ‖W.cubicHnnTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval 3 _

theorem cubicHhnTensor_unit (x : Fin 2 → ℤ) :
    ∑ a : Fin 3 → Fin W.outputDim, ‖W.cubicHhnTensor a x‖ ^ 2 = 1 :=
  tensorVector_unit W.eval W.unit_eval 3 _

theorem cubicSymmetricSeven_merge (a b : Fin 3 → Fin W.outputDim)
    (c : Fin W.outputDim) (x : Fin 2 → ℤ) :
    star (W.cubicSymmetricSeven (cubicSevenMerge a b c) x) =
      W.cubicHnnTensor a x * W.cubicHhnTensor b x * W.eval c (fun _ => x 0) := by
  rw [W.cubicSymmetricSeven_explicit, star_star]
  simp only [cubicSevenMerge, cubicHnnTensor, cubicHhnTensor, tensorVector, Fin.prod_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  have hdiag : cubicTrilinearInput (x 0) (x 0) (x 0) = fun _ => x 0 := by
    funext j
    simp [cubicTrilinearInput]
  rw [hdiag]
  rfl

end NativeMultidegreeNilcharacter
end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicRawSevenFactor (a b : Fin 7 → Fin W.outputDim)
    (k : Fin 7) (x : Fin 2 → ℤ) : ℂ :=
  W.eval (a k) (cubicDiagonalCorner k.succ x) *
    star (W.eval (b k) (cubicSymmetricCorner k x))

theorem cubicRawSevenFactor_norm (a b : Fin 7 → Fin W.outputDim)
    (k : Fin 7) (x : Fin 2 → ℤ) : ‖W.cubicRawSevenFactor a b k x‖ ≤ 1 := by
  rw [cubicRawSevenFactor, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)

theorem cubicMixedSeven_cross_symmetric_raw
    (a b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.cubicMixedSeven a x * star (W.cubicSymmetricSeven b x) =
      star (∏ k, W.cubicRawSevenFactor a b k x) := by
  simp only [cubicMixedSeven, cubicSymmetricSeven, cubicRawSevenFactor,
    Finset.prod_mul_distrib, star_prod, star_mul, star_star]
  ring

noncomputable def cubicPermutedSevenFactor
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin 7 → Fin W.outputDim) (k : Fin 7) (x : Fin 2 → ℤ) : ℂ :=
  ![W.cubicPermutedExchangeLeft G (a 0) (b 0) x, star (G (b 1) (a 1) x),
    W.cubicPermutedExchangeRight G (a 2) (b 2) x,
    W.cubicRawSevenFactor a b 3 x, W.cubicRawSevenFactor a b 4 x,
    W.cubicRawSevenFactor a b 5 x, W.cubicRawSevenFactor a b 6 x] k

noncomputable def cubicPermutedSevenProduct
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (a b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ℤ) : ℂ :=
  star (∏ k, W.cubicPermutedSevenFactor G a b k x)

theorem cubicPermutedSevenFactor_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (a b : Fin 7 → Fin W.outputDim) (k : Fin 7) (x : Fin 2 → ZMod N) :
    ‖W.cubicPermutedSevenFactor G a b k (fun z => ((x z).val : ℤ))‖ ≤
      (W.outputDim : ℝ) ^ 2 * B := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hBQ : B ≤ (W.outputDim : ℝ) ^ 2 * B :=
    le_mul_of_one_le_left (zero_le_one.trans hB) hd2
  fin_cases k
  · exact W.cubicPermutedExchangeLeft_norm G hG _ _ x
  · exact ((norm_star _).le.trans (hG _ _ x)).trans hBQ
  · exact W.cubicPermutedExchangeRight_norm G hG _ _ x
  all_goals exact (W.cubicRawSevenFactor_norm _ _ _ _).trans (hB.trans hBQ)

theorem cubicPermutedSevenProduct_norm {N : ℕ} [NeZero N] {B : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (a b : Fin 7 → Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicPermutedSevenProduct G a b (fun z => ((x z).val : ℤ))‖ ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ 7 := by
  rw [cubicPermutedSevenProduct, norm_star, norm_prod]
  calc
    _ ≤ ∏ _ : Fin 7, (W.outputDim : ℝ) ^ 2 * B :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun k _ => W.cubicPermutedSevenFactor_norm G hB hG a b k x)
    _ = _ := by simp

theorem cubicPermutedSevenFactor_mean_error {N : ℕ} [NeZero N] {ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a b : Fin 7 → Fin W.outputDim) (k : Fin 7) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicRawSevenFactor a b k (fun z => ((x z).val : ℤ)) -
        W.cubicPermutedSevenFactor G a b k (fun z => ((x z).val : ℤ))‖) ≤
      ![(W.outputDim : ℝ) ^ 2 * ε, ε, (W.outputDim : ℝ) ^ 2 * ε, 0, 0, 0, 0] k := by
  have hstar (u v g : ℂ) : ‖v * star u - star g‖ = ‖u * star v - g‖ := by
    rw [← norm_star (u * star v - g)]
    simp only [star_sub, star_mul, star_star]
  fin_cases k
  · exact W.cubicPermutedExchangeLeft_mean_error G herr (a 0) (b 0)
  · change (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval (a 1) (cubicTrilinearInput (x 1).val (x 0).val (x 1).val) *
          star (W.eval (b 1) (cubicTrilinearInput (x 0).val (x 1).val (x 1).val)) -
        star (G (b 1) (a 1) (fun z => ((x z).val : ℤ)))‖) ≤ ε
    simpa only [hstar] using herr (b 1) (a 1)
  · exact W.cubicPermutedExchangeRight_mean_error G herr (a 2) (b 2)
  all_goals simp [cubicPermutedSevenFactor]

theorem cubicPermutedSevenProduct_mean_error {N : ℕ} [NeZero N] {B ε : ℝ}
    (G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ) (hB : 1 ≤ B)
    (hG : ∀ a b (x : Fin 2 → ZMod N), ‖G a b (fun z => ((x z).val : ℤ))‖ ≤ B)
    (herr : ∀ a b, (𝔼 x : Fin 2 → ZMod N,
      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
          star (W.eval b (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
        G a b (fun z => ((x z).val : ℤ))‖) ≤ ε)
    (a b : Fin 7 → Fin W.outputDim) :
    (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicMixedSeven a (fun z => ((x z).val : ℤ)) *
          star (W.cubicSymmetricSeven b (fun z => ((x z).val : ℤ))) -
        W.cubicPermutedSevenProduct G a b (fun z => ((x z).val : ℤ))‖) ≤
      ((W.outputDim : ℝ) ^ 2 * B) ^ 7 * ((2 * (W.outputDim : ℝ) ^ 2 + 1) * ε) := by
  have hd : (1 : ℝ) ≤ W.outputDim := by exact_mod_cast W.output_pos
  have hd2 : (1 : ℝ) ≤ (W.outputDim : ℝ) ^ 2 := by nlinarith
  have hQ : 1 ≤ (W.outputDim : ℝ) ^ 2 * B :=
    hB.trans (le_mul_of_one_le_left (zero_le_one.trans hB) hd2)
  calc
    _ ≤ 𝔼 x : Fin 2 → ZMod N, ((W.outputDim : ℝ) ^ 2 * B) ^ 7 * ∑ k : Fin 7,
        ‖W.cubicRawSevenFactor a b k (fun z => ((x z).val : ℤ)) -
          W.cubicPermutedSevenFactor G a b k (fun z => ((x z).val : ℤ))‖ := by
      apply Finset.expect_le_expect
      intro x _
      rw [W.cubicMixedSeven_cross_symmetric_raw, cubicPermutedSevenProduct, ← star_sub, norm_star]
      exact norm_prod_sub_prod_le_sum_error Finset.univ _ _ hQ
        (fun k _ => (W.cubicRawSevenFactor_norm _ _ k _).trans hQ)
        (fun k _ => W.cubicPermutedSevenFactor_norm G hB hG _ _ k x)
    _ = ((W.outputDim : ℝ) ^ 2 * B) ^ 7 * ∑ k : Fin 7, 𝔼 x : Fin 2 → ZMod N,
        ‖W.cubicRawSevenFactor a b k (fun z => ((x z).val : ℤ)) -
          W.cubicPermutedSevenFactor G a b k (fun z => ((x z).val : ℤ))‖ := by
      rw [← Finset.mul_expect, Finset.expect_sum_comm]
    _ ≤ ((W.outputDim : ℝ) ^ 2 * B) ^ 7 * ∑ k : Fin 7,
        ![(W.outputDim : ℝ) ^ 2 * ε, ε, (W.outputDim : ℝ) ^ 2 * ε, 0, 0, 0, 0] k :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k _ => W.cubicPermutedSevenFactor_mean_error G herr a b k))
        (by positivity)
    _ = _ := by rw [Fin.sum_univ_seven]; dsimp; ring

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
