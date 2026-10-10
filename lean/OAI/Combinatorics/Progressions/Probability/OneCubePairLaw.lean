import OAI.Combinatorics.Progressions.Estimates.SampledCommonSlice

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A : Type*} [AddCommGroup A]

def oneCubePairEquiv (Q : Set A) : SupportedCube 1 Q ≃ Q × Q where
  toFun p := (⟨p.val.2, p.base_mem⟩, ⟨p.val.2 + p.val.1 0, p.axis_mem 0⟩)
  invFun p := ⟨(fun _ => p.2.val - p.1.val, p.1.val), by
    intro ω
    simp only [cubeShift, Fin.sum_univ_one]
    cases h : ω 0 <;> simp [p.1.property, p.2.property]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      dsimp
      abel
    · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      dsimp
      abel

theorem oneCube_expect_eq_pair (Q : Set A) [Fintype Q] (F : A → A → ℂ) :
    (𝔼 p : SupportedCube 1 Q, F p.val.2 (p.val.2 + p.val.1 0)) =
      𝔼 x : Q, 𝔼 y : Q, F x.val y.val := by
  calc
    _ = 𝔼 p : Q × Q, F p.1.val p.2.val :=
      Fintype.expect_equiv (oneCubePairEquiv Q) _ _ (fun _ => rfl)
    _ = _ := expect_prod_split _

theorem oneCube_expect_product (Q : Set A) [Fintype Q] (f g : A → ℂ) :
    (𝔼 p : SupportedCube 1 Q, f p.val.2 * g (p.val.2 + p.val.1 0)) =
      (𝔼 x : Q, f x.val) * (𝔼 y : Q, g y.val) := by
  rw [oneCube_expect_eq_pair Q (fun x y => f x * g y)]
  simp_rw [← Finset.mul_expect]
  exact (Finset.expect_mul _ _ _).symm

theorem mixedCubeProduct_one (F : (Fin 1 → Bool) → A → ℂ)
    (h : Fin 1 → A) (x : A) :
    mixedCubeProduct F h x =
      F (fun _ => false) x * star (F (fun _ => true) (x + h 0)) := by
  rw [← Fin.cons_self_tail h, mixedCubeProduct_cons]
  simp only [mixedCubeProduct_zero, Fin.cons_zero]
  have hc (v : Bool) : Fin.cons v (default : Fin 0 → Bool) = (fun _ => v) := by
    funext i
    fin_cases i
    rfl
  rw [hc, hc]

theorem oneCube_mixed_mean (Q : Set A) [Fintype Q]
    (F : (Fin 1 → Bool) → A → ℂ) :
    (𝔼 p : SupportedCube 1 Q, mixedCubeProduct F p.val.1 p.val.2) =
      (𝔼 x : Q, F (fun _ => false) x.val) *
        star (𝔼 y : Q, F (fun _ => true) y.val) := by
  simp_rw [mixedCubeProduct_one]
  rw [oneCube_expect_product Q (F (fun _ => false))
    (fun y => star (F (fun _ => true) y)), expect_star]

theorem normalizedSupportedCubeSum_one (Q : Finset A)
    (F : (Fin 1 → Bool) → A → ℂ) :
    normalizedSupportedCubeSum 1 Q F =
      (𝔼 x ∈ Q, F (fun _ => false) x) * star (𝔼 y ∈ Q, F (fun _ => true) y) := by
  classical
  have hm := oneCube_mixed_mean (Q : Set A) F
  simpa [Fintype.expect_eq_sum_div_card, normalizedSupportedCubeSum, Finset.sum_attach,
    supportedCubeSum, Nat.card_eq_fintype_card,
    Finset.expect_eq_sum_div_card] using hm

theorem normalizedSupportedCubeSum_one_self (Q : Finset A) (f : A → ℂ) :
    normalizedSupportedCubeSum 1 Q (fun _ => f) = (‖𝔼 x ∈ Q, f x‖ ^ 2 : ℝ) := by
  rw [normalizedSupportedCubeSum_one]
  exact (Complex.mul_conj _).trans (by rw [Complex.normSq_eq_norm_sq])

end Erdos3

end

end OAI
