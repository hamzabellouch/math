import Mathlib

namespace OAI

noncomputable section
open scoped NNReal

namespace Problem367
namespace CavityPair

variable {ψ : ℝ → ℝ} {θ : ℝ≥0}

def step (ψ : ℝ → ℝ) (H K x : ℝ) : ℝ := H - ψ (K - ψ x)

theorem contracting_step (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (H K : ℝ) :
    ContractingWith (θ * θ) (step ψ H K) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
  · have hnonneg : (0 : ℝ) ≤ θ := θ.coe_nonneg
    have hlt : (θ : ℝ) < 1 := hθ
    change (θ : ℝ) * θ < 1
    nlinarith
  · intro x y
    simp only [step, dist_sub_left, NNReal.coe_mul]
    calc
      dist (ψ (K - ψ x)) (ψ (K - ψ y)) ≤
          θ * dist (K - ψ x) (K - ψ y) := hψ.dist_le_mul _ _
      _ = θ * dist (ψ x) (ψ y) := by rw [dist_sub_left]
      _ ≤ θ * (θ * dist x y) :=
        mul_le_mul_of_nonneg_left (hψ.dist_le_mul x y) θ.coe_nonneg
      _ = θ * θ * dist x y := by ring

theorem existsUnique (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (H K : ℝ) :
    ∃! p : ℝ × ℝ, p.1 + ψ p.2 = H ∧ p.2 + ψ p.1 = K := by
  let F := step ψ H K
  have hF : ContractingWith (θ * θ) F := contracting_step hψ hθ H K
  let x := hF.fixedPoint F
  have hx : F x = x := hF.fixedPoint_isFixedPt
  refine ⟨(x, K - ψ x), ?_, ?_⟩
  · change x + ψ (K - ψ x) = H ∧ K - ψ x + ψ x = K
    dsimp [F, step] at hx
    constructor <;> linarith
  · intro p hp
    have hpF : F p.1 = p.1 := by
      dsimp [F, step]
      rw [show K - ψ p.1 = p.2 by linarith [hp.2]]
      linarith [hp.1]
    have hp1 : p.1 = x := hF.fixedPoint_unique hpF
    apply Prod.ext hp1
    change p.2 = K - ψ x
    rw [← hp1]
    linarith [hp.2]

theorem stability_fst (hψ : LipschitzWith θ ψ) (hθ : θ < 1)
    {x y x' y' H K H' K' : ℝ}
    (hx : x + ψ y = H) (hy : y + ψ x = K)
    (hx' : x' + ψ y' = H') (hy' : y' + ψ x' = K') :
    dist x x' ≤ (dist H H' + θ * dist K K') / (1 - (θ : ℝ)^2) := by
  have hθ0 : (0 : ℝ) ≤ θ := θ.coe_nonneg
  have hθ1 : (θ : ℝ) < 1 := hθ
  have hden : 0 < 1 - (θ : ℝ)^2 := by nlinarith
  have hX : dist x x' ≤ dist H H' + θ * dist y y' := by
    calc
      dist x x' = dist (H - ψ y) (H' - ψ y') := by
        congr 1 <;> linarith
      _ ≤ dist H H' + dist (ψ y) (ψ y') := dist_sub_sub_le _ _ _ _
      _ ≤ dist H H' + θ * dist y y' := by
        gcongr
        exact hψ.dist_le_mul _ _
  have hY : dist y y' ≤ dist K K' + θ * dist x x' := by
    calc
      dist y y' = dist (K - ψ x) (K' - ψ x') := by
        congr 1 <;> linarith
      _ ≤ dist K K' + dist (ψ x) (ψ x') := dist_sub_sub_le _ _ _ _
      _ ≤ dist K K' + θ * dist x x' := by
        gcongr
        exact hψ.dist_le_mul _ _
  apply (le_div_iff₀ hden).2
  have hY' := mul_le_mul_of_nonneg_left hY hθ0
  nlinarith

theorem stability (hψ : LipschitzWith θ ψ) (hθ : θ < 1)
    {p p' z z' : ℝ × ℝ}
    (hp : p.1 + ψ p.2 = z.1 ∧ p.2 + ψ p.1 = z.2)
    (hp' : p'.1 + ψ p'.2 = z'.1 ∧ p'.2 + ψ p'.1 = z'.2) :
    dist p.1 p'.1 ≤ (dist z.1 z'.1 + θ * dist z.2 z'.2) / (1 - (θ : ℝ)^2) ∧
    dist p.2 p'.2 ≤ (dist z.2 z'.2 + θ * dist z.1 z'.1) / (1 - (θ : ℝ)^2) :=
  ⟨stability_fst hψ hθ hp.1 hp.2 hp'.1 hp'.2,
    stability_fst hψ hθ hp.2 hp.1 hp'.2 hp'.1⟩

def solve (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) : ℝ × ℝ :=
  Classical.choose (existsUnique hψ hθ z.1 z.2)

theorem solve_spec (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) :
    (solve hψ hθ z).1 + ψ (solve hψ hθ z).2 = z.1 ∧
    (solve hψ hθ z).2 + ψ (solve hψ hθ z).1 = z.2 :=
  (Classical.choose_spec (existsUnique hψ hθ z.1 z.2)).1

theorem solve_eq (hψ : LipschitzWith θ ψ) (hθ : θ < 1) {z p : ℝ × ℝ}
    (hp : p.1 + ψ p.2 = z.1 ∧ p.2 + ψ p.1 = z.2) :
    solve hψ hθ z = p :=
  ((Classical.choose_spec (existsUnique hψ hθ z.1 z.2)).2 p hp).symm

theorem lipschitzWith_solve (hψ : LipschitzWith θ ψ) (hθ : θ < 1) :
    LipschitzWith (((1 + (θ : ℝ)) / (1 - (θ : ℝ)^2)).toNNReal)
      (solve hψ hθ) := by
  apply LipschitzWith.of_dist_le'
  intro z z'
  have hθ0 : (0 : ℝ) ≤ θ := θ.coe_nonneg
  have hθ1 : (θ : ℝ) < 1 := hθ
  have hden : 0 < 1 - (θ : ℝ)^2 := by nlinarith
  have h := stability hψ hθ (solve_spec hψ hθ z) (solve_spec hψ hθ z')
  have hfst : dist z.1 z'.1 ≤ dist z z' := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hsnd : dist z.2 z'.2 ≤ dist z z' := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  rw [Prod.dist_eq]
  apply max_le
  · apply h.1.trans
    calc
      (dist z.1 z'.1 + θ * dist z.2 z'.2) / (1 - (θ : ℝ)^2) ≤
          (dist z z' + θ * dist z z') / (1 - (θ : ℝ)^2) := by
        gcongr
      _ = (1 + (θ : ℝ)) / (1 - (θ : ℝ)^2) * dist z z' := by ring
  · apply h.2.trans
    calc
      (dist z.2 z'.2 + θ * dist z.1 z'.1) / (1 - (θ : ℝ)^2) ≤
          (dist z z' + θ * dist z z') / (1 - (θ : ℝ)^2) := by
        gcongr
      _ = (1 + (θ : ℝ)) / (1 - (θ : ℝ)^2) * dist z z' := by ring

theorem continuous_solve (hψ : LipschitzWith θ ψ) (hθ : θ < 1) :
    Continuous (solve hψ hθ) :=
  (lipschitzWith_solve hψ hθ).continuous

theorem measurable_solve (hψ : LipschitzWith θ ψ) (hθ : θ < 1) :
    Measurable (solve hψ hθ) :=
  (continuous_solve hψ hθ).measurable

theorem solve_swap (hψ : LipschitzWith θ ψ) (hθ : θ < 1) (z : ℝ × ℝ) :
    solve hψ hθ z.swap = (solve hψ hθ z).swap := by
  apply solve_eq hψ hθ
  exact ⟨(solve_spec hψ hθ z).2, (solve_spec hψ hθ z).1⟩

theorem continuous_solve_comp {T : Type*} [TopologicalSpace T]
    (hψ : LipschitzWith θ ψ) (hθ : θ < 1)
    {H K : T → ℝ} (hH : Continuous H) (hK : Continuous K) :
    Continuous (fun t => solve hψ hθ (H t, K t)) :=
  (continuous_solve hψ hθ).comp (hH.prodMk hK)

end CavityPair
end Problem367

end

end OAI
