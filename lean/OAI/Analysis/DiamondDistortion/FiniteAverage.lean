import Mathlib

namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace FiniteAverage
variable {Ω : Type*} [Fintype Ω]

lemma jensen_sq (w f : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω, w ω = 1) :
    (∑ ω, w ω * f ω) ^ 2 ≤ ∑ ω, w ω * f ω ^ 2 := by
  let m := ∑ ω, w ω * f ω
  have hpos : 0 ≤ ∑ ω, w ω * (f ω - m) ^ 2 := by
    exact Finset.sum_nonneg (fun ω _ => mul_nonneg (hw ω) (sq_nonneg _))
  have he : (∑ ω, w ω * (f ω - m) ^ 2) =
      (∑ ω, w ω * f ω ^ 2) - 2*m*(∑ ω, w ω*f ω) + m^2*(∑ ω,w ω) := by
    calc
      _ = ∑ ω, (w ω * f ω ^ 2 - (2*m)*(w ω*f ω) + m^2*w ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  rw [he, hs] at hpos
  dsimp [m] at hpos
  nlinarith

lemma sum_mul_sq_le (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hs : ∑ ω,w ω = 1) (f : Ω → ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hf : (∑ ω, w ω * f ω ^ 2) ≤ V) :
    |∑ ω, w ω * f ω| ≤ Real.sqrt V := by
  have h := (jensen_sq w f hw hs).trans hf
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp (by
    rw [sq_abs, Real.sq_sqrt hV]
    exact h)

lemma double_product (w f g : Ω → ℝ) :
    (∑ ω, w ω * f ω) * (∑ ω, w ω * g ω) =
      ∑ ω, ∑ ν, w ω * w ν * (f ω * g ν) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

lemma norm_mean_le_sqrt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω,w ω = 1)
    (z : Ω → E) {V : ℝ} (hV : 0 ≤ V)
    (hz : (∑ ω, w ω * ‖z ω‖ ^ 2) ≤ V) :
    ‖∑ ω, w ω • z ω‖ ≤ Real.sqrt V := by
  calc
    _ ≤ ∑ ω, ‖w ω • z ω‖ := norm_sum_le _ _
    _ = ∑ ω, w ω * ‖z ω‖ := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw ω)]
    _ ≤ |∑ ω, w ω * ‖z ω‖| := le_abs_self _
    _ ≤ _ := sum_mul_sq_le w hw hs (fun ω => ‖z ω‖) hV hz

/-- Averaged opposite-sign cancellation, including the error's gate energy. -/
lemma pooled_mass {κ : Type*} [Fintype κ]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hs : ∑ ω,w ω = 1)
    (b W : Ω → κ → ℝ) (V L : Ω → ℝ)
    (hmean : ∀ g, (∑ ω,w ω*b ω g) = -(∑ ω,w ω*W ω g))
    (hW : ∀ ω, (∑ g,W ω g ^ 2) ≤ V ω)
    (hopp : ∀ ω ν, (∑ g, (|b ω g| * |b ν g| - b ω g*b ν g)) ≤ L ω + L ν) :
    (∑ g, (∑ ω,w ω* |b ω g|)^2) ≤ (∑ ω,w ω*V ω) + 2*(∑ ω,w ω*L ω) := by
  have hsign : (∑ g, (∑ ω,w ω*b ω g)^2) ≤ ∑ ω,w ω*V ω := by
    calc
      _ ≤ ∑ g, ∑ ω,w ω*(W ω g)^2 := by
        apply Finset.sum_le_sum
        intro g _
        rw [hmean g, neg_sq]
        exact jensen_sq w (fun ω => W ω g) hw hs
      _ = ∑ ω,w ω*(∑ g,W ω g^2) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hW ω) (hw ω)
  have hleft : (∑ g, ((∑ ω,w ω* |b ω g|)^2 - (∑ ω,w ω*b ω g)^2)) =
      ∑ ω,∑ ν,w ω*w ν*(∑ g,(|b ω g| * |b ν g| - b ω g*b ν g)) := by
    calc
      _ = ∑ g, ∑ ω,∑ ν,w ω*w ν*(|b ω g| * |b ν g| - b ω g*b ν g) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [sq, sq, double_product, double_product, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ν _
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
  have hright : (∑ ω,∑ ν,w ω*w ν*(L ω+L ν)) = 2*(∑ ω,w ω*L ω) := by
    calc
      _ = (∑ ω,w ω*L ω)*(∑ ν,w ν) + (∑ ω,w ω)*(∑ ν,w ν*L ν) := by
        simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        apply Finset.sum_congr rfl
        intro ν _
        ring
      _ = _ := by rw [hs]; ring
  have hcross : (∑ ω,∑ ν,w ω*w ν*(∑ g,(|b ω g| * |b ν g| - b ω g*b ν g))) ≤
      ∑ ω,∑ ν,w ω*w ν*(L ω+L ν) := by
    apply Finset.sum_le_sum
    intro ω _
    apply Finset.sum_le_sum
    intro ν _
    exact mul_le_mul_of_nonneg_left (hopp ω ν) (mul_nonneg (hw ω) (hw ν))
  rw [← hleft, hright, Finset.sum_sub_distrib] at hcross
  linarith

lemma joint_budget (w : Ω → ℝ) (hw : ∀ ω,0 ≤ w ω) (hs : ∑ ω,w ω=1)
    (I : Ω → Type*) [∀ ω,Fintype (I ω)] (a b : ∀ ω,I ω→ℝ) {r R : ℝ}
    (he : ∀ ω,(∑ i,a ω i^2) ≤ R^2)
    (hc : (∑ ω,w ω*(∑ i,a ω i*b ω i)) = r^2) :
    (∑ ω,w ω*(∑ i,(a ω i-b ω i)^2)) +
      (∑ ω,w ω*(r^2-∑ i,b ω i^2)) ≤ R^2-r^2 := by
  have hrow (ω : Ω) : (∑ i,(a ω i-b ω i)^2) + (r^2-∑ i,b ω i^2) =
      (∑ i,a ω i^2) - 2*(∑ i,a ω i*b ω i) + r^2 := by
    have hex : (∑ i,(a ω i-b ω i)^2) =
        (∑ i,a ω i^2) - 2*(∑ i,a ω i*b ω i) + (∑ i,b ω i^2) := by
      calc
        _ = ∑ i,(a ω i^2 - 2*(a ω i*b ω i) + b ω i^2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hex]
    ring
  have hid : (∑ ω,w ω*(∑ i,(a ω i-b ω i)^2)) +
      (∑ ω,w ω*(r^2-∑ i,b ω i^2)) = (∑ ω,w ω*(∑ i,a ω i^2)) - r^2 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add, hrow]
    calc
      _ = (∑ ω,w ω*(∑ i,a ω i^2)) - 2*(∑ ω,w ω*(∑ i,a ω i*b ω i)) +
          r^2*(∑ ω,w ω) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ = _ := by rw [hc,hs]; ring
  rw [hid]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ ω,w ω*R^2 := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (he ω) (hw ω)
    _ = R^2 := by rw [← Finset.sum_mul,hs,one_mul]

lemma sqrt_pooled {η θ : ℝ} (hη : 0 ≤ η) (hθ : 0 ≤ θ) :
    Real.sqrt η + Real.sqrt (η+2*θ) ≤ 2*Real.sqrt (η+θ) := by
  have h2 : 0 ≤ η+2*θ := by positivity
  have h1 : 0 ≤ η+θ := add_nonneg hη hθ
  have he0 := Real.sq_sqrt hη
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : Real.sqrt η * Real.sqrt (η+2*θ) ≤ η+θ := by
    have he : (Real.sqrt η * Real.sqrt (η+2*θ))^2 = η*(η+2*θ) := by
      rw [mul_pow, he0, he2]
    have hn := mul_nonneg (Real.sqrt_nonneg η) (Real.sqrt_nonneg (η+2*θ))
    nlinarith [sq_nonneg θ]
  apply (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
  nlinarith

end FiniteAverage

end DiamondDistortion

end

end OAI
