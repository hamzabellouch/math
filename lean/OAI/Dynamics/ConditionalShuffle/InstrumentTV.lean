import OAI.Dynamics.ConditionalShuffle.Ranks

namespace OAI

noncomputable section
namespace Revealed.Instrument
open scoped Classical
open Thorp Thorp.Conditional Thorp.Fourier Revealed.Disintegration
variable {E S G Ω : Type} [fintype_S : Fintype S] [fintype_G : Fintype G] [group_G : Group G] [Fintype Ω] [nonempty_Ω : Nonempty Ω]
variable (I : Data E S G Ω)

lemma pathJoint_marginal (e : E) (n : ℕ) (p : Fin n → S) :
    marginal (pathJoint I e n) p = weights I e n p := by
  unfold marginal
  simp_rw [pathJoint_factor]
  rw [← Finset.mul_sum, realProduct_sum _ _ (kernels_sum I e n p), mul_one]

lemma conditional_pathJoint (e : E) (n : ℕ) (p : Fin n → S)
    (hp : weights I e n p ≠ 0) :
    conditional (pathJoint I e n) p = realProduct n (kernels I e n p) := by
  funext g
  rw [conditional, pathJoint_marginal, ite_eq_right hp, pathJoint_factor]
  exact mul_div_cancel_left₀ _ hp

def distance (e : E) (n : ℕ) : ℝ :=
  ∑ p, weights I e n p * tv (realProduct n (kernels I e n p))
    (fun _ => (Fintype.card G : ℝ)⁻¹)

lemma distance_disintegration (e : E) (n : ℕ) :
    distance I e n = ∑ p, marginal (pathJoint I e n) p *
      tv (conditional (pathJoint I e n) p) (fun _ => (Fintype.card G : ℝ)⁻¹) := by
  apply Finset.sum_congr rfl
  intro p _
  rw [pathJoint_marginal]
  by_cases hp : weights I e n p = 0
  · simp [hp]
  · rw [conditional_pathJoint I e n p hp]

lemma distance_joint (e : E) (n : ℕ) :
    distance I e n = tv (pathJoint I e n)
      (fun a => weights I e n a.1 * (Fintype.card G : ℝ)⁻¹) := by
  rw [distance_disintegration, average_tv_eq (pathJoint I e n) (fairMass_nonneg _)]
  simp_rw [pathJoint_marginal]

lemma distance_nonneg (e : E) (n : ℕ) : 0 ≤ distance I e n :=
  Finset.sum_nonneg (fun p _ => mul_nonneg (weights_nonneg I e n p) (tv_nonneg _ _))

lemma realConv_uniform (μ : G → ℝ) (hμ : ∑ g, μ g = 1) :
    realConv μ (fun _ => (Fintype.card G : ℝ)⁻¹) = fun _ => (Fintype.card G : ℝ)⁻¹ := by
  funext g
  simp only [realConv, ← Finset.sum_mul, hμ, one_mul]

lemma distance_succ_le (e : E) (n : ℕ) : distance I e (n + 1) ≤ distance I e n := by
  unfold distance
  rw [sum_snoc]
  calc
    _ ≤ ∑ p : Fin n → S, ∑ s, weights I e n p * probability I (base I e n p) s *
        tv (realProduct n (kernels I e n p)) (fun _ => (Fintype.card G : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro s _
      simp only [weights, kernels, Fin.init_snoc, Fin.snoc_last, realProduct]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weights_nonneg I e n p)
        (probability_nonneg I _ s))
      have hh := tv_realConv_left (kernel I (base I e n p) s)
        (realProduct n (kernels I e n p)) (fun _ => (Fintype.card G : ℝ)⁻¹)
        (kernel_nonneg I _ s) (kernel_sum I _ s)
      rwa [realConv_uniform _ (kernel_sum I _ s)] at hh
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_mul, ← Finset.mul_sum, probability_sum, mul_one]

lemma distance_antitone (e : E) : Antitone (distance I e) :=
  antitone_nat_of_succ_le (distance_succ_le I e)

def costs (c : E → S → ℝ) (e : E) : (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => 0
  | n+1, p => costs c e n (Fin.init p) + c (base I e n (Fin.init p)) (p (Fin.last n))

lemma costs_sum_le (c : E → S → ℝ) (C : ℝ)
    (h : ∀ e, ∑ s, probability I e s * c e s ≤ C) (e : E) (n : ℕ) :
    (∑ p, weights I e n p * costs I c e n p) ≤ n * C := by
  induction n with
  | zero => simp [weights, costs]
  | succ n ih =>
      rw [sum_snoc]
      simp only [weights, costs, Fin.init_snoc, Fin.snoc_last, mul_add, Finset.sum_add_distrib]
      have ha : (∑ p : Fin n → S, ∑ s,
          weights I e n p * probability I (base I e n p) s * costs I c e n p) =
          ∑ p, weights I e n p * costs I c e n p := by
        apply Finset.sum_congr rfl
        intro p _
        rw [← Finset.sum_mul, ← Finset.mul_sum, probability_sum, mul_one]
      rw [ha]
      have hb : (∑ p : Fin n → S, ∑ s,
          weights I e n p * probability I (base I e n p) s * c (base I e n p) s) ≤ C := by
        simp_rw [mul_assoc, ← Finset.mul_sum]
        calc
          _ ≤ ∑ p : Fin n → S, weights I e n p * C := Finset.sum_le_sum
            (fun p _ => mul_le_mul_of_nonneg_left (h _) (weights_nonneg I e n p))
          _ = C := by rw [← Finset.sum_mul, weights_sum, one_mul]
      push_cast
      linarith

lemma costs_kernels (c : (G → ℝ) → ℝ) (e : E) (n : ℕ) (p : Fin n → S) :
    costs I (fun e s => c (kernel I e s)) e n p = ∑ i, c (kernels I e n p i) := by
  let retained_fintype_S := fintype_S
  let retained_group_G := group_G
  let retained_nonempty_Ω := nonempty_Ω
  induction n with
  | zero => simp [costs]
  | succ n ih =>
      rw [costs, ih, Fin.sum_univ_castSucc]
      simp only [kernels, Fin.snoc_castSucc, Fin.snoc_last]

def block (t : ℕ) : Data E (Fin t → S) G (Fin t → Ω) where
  obs e ω := observed I e t ω
  inc e ω := groupRun I e t ω
  next e p := base I e t p

lemma block_joint (e : E) (t : ℕ) : joint (block I t) e = pathJoint I e t := by
  let retained_fintype_S := fintype_S
  let retained_fintype_G := fintype_G
  let retained_nonempty_Ω := nonempty_Ω
  exact rfl
lemma block_probability (e : E) (t : ℕ) (p : Fin t → S) :
    probability (block I t) e p = weights I e t p := pathJoint_marginal I e t p

end Revealed.Instrument

end

end OAI
