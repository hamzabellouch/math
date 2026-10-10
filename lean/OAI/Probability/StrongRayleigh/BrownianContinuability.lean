import OAI.Probability.StrongRayleigh.DyadicTimes
import OAI.Probability.StrongRayleigh.DyadicTail
import OAI.Probability.StrongRayleigh.LocalDyadicContinuity
import OAI.Probability.StrongRayleigh.DensePathExtension

namespace OAI

universe u_1 u_2

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336AdditiveD139.BrownianConstruction

theorem preBrownian_ae_dyadic_bound {Ω : Type u_1} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (T : ℕ) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ k, k < T * 2 ^ n →
      |B (dyadicTime (n, k + 1)) ω - B (dyadicTime (n, k)) ω| ≤
        (9 / 10 : ℝ) ^ n := by
  let D : ∀ n, Fin (T * 2 ^ n) → Ω → ℝ := fun n k ω =>
    B (dyadicTime (n, k.val + 1)) ω - B (dyadicTime (n, k.val)) ω
  have hD (n) (k : Fin (T * 2 ^ n)) : Integrable (fun ω => |D n k ω| ^ 4) P :=
    integrable_abs_pow_four_of_hasLaw
      (hB.hasLaw_sub (dyadicTime (n, k.val + 1)) (dyadicTime (n, k.val)))
  have hm (n) (k : Fin (T * 2 ^ n)) :
      (∫ ω, |D n k ω| ^ 4 ∂P) ≤ 3 * (1 / 4 : ℝ) ^ n := by
    apply le_of_eq
    exact dyadic_increment_fourth_moment (fun s t => by
      convert hB.hasLaw_sub s t using 1; rfl) n k.val
  have hs : Summable (fun n : ℕ =>
      (Fintype.card (Fin (T * 2 ^ n)) : ℝ) * (3 * (1 / 4 : ℝ)^n) /
        ((9 / 10 : ℝ)^n)^4) := by
    have hgeom : Summable (fun n : ℕ =>
        (T : ℝ) * (3 * (5000 / 6561 : ℝ)^n)) :=
      ((summable_geometric_of_norm_lt_one
        (by norm_num : ‖(5000 / 6561 : ℝ)‖ < 1)).mul_left 3).mul_left (T : ℝ)
    convert hgeom using 1
    funext n
    simp only [Fintype.card_fin, Nat.cast_mul]
    calc
      _ = (T : ℝ) * (((2 ^ n : ℕ) : ℝ) * (3 * (1 / 4 : ℝ)^n) /
          ((9 / 10 : ℝ)^n)^4) := by ring
      _ = _ := congrArg (fun x : ℝ => (T : ℝ) * x)
        (DyadicTail.dyadic_fourth_moment_cost 3 n)
  have h := DyadicTail.ae_eventually_forall_abs_le_of_summable_fourth_moments
    D (fun n => pow_pos (by norm_num) n) (fun n => by positivity) hD hm hs
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro k hk
  exact hn ⟨k, hk⟩

theorem preBrownian_ae_continuable {Ω : Type u_2} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, DensePathExtension.Continuable dyadicTime
      (fun p => B (dyadicTime p) ω) := by
  have hr := LocalDyadicContinuity.ae_globalLimit_properties_of_eventually P
    (fun ω n k => B (dyadicTime (n, k)) ω)
    (fun _ n => (9 / 10 : ℝ)^n)
    (fun _ n => by positivity)
    (fun _ => summable_geometric_of_norm_lt_one (by norm_num))
    (ae_of_all _ (fun ω n k => by rw [dyadicTime_parent]))
    (preBrownian_ae_dyadic_bound hB)
  filter_upwards [hr] with ω hω
  refine ⟨⟨_, hω.1⟩, ?_⟩
  funext p
  exact hω.2 p.1 p.2 (dyadicTime p) rfl

end Problem336AdditiveD139.BrownianConstruction

end

end OAI
