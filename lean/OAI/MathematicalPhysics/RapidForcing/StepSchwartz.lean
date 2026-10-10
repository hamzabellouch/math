import OAI.MathematicalPhysics.RapidForcing.ScaleBounds
import OAI.MathematicalPhysics.RapidForcing.Rapid

namespace OAI

section

open scoped BigOperators ENNReal Topology SchwartzMap ContDiff
open Set MeasureTheory

namespace RapidForcing

lemma joint_tsupport_subset {E : Type} [NormedAddCommGroup E]
    {v : Field E} {a b : ℝ}
    (ht : ∀ t, t < a ∨ b < t → v t = 0)
    (hx : ∀ t, tsupport (v t) ⊆ K) :
    tsupport (Function.uncurry v) ⊆ Icc a b ×ˢ K := by
  apply closure_minimal _ (isClosed_Icc.prod K_closed)
  intro p hp
  refine ⟨?_, hx p.1 (subset_closure hp)⟩
  by_contra h
  have hor : p.1 < a ∨ b < p.1 := by
    by_cases ha : a ≤ p.1
    · exact Or.inr (lt_of_not_ge (fun hb => h ⟨ha, hb⟩))
    · exact Or.inl (lt_of_not_ge ha)
  exact hp (congrFun (ht p.1 hor) p.2)

lemma stepVelocity_joint_tsupport (M : Machine) (w : M.Input) (n : ℕ) :
    tsupport (Function.uncurry (stepVelocity M w n)) ⊆
      Icc ((n : ℝ) + 1) ((n : ℝ) + 2) ×ˢ K := by
  apply joint_tsupport_subset
  · intro t ht
    rcases ht with ht | ht
    · exact stepVelocity_left_collar M w n (by linarith)
    · exact stepVelocity_right_collar M w n (by linarith)
  · intro t
    apply closure_minimal _ K_closed
    intro x hx
    by_contra hK
    apply hx
    apply Finset.sum_eq_zero
    intro m hm
    exact image_eq_zero_of_notMem_tsupport (fun h => hK
      (addressCurl_tsupport_subset_K M w n m
        (Nat.le_of_lt_succ (Finset.mem_range.mp hm)) _ h))

lemma loadingVelocity_joint_tsupport (M : Machine) (w : M.Input) :
    tsupport (Function.uncurry (loadingVelocity M w)) ⊆ Icc (0 : ℝ) 1 ×ˢ K := by
  apply joint_tsupport_subset
  · intro t ht
    rcases ht with ht | ht
    · have hh := movingCurl_left_collar 0
        (vec (-1) ((M.scaleData w).δ 0 * (M.initialDigit w : ℝ)) 0) 1
        (by linarith : t < 1 / 4)
      funext x
      simpa only [loadingVelocity, zero_add, Pi.zero_apply] using congrFun hh x
    · exact loadingVelocity_right_collar M w (by linarith)
  · exact loadingCurl_tsupport_subset_K M w

lemma norm_le_slot {n : ℕ} {p : ℝ × Space}
    (hp : p ∈ Icc ((n : ℝ) + 1) ((n : ℝ) + 2) ×ˢ K) :
    ‖p‖ ≤ (n : ℝ) + 3 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  change max ‖p.1‖ ‖p.2‖ ≤ _
  apply max_le
  · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hp.1.1])]
    linarith [hp.1.2]
  · have hx := norm_le_three_of_mem_K hp.2
    linarith

lemma stepVelocity_weighted_derivative_bound (M : Machine) (w : M.Input) (J k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p : ℝ × Space,
      ‖p‖ ^ J * ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖ ≤
        C * (((n : ℝ) + 3) ^ J *
          ((M.scaleData w).b n / (M.scaleData w).δ n ^ (k + 1))) := by
  obtain ⟨C, hC, hB⟩ := stepVelocity_derivative_bound M w k
  refine ⟨C, hC, ?_⟩
  intro n p
  by_cases hp : p ∈ tsupport (Function.uncurry (stepVelocity M w n))
  · calc
      _ ≤ ((n : ℝ) + 3) ^ J *
          (C * ((M.scaleData w).b n / (M.scaleData w).δ n ^ (k + 1))) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (norm_le_slot
          (stepVelocity_joint_tsupport M w n hp)) _) (hB n p)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_iteratedFDeriv_subset k h))
    rw [hz, norm_zero, mul_zero]
    exact mul_nonneg hC (mul_nonneg (by positivity)
      (div_nonneg ((M.scaleData w).b_pos _).le (pow_nonneg ((M.scaleData w).delta_nonneg _) _)))

lemma addressedVelocity_schwartz_decay (M : Machine) (w : M.Input) (J k : ℕ) :
    ∃ C : ℝ, ∀ p : ℝ × Space,
      ‖p‖ ^ J * ‖iteratedFDeriv ℝ k (Function.uncurry (addressedVelocity M w)) p‖ ≤ C := by
  have hc : HasCompactSupport (Function.uncurry (loadingVelocity M w)) :=
    (isCompact_Icc.prod K_compact).of_isClosed_subset (isClosed_tsupport _)
      (loadingVelocity_joint_tsupport M w)
  let load : 𝓢(ℝ × Space, Space) := hc.toSchwartzMap (loadingVelocity_smooth M w)
  obtain ⟨B, hBpos, hB⟩ := load.decay J k
  obtain ⟨C, hC, hbound⟩ := stepVelocity_weighted_derivative_bound M w J k
  let d := M.scaleData w
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 3) ^ J * (d.b n / d.δ n ^ (k + 1))
  have ha : ∀ n, 0 ≤ a n := fun n => mul_nonneg (by positivity)
    (div_nonneg (d.b_pos n).le (pow_nonneg (d.delta_nonneg n) _))
  have hsum : Summable a := d.velocity_coefficient_summable J (k + 1)
  refine ⟨B + C * ∑' n, a n, ?_⟩
  intro p
  obtain ⟨N, hN⟩ := exists_nat_gt p.1
  have he : Function.uncurry (addressedVelocity M w) =ᶠ[𝓝 p]
      fun q : ℝ × Space => loadingVelocity M w q.1 q.2 +
        ∑ n ∈ Finset.range N, stepVelocity M w n q.1 q.2 := by
    have hopen : IsOpen {q : ℝ × Space | q.1 < (N : ℝ) + 1} :=
      isOpen_lt continuous_fst continuous_const
    have ho : ∀ᶠ q : ℝ × Space in 𝓝 p, q.1 < (N : ℝ) + 1 :=
      hopen.mem_nhds (by change p.1 < (N : ℝ) + 1; linarith)
    filter_upwards [ho] with q hq
    simpa only [Function.uncurry, Pi.add_apply, Finset.sum_apply] using
      congrFun (addressedVelocity_eq_finite M w N hq) q.2
  have hk : (k : ℕ∞ω) ≤ (⊤ : ℕ∞) := by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)
  have hload : ContDiffAt ℝ k (Function.uncurry (loadingVelocity M w)) p :=
    ((loadingVelocity_smooth M w).of_le hk).contDiffAt
  have hstep (n : ℕ) : ContDiffAt ℝ k (Function.uncurry (stepVelocity M w n)) p :=
    ((stepVelocity_smooth M w n).of_le hk).contDiffAt
  have hsplit : iteratedFDeriv ℝ k
      (fun q : ℝ × Space => loadingVelocity M w q.1 q.2 +
        ∑ n ∈ Finset.range N, stepVelocity M w n q.1 q.2) p =
      iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p +
        ∑ n ∈ Finset.range N,
          iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p := by
    calc
      _ = iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p +
          iteratedFDeriv ℝ k (fun q : ℝ × Space =>
            ∑ n ∈ Finset.range N, stepVelocity M w n q.1 q.2) p := by
        exact fun_iteratedFDeriv_add_apply hload
          (ContDiffAt.sum (s := Finset.range N) (fun n _ => hstep n))
      _ = _ := congrArg (_ + ·) (iteratedFDeriv_fun_sum_apply (fun n _ => hstep n))
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds, hsplit]
  calc
    _ ≤ ‖p‖ ^ J * (‖iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p‖ +
        ∑ n ∈ Finset.range N, ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = ‖p‖ ^ J * ‖iteratedFDeriv ℝ k (Function.uncurry (loadingVelocity M w)) p‖ +
        ∑ n ∈ Finset.range N, ‖p‖ ^ J *
          ‖iteratedFDeriv ℝ k (Function.uncurry (stepVelocity M w n)) p‖ := by
      rw [mul_add, Finset.mul_sum]
    _ ≤ B + ∑ n ∈ Finset.range N, C * a n := by
      exact add_le_add (hB p) (Finset.sum_le_sum (fun n _ => hbound n p))
    _ = B + C * ∑ n ∈ Finset.range N, a n := by rw [Finset.mul_sum]
    _ ≤ B + C * ∑' n, a n := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (hsum.sum_le_tsum _ (fun n _ => ha n)) hC)

noncomputable def addressedSchwartz (M : Machine) (w : M.Input) : 𝓢(ℝ × Space, Space) where
  toFun := Function.uncurry (addressedVelocity M w)
  smooth' := addressedVelocity_joint_smooth M w
  decay' := addressedVelocity_schwartz_decay M w

end RapidForcing

end

end OAI
