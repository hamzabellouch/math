import OAI.Probability.LatticePassage.CalibrationShift
import OAI.Probability.LatticePassage.SecondMoment

namespace OAI

namespace CompanionFPP
open MeasureTheory Real Finset Filter Topology

noncomputable def rectangleTargetCocycle (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) : ℝ :=
  (∑ i ∈ range N, ∑ j ∈ range M,
    targetCocycle (z+scaleVertex i a+scaleVertex j b) ω x y) / ((N : ℝ)*M)

@[fun_prop] lemma measurable_rectangleTargetCocycle (z a b x y : Vertex) (N M : ℕ) :
    Measurable (fun ω => rectangleTargetCocycle z a b N M ω x y) := by
  unfold rectangleTargetCocycle
  fun_prop

lemma integrable_rectangleTargetCocycle (z a b x y : Vertex) (N M : ℕ) :
    Integrable (fun ω => rectangleTargetCocycle z a b N M ω x y) environmentLaw :=
  (integrable_finsetSum _ (fun _i _ => integrable_finsetSum _
    (fun _j _ => integrable_targetCocycle _ _ _))).div_const _

theorem rectangleTargetCocycle_add (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y w : Vertex) :
    rectangleTargetCocycle z a b N M ω x w =
      rectangleTargetCocycle z a b N M ω x y + rectangleTargetCocycle z a b N M ω y w := by
  unfold rectangleTargetCocycle
  simp only [targetCocycle, sum_sub_distrib]
  ring

lemma rectangleTargetCocycle_swap (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    rectangleTargetCocycle z a b N M ω x y = rectangleTargetCocycle z b a M N ω x y := by
  unfold rectangleTargetCocycle
  rw [sum_comm, mul_comm (N : ℝ)]
  congr 1
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  rw [show z+scaleVertex i a+scaleVertex j b = z+scaleVertex j b+scaleVertex i a by abel]

theorem rectangleTargetCocycle_dominated (z a b : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∀ᵐ ω ∂environmentLaw, ∀ x y,
      |rectangleTargetCocycle z a b N M ω x y| ≤ passageTime ω x y := by
  filter_upwards [targetCocycle_dominated] with ω hω
  intro x y
  unfold rectangleTargetCocycle
  rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)*M)]
  have hb : |∑ i ∈ range N, ∑ j ∈ range M,
      targetCocycle (z+scaleVertex i a+scaleVertex j b) ω x y| ≤
      (N : ℝ)*M*passageTime ω x y := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i ∈ range N, ∑ j ∈ range M, passageTime ω x y := by
        apply sum_le_sum
        intro i _
        exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _ => hω _ x y))
      _ = _ := by simp; ring
  have hp : 0 < (N : ℝ)*M := mul_pos (by exact_mod_cast hN) (by exact_mod_cast hM)
  exact (div_le_iff₀ hp).mpr (by simpa only [mul_comm (passageTime ω x y)] using hb)

theorem rectangleTargetCocycle_shift_identity (z a b : Vertex) (N M : ℕ)
    (ω : Environment) (x y : Vertex) :
    rectangleTargetCocycle z a b N M (environmentTranslation a ω) x y -
      rectangleTargetCocycle z a b N M ω (a+x) (a+y) =
    (∑ j ∈ range M,
      (targetCocycle (z+scaleVertex N a+scaleVertex j b) ω (a+x) (a+y) -
       targetCocycle (z+scaleVertex j b) ω (a+x) (a+y))) / ((N : ℝ)*M) := by
  unfold rectangleTargetCocycle
  rw [← sub_div, ← sum_sub_distrib]
  have he : ∀ i j : ℕ,
      targetCocycle (z+scaleVertex i a+scaleVertex j b) (environmentTranslation a ω) x y =
      targetCocycle (z+scaleVertex (i+1) a+scaleVertex j b) ω (a+x) (a+y) := by
    intro i j
    rw [← targetCocycle_translation]
    congr 1
    rw [scaleVertex_succ]
    abel
  simp only [he, ← sum_sub_distrib]
  rw [sum_comm]
  have htel (j : ℕ) := sum_range_sub
    (fun i : ℕ => targetCocycle (z+scaleVertex i a+scaleVertex j b) ω (a+x) (a+y)) N
  simp_rw [htel]
  have hz : scaleVertex 0 a = (0 : Vertex) := by ext <;> simp [scaleVertex]
  simp only [hz, add_zero]

theorem rectangleTargetCocycle_shift_bound (z a b : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (x y : Vertex) :
    ∀ᵐ ω ∂environmentLaw,
      |rectangleTargetCocycle z a b N M (environmentTranslation a ω) x y -
        rectangleTargetCocycle z a b N M ω (a+x) (a+y)| ≤
      2*passageTime ω (a+x) (a+y)/N := by
  filter_upwards [targetCocycle_dominated] with ω hω
  rw [rectangleTargetCocycle_shift_identity, abs_div,
    abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)*M)]
  have hb : |∑ j ∈ range M,
      (targetCocycle (z+scaleVertex N a+scaleVertex j b) ω (a+x) (a+y) -
       targetCocycle (z+scaleVertex j b) ω (a+x) (a+y))| ≤
      (M : ℝ)*(2*passageTime ω (a+x) (a+y)) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j ∈ range M, 2*passageTime ω (a+x) (a+y) := by
        apply sum_le_sum
        intro j _
        apply (abs_sub _ _).trans
        linarith [hω (z+scaleVertex N a+scaleVertex j b) (a+x) (a+y),
          hω (z+scaleVertex j b) (a+x) (a+y)]
      _ = _ := by simp
  apply (div_le_div_of_nonneg_right hb (by positivity)).trans_eq
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp

theorem rectangleTargetCocycle_shift_integral (z a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (∫ ω, |rectangleTargetCocycle z a b N M (environmentTranslation a ω) x y -
      rectangleTargetCocycle z a b N M ω (a+x) (a+y)| ∂environmentLaw) ≤
      2*(latticeDistance x y : ℝ)/N := by
  have hi := ((environmentTranslation_preserving a).integrable_comp_of_integrable
    (integrable_rectangleTargetCocycle z a b x y N M)).sub
    (integrable_rectangleTargetCocycle z a b (a+x) (a+y) N M)
  apply (integral_mono_ae hi.abs
    (((integrable_passageTime (a+x) (a+y)).const_mul 2).div_const N)
    (rectangleTargetCocycle_shift_bound z a b N M hN hM x y)).trans
  rw [integral_div, integral_const_mul, mean_passageTime_translation]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact mul_le_mul_of_nonneg_left (mean_passageTime_le_distance x y) (by norm_num)

theorem rectangleTargetCocycle_second_shift_integral (z a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (∫ ω, |rectangleTargetCocycle z a b N M (environmentTranslation b ω) x y -
      rectangleTargetCocycle z a b N M ω (b+x) (b+y)| ∂environmentLaw) ≤
      2*(latticeDistance x y : ℝ)/M := by
  simp_rw [rectangleTargetCocycle_swap z a b N M]
  exact rectangleTargetCocycle_shift_integral z b a x y M N hM hN

theorem rectangleTargetCocycle_memLp_two (z a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    MemLp (fun ω => rectangleTargetCocycle z a b N M ω x y) 2 environmentLaw := by
  apply (passageTime_memLp_two x y).mono' (by fun_prop)
  filter_upwards [rectangleTargetCocycle_dominated z a b N M hN hM] with ω hω
  simpa only [Real.norm_eq_abs] using hω x y

theorem rectangleTargetCocycle_second_moment (z a b x y : Vertex) (N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M) :
    (∫ ω, (rectangleTargetCocycle z a b N M ω x y)^2 ∂environmentLaw) ≤
      (latticeDistance x y : ℝ)*(latticeDistance x y+1) := by
  apply (integral_mono_ae (rectangleTargetCocycle_memLp_two z a b x y N M hN hM).integrable_sq
    (passageTime_memLp_two x y).integrable_sq (by
      filter_upwards [rectangleTargetCocycle_dominated z a b N M hN hM] with ω hω
      have h := pow_le_pow_left₀ (abs_nonneg _) (hω x y) 2
      simpa only [sq_abs] using h)).trans (passageTime_second_moment x y)

theorem rectangleTargetCocycle_shift_tendsto (z : ℕ → Vertex) (a b x y : Vertex) :
    Tendsto (fun n : ℕ => ∫ ω,
      |rectangleTargetCocycle (z n) a b n n (environmentTranslation a ω) x y -
        rectangleTargetCocycle (z n) a b n n ω (a+x) (a+y)| ∂environmentLaw)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _))
    (fun n => ?_) (tendsto_const_div_atTop_nhds_zero_nat (2*(latticeDistance x y : ℝ)))
  by_cases hn : n = 0
  · subst n
    simp [rectangleTargetCocycle]
  · exact rectangleTargetCocycle_shift_integral (z n) a b x y n n (by omega) (by omega)

theorem rectangleTargetCocycle_second_shift_tendsto (z : ℕ → Vertex) (a b x y : Vertex) :
    Tendsto (fun n : ℕ => ∫ ω,
      |rectangleTargetCocycle (z n) a b n n (environmentTranslation b ω) x y -
        rectangleTargetCocycle (z n) a b n n ω (b+x) (b+y)| ∂environmentLaw)
      atTop (𝓝 0) := by
  simp_rw [rectangleTargetCocycle_swap (z _) a b]
  exact rectangleTargetCocycle_shift_tendsto z b a x y

end CompanionFPP

end OAI
