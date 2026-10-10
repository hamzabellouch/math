import OAI.Probability.InvariantIsing.Arrays.TensorGGRate

namespace OAI

/-! Choosing system sizes fast enough for a prescribed sequence of finite
cascade depths. Each row requires only finitely many error estimates. -/

noncomputable section
open Filter IsingPerceptron
open scoped Topology

namespace InvariantIsing

private def cavityDiagonalIndex (M : ℕ → ℕ) : ℕ → ℕ
  | 0 => M 0
  | r+1 => max (cavityDiagonalIndex M r+1) (M (r+1))

private lemma cavityDiagonalIndex_ge (M : ℕ → ℕ) (r : ℕ) : M r≤cavityDiagonalIndex M r := by
  cases r with
  | zero => exact le_rfl
  | succ r => exact le_max_right _ _

private lemma cavityDiagonalIndex_strict (M : ℕ → ℕ) : StrictMono (cavityDiagonalIndex M) := by
  apply strictMono_nat_of_lt_succ
  intro r
  exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

lemma cavity_choose_diagonal_errors (F : ℕ → ℕ → ℕ → ℝ)
    (hF : ∀ r j, Tendsto (fun k => F r k j) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Tendsto (fun r => F r (φ r) j) atTop (𝓝 0) := by
  have hrow r : ∃ M : ℕ, ∀ k≥M, ∀ j≤r, |F r k j|<1/((r : ℝ)+1) := by
    have he : 0<1/((r : ℝ)+1) := by positivity
    have hall : ∀ᶠ k in atTop, ∀ j : Fin (r+1), |F r k j|<1/((r : ℝ)+1) := by
      apply eventually_all.mpr
      intro j
      have ha : Tendsto (fun k => |F r k j|) atTop (𝓝 0) := by
        simpa only [abs_zero] using (hF r j).abs
      exact ha.eventually (gt_mem_nhds he)
    obtain ⟨M,hM⟩ := eventually_atTop.mp hall
    refine ⟨M, fun k hk j hj => ?_⟩
    exact hM k hk ⟨j, by omega⟩
  choose M hM using hrow
  let φ := cavityDiagonalIndex M
  refine ⟨φ, cavityDiagonalIndex_strict M, ?_⟩
  intro j
  apply squeeze_zero_norm' _ (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [eventually_ge_atTop j] with r hr
  rw [Real.norm_eq_abs]
  exact (hM r (φ r) (cavityDiagonalIndex_ge M r) j hr).le

lemma cavity_choose_depth_rates (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ℕ) (L : ℕ → ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun r => diagonalContactRate (N (φ r)) (L r)) atTop (𝓝 0) ∧
      ∀ j B, Tendsto (fun r => tensorContactGGRate (N (φ r)) j m (L r) B) atTop (𝓝 0) := by
  let F := fun r k j => if j=0 then diagonalContactRate (N k) (L r)
    else tensorContactGGRate (N k) (j-1) m (L r) 1
  have hF r j : Tendsto (fun k => F r k j) atTop (𝓝 0) := by
    by_cases hj : j=0
    · simpa only [F, hj, ite_true, Function.comp_def] using (diagonalContactRate_tendsto (L r)).comp hN
    · simpa only [F, ite_eq_right hj, Function.comp_def] using (tensorContactGGRate_tendsto (j-1) m (L r) 1).comp hN
  obtain ⟨φ,hφ,hlim⟩ := cavity_choose_diagonal_errors F hF
  refine ⟨φ,hφ,?_,?_⟩
  · simpa only [F, ite_true] using hlim 0
  · intro j B
    have h := (hlim (j+1)).const_mul B
    have he r : B*F r (φ r) (j+1)=tensorContactGGRate (N (φ r)) j m (L r) B := by
      have hj : j+1≠0 := Nat.succ_ne_zero j
      simp only [F, ite_eq_right hj, Nat.add_sub_cancel]
      unfold tensorContactGGRate contactGGRate
      ring
    simpa only [he, mul_zero] using h

end InvariantIsing

end

end OAI
