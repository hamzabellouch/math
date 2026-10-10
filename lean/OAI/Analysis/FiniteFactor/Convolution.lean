import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate ENNReal

/-- Monotonicity follows from the integer cocycle's one-step recurrence;
this includes negative integer indices. -/
theorem cocycle_antitone_of_step {F w : ℤ → ℝ}
    (hF : ∀ k, 0 ≤ F k) (hw : ∀ k, w k ≤ 1)
    (hstep : ∀ k, F (k+1) = w k * F k) : Antitone F := by
  apply antitone_int_of_succ_le
  intro k
  rw [hstep]
  simpa using mul_le_mul_of_nonneg_right (hw k) (hF k)

/-- Both cocycle ratio bounds, valid at every integer index. -/
theorem cocycle_two_ratio_bounds {F G : ℤ → ℝ}
    (hF : ∀ k, 0 < F k) (hG : ∀ k, 0 < G k)
    (hFa : Antitone F) (hGa : Antitone G) (hGF : ∀ k, G k ≤ F k)
    {n v : ℤ} (hn : 0 ≤ n) :
    0 < G (n + v) / F v ∧
    G (n + v) / F v ≤ min (G v / F v) (G (n + v) / F (n + v)) ∧
    min (G v / F v) (G (n + v) / F (n + v)) ≤ 1 := by
  have hv : v ≤ n + v := by omega
  refine ⟨div_pos (hG _) (hF _), le_min ?_ ?_, ?_⟩
  · exact div_le_div_of_nonneg_right (hGa hv) (hF v).le
  · exact div_le_div_of_nonneg_left (hG _).le (hF _) (hFa hv)
  · exact (min_le_left _ _).trans ((div_le_one (hF v)).2 (hGF v))

/-- Cauchy--Schwarz with a genuine integer translation of the second vector. -/
theorem shifted_l2_norm_product (ξ γ : lp (fun _ : ℤ => ℂ) 2) (n : ℤ) :
    Summable (fun v => ‖ξ v‖ * ‖γ (n + v)‖) ∧
    (∑' v, ‖ξ v‖ * ‖γ (n + v)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  have hp : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hξ : HasSum (fun v => ‖ξ v‖ ^ (2 : ℝ)) (‖ξ‖ ^ (2 : ℝ)) := by
    simpa using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) ξ
  have hγ : HasSum (fun v => ‖γ (n + v)‖ ^ (2 : ℝ)) (‖γ‖ ^ (2 : ℝ)) := by
    have h : HasSum (fun v : ℤ => ‖γ v‖ ^ (2 : ℝ)) (‖γ‖ ^ (2 : ℝ)) := by
      simpa using lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) γ
    exact (Equiv.addLeft n).hasSum_iff.mpr h
  obtain ⟨C, _, hC, hs⟩ := Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hp
    (norm_nonneg ξ) (norm_nonneg γ) (fun v => norm_nonneg (ξ v))
    (fun v => norm_nonneg (γ (n + v))) hξ hγ
  exact ⟨hs.summable, hs.tsum_eq ▸ hC⟩

/-- The ratio-weighted convolution is absolutely convergent and has the sharp
product-of-L²-norms bound. -/
theorem weighted_convolution_summable (ξ γ : lp (fun _ : ℤ => ℂ) 2)
    (n : ℤ) {r : ℤ → ℝ} (hr0 : ∀ v, 0 ≤ r v) (hr1 : ∀ v, r v ≤ 1) :
    Summable (fun v => ‖(r v : ℂ) * ξ v * conj (γ (n + v))‖) ∧
    (∑' v, ‖(r v : ℂ) * ξ v * conj (γ (n + v))‖) ≤ ‖ξ‖ * ‖γ‖ := by
  obtain ⟨hs, hb⟩ := shifted_l2_norm_product ξ γ n
  have hbound : ∀ v, ‖(r v : ℂ) * ξ v * conj (γ (n + v))‖ ≤
      ‖ξ v‖ * ‖γ (n + v)‖ := by
    intro v
    simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hr0 v)]
    calc
      r v * ‖ξ v‖ * ‖γ (n + v)‖ = r v * (‖ξ v‖ * ‖γ (n + v)‖) := mul_assoc _ _ _
      _ ≤ 1 * (‖ξ v‖ * ‖γ (n + v)‖) := mul_le_mul_of_nonneg_right (hr1 v) (by positivity)
      _ = _ := one_mul _
  have hsum := hs.of_nonneg_of_le (fun v => norm_nonneg _) hbound
  exact ⟨hsum, (hsum.tsum_le_tsum hbound hs).trans hb⟩

/-- Exact rescaling used in coefficient-sequences; neither sequence is required
 to belong to ℓ². -/
noncomputable def leftCoefficient (F : ℤ → ℝ) (ξ : ℤ → ℂ) (v : ℤ) : ℂ :=
  ξ v / (F v : ℂ)

noncomputable def rightCoefficient (G : ℤ → ℝ) (γ : ℤ → ℂ) (v : ℤ) : ℂ :=
  (G (-v) : ℂ) * conj (γ (-v))

theorem cocycle_convolution_term_eq (F G : ℤ → ℝ) (ξ γ : ℤ → ℂ) (n v : ℤ) :
    leftCoefficient F ξ v * rightCoefficient G γ (-n-v) =
      (G (n+v) / F v : ℝ) * ξ v * conj (γ (n+v)) := by
  have hi : -(-n-v) = n+v := by omega
  simp only [leftCoefficient, rightCoefficient, hi, Complex.ofReal_div]
  ring

theorem cocycle_convolution_absolute_convergence
    (ξ γ : lp (fun _ : ℤ => ℂ) 2) {F G : ℤ → ℝ}
    (hF : ∀ k, 0 < F k) (hG : ∀ k, 0 < G k)
    (hFa : Antitone F) (hGa : Antitone G) (hGF : ∀ k, G k ≤ F k)
    {n : ℤ} (hn : 0 ≤ n) :
    Summable (fun v => ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖) ∧
    (∑' v, ‖leftCoefficient F ξ v * rightCoefficient G γ (-n-v)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  simp only [cocycle_convolution_term_eq]
  apply weighted_convolution_summable
  · intro v
    exact (cocycle_two_ratio_bounds hF hG hFa hGa hGF hn).1.le
  · intro v
    have h := cocycle_two_ratio_bounds hF hG hFa hGa hGF (v := v) hn
    exact h.2.1.trans h.2.2

/-- Reindexing the Hilbert inner product gives the exact convolution from
coordinates of the shifted weighted vector. -/
theorem weighted_shift_convolution_eq_inner
    (ξ γ η : lp (fun _ : ℤ => ℂ) 2) (r : ℤ → ℝ) (n : ℤ)
    (hη : ∀ v, η (n+v) = (r v : ℂ) * ξ v) :
    (∑' v, (r v : ℂ) * ξ v * conj (γ (n+v))) = inner ℂ γ η := by
  rw [lp.inner_eq_tsum]
  rw [← (Equiv.addLeft n).tsum_eq (fun k : ℤ => inner ℂ (γ k) (η k))]
  apply tsum_congr
  intro v
  change (r v : ℂ) * ξ v * conj (γ (n+v)) = inner ℂ (γ (n+v)) (η (n+v))
  rw [hη]
  simp only [RCLike.inner_apply]

/-- Orthogonality of the image vector to the complementary range produces
convolution-identity, with its original rescaled coefficients and signs. -/
theorem cocycle_convolution_zero_of_range
    (ξ γ η : lp (fun _ : ℤ => ℂ) 2) (F G : ℤ → ℝ) (n : ℤ)
    (V : Submodule ℂ (lp (fun _ : ℤ => ℂ) 2))
    (hηV : η ∈ V) (hγV : γ ∈ Vᗮ)
    (hη : ∀ v, η (n+v) = (G (n+v) / F v : ℝ) * ξ v) :
    (∑' v, leftCoefficient F ξ v * rightCoefficient G γ (-n-v)) = 0 := by
  simp only [cocycle_convolution_term_eq]
  rw [weighted_shift_convolution_eq_inner ξ γ η _ n hη]
  exact (Submodule.mem_orthogonal' V γ).mp hγV η hηV

/-- Removing any finite part of a zero absolutely convergent series gives its
 exact complementary tail, before applying the triangle inequality. -/
theorem finite_part_eq_neg_tail {t : ℤ → ℂ} (ht : Summable t)
    (hzero : ∑' v, t v = 0) (W : Finset ℤ) :
    (∑ v ∈ W, t v) = -(∑' v : {v : ℤ // v ∉ W}, t v) := by
  have h := ht.sum_add_tsum_subtype_compl W
  rw [hzero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem finite_part_norm_le_tail {t : ℤ → ℂ} (ht : Summable (fun v => ‖t v‖))
    (hzero : ∑' v, t v = 0) (W : Finset ℤ) :
    ‖∑ v ∈ W, t v‖ ≤ ∑' v : {v : ℤ // v ∉ W}, ‖t v‖ := by
  rw [finite_part_eq_neg_tail ht.of_norm hzero W, norm_neg]
  exact norm_tsum_le_tsum_norm (ht.subtype _)

/-- The deterministic omitted-index choice used for both complementary masks. -/
def omittedIndex (K : ℕ) (n v : ℤ) : ℤ :=
  if (K : ℤ) < |v| then v else n+v

theorem omittedIndex_spec (K : ℕ) (n v : ℤ)
    (h : (K : ℤ) < |v| ∨ (K : ℤ) < |n+v|) :
    (K : ℤ) < |omittedIndex K n v| ∧
    (omittedIndex K n v = v ∨ omittedIndex K n v = n+v) := by
  unfold omittedIndex
  split_ifs with hv
  · exact ⟨hv, Or.inl rfl⟩
  · exact ⟨h.resolve_left hv, Or.inr rfl⟩

end FiniteFactor

end OAI
