import OAI.NumberTheory.CubicMoment.Estimates.CompactParameterWeights
import OAI.NumberTheory.CubicMoment.Estimates.UniformWeightCoordinates

namespace OAI

/-! Uniform support and derivative bounds survive the compact family
of logarithmic-denominator multipliers used in the original coefficients. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

 def UniformLogWeights.compactMultiplier {γ E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W : γ → ℝ → ℂ} (h : UniformLogWeights W)
    (K : Set E) (hK : IsCompact K) (F : E → ℝ → ℂ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    UniformLogWeights (fun z : γ × K => fun x => F z.2 x*W z.1 x) := by
  let G : E × ℝ → ℂ := fun z => F z.1 (Real.exp (-z.2))
  have hmap : ContDiff ℝ ∞ (fun z : E × ℝ => (z.1,Real.exp (-z.2))) := by fun_prop
  have hG : ContDiff ℝ ∞ G := hF.comp hmap
  have hbound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p : K, ∀ u : ℝ, |u| ≤ h.radius →
      ‖iteratedFDeriv ℝ n (fun v => F p (Real.exp (-v))) u‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hK.prod (isCompact_Icc (a := -h.radius) (b := h.radius))).exists_bound_of_continuousOn
      ((hG.continuous_iteratedFDeriv (show (n:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousOn)
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro p u hu
    exact (norm_iteratedFDeriv_slice_le G hG p u n).trans
      ((hC (p,u) ⟨p.property,abs_le.mp hu⟩).trans (le_max_left _ _))
  choose C hC hCb using hbound
  choose B hB hBb using h.derivative_bound
  refine ⟨fun z => (h.compact z.1).mono (Function.support_mul_subset_right _ _),
    fun z => tsupport_mul_subset_right.trans (h.positive z.1),
    fun z => (hF.comp (contDiff_const.prodMk contDiff_id)).mul (h.smooth z.1),
    h.radius,h.radius_nonneg,?_,?_⟩
  · intro z u hu
    exact h.support_bound z.1 u (tsupport_mul_subset_right hu)
  · intro n
    let A := ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*C j*B (n-j)
    have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC j)) (hB (n-j)))
    refine ⟨A,hA,?_⟩
    intro z u
    by_cases hu : |u| ≤ h.radius
    · have hf : ContDiff ℝ ∞ (fun v => F z.2 (Real.exp (-v))) :=
        hG.comp (contDiff_const.prodMk contDiff_id)
      have hw : ContDiff ℝ ∞ (fun v => W z.1 (Real.exp (-v))) :=
        (h.smooth z.1).comp (by fun_prop)
      apply (norm_iteratedFDeriv_mul_le hf hw u (by exact_mod_cast le_top : (n:ℕ∞ω) ≤ ∞)).trans
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hCb j z.2 u hu) (Nat.cast_nonneg _))
        (hBb (n-j) z.1 u) (_root_.norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hC j))
    · have hz : iteratedFDeriv ℝ n (fun v => F z.2 (Real.exp (-v))*W z.1 (Real.exp (-v))) u = 0 := by
        by_contra hn
        have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
          (f := fun v => F z.2 (Real.exp (-v))*W z.1 (Real.exp (-v))) n hn
        exact hu (h.support_bound z.1 u (tsupport_mul_subset_right hs))
      rw [hz,norm_zero]
      exact hA

lemma UniformLogWeights.norm_bound {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, ‖W i x‖ ≤ M := by
  obtain ⟨M,hM,hbound⟩ := h.derivative_bound 0
  refine ⟨M,hM,?_⟩
  intro i x
  by_cases hx : 0 < x
  · have he : Real.exp (-(-Real.log x)) = x := by simp [Real.exp_log hx]
    have hb := hbound i (-Real.log x)
    simpa only [norm_iteratedFDeriv_zero,he] using hb
  · have hz : W i x = 0 := by
      by_contra hn
      have hp := h.positive i (subset_closure hn)
      exact hx hp
    simpa only [hz,norm_zero] using hM

end CubicFirstMoment

end

end OAI
