import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.CompactContDiffOnDerivativeBound
import OAI.MeasureTheory.FalconerCompletion.Estimates.SmoothReciprocal

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
namespace Attempt4FullFar
open Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma smoothReciprocal_norm_comp_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : V →L[ℝ] ℝ) j, j ≤ m → ∀ w,
      ‖iteratedFDeriv ℝ j (fun x => (smoothReciprocal (L x) : ℂ)) w‖ ≤ C*‖L‖^j := by
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ m, ∀ x,
      ‖iteratedFDeriv ℝ j smoothReciprocal x‖ ≤ C := by
    induction m with
    | zero =>
      obtain ⟨C,hC,hCb⟩ := smoothReciprocal_deriv_bound 0
      refine ⟨C,hC,?_⟩
      intro j hj
      have : j=0 := Nat.eq_zero_of_le_zero hj
      subst j
      exact hCb
    | succ m ih =>
      obtain ⟨C,hC,hCb⟩ := ih
      obtain ⟨D,hD,hDb⟩ := smoothReciprocal_deriv_bound (m+1)
      refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
      intro j hj x
      by_cases hjm : j ≤ m
      · exact (hCb j hjm x).trans (le_max_left _ _)
      · have he : j=m+1 := by omega
        exact (he ▸ hDb x).trans (le_max_right _ _)
  obtain ⟨C,hC,hCb⟩ := hbound
  refine ⟨C,hC,?_⟩
  intro L j hj w
  rw [show (fun x => (smoothReciprocal (L x) : ℂ)) =
    Complex.ofRealLI ∘ (smoothReciprocal ∘ L) from rfl,
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      (smoothReciprocal_contDiff.comp_continuousLinearMap.contDiffAt)
      (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)),
    L.iteratedFDeriv_comp_right smoothReciprocal_contDiff w
      (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))]
  exact ((iteratedFDeriv ℝ j smoothReciprocal (L w)).norm_compContinuousLinearMap_le
    (fun _ => L)).trans (by simpa using
      (mul_le_mul_of_nonneg_right (hCb j hj (L w)) (pow_nonneg (norm_nonneg L) j)))

lemma angularDerivative_uniform_bound [FiniteDimensional ℝ V] (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : V →L[ℝ] V) (b : V → ℂ) (A B : ℝ),
      ‖T‖ ≤ 2 → ContDiff ℝ ∞ b → 1 ≤ A → 0 ≤ B →
      (∀ j ≤ m+1, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b w‖ ≤ B*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖=1 →
        ‖iteratedFDeriv ℝ j (angularDerivativeND T b) w‖ ≤ D*B*A^(j+1) := by
  obtain ⟨M,hM,hMb⟩ := compact_contDiffOn_derivative_bound isOpen_univ
    (isCompact_sphere (0:V) 1) (subset_univ _)
    (contDiff_id : ContDiff ℝ ∞ (id : V → V)).contDiffOn m
  refine ⟨2^m*(2*M), by positivity, ?_⟩
  intro T b A B hT hb hA hB hderiv j hj w hw
  have hTb (k : ℕ) (hk : k ≤ m) : ‖iteratedFDeriv ℝ k T w‖ ≤ 2*M := by
    have hh := T.norm_iteratedFDeriv_comp_left
      (contDiffAt_id : ContDiffAt ℝ ∞ (id : V → V) w) (n := k) (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))
    simp only [Function.comp_id] at hh
    apply hh.trans
    apply mul_le_mul hT
    · simpa only [iteratedFDerivWithin_univ] using hMb k hk w (by simpa using hw)
    · exact norm_nonneg _
    · norm_num
  have hh := norm_iteratedFDeriv_clm_apply (N := ∞) (n := j)
    (hb.fderiv_right (by simp)) T.contDiff w (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))
  change ‖iteratedFDeriv ℝ j (angularDerivativeND T b) w‖ ≤ _ at hh
  apply hh.trans
  have hsum : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)) = 2^j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ) * (B*A^(j+1)) * (2*M) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := by simpa using Finset.mem_range.mp hi
      rw [norm_iteratedFDeriv_fderiv]
      gcongr
      · exact (hderiv (i+1) (by omega) w hw).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (by omega)) hB)
      · exact hTb (j-i) (by omega)
    _ = 2^j*(2*M)*B*A^(j+1) := by rw [← Finset.sum_mul,← Finset.sum_mul,hsum]; ring
    _ ≤ 2^m*(2*M)*B*A^(j+1) := by gcongr; norm_num

lemma sphere_product_derivative_bound [FiniteDimensional ℝ V] (m : ℕ) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfb : ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j f w‖ ≤ B*A^j)
    (hgb : ∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j g w‖ ≤ C*A^j) :
    ∀ j ≤ m, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (fun x => f x*g x) w‖ ≤ (2^m*B*C)*A^j := by
  intro j hj w hw
  apply (norm_iteratedFDeriv_mul_le hf hg w (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤) : (j:ℕ∞ω) ≤ ∞)).trans
  have hsum : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)) = 2^j := by
    exact_mod_cast Nat.sum_range_choose j
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(B*A^i)*(C*A^(j-i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := by simpa using Finset.mem_range.mp hi
      gcongr
      · exact hfb i (by omega) w hw
      · exact hgb (j-i) (by omega) w hw
    _ = 2^j*B*C*A^j := by
      calc
        _ = ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(B*C*A^j) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hij : i ≤ j := by simpa using Finset.mem_range.mp hi
          rw [show (j.choose i:ℝ)*(B*A^i)*(C*A^(j-i)) =
            (j.choose i:ℝ)*(B*C)*(A^i*A^(j-i)) by ring,
            ← pow_add, Nat.add_sub_of_le hij]
          ring
        _ = _ := by rw [← Finset.sum_mul,hsum]; ring
    _ ≤ (2^m*B*C)*A^j := by gcongr; norm_num

end Attempt4FullFar
end
end

end OAI
