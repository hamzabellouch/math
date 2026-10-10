import OAI.Geometry.NodalSets.Elliptic.ContinuousPolynomialFamily
import OAI.Geometry.NodalSets.Elliptic.TaylorMatching

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma tensorPolynomial_coeff_continuous (n : ℕ) (d : Fin 4 →₀ ℕ) :
    Continuous (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ ↦
      (tensorPolynomial T).coeff d) := by
  induction n generalizing d with
  | zero =>
    simp only [tensorPolynomial, coeff_C]
    split_ifs
    · exact (ContinuousMultilinearMap.apply ℝ _ ℂ 0).continuous
    · exact continuous_const
  | succ n ih =>
    simp only [tensorPolynomial, coeff_sum, coeff_X_mul']
    apply continuous_finsetSum
    intro i _
    split_ifs
    · apply (ih _).comp
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ Coord) ℂ).continuous.clm_apply
        continuous_const
    · exact continuous_const

lemma tensorPolynomial_family {T : Type*} [TopologicalSpace T] {n : ℕ}
    (A : T → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Coord) ℂ) (hA : Continuous A) :
    ContinuousPolyFamily (fun t ↦ tensorPolynomial (A t)) := by
  classical
  refine ⟨fun d ↦ (tensorPolynomial_coeff_continuous n d).comp hA,
    (Finsupp.finite_of_degree_eq (σ := Fin 4) n).toFinset, ?_⟩
  intro t d hd
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [Finsupp.degree_eq_weight_one]
  have hw : (fun _ : Fin 4 ↦ (1 : ℕ)) = (1 : Fin 4 → ℕ) := by funext i; rfl
  rw [hw]
  exact tensorPolynomial_homogeneous (A t) (mem_support_iff.mp hd)

theorem taylorPolynomial_family {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    ContinuousPolyFamily (fun y ↦ taylorPolynomial f y m) := by
  apply ContinuousPolyFamily.sum
  intro k _
  exact (ContinuousPolyFamily.const _).mul (tensorPolynomial_family _
    (hf.continuous_iteratedFDeriv (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))))

theorem taylorPolynomial_uniform_derivative_bound {f : Coord → ℂ}
    (hf : ContDiff ℝ ∞ f) (m k : ℕ) (s : Set Coord) (hs : IsCompact s) (R : ℝ) :
    ∃ C > 0, ∀ y ∈ s, ∀ x : Coord, ‖x‖ ≤ R →
      ‖iteratedFDeriv ℝ k (reval (taylorPolynomial f y m)) x‖ ≤ C :=
  (taylorPolynomial_family hf m).uniform_derivative_bound s hs R k

theorem flatAt_translated_taylorPolynomial {f : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (y : Coord) (m : ℕ) :
    FlatAt m (fun x ↦ f (y + x) - reval (taylorPolynomial f y m) x) 0 := by
  have hshift : ContDiff ℝ ∞ (fun x ↦ f (y + x)) :=
    hf.comp (contDiff_const.add contDiff_id)
  intro k hk
  change iteratedFDeriv ℝ k ((fun x ↦ f (y + x)) - reval (taylorPolynomial f y m)) 0 = 0
  rw [iteratedFDeriv_sub_apply
    (hshift.contDiffAt.of_le
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))
    ((reval_contDiff _).contDiffAt.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)))]
  rw [iteratedFDeriv_taylorPolynomial hf y m k hk, iteratedFDeriv_comp_add_left]
  simp

end
end Yau.Jets

end OAI
