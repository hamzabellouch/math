import OAI.Analysis.AncientFlat.Evolution.TraceFour

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace FlatSymmetry
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
lemma laplacian_rotate (R : V ≃ₗᵢ[ℝ] V) (f : V → ℂ) (hf : ContDiff ℝ 2 f) :
    Δ (fun x => f (R x))=fun x => Δ f (R x) := by
  let e := stdOrthonormalBasis ℝ V
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (e.map R)]
  funext x
  have he := R.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x le_rfl
  change iteratedFDeriv ℝ 2 (fun x => f (R x)) x=_ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,OrthonormalBasis.map_apply]
  congr 1
  funext j
  fin_cases j <;> rfl
lemma bilaplacian_rotate (R : V ≃ₗᵢ[ℝ] V) (f : V → ℂ) (hf : ContDiff ℝ 4 f) :
    Δ (Δ (fun x => f (R x)))=fun x => Δ (Δ f) (R x) := by
  rw [laplacian_rotate R f (hf.of_le (by norm_num))]
  exact laplacian_rotate R (Δ f) (ClassicalIBP.contDiff_laplacian f 2 hf)
omit [FiniteDimensional ℝ V] in
lemma bounded_jets_rotate (R : V ≃ₗᵢ[ℝ] V) (f : V → ℂ) (hf : ContDiff ℝ 4 f)
    (hb : ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖≤M) :
    ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fun y => f (R y)) x‖≤M := by
  intro n hn
  obtain ⟨M,hM⟩ := hb n hn
  refine ⟨max M 0,fun x => ?_⟩
  have he := R.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x
    (show (n : WithTop ℕ∞)≤4 by exact_mod_cast hn)
  change iteratedFDeriv ℝ n (fun x => f (R x)) x=_ at he
  rw [he]
  calc
    _≤‖iteratedFDeriv ℝ n f (R x)‖ * ∏ _i : Fin n, ‖R.toContinuousLinearEquiv.toContinuousLinearMap‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _≤‖iteratedFDeriv ℝ n f (R x)‖ * 1 := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      intro i hi
      exact R.toLinearIsometry.norm_toContinuousLinearMap_le
    _≤ max M 0 := by simpa only [mul_one] using (hM (R x)).trans (le_max_left M (0:ℝ))
lemma bilaplacian_star (f : V → ℂ) :
    Δ (Δ (fun x => star (f x)))=fun x => star (Δ (Δ f) x) := by
  change Δ (Δ (Complex.conjCLE ∘ f))=_
  rw [InnerProductSpace.laplacian_CLE_comp_left,InnerProductSpace.laplacian_CLE_comp_left]
  rfl
omit [FiniteDimensional ℝ V] in
lemma bounded_jets_star (f : V → ℂ)
    (hb : ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖≤M) :
    ∀ n : ℕ, n≤4 → ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (fun y => star (f y)) x‖≤M := by
  intro n hn
  obtain ⟨M,hM⟩ := hb n hn
  refine ⟨M,fun x => ?_⟩
  change ‖iteratedFDeriv ℝ n (Complex.conjCLE ∘ f) x‖≤M
  rw [ContinuousLinearEquiv.iteratedFDeriv_comp_left]
  calc
    _≤‖Complex.conjCLE.toContinuousLinearMap‖*‖iteratedFDeriv ℝ n f x‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _=‖iteratedFDeriv ℝ n f x‖ := by
      rw [show ‖Complex.conjCLE.toContinuousLinearMap‖=1 from Complex.conjLIE.norm_toContinuousLinearMap,one_mul]
    _≤M := hM x
end FlatSymmetry

end

end OAI
