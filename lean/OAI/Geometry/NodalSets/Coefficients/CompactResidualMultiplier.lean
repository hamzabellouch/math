import OAI.Geometry.NodalSets.Charts.FixedChartSeedSupport

namespace OAI

namespace Yau.Target
open Yau.Geometry Yau.Jets Set
open scoped ContDiff Topology
noncomputable section

lemma compact_scalar_derivativeBound (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    {Q : Set Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ C > 0, ∀ x ∈ Q, DerivativeBound k f x C := by
  have hb (j : Fin (k+1)) : ∃ C > 0, ∀ x ∈ Q, ‖iteratedFDeriv ℝ j.val f x‖ ≤ C := by
    have hc : Continuous (iteratedFDeriv ℝ j.val f) := hf.continuous_iteratedFDeriv
      (by exact_mod_cast (show (j.val:ℕ∞) ≤ ⊤ from le_top))
    obtain ⟨C,hC,h⟩ := (hQ.image hc).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx ↦ h _ ⟨x,hx,rfl⟩⟩
  choose C hC hb using hb
  refine ⟨∑ j, C j,?_,?_⟩
  · exact (hC ⟨0,by omega⟩).trans_le
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))
  · intro x hx j hj
    exact (hb ⟨j,by omega⟩ x hx).trans
      (Finset.single_le_sum (fun j _ ↦ (hC j).le) (Finset.mem_univ _))

lemma product_tsupport_subset_right (f R : Coord → ℂ) :
    tsupport (fun x ↦ f x*R x) ⊆ tsupport R := by
  apply closure_mono
  intro x hx hz
  exact hx (by simp [hz])

theorem compact_residual_multiplier (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    {Q : Set Coord} (hQ : IsCompact Q) (k : ℕ) :
    ∃ B > 0, ∀ (R : Coord → ℂ), ContDiff ℝ ∞ R → tsupport R ⊆ Q →
      ContDiff ℝ ∞ (fun x ↦ f x*R x) ∧
      tsupport (fun x ↦ f x*R x) ⊆ Q ∧
      ∀ (H : Coord → ℝ), (∀ x, 0 ≤ H x) →
        (∀ x, DerivativeBound k R x (H x)) →
        ∀ x, DerivativeBound k (fun z ↦ f z*R z) x (B*H x) := by
  obtain ⟨C,hC,hbound⟩ := compact_scalar_derivativeBound f hf hQ k
  refine ⟨2^k*C,by positivity,?_⟩
  intro R hR hRQ
  have hprod := (product_tsupport_subset_right f R).trans hRQ
  refine ⟨hf.mul hR,hprod,?_⟩
  intro H hH hb x
  by_cases hx : x ∈ Q
  · exact DerivativeBound.mul hf hR hC.le (hH x) (hbound x hx) (hb x)
  · intro j hj
    rw [iteratedFDeriv_zero_off_tsupport hprod hx j,norm_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) k) hC.le) (hH x)

end
end Yau.Target

end OAI
