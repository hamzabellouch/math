import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyTransform
import OAI.Analysis.KadisonSimilarity.Representation.SelfAdjointStrongDensity
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicApproximation

namespace OAI

/-! The selfadjoint unit ball of the source algebra is strongly dense in
the selfadjoint unit ball of the represented bicommutant. -/
noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem lift_selfAdjoint_range (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : σ.range) (hb : IsSelfAdjoint b.val) :
    ∃ a : A, IsSelfAdjoint a ∧ σ a = b.val := by
  obtain ⟨c, hc⟩ := b.property
  change σ c = b.val at hc
  refine ⟨(1 / 2 : ℝ) • (c + star c),
    (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.add_star_self c), ?_⟩
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul, map_add, map_star, hc, hb.star_eq]
  norm_num only [map_div₀, map_one]
  module

/-- Exact source norm control, on any finite family of test vectors. -/
theorem selfAdjoint_kaplansky_approximation
    (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ representationVonNeumannAlgebra σ) (hTs : IsSelfAdjoint T)
    (hTn : ‖T‖ ≤ 1) (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖ ≤ 1 ∧ ∀ x ∈ s, ‖σ a x - T x‖ < ε := by
  classical
  let P := representationVonNeumannAlgebra σ
  let D := kaplanskyPreimage T
  have hD : IsSelfAdjoint D := kaplanskyPreimage_selfAdjoint T
  have hDP : D ∈ P := by
    apply kaplanskyPreimage_mem P.toStarSubalgebra _ T hT
    change IsClosed P.carrier
    rw [← P.centralizer_centralizer']
    exact Set.isClosed_centralizer _
  have hDb : D ∈ Set.centralizer (Set.centralizer (σ.range : Set (H →L[ℂ] H))) := by
    simpa only [P, ← SetLike.mem_coe, coe_representationVonNeumannAlgebra] using hDP
  let s' : Finset H := s.image (fun x => kaplanskyReciprocal D x) ∪
    s.image (fun x => D (kaplanskyReciprocal D x))
  obtain ⟨b, hb, happrox⟩ := selfAdjoint_bicommutant_finite_approximation
    σ.range D hDb hD s' (ε / 4) (by positivity)
  obtain ⟨a, ha, hab⟩ := lift_selfAdjoint_range σ b hb
  refine ⟨kaplanskyTransform a, ?_, kaplanskyTransform_norm_le a ha, ?_⟩
  · rw [kaplanskyTransform_eq_cfc a ha]
    exact cfc_predicate _ a
  · intro x hx
    have h₁ : ‖(b.val - D) (kaplanskyReciprocal D x)‖ < ε / 4 := by
      simpa only [sub_apply, norm_sub_rev] using
        happrox _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    have h₂ : ‖(b.val - D) (D (kaplanskyReciprocal D x))‖ < ε / 4 := by
      simpa only [sub_apply, norm_sub_rev] using
        happrox _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    rw [map_kaplanskyTransform σ a ha, hab, ← kaplanskyTransform_preimage T hTs hTn]
    have he : kaplanskyTransform b.val x - kaplanskyTransform D x =
        (2 : ℝ) • ((b.val * kaplanskyReciprocal b.val - D * kaplanskyReciprocal D) x) := by
      simp only [kaplanskyTransform, smul_apply, sub_apply, smul_sub]
    rw [he, norm_smul]
    have hbound := kaplanskyReciprocal_difference_apply_le b.val D hb hD x
    rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith

end KadisonSimilarity

end

end OAI
