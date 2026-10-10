import OAI.Analysis.KadisonKastler.AbelianEmbedding
import OAI.Analysis.KadisonKastler.CenterGap
import OAI.Analysis.KadisonKastler.PublishedCenterInjectivity
import OAI.Analysis.KadisonKastler.AmenableEmbedding
import OAI.Analysis.KadisonKastler.CenterTransport
import OAI.Analysis.KadisonKastler.InjectiveStability

namespace OAI

/-! # Quantitative alignment of the centers

The threefold center gap feeds the constructed abelian embedding theorem.
The proved small-gap inclusion lemma makes that embedding onto. Moving the
neighbor by the inverse unitary costs at most 900g.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The center alignment constants in Section 9: 450 for the unitary and
901 for the moved algebra gap. -/
theorem exists_near_unitary_aligning_centers
    (M N : VonNeumannAlgebra H)
    (hM : PublishedDixmierAveraging M) (hN : PublishedDixmierAveraging N)
    {g : ℝ} (hgap : kkDistance M N < g) (hg : g < 1 / 4000) :
    ∃ w : unitary (H →L[ℂ] H), Conjugates w (concreteCenter M) (concreteCenter N) ∧
      ‖(w : H →L[ℂ] H) - 1‖ ≤ 450 * g ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) < 901 * g := by
  have hg0 : 0 < g := (kkDistance_nonneg M N).trans_lt hgap
  have hcent : kkDistance (concreteCenter M) (concreteCenter N) < 3 * g :=
    (kkDistance_concreteCenter_le M N hM hN).trans_lt (by linarith)
  have hcomm (x y : Algebra (concreteCenter M)) : x * y = y * x := by
    apply Subtype.ext
    exact (VonNeumannAlgebra.mem_commutant_iff.mp x.property.2 y.val y.property.1).symm
  obtain ⟨w, hw, hn⟩ := exists_abelian_conjugacy_of_kkDistance_lt hcomm
    (by linarith : 3 * g ≤ 1 / 1152) hcent
  have hn' : ‖(w : H →L[ℂ] H) - 1‖ ≤ 450 * g := by linarith
  refine ⟨w, hw, hn', ?_⟩
  have he : ‖(star w : H →L[ℂ] H) - 1‖ = ‖(w : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((w : H →L[ℂ] H) - 1)
  have hdist := kkDistance_conjugate_le (M := M)
    (conjugates_unitaryConjugateAlgebra (star w) N)
  rw [Unitary.coe_star, he] at hdist
  linarith

/-- The moved pair has literally the same concrete center. -/
theorem exists_common_center_neighbor
    (M N : VonNeumannAlgebra H)
    (hM : PublishedDixmierAveraging M) (hN : PublishedDixmierAveraging N)
    {g : ℝ} (hgap : kkDistance M N < g) (hg : g < 1 / 4000) :
    ∃ w : unitary (H →L[ℂ] H), ‖(w : H →L[ℂ] H) - 1‖ ≤ 450 * g ∧
      concreteCenter (unitaryConjugateAlgebra (star w) N) = concreteCenter M ∧
      kkDistance M (unitaryConjugateAlgebra (star w) N) < 901 * g := by
  obtain ⟨w, hw, hn, hd⟩ := exists_near_unitary_aligning_centers M N hM hN hgap hg
  exact ⟨w, hn, concreteCenter_conjugated_neighbor_eq w hw, hd⟩

end

end KadisonKastler

end OAI
