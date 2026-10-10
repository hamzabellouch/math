import OAI.Geometry.Immersion.ClosedSurface.DirectionStability
import OAI.Geometry.Immersion.ClosedSurface.ImmersionJets

namespace OAI

/-! The nonzero second-form margin persists at the polynomial C2 radius. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates PhaseGeometry

theorem uniform_fast_normal_margin (R c A b : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ s : ℝ, 0 < s → s ≤ η →
    ∀ F G : RField 4, ContDiff ℝ ∞ F → WeightedBound univ s 3 A F → ∀ x : Base,
      ‖firstJetPair F x‖ ≤ R →
      c ≤ NormalFrame.gramDet (firstJetPair F x).1 (firstJetPair F x).2 →
      b ≤ ‖realSecondTensor F x‖ →
      ‖firstJetPair F x-firstJetPair G x‖ ≤ s^4 →
      ‖secondJetTriple F x-secondJetTriple G x‖ ≤ s^4 →
      Function.Injective (fderiv ℝ G x) ∧ b/2 ≤ ‖realSecondTensor G x‖ := by
  obtain ⟨ηn,C,hηn,hC,hn⟩ := secondTensor_z4_stability R c A hc hA
  obtain ⟨ηg,hηg,_,hg⟩ := uniform_gram_neighborhood R c hc
  let η := min 1 (min ηn (min ηg (b/(2*(C+1)))))
  have hη : 0 < η := lt_min zero_lt_one (lt_min hηn (lt_min hηg (by positivity)))
  refine ⟨η,hη,min_le_left _ _,?_⟩
  intro s hs hsη F G hF hFb x hR hcF hbF hdiff hsecond
  have hs1 : s ≤ 1 := hsη.trans (min_le_left _ _)
  have hs4 : s^4 ≤ s := by simpa only [pow_one] using pow_le_pow_of_le_one hs.le hs1 (by norm_num : 1 ≤ 4)
  have hs2 : s^2 ≤ s := by simpa only [pow_one] using pow_le_pow_of_le_one hs.le hs1 (by norm_num : 1 ≤ 2)
  have hsn : s^4 ≤ ηn := hs4.trans (hsη.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hsg : s^4 ≤ ηg := hs4.trans (hsη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hsb : s ≤ b/(2*(C+1)) := hsη.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hsmall : C*s^2 ≤ b/2 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(C+1))).mp hsb
    nlinarith [mul_le_mul_of_nonneg_left hs2 hC]
  have hnormjet := (coordinate_jets_variation isOpen_univ (convex_univ : Convex ℝ (univ : Set Base))
    hF.contDiffOn hs hA hFb (mem_univ x) (mem_univ x)).2.1
  have hbound := hn s hs hs1 hsn F G x hR hcF hdiff hnormjet hsecond
  have hgram := (hg _ _ hR hcF (hdiff.trans hsg)).2
  refine ⟨injective_of_gramDet_ne_zero _ ((half_pos hc).trans_le hgram).ne',?_⟩
  have hh := norm_sub_norm_le (realSecondTensor F x) (realSecondTensor G x)
  linarith [hbound.trans hsmall]

end ClosedSurfaceR4.RealModes

end

end OAI
