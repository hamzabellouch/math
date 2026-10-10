import OAI.NumberTheory.CubicMoment.Angular.AngularSmallPartTransfer
import OAI.NumberTheory.CubicMoment.Estimates.SmallPairParts
import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedFullRows

namespace OAI

/-! Exact two-variable conductor partitions and their arithmetic size. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angular_small_pair_fiber_smooth_moment (ℓ : ℤ) (v : Eisenstein) (s : Eisenstein × Eisenstein)
    (S : Finset (Eisenstein × Eisenstein))
    (hs : primary s.1 ∧ primary s.2)
    (hS : ∀ p ∈ S, primary p.1 ∧ primary p.2 ∧ pairSmallParts v p = s)
    {q : Eisenstein} (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) :
    (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) =
      ∑ r ∈ S.image (pairOutsideParts v),
        ‖primaryAngularSmallTwistSmoothSum ℓ r.1 r.2 ((3*(s.1*s.2))*q)
          (productResidueChar (primaryMixedResidueChar s.1 s.2 hs.1 hs.2) η) W Z t‖^2 := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    have hpa : primarySmallPart v p.1 = s.1 := congrArg Prod.fst (hS p hp).2.2
    have hpb : primarySmallPart v p.2 = s.2 := congrArg Prod.snd (hS p hp).2.2
    rw [primaryAngularSmallTwistSmoothSum_factor ℓ hs.1 (primaryOutsidePart_primary v (hS p hp).1)
      hs.2 (primaryOutsidePart_primary v (hS p hp).2.1)
      (by rw [← hpa,primary_small_outside_mul v (hS p hp).1])
      (by rw [← hpb,primary_small_outside_mul v (hS p hp).2.1])]
    rfl
  · intro p hp r hr he
    apply pairOutsideParts_fiber_injective v s S (fun p hp => ⟨(hS p hp).1,(hS p hp).2.1⟩)
      (Finset.mem_filter.mpr ⟨hp,(hS p hp).2.2⟩)
      (Finset.mem_filter.mpr ⟨hr,(hS r hr).2.2⟩) he

end CubicFirstMoment

end

end OAI
