import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedLogSmallTwist
import OAI.NumberTheory.CubicMoment.Estimates.BalancedFullRows

namespace OAI

/-! Collection over the second conductor variable, with literal row fibers. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem balanced_angular_smalltwist_log_pair_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z → norm q ≤ Y^(1/1000:ℝ) →
      |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2 ∧
        norm p.1 ≤ Y^(17/50:ℝ) ∧ norm p.2 ≤ Y^(17/50:ℝ) ∧
        IsCoprime p.1 p.2 ∧ ¬ IsUnit (p.1*p.2) ∧ IsCoprime (p.1*p.2) q) →
      (∑ p ∈ S, ‖primaryAngularSmallTwistLogSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(221/100:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_angular_smalltwist_log_smooth_power_at_height hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨18*C,T,by positivity,hT,?_⟩
  intro S q η Y Z t hY hq hη hZY hYZ hqY ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hrow (b : Eisenstein) (hb : b ∈ S.image Prod.snd) :
      (∑ a ∈ pairFirstFiber S b, ‖primaryAngularSmallTwistLogSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(181/100:ℝ) := by
    obtain ⟨p,hp,hpb⟩ := Finset.mem_image.mp hb
    have hbp := hS p hp
    apply hbound (pairFirstFiber S b) b q η (Y^(17/50:ℝ)) Y Z t hY
      (hpb ▸ hbp.2.2.1) (hpb ▸ hbp.2.2.2.1) hq hη
      (fun a ha => (hS (a,b) (mem_pairFirstFiber.mp ha)).2.2.2.2.2.2.2.2)
      (Real.one_le_rpow hY1 (by norm_num)) le_rfl hZY hYZ
      (hpb ▸ hbp.2.2.2.2.2.1) hqY ht
    intro a ha
    have hs := hS (a,b) (mem_pairFirstFiber.mp ha)
    exact ⟨hs.1,hs.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1⟩
  have hcollect := balanced_pair_moment_collection S
    (fun p => ‖primaryAngularSmallTwistLogSmoothSum ℓ p.1 p.2 q η W Z t‖^2) hY1 hC
    (fun p hp => ⟨(hS p hp).2.2.1,(hS p hp).2.2.2.2.2.1⟩) hrow
  convert hcollect using 1
  norm_num

theorem balanced_angular_smalltwist_pair_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z → norm q ≤ Y^(1/1000:ℝ) →
      |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2 ∧
        norm p.1 ≤ Y^(17/50:ℝ) ∧ norm p.2 ≤ Y^(17/50:ℝ) ∧
        IsCoprime p.1 p.2 ∧ ¬ IsUnit (p.1*p.2) ∧ IsCoprime (p.1*p.2) q) →
      (∑ p ∈ S, ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_angular_smalltwist_smooth_power_at_height hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨18*C,T,by positivity,hT,?_⟩
  intro S q η Y Z t hY hq hη hZY hYZ hqY ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hrow (b : Eisenstein) (hb : b ∈ S.image Prod.snd) :
      (∑ a ∈ pairFirstFiber S b, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
    obtain ⟨p,hp,hpb⟩ := Finset.mem_image.mp hb
    have hbp := hS p hp
    apply hbound (pairFirstFiber S b) b q η (Y^(17/50:ℝ)) Y Z t hY
      (hpb ▸ hbp.2.2.1) (hpb ▸ hbp.2.2.2.1) hq hη
      (fun a ha => (hS (a,b) (mem_pairFirstFiber.mp ha)).2.2.2.2.2.2.2.2)
      (Real.one_le_rpow hY1 (by norm_num)) le_rfl hZY hYZ
      (hpb ▸ hbp.2.2.2.2.2.1) hqY ht
    intro a ha
    have hs := hS (a,b) (mem_pairFirstFiber.mp ha)
    exact ⟨hs.1,hs.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1⟩
  have hcollect := balanced_pair_moment_collection S
    (fun p => ‖primaryAngularSmallTwistSmoothSum ℓ p.1 p.2 q η W Z t‖^2) hY1 hC
    (fun p hp => ⟨(hS p hp).2.2.1,(hS p hp).2.2.2.2.2.1⟩) hrow
  convert hcollect using 1
  norm_num

end CubicFirstMoment

end

end OAI
