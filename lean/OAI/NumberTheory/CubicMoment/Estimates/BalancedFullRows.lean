import OAI.NumberTheory.CubicMoment.Estimates.BalancedLogSmallTwist

namespace OAI

/-! Collection over the second conductor variable, with literal row fibers. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def pairFirstFiber (S : Finset (Eisenstein × Eisenstein)) (b : Eisenstein) : Finset Eisenstein :=
  (S.filter (fun p => p.2 = b)).image Prod.fst

lemma mem_pairFirstFiber {S : Finset (Eisenstein × Eisenstein)} {a b : Eisenstein} :
    a ∈ pairFirstFiber S b ↔ (a,b) ∈ S := by
  simp only [pairFirstFiber,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨⟨x,y⟩,⟨h,hy⟩,hx⟩
    change x = a at hx
    change y = b at hy
    subst x
    subst y
    exact h
  · intro h
    exact ⟨(a,b),⟨h,rfl⟩,rfl⟩

lemma pair_sum_fibers (S : Finset (Eisenstein × Eisenstein))
    (f : Eisenstein × Eisenstein → ℝ) :
    (∑ p ∈ S, f p) = ∑ b ∈ S.image Prod.snd, ∑ a ∈ pairFirstFiber S b, f (a,b) := by
  have hf (b : Eisenstein) : (∑ a ∈ pairFirstFiber S b, f (a,b)) =
      ∑ p ∈ S.filter (fun p => p.2 = b), f p := by
    unfold pairFirstFiber
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [← (Finset.mem_filter.mp hp).2]
    · intro p hp q hq he
      exact Prod.ext he ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
  simp_rw [hf]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image_of_mem Prod.snd hp) f).symm

lemma balanced_pair_moment_collection (S : Finset (Eisenstein × Eisenstein))
    (f : Eisenstein × Eisenstein → ℝ) {Y C γ : ℝ} (hY : 1 ≤ Y) (hC : 0 ≤ C)
    (hS : ∀ p ∈ S, primary p.2 ∧ norm p.2 ≤ Y^(17/50:ℝ))
    (hf : ∀ b ∈ S.image Prod.snd, (∑ a ∈ pairFirstFiber S b, f (a,b)) ≤ C*Y^γ) :
    (∑ p ∈ S, f p) ≤ (18*C)*Y^(2/5+γ) := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hsub : S.image Prod.snd ⊆ primaryElementBall (Y^(17/50:ℝ)) := by
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    exact mem_primaryElementBall.mpr (hS p hp)
  have hcard : ((S.image Prod.snd).card:ℝ) ≤ 18*Y^(2/5:ℝ) := by
    calc
      _ ≤ ((primaryElementBall (Y^(17/50:ℝ))).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
      _ ≤ 18*Y^(17/50:ℝ) := primaryElementBall_card_le (Real.rpow_nonneg hY0.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by norm_num)
  calc
    _ = ∑ b ∈ S.image Prod.snd, ∑ a ∈ pairFirstFiber S b, f (a,b) := pair_sum_fibers S f
    _ ≤ ∑ _b ∈ S.image Prod.snd, C*Y^γ := Finset.sum_le_sum hf
    _ = ((S.image Prod.snd).card:ℝ)*(C*Y^γ) := by simp
    _ ≤ (18*Y^(2/5:ℝ))*(C*Y^γ) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hC (Real.rpow_nonneg hY0.le _))
    _ = _ := by rw [Real.rpow_add hY0]; ring

theorem balanced_smalltwist_log_pair_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → q ≠ 0 →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) v) = 1) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z → norm q ≤ Y^(1/1000:ℝ) →
      |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2 ∧
        norm p.1 ≤ Y^(17/50:ℝ) ∧ norm p.2 ≤ Y^(17/50:ℝ) ∧
        IsCoprime p.1 p.2 ∧ ¬ IsUnit (p.1*p.2) ∧ IsCoprime (p.1*p.2) q) →
      (∑ p ∈ S, ‖primarySmallTwistLogSmoothSum p.1 p.2 q η W Z t‖^2) ≤ C*Y^(221/100:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_smalltwist_log_smooth_power_at_height hpub W hW hpos hsm hGI hGQ
  refine ⟨18*C,T,by positivity,hT,?_⟩
  intro S q η Y Z t hY hq hη hZY hYZ hqY ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hrow (b : Eisenstein) (hb : b ∈ S.image Prod.snd) :
      (∑ a ∈ pairFirstFiber S b, ‖primarySmallTwistLogSmoothSum a b q η W Z t‖^2) ≤ C*Y^(181/100:ℝ) := by
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
    (fun p => ‖primarySmallTwistLogSmoothSum p.1 p.2 q η W Z t‖^2) hY1 hC
    (fun p hp => ⟨(hS p hp).2.2.1,(hS p hp).2.2.2.2.2.1⟩) hrow
  convert hcollect using 1
  norm_num

theorem balanced_smalltwist_pair_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (S : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (Y Z t : ℝ), Y₀ ≤ Y → q ≠ 0 →
      (∀ v : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) v) = 1) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z → norm q ≤ Y^(1/1000:ℝ) →
      |t| ≤ Y^(37/100:ℝ) →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2 ∧
        norm p.1 ≤ Y^(17/50:ℝ) ∧ norm p.2 ≤ Y^(17/50:ℝ) ∧
        IsCoprime p.1 p.2 ∧ ¬ IsUnit (p.1*p.2) ∧ IsCoprime (p.1*p.2) q) →
      (∑ p ∈ S, ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) ≤ C*Y^(11/5:ℝ) := by
  obtain ⟨C,T,hC,hT,hbound⟩ := balanced_smalltwist_smooth_power_at_height hpub W hW hpos hsm hGI hGQ
  refine ⟨18*C,T,by positivity,hT,?_⟩
  intro S q η Y Z t hY hq hη hZY hYZ hqY ht hS
  have hY1 : 1 ≤ Y := hT.trans hY
  have hrow (b : Eisenstein) (hb : b ∈ S.image Prod.snd) :
      (∑ a ∈ pairFirstFiber S b, ‖primarySmallTwistSmoothSum a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
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
    (fun p => ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) hY1 hC
    (fun p hp => ⟨(hS p hp).2.2.1,(hS p hp).2.2.2.2.2.1⟩) hrow
  convert hcollect using 1
  norm_num

end CubicFirstMoment

end

end OAI
