import OAI.NumberTheory.CubicMoment.Estimates.SmallPartTransfer
import OAI.NumberTheory.CubicMoment.Estimates.BalancedFullRows

namespace OAI

/-! Exact two-variable conductor partitions and their arithmetic size. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def pairSmallParts (v : Eisenstein) (p : Eisenstein × Eisenstein) : Eisenstein × Eisenstein :=
  (primarySmallPart v p.1,primarySmallPart v p.2)

def pairOutsideParts (v : Eisenstein) (p : Eisenstein × Eisenstein) : Eisenstein × Eisenstein :=
  (primaryOutsidePart v p.1,primaryOutsidePart v p.2)

lemma pairOutsideParts_fiber_injective (v : Eisenstein) (s : Eisenstein × Eisenstein)
    (S : Finset (Eisenstein × Eisenstein)) (hS : ∀ p ∈ S, primary p.1 ∧ primary p.2) :
    Set.InjOn (pairOutsideParts v) ↑(S.filter (fun p => pairSmallParts v p = s)) := by
  intro p hp r hr he
  have hp' := Finset.mem_filter.mp hp
  have hr' := Finset.mem_filter.mp hr
  have hsmall : pairSmallParts v p = pairSmallParts v r := hp'.2.trans hr'.2.symm
  apply Prod.ext
  · have hs := congrArg Prod.fst hsmall
    have ho := congrArg Prod.fst he
    have ha := primary_small_outside_mul v (hS p hp'.1).1
    have hb := primary_small_outside_mul v (hS r hr'.1).1
    change primarySmallPart v p.1 = primarySmallPart v r.1 at hs
    change primaryOutsidePart v p.1 = primaryOutsidePart v r.1 at ho
    rw [hs,ho] at ha
    exact ha.symm.trans hb
  · have hs := congrArg Prod.snd hsmall
    have ho := congrArg Prod.snd he
    have ha := primary_small_outside_mul v (hS p hp'.1).2
    have hb := primary_small_outside_mul v (hS r hr'.1).2
    change primarySmallPart v p.2 = primarySmallPart v r.2 at hs
    change primaryOutsidePart v p.2 = primaryOutsidePart v r.2 at ho
    rw [hs,ho] at ha
    exact ha.symm.trans hb

lemma pair_small_parts_card {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Eisenstein × Eisenstein)) (v : Eisenstein), v ≠ 0 →
      (∀ p ∈ S, primary p.1 ∧ Squarefree p.1 ∧ primary p.2 ∧ Squarefree p.2) →
      ((S.image (pairSmallParts v)).card:ℝ) ≤ C*norm v^(2*ε) := by
  obtain ⟨D,hD,hbound⟩ := smallPrimeParts_card hε
  refine ⟨D^2,sq_pos_of_pos hD,?_⟩
  intro S v hv hS
  let A := (S.image Prod.fst).image (primarySmallPart v)
  let B := (S.image Prod.snd).image (primarySmallPart v)
  have ha : (A.card:ℝ) ≤ D*norm v^ε := by
    apply hbound (S.image Prod.fst) v hv
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact ⟨(hS p hp).1,(hS p hp).2.1⟩
  have hb : (B.card:ℝ) ≤ D*norm v^ε := by
    apply hbound (S.image Prod.snd) v hv
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    exact ⟨(hS p hp).2.2.1,(hS p hp).2.2.2⟩
  have hsub : S.image (pairSmallParts v) ⊆ A.product B := by
    intro p hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem Prod.fst hr),
        Finset.mem_image_of_mem _ (Finset.mem_image_of_mem Prod.snd hr)⟩
  calc
    _ ≤ ((A.product B).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = (A.card:ℝ)*(B.card:ℝ) := by rw [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
    _ ≤ (D*norm v^ε)*(D*norm v^ε) :=
      mul_le_mul ha hb (Nat.cast_nonneg _) (mul_nonneg hD.le (Real.rpow_nonneg (norm_nonneg v) _))
    _ = D^2*norm v^(2*ε) := by
      rw [show 2*ε = ε+ε by ring,Real.rpow_add (norm_pos_of_ne_zero hv)]
      ring

lemma small_pair_fiber_smooth_moment (v : Eisenstein) (s : Eisenstein × Eisenstein)
    (S : Finset (Eisenstein × Eisenstein))
    (hs : primary s.1 ∧ primary s.2)
    (hS : ∀ p ∈ S, primary p.1 ∧ primary p.2 ∧ pairSmallParts v p = s)
    {q : Eisenstein} (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) :
    (∑ p ∈ S, ‖primarySmallTwistSmoothSum p.1 p.2 q η W Z t‖^2) =
      ∑ r ∈ S.image (pairOutsideParts v),
        ‖primarySmallTwistSmoothSum r.1 r.2 ((3*(s.1*s.2))*q)
          (productResidueChar (primaryMixedResidueChar s.1 s.2 hs.1 hs.2) η) W Z t‖^2 := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    have hpa : primarySmallPart v p.1 = s.1 := congrArg Prod.fst (hS p hp).2.2
    have hpb : primarySmallPart v p.2 = s.2 := congrArg Prod.snd (hS p hp).2.2
    rw [primarySmallTwistSmoothSum_factor hs.1 (primaryOutsidePart_primary v (hS p hp).1)
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
