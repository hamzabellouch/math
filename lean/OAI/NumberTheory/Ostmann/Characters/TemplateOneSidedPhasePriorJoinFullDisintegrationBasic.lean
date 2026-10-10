import OAI.NumberTheory.Ostmann.Characters.WordSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction
attribute [local instance] Classical.propDecidable

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

def coordinateResampleEquiv (i : I) : ((I → Ω) × Ω) ≃ ((I → Ω) × Ω) where
  toFun z := (Function.update z.1 i z.2,z.1 i)
  invFun z := (Function.update z.1 i z.2,z.1 i)
  left_inv z := by
    apply Prod.ext
    · funext a
      by_cases ha : a=i
      · subst a; simp
      · simp [Function.update_of_ne ha]
    · simp
  right_inv z := by
    apply Prod.ext
    · funext a
      by_cases ha : a=i
      · subst a; simp
      · simp [Function.update_of_ne ha]
    · simp

theorem productPrior_resample_mass (μ : I → FinitePrior Ω) (i : I) (p : I → Ω) (q : Ω) :
    (productPrior μ).mass (Function.update p i q)*(μ i).mass (p i) =
      (productPrior μ).mass p*(μ i).mass q := by
  change (∏ a,(μ a).mass (Function.update p i q a))*(μ i).mass (p i) =
    (∏ a,(μ a).mass (p a))*(μ i).mass q
  rw [← Finset.prod_erase_mul Finset.univ (fun a => (μ a).mass (Function.update p i q a))
    (Finset.mem_univ i)]
  rw [← Finset.prod_erase_mul Finset.univ (fun a => (μ a).mass (p a)) (Finset.mem_univ i)]
  have he : (∏ a ∈ Finset.univ.erase i,(μ a).mass (Function.update p i q a)) =
      ∏ a ∈ Finset.univ.erase i,(μ a).mass (p a) := by
    apply Finset.prod_congr rfl
    intro a ha
    rw [Function.update_of_ne (Finset.mem_erase.mp ha).1]
  rw [he]
  simp only [Function.update_self]
  ring

theorem productPrior_cmean_update (μ : I → FinitePrior Ω) (i : I) (F : (I → Ω) → ℂ) :
    (productPrior μ).cmean F =
      (productPrior μ).cmean (fun p => (μ i).cmean (fun q => F (Function.update p i q))) := by
  have hm : (∑ q,((μ i).mass q:ℂ)) = 1 := by
    rw [← Complex.ofReal_sum,(μ i).mass_total,Complex.ofReal_one]
  calc
    (productPrior μ).cmean F =
        ∑ z : (I → Ω) × Ω,((productPrior μ).mass z.1:ℂ)*((μ i).mass z.2:ℂ)*F z.1 := by
      simp only [Fintype.sum_prod_type,FinitePrior.cmean]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_mul,← Finset.mul_sum,hm,mul_one]
    _ = ∑ z : (I → Ω) × Ω,
        ((productPrior μ).mass z.1:ℂ)*((μ i).mass z.2:ℂ)*F (Function.update z.1 i z.2) := by
      rw [← (coordinateResampleEquiv i).sum_comp
        (fun z : (I → Ω) × Ω => ((productPrior μ).mass z.1:ℂ)*((μ i).mass z.2:ℂ)*F z.1)]
      apply Finset.sum_congr rfl
      intro z hz
      change ((productPrior μ).mass (Function.update z.1 i z.2):ℂ)*((μ i).mass (z.1 i):ℂ)*_ = _
      rw [← Complex.ofReal_mul,productPrior_resample_mass,Complex.ofReal_mul]
      rfl
    _ = _ := by
      simp only [FinitePrior.cmean,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
