import OAI.Analysis.FreeEntropy.TensorGradient

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Finset
namespace FiniteEntropySeparation
variable {κ : Type u1} {Ω : Type u2} [MeasurableSpace Ω]
 def linearExpand (g : κ → Ω → ℝ) (a : κ →₀ ℝ) : Ω → ℝ := a.sum (fun k r => r • g k)
 theorem linearExpand_apply {κ : Type u1} {Ω : Type u2} [MeasurableSpace Ω] (g : κ → Ω → ℝ) (a : κ →₀ ℝ) (x : Ω) :
    linearExpand g a x = ∑ k ∈ a.support, a k*g k x := by
  simp [linearExpand, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
 theorem linearExpand_integrable {μ : Measure Ω} {g : κ → Ω → ℝ}
    (hg : ∀ k, Integrable (g k) μ) (a : κ →₀ ℝ) : Integrable (linearExpand g a) μ := by
  change Integrable (fun x => linearExpand g a x) μ
  simp only [linearExpand_apply]
  exact integrable_finsetSum _ (fun k _ => (hg k).const_mul (a k))
 theorem linearExpand_mul_integrable {μ : Measure Ω} {g h : κ → Ω → ℝ}
    (hgh : ∀ k l, Integrable (fun x => g k x*h l x) μ) (a b : κ →₀ ℝ) :
    Integrable (fun x => linearExpand g a x*linearExpand h b x) μ := by
  simp only [linearExpand_apply, sum_mul, mul_sum]
  apply integrable_finsetSum
  intro k hk
  apply integrable_finsetSum
  intro l hl
  convert (hgh l k).const_mul (a l*b k) using 1 ; try rfl
  funext x; ring
 theorem linearExpand_integral {μ : Measure Ω} {g : κ → Ω → ℝ}
    (hg : ∀ k, Integrable (g k) μ) (a : κ →₀ ℝ) :
    (∫ x, linearExpand g a x ∂μ) = ∑ k ∈ a.support, a k*∫ x, g k x ∂μ := by
  simp only [linearExpand_apply]
  rw [integral_finsetSum _ (fun k _ => (hg k).const_mul (a k))]
  simp only [integral_const_mul]
 theorem linearExpand_inner {μ : Measure Ω} {g h : κ → Ω → ℝ}
    (hgh : ∀ k l, Integrable (fun x => g k x*h l x) μ) (a b : κ →₀ ℝ) :
    (∫ x, linearExpand g a x*linearExpand h b x ∂μ) =
      ∑ k ∈ a.support, ∑ l ∈ b.support, a k*b l*∫ x, g k x*h l x ∂μ := by
  have he : (fun x => linearExpand g a x*linearExpand h b x) =
      fun x => ∑ k ∈ a.support, ∑ l ∈ b.support, (a k*b l)*(g k x*h l x) := by
    funext x
    simp only [linearExpand_apply, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro l hl
    ring
  rw [he, integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => (hgh k l).const_mul _))]
  apply sum_congr rfl
  intro k hk
  rw [integral_finsetSum _ (fun l _ => (hgh k l).const_mul _)]
  simp only [integral_const_mul]
 theorem linearExpand_orthogonal [DecidableEq κ] {μ : Measure Ω} {g h : κ → Ω → ℝ}
    (hgh : ∀ k l, Integrable (fun x => g k x*h l x) μ) (w : κ → ℝ)
    (horth : ∀ k l, (∫ x, g k x*h l x ∂μ) = if k=l then w k else 0)
    (a b : κ →₀ ℝ) :
    (∫ x, linearExpand g a x*linearExpand h b x ∂μ) =
      ∑ k ∈ a.support, a k*b k*w k := by
  classical
  rw [linearExpand_inner hgh]
  apply sum_congr rfl
  intro k hk
  simp_rw [horth]
  by_cases hkb : k ∈ b.support
  · rw [sum_eq_single k]
    · simp
    · intro l hl hlk; simp [Ne.symm hlk]
    · exact fun h => (h hkb).elim
  · have hb : b k=0 := Finsupp.notMem_support_iff.mp hkb
    rw [hb, mul_zero, zero_mul]
    apply sum_eq_zero
    intro l hl
    have hkl : k ≠ l := fun h => hkb (h.symm ▸ hl)
    simp [hkl]
 theorem integral_center_sq {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x => f x*f x) μ) :
    (∫ x, (f x-∫ y, f y ∂μ)^2 ∂μ) = (∫ x, f x*f x ∂μ) - (∫ x, f x ∂μ)^2 := by
  let m := ∫ x, f x ∂μ
  have he : (fun x => (f x-m)^2) = fun x => f x*f x - (2*m)*f x + m^2 := by
    funext x; ring
  change (∫ x, (f x-m)^2 ∂μ) = _
  rw [he]
  have ha : (∫ x, f x*f x - (2*m)*f x + m^2 ∂μ) =
      (∫ x, f x*f x - (2*m)*f x ∂μ) + ∫ x, m^2 ∂μ :=
    integral_add (hfsq.sub (hf.const_mul (2*m))) (integrable_const _)
  have hs : (∫ x, f x*f x - (2*m)*f x ∂μ) =
      (∫ x, f x*f x ∂μ) - ∫ x, (2*m)*f x ∂μ := integral_sub hfsq (hf.const_mul _)
  rw [ha, hs, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  dsimp [m]; ring
end FiniteEntropySeparation

end

end OAI
