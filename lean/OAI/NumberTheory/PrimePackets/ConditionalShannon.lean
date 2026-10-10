import OAI.NumberTheory.PrimePackets.EntropyMixtures

namespace OAI

/-!
# Finite conditional entropy, including zero-mass cells

These algebraic chain rules are used to compare finite observations with
the expanding leaf partitions in the metric entropy calculation.
-/

noncomputable section
open scoped BigOperators

namespace PrimeDegreePackets

lemma finiteShannon_mul {α : Type*} [Fintype α] (r : ℝ) (p : α → ℝ) :
    finiteShannon (fun a => r * p a) =
      Real.negMulLog r * (∑ a, p a) + r * finiteShannon p := by
  simp only [finiteShannon, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma finiteShannon_mass_decomposition {α : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    finiteShannon p = Real.negMulLog (∑ a, p a) +
      (∑ a, p a) * finiteShannon (fun a => p a / (∑ b, p b)) := by
  classical
  let r := ∑ a, p a
  by_cases hr : r = 0
  · have hp0 : ∀ a, p a = 0 := by
      intro a
      have h := Finset.single_le_sum (fun b _ => hp b) (Finset.mem_univ a)
      change p a ≤ r at h
      exact le_antisymm (hr ▸ h) (hp a)
    simp only [hp0, finiteShannon, Finset.sum_const_zero, Real.negMulLog_zero,
      zero_div, zero_mul, zero_add]
  · have hs : ∑ a, p a / r = 1 := by rw [← Finset.sum_div]; exact div_self hr
    have heq : (fun a => r * (p a / r)) = p := by
      funext a
      exact mul_div_cancel₀ (p a) hr
    have h := finiteShannon_mul r (fun a => p a / r)
    rw [heq, hs, mul_one] at h
    exact h

/-- Subadditivity for a nonnegative finite measure; its total mass need not be one. -/
theorem finiteShannon_joint_mass_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon p + Real.negMulLog (∑ z, p z) ≤
      finiteShannon (fun a => ∑ b, p (a,b)) +
      finiteShannon (fun b => ∑ a, p (a,b)) := by
  classical
  let r := ∑ z, p z
  have hr0 : 0 ≤ r := Finset.sum_nonneg (fun z _ => hp z)
  by_cases hr : r = 0
  · have hp0 : ∀ z, p z = 0 := by
      intro z
      have h := Finset.single_le_sum (fun w _ => hp w) (Finset.mem_univ z)
      change p z ≤ r at h
      exact le_antisymm (hr ▸ h) (hp z)
    simp [hp0, finiteShannon]
  have hnorm : ∑ z, p z / r = 1 := by rw [← Finset.sum_div]; exact div_self hr
  have H := mul_le_mul_of_nonneg_left
    (finiteShannon_joint_le (p := fun z => p z / r)
      (fun z => div_nonneg (hp z) hr0) hnorm) hr0
  have hrow : (∑ a, ∑ b, p (a,b)) = r := by simp only [r, Fintype.sum_prod_type]
  have hcol : (∑ b, ∑ a, p (a,b)) = r := by rw [Finset.sum_comm]; exact hrow
  have h1 := finiteShannon_mass_decomposition p hp
  have h2 := finiteShannon_mass_decomposition (fun a => ∑ b, p (a,b))
    (fun a => Finset.sum_nonneg (fun b _ => hp (a,b)))
  have h3 := finiteShannon_mass_decomposition (fun b => ∑ a, p (a,b))
    (fun b => Finset.sum_nonneg (fun a _ => hp (a,b)))
  simp only [hrow] at h2
  simp only [hcol] at h3
  simp only [← Finset.sum_div] at H
  change finiteShannon p = Real.negMulLog r + r * _ at h1
  linarith

/-- The finite entropy submodularity inequality `H(ABC)+H(A) ≤ H(AB)+H(AC)`. -/
theorem finiteShannon_submodular {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × (β × γ) → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon p + finiteShannon (fun a => ∑ z : β × γ, p (a,z)) ≤
      finiteShannon (fun z : α × β => ∑ c, p (z.1,(z.2,c))) +
      finiteShannon (fun z : α × γ => ∑ b, p (z.1,(b,z.2))) := by
  have H := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    finiteShannon_joint_mass_le (fun z : β × γ => p (a,z)) (fun z => hp (a,z)))
  simpa only [finiteShannon, Fintype.sum_prod_type, Finset.sum_add_distrib] using H

lemma finiteShannon_fst_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon (fun a => ∑ b, p (a,b)) ≤ finiteShannon p := by
  simpa only [finiteShannon, Fintype.sum_prod_type] using
    Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      negMulLog_sum_le (fun b => p (a,b)) (fun b => hp (a,b)))

lemma finiteShannon_joint_decomposition {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (hp : ∀ z, 0 ≤ p z) :
    finiteShannon p = finiteShannon (fun a => ∑ b, p (a,b)) +
      ∑ a, (∑ b, p (a,b)) *
        finiteShannon (fun b => p (a,b) / (∑ c, p (a,c))) := by
  have H := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ =>
    finiteShannon_mass_decomposition (fun b => p (a,b)) (fun b => hp (a,b)))
  simpa only [finiteShannon, Fintype.sum_prod_type, Finset.sum_add_distrib] using H

end PrimeDegreePackets

end

end OAI
