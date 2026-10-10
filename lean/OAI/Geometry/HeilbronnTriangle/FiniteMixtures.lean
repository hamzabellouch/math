import OAI.Geometry.HeilbronnTriangle.ConditionalSamples

namespace OAI


namespace Problem355.ConditionalSamples

noncomputable section

variable {α β ι : Type*}

def mixtureWeight [Fintype β] (p : β → ℝ) (ν : β → α → ℝ) (a : α) : ℝ :=
  ∑ b, p b * ν b a

lemma mixtureWeight_nonneg [Fintype β] (p : β → ℝ) (ν : β → α → ℝ)
    (hp : ∀ b, 0 ≤ p b) (hν : ∀ b a, 0 ≤ ν b a) (a : α) :
    0 ≤ mixtureWeight p ν a :=
  Finset.sum_nonneg fun b _ => mul_nonneg (hp b) (hν b a)

lemma sum_mixtureWeight [Fintype α] [Fintype β]
    (p : β → ℝ) (ν : β → α → ℝ)
    (hp : ∑ b, p b = 1) (hν : ∀ b, ∑ a, ν b a = 1) :
    ∑ a, mixtureWeight p ν a = 1 := by
  unfold mixtureWeight
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hν, mul_one]
  exact hp

lemma productWeight_mixture [Fintype ι] [DecidableEq ι] [Fintype β]
    (p : β → ℝ) (ν : β → α → ℝ) (x : ι → α) :
    productWeight (mixtureWeight p ν) x =
      ∑ labels : ι → β, productWeight p labels * ∏ i, ν (labels i) (x i) := by
  classical
  unfold productWeight mixtureWeight
  have h := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset β))
    (fun i b => p b * ν b (x i))
  simpa [Finset.prod_mul_distrib] using h

lemma expectation_productWeight_mixture
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (p : β → ℝ) (ν : β → α → ℝ) (F : (ι → α) → ℝ) :
    (∑ x : ι → α, productWeight (mixtureWeight p ν) x * F x) =
      ∑ labels : ι → β, productWeight p labels *
        ∑ x : ι → α, (∏ i, ν (labels i) (x i)) * F x := by
  simp_rw [productWeight_mixture, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro labels _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end
end Problem355.ConditionalSamples

end OAI
