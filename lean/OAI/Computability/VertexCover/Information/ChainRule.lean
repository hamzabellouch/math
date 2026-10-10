import Mathlib
import OAI.Computability.VertexCover.Information.Finite

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                                                                          
section

namespace UniqueGames.Foundations.Information

open scoped BigOperators

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def firstMarginal (p : α × β → ℝ) (a : α) : ℝ := ∑ b, p (a, b)

noncomputable def secondMarginal (p : α × β → ℝ) (b : β) : ℝ := ∑ a, p (a, b)

def product (p : α → ℝ) (q : β → ℝ) : α × β → ℝ := fun ab => p ab.1 * q ab.2

theorem firstMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (firstMarginal p) := by
  constructor
  · intro a
    exact Finset.sum_nonneg (fun b _ => hp.1 (a, b))
  · simpa only [firstMarginal, Fintype.sum_prod_type] using hp.2

theorem secondMarginal_isProbability (p : α × β → ℝ) (hp : IsProbability p) :
    IsProbability (secondMarginal p) := by
  constructor
  · intro b
    exact Finset.sum_nonneg (fun a _ => hp.1 (a, b))
  · change (∑ b, ∑ a, p (a, b)) = 1
    rw [Finset.sum_comm]
    exact (firstMarginal_isProbability p hp).2

theorem product_isProbability (p : α → ℝ) (q : β → ℝ)
    (hp : IsProbability p) (hq : IsProbability q) : IsProbability (product p q) := by
  constructor
  · intro ab
    exact mul_nonneg (hp.1 ab.1) (hq.1 ab.2)
  · simp only [product, Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, mul_one, hp.2]

theorem point_le_firstMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ firstMarginal p a := by
  classical
  exact Finset.single_le_sum (fun b _ => hp.1 (a, b)) (Finset.mem_univ b)

theorem point_le_secondMarginal (p : α × β → ℝ) (hp : IsProbability p) (a : α) (b : β) :
    p (a, b) ≤ secondMarginal p b := by
  classical
  exact Finset.single_le_sum (fun a _ => hp.1 (a, b)) (Finset.mem_univ a)

theorem joint_supportedBy_product_marginals (p : α × β → ℝ) (hp : IsProbability p) :
    SupportedBy p (product (firstMarginal p) (secondMarginal p)) := by
  intro ab hpne
  have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hpne)
  exact mul_ne_zero
    (ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2)))
    (ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2)))

theorem relativeEntropy_product_reference (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (_hu : IsProbability u) (_hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy p (product u v) =
      relativeEntropy p (product (firstMarginal p) (secondMarginal p)) +
        relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v := by
  have hpoint : ∀ ab : α × β, p ab * Real.log (p ab / product u v ab) =
      p ab * Real.log (p ab / product (firstMarginal p) (secondMarginal p) ab) +
      p ab * Real.log (firstMarginal p ab.1 / u ab.1) +
      p ab * Real.log (secondMarginal p ab.2 / v ab.2) := by
    intro ab
    by_cases hzero : p ab = 0
    · simp [hzero]
    have hpos : 0 < p ab := lt_of_le_of_ne (hp.1 ab) (Ne.symm hzero)
    have hleft := ne_of_gt (hpos.trans_le (point_le_firstMarginal p hp ab.1 ab.2))
    have hright := ne_of_gt (hpos.trans_le (point_le_secondMarginal p hp ab.1 ab.2))
    have hune := hsu ab.1 hleft
    have hvne := hsv ab.2 hright
    simp only [product, Real.log_div hzero (mul_ne_zero hune hvne),
      Real.log_div hzero (mul_ne_zero hleft hright), Real.log_mul hune hvne,
      Real.log_mul hleft hright, Real.log_div hleft hune, Real.log_div hright hvne]
    ring
  have hleftSum : (∑ ab : α × β, p ab * Real.log (firstMarginal p ab.1 / u ab.1)) =
      relativeEntropy (firstMarginal p) u := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_mul, relativeEntropy, firstMarginal]
  have hrightSum : (∑ ab : α × β, p ab * Real.log (secondMarginal p ab.2 / v ab.2)) =
      relativeEntropy (secondMarginal p) v := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [← Finset.sum_mul, relativeEntropy, secondMarginal]
  unfold relativeEntropy
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hleftSum, hrightSum]
  rfl

theorem marginal_relativeEntropy_sum_le (p : α × β → ℝ) (u : α → ℝ) (v : β → ℝ)
    (hp : IsProbability p) (hu : IsProbability u) (hv : IsProbability v)
    (hsu : SupportedBy (firstMarginal p) u) (hsv : SupportedBy (secondMarginal p) v) :
    relativeEntropy (firstMarginal p) u + relativeEntropy (secondMarginal p) v ≤
      relativeEntropy p (product u v) := by
  rw [relativeEntropy_product_reference p u v hp hu hv hsu hsv]
  have hn := relativeEntropy_nonneg p (product (firstMarginal p) (secondMarginal p)) hp
    (product_isProbability _ _ (firstMarginal_isProbability p hp)
      (secondMarginal_isProbability p hp)) (joint_supportedBy_product_marginals p hp)
  linarith

end UniqueGames.Foundations.Information

end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
