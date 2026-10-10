import OAI.Probability.InvariantIsing.Magnetic.MagneticPopulationCoupling

namespace OAI

/-! The field contribution changes by at most the transportation cost
when an interior profile is averaged across field populations. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma transportedMagnetization_field_term {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℝ) (δ c : B → ℝ) (mag : A → ℝ) (hδ : ∀ b, 0 < δ b) :
    (∑ b, δ b*c b*transportedMagnetization w δ mag b)=
      ∑ a, ∑ b, w a b*c b*mag a := by
  calc
    _ = ∑ b, c b*(∑ a, w a b*mag a) := by
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [transportedMagnetization]
      field_simp [(hδ b).ne']
    _ = ∑ b, ∑ a, w a b*c b*mag a := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := Finset.sum_comm

lemma transportedMagnetization_field_cost {A B : Type*} [Fintype A] [Fintype B]
    (w : A → B → ℝ) (γ b : A → ℝ) (δ c : B → ℝ) (mag : A → ℝ)
    (hw : ∀ a j, 0 ≤ w a j) (hδ : ∀ j, 0 < δ j)
    (hrow : ∀ a, ∑ j, w a j=γ a) (hm : ∀ a, |mag a| ≤ 1) :
    (∑ a, γ a*b a*mag a)-(∑ j, δ j*c j*transportedMagnetization w δ mag j) ≤
      ∑ a, ∑ j, w a j* |b a-c j| := by
  have hsource : (∑ a, γ a*b a*mag a)=∑ a, ∑ j, w a j*b a*mag a := by
    simp_rw [← Finset.sum_mul,hrow]
  rw [hsource,transportedMagnetization_field_term w δ c mag hδ,← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j _
  calc
    _ = w a j*(b a-c j)*mag a := by ring
    _ ≤ |w a j*(b a-c j)*mag a| := le_abs_self _
    _ = w a j* |b a-c j| * |mag a| := by rw [abs_mul,abs_mul,abs_of_nonneg (hw a j)]
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg (hw a j) (abs_nonneg _)) (hm a)

end InvariantIsing

end

end OAI
