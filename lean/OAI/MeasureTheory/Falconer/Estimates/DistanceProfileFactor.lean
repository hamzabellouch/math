import OAI.MeasureTheory.Falconer.Graphs.ProductEnergyMaximum

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

theorem graphProfileCoefficient_distance_product (N : ℕ) (m₁ m₂ : ℝ → ℝ) (a p : ℝ) :
    graphProfileCoefficient N ![m₁,m₂,m₂,m₁] a p =
      graphProfileCoefficient N ![m₁,m₁,m₂,m₂] a p := by
  simp only [graphProfileCoefficient,Fin.prod_univ_four,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  ring

theorem distance_profile_sum_bound {ι : Type*} (S : Finset ι) (E : ι → ℝ≥0∞)
    (N : ℕ) (hN : 0 < N) (m₁ m₂ : ℝ → ℝ) (a p k lam : ℝ)
    (hcard : (S.card:ℝ) ≤ 4096*((2:ℝ)^N)^(m₁ p-m₁ a+(m₂ p-m₂ a)+12*lam)) :
    (2:ℝ)^(2*(p-a))*graphProfileCoefficient N ![m₁,m₂,m₂,m₁] a p *
      (144*((2:ℝ)^N)^k) * (∑ i ∈ S, (E i).toReal) ≤
    589824*((2:ℝ)^N)^(-(m₁ p-p/N-(m₁ a-a/N))-(m₂ p-p/N-(m₂ a-a/N))+k+12*lam) *
      finiteEnergyMaximum S E := by
  rw [graphProfileCoefficient_distance_product]
  exact product_profile_sum_bound S E N hN m₁ m₂ a p k lam hcard

end PlanarFalconer

end OAI
