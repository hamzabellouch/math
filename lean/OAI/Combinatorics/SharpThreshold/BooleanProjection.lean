import OAI.Combinatorics.SharpThreshold.FourierProjection
import OAI.Combinatorics.SharpThreshold.InfluenceReindex
import OAI.Combinatorics.SharpThreshold.Model

namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- Low-degree projection bound for a Boolean coordinate difference, with the
pivotal probability expressed by the shared generic influence definition. -/
theorem booleanDifference_project_energy_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (L : Finset (Finset ι)) (f : (ι → Bool) → Bool) (i : ι)
    (hdegree : ∀ S ∈ L, (S.card : ℝ) ≤ k) :
    (∑ S ∈ L, (coeff p
      (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S) ^ 2) ≤
      rho ^ (-2 * k) * (Reindex.influence p f i) ^ (3 / 2 : ℝ) := by
  let g : (ι → Bool) → ℝ := fun x =>
    boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))
  have hg (x : ι → Bool) : g x = -1 ∨ g x = 0 ∨ g x = 1 := by
    cases ht : f (Function.update x i true) <;>
      cases hf : f (Function.update x i false) <;> simp [g, ht, hf, boolReal]
  have hpiv : (∑ x, if g x ≠ 0 then weight p x else 0) =
      Reindex.influence p f i := by
    unfold Reindex.influence
    apply Finset.sum_congr rfl
    intro x hx
    cases ht : f (Function.update x i true) <;>
      cases hf : f (Function.update x i false) <;>
        simp [g, ht, hf, boolReal, weight, scalarWeight, Reindex.weight]
  simpa only [hpiv] using
    project_energy_le_of_noise hp hp1 rho k hrho hrho1 hnoise L g hg hdegree

/-- The Boolean coordinate-difference energy bound with a real degree cutoff. -/
theorem booleanDifference_lowDegree_energy_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (f : (ι → Bool) → Bool) (i : ι) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset ι => (S.card : ℝ) ≤ k),
      (coeff p (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S) ^ 2) ≤
      rho ^ (-2 * k) * (Reindex.influence p f i) ^ (3 / 2 : ℝ) := by
  apply booleanDifference_project_energy_le hp hp1 rho k hrho hrho1 hnoise _ f i
  intro S hS
  exact (Finset.mem_filter.mp hS).2

end Problem313.BiasedFourier

end

end OAI
