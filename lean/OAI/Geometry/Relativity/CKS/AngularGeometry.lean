import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import Mathlib

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise
abbrev Mat := Matrix I I ℝ
abbrev Jet := Mat × (I → Mat) × (I → I → Mat)
abbrev ScalarJet := ℝ × (I → ℝ) × Mat
abbrev CombinedJet := Jet × ScalarJet

def determinant (q : Mat) : ℝ := q 0 0 * q 1 1 - q 0 1 * q 1 0

def inverse (q : Mat) : Mat :=
  fun i j => (!![q 1 1, -q 0 1; -q 1 0, q 0 0] : Mat) i j / determinant q

lemma determinant_eq (q : Mat) : determinant q = q.det := by
  exact (Matrix.det_fin_two q).symm

lemma inverse_eq (q : Mat) : inverse q = q⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, ← determinant_eq]
  ext i j
  simp [inverse, div_eq_mul_inv, mul_comm]

def christoffel (j : Jet) (a i k : I) : ℝ :=
  (∑ l, inverse j.1 a l * (j.2.1 i k l + j.2.1 k i l - j.2.1 l i k)) / 2

def inverseDerivative (j : Jet) (s a b : I) : ℝ :=
  - ∑ i, ∑ k, inverse j.1 a i * j.2.1 s i k * inverse j.1 k b

def christoffelDerivative (j : Jet) (s a i k : I) : ℝ :=
  (∑ l, (inverseDerivative j s a l * (j.2.1 i k l + j.2.1 k i l - j.2.1 l i k) +
    inverse j.1 a l * (j.2.2 s i k l + j.2.2 s k i l - j.2.2 s l i k))) / 2

def ricci (j : Jet) (i k : I) : ℝ :=
  (∑ a, (christoffelDerivative j a a i k - christoffelDerivative j k a i a)) +
  ∑ a, ∑ b, (christoffel j a a b * christoffel j b i k -
    christoffel j a k b * christoffel j b i a)

def scalarCurvature (j : Jet) : ℝ := ∑ i, ∑ k, inverse j.1 i k * ricci j i k

def laplace (j : Jet) (f : ScalarJet) : ℝ :=
  ∑ i, ∑ k, inverse j.1 i k * (f.2.2 i k - ∑ a, christoffel j a i k * f.2.1 a)

def lapseLaplacian (j : Jet) (z : ScalarJet) : ℝ :=
  (∑ i, ∑ k, inverse j.1 i k *
    (2 * z.2.1 i * z.2.1 k / z.1^2 - z.2.2 i k / z.1 +
      (∑ a, christoffel j a i k * z.2.1 a) / z.1))

def operators (j : CombinedJet) : ℝ × ℝ :=
  (scalarCurvature j.1, lapseLaplacian j.1 j.2)

def regular : Set CombinedJet := {j | determinant j.1.1 ≠ 0 ∧ j.2.1 ≠ 0}

lemma determinant_smooth : ContDiff ℝ ∞ determinant := by
  unfold determinant
  fun_prop

lemma inverse_component_smooth {j : CombinedJet} (hj : j ∈ regular) (i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => inverse y.1.1 i k) j := by
  unfold inverse
  apply ContDiffAt.div
  · fin_cases i <;> fin_cases k <;> dsimp <;> fun_prop
  · exact determinant_smooth.contDiffAt.comp j (by fun_prop)
  · exact hj.1

lemma christoffel_smooth {j : CombinedJet} (hj : j ∈ regular) (a i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => christoffel y.1 a i k) j := by
  unfold christoffel
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro l hl
  exact (inverse_component_smooth hj a l).mul (by fun_prop)

lemma inverseDerivative_smooth {j : CombinedJet} (hj : j ∈ regular) (s a b : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => inverseDerivative y.1 s a b) j := by
  unfold inverseDerivative
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro i hi
  apply ContDiffAt.sum
  intro k hk
  exact ((inverse_component_smooth hj a i).mul (by fun_prop)).mul
    (inverse_component_smooth hj k b)

lemma christoffelDerivative_smooth {j : CombinedJet} (hj : j ∈ regular) (s a i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => christoffelDerivative y.1 s a i k) j := by
  unfold christoffelDerivative
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro l hl
  exact ((inverseDerivative_smooth hj s a l).mul (by fun_prop)).add
    ((inverse_component_smooth hj a l).mul (by fun_prop))

lemma ricci_smooth {j : CombinedJet} (hj : j ∈ regular) (i k : I) :
    ContDiffAt ℝ ∞ (fun y : CombinedJet => ricci y.1 i k) j := by
  unfold ricci
  apply ContDiffAt.add
  · apply ContDiffAt.sum
    intro a ha
    exact (christoffelDerivative_smooth hj a a i k).sub
      (christoffelDerivative_smooth hj k a i a)
  · apply ContDiffAt.sum
    intro a ha
    apply ContDiffAt.sum
    intro b hb
    exact ((christoffel_smooth hj a a b).mul (christoffel_smooth hj b i k)).sub
      ((christoffel_smooth hj a k b).mul (christoffel_smooth hj b i a))

lemma operators_smooth {j : CombinedJet} (hj : j ∈ regular) :
    ContDiffAt ℝ ∞ operators j := by
  apply ContDiffAt.prodMk
  · unfold scalarCurvature
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro k hk
    exact (inverse_component_smooth hj i k).mul (ricci_smooth hj i k)
  · unfold lapseLaplacian
    apply ContDiffAt.sum
    intro i hi
    apply ContDiffAt.sum
    intro k hk
    apply (inverse_component_smooth hj i k).mul
    apply ContDiffAt.add
    · apply ContDiffAt.sub
      · apply ContDiffAt.div (g := fun y : CombinedJet => y.2.1^2)
        · fun_prop
        · fun_prop
        · exact pow_ne_zero 2 hj.2
      · apply ContDiffAt.div (g := fun y : CombinedJet => y.2.1)
        · fun_prop
        · fun_prop
        · exact hj.2
    · apply ContDiffAt.div (g := fun y : CombinedJet => y.2.1)
      · apply ContDiffAt.sum
        intro a ha
        exact (christoffel_smooth hj a i k).mul (by fun_prop)
      · fun_prop
      · exact hj.2

lemma regular_open : IsOpen regular := by
  apply IsOpen.inter
  · exact isOpen_ne_fun (determinant_smooth.continuous.comp (by fun_prop)) continuous_const
  · exact isOpen_ne_fun (by fun_prop) continuous_const

theorem operators_uniform_lipschitz {K : Set CombinedJet} (hK : IsCompact K)
    (hreg : K ⊆ regular) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      LipschitzOnWith C operators (Metric.cthickening δ K) := by
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open regular_open hreg
  refine ⟨δ,hδ,?_⟩
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hK.cthickening (r := δ))
  intro j hj
  obtain ⟨C,t,ht,hCt⟩ := ((operators_smooth (hsub hj)).of_le (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hCt⟩

end
end CKSAngularGeometry

end

end OAI
