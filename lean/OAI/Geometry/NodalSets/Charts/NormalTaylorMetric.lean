import OAI.Geometry.NodalSets.Elliptic.UniformTaylor

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma tensorPolynomial_zero (k : ℕ) : tensorPolynomial (0 : Coord [×k]→L[ℝ] ℂ) = 0 := by
  induction k with
  | zero => simp [tensorPolynomial]
  | succ k ih =>
    simp only [tensorPolynomial]
    have hz (i : Fin 4) : (0 : Coord [×(k+1)]→L[ℝ] ℂ).curryLeft (Pi.single i 1) = 0 := by ext v; simp
    simp_rw [hz, ih]
    simp

lemma taylorPolynomial_component (f : Coord → ℂ) (y : Coord) (m k : ℕ) (hk : k ≤ m) :
    homogeneousComponent k (taylorPolynomial f y m) =
      C (((k.factorial:ℝ)⁻¹:ℝ):ℂ) * tensorPolynomial (iteratedFDeriv ℝ k f y) := by
  unfold taylorPolynomial
  rw [map_sum]
  have ht (l : ℕ) :
      (C (((l.factorial:ℝ)⁻¹:ℝ):ℂ) * tensorPolynomial (iteratedFDeriv ℝ l f y)).IsHomogeneous l :=
    (tensorPolynomial_homogeneous _).C_mul _
  simp_rw [homogeneousComponent_of_mem (ht _)]
  simp [Finset.mem_range, show k < m+1 by omega]

lemma taylorPolynomial_value_component (f : Coord → ℂ) (y : Coord) (m : ℕ) :
    homogeneousComponent 0 (taylorPolynomial f y m) = C (f y) := by
  rw [taylorPolynomial_component f y m 0 (by omega)]
  simp [tensorPolynomial]

lemma taylorPolynomial_first_zero (f : Coord → ℂ) (y : Coord) (m : ℕ)
    (hm : 1 ≤ m) (hf : fderiv ℝ f y = 0) :
    homogeneousComponent 1 (taylorPolynomial f y m) = 0 := by
  rw [taylorPolynomial_component f y m 1 hm]
  have hd : iteratedFDeriv ℝ 1 f y = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_one, hf, norm_zero]
  rw [hd, tensorPolynomial_zero, mul_zero]

theorem normal_metric_matching_taylor
    (g : Fin 4 → Fin 4 → Coord → ℂ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (h0 : ∀ i j, g i j 0 = if i=j then 1 else 0)
    (h1 : ∀ i j, fderiv ℝ (g i j) 0 = 0) (m : ℕ) (hm : 1 ≤ m) :
    let G := fun i j ↦ taylorPolynomial (g i j) 0 m
    (∀ i j, homogeneousComponent 0 (G i j) = if i=j then 1 else 0) ∧
    (∀ i j, homogeneousComponent 1 (G i j) = 0) ∧
    ∀ i j, FlatAt m (fun x ↦ g i j x-reval (G i j) x) 0 := by
  refine ⟨?_,fun i j ↦ taylorPolynomial_first_zero _ _ _ hm (h1 i j),
    fun i j ↦ flatAt_taylorPolynomial (hg i j) m⟩
  intro i j
  rw [taylorPolynomial_value_component, h0]
  split_ifs <;> simp

end
end Yau.Jets

end OAI
