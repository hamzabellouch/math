import Mathlib
import OAI.Analysis.AffineBernstein.ParametricGraphJets

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

lemma trace_sum_matrices {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (g : κ → ℝ) (C : κ → Matrix ι ι ℝ) :
    (∑ i, ∑ j, A i j * ∑ k, g k * C k i j) =
      ∑ k, g k * ∑ i, ∑ j, A i j * C k i j := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma hasDerivAt_graphVariationArea_raw {n : ℕ} {u β : Space n → ℝ}
    (a : Fin n → Space n → ℝ) {x : Space n} (hp : (hessian u x).PosDef) :
    HasDerivAt (graphVariationArea u β a x)
      ((1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        ((∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian β x i j) -
          ∑ k, dirDeriv (coordinateVector n k) u x *
            ∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian (a k) x i j) +
        affineAreaDensity u x * ((n : ℝ) * (1 / ((n : ℝ) + 2)) *
          ∑ k, dirDeriv (coordinateVector n k) (a k) x)) 0 := by
  have hh := hasDerivAt_variationAreaDensity_raw (hessian u x) (hessian β x)
    (horizontalJacobian a x) hp (fun k => dirDeriv (coordinateVector n k) u x)
    (fun k => dirDeriv (coordinateVector n k) β x) (fun k => hessian (a k) x)
    (1 / ((n : ℝ) + 2))
  have hw : (1 / ((n : ℝ) + 2)) - 1 = -(((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    field_simp
    ring
  have hcof (i j : Fin n) : (hessian u x).adjugate j i = cofactorHessian u x i j := by
    rw [← cofactorHessian_eq_adjugate u x (ne_of_gt hp.det_pos)]
    exact (cofactorHessian_isSymm u x hp).apply i j
  have he (T : Matrix (Fin n) (Fin n) ℝ) :
      (1 / ((n : ℝ) + 2)) * Real.rpow (hessian u x).det ((1 / ((n : ℝ) + 2)) - 1) *
        (∑ i, ∑ j, (hessian u x).adjugate j i * T i j) =
      (1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * T i j) := by
    rw [hw]
    change (1 / ((n : ℝ) + 2)) * affineWeight u x * _ = _
    simp only [Finset.mul_sum, hcof]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = (1 / ((n : ℝ) + 2)) * (affineWeight u x * cofactorHessian u x i j) * T i j := by ring
      _ = _ := by rw [affine_weight_cofactor_entry hp]; ring
  convert! hh using 1
  symm
  erw [he (Matrix.of fun i j => hessian β x i j -
    ∑ k, dirDeriv (coordinateVector n k) u x * hessian (a k) x i j)]
  simp only [Matrix.of_apply, mul_sub, Finset.sum_sub_distrib, trace_sum_matrices, Fintype.card_fin]
  rfl

/- The tangential part of the exact parametrized first-variation density is
an ordinary divergence; the remaining part is the genuine graph variation. -/
lemma hasDerivAt_graphVariationArea_normal {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u η : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) (hη : ContDiffOn ℝ ∞ η Ω)
    {a : Fin n → Space n → ℝ} (ha : ∀ k, ContDiffOn ℝ ∞ (a k) Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    HasDerivAt (graphVariationArea u (verticalVariation u η a) a x)
      ((1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian η x i j) +
        ∑ k, dirDeriv (coordinateVector n k) (fun y => affineAreaDensity u y * a k y) x) 0 := by
  have hh := hasDerivAt_graphVariationArea_raw (u := u) (β := verticalVariation u η a) a hp
  rw [trace_hessian_verticalVariation hΩ hu hη ha hx hp] at hh
  have hd (k : Fin n) :
      dirDeriv (coordinateVector n k) (fun y => affineAreaDensity u y * a k y) x =
      (1 / ((n : ℝ) + 2)) * affineAreaDensity u x *
        (a k x * ∑ i, ∑ j, (hessian u x)⁻¹ i j *
          dirDeriv (coordinateVector n k) (fun y => hessian u y i j) x) +
      affineAreaDensity u x * dirDeriv (coordinateVector n k) (a k) x := by
    rw [dirDeriv_mul ((contDiffAt_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds hx)) hp).differentiableAt (by simp))
      (((ha k).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)),
      dirDeriv_affineAreaDensity (hu.contDiffAt (hΩ.mem_nhds hx)) hp]
    ring
  convert! hh using 1
  simp only [hd, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hn : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

end AffineBernstein
end

end OAI
