import OAI.NumberTheory.PiExponent.Approximation.AdmissibleParameters
import OAI.NumberTheory.PiExponent.Approximation.PersistentWeightComparison

namespace OAI

namespace PiExponent.AdmissibleParameters
noncomputable section
open scoped BigOperators
variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

def curveDegreeWeights : Fin (d.m + 1) → ℚ :=
  Fin.cases d.w0 (fun i => d.rationalWeight (i.val + 1))

def curveJetWeights : Fin (d.m + 1) → ℚ :=
  Fin.cases d.v0 (fun i => d.rationalWeight (i.val + 1) / d.base.theta)

@[simp] lemma curveDegreeWeights_zero : d.curveDegreeWeights 0 = d.w0 := rfl
@[simp] lemma curveDegreeWeights_succ (i : Fin d.m) :
    d.curveDegreeWeights i.succ = d.rationalWeight (i.val + 1) := rfl
@[simp] lemma curveJetWeights_zero : d.curveJetWeights 0 = d.v0 := rfl
@[simp] lemma curveJetWeights_succ (i : Fin d.m) :
    d.curveJetWeights i.succ = d.rationalWeight (i.val + 1) / d.base.theta := rfl

lemma curveDegreeWeights_pos (i : Fin (d.m + 1)) : 0 < d.curveDegreeWeights i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact_mod_cast d.w0_pos
  · simpa only [curveDegreeWeights_succ] using d.rationalWeight_pos (i.val + 1)

lemma curveJetWeights_pos (i : Fin (d.m + 1)) : 0 < d.curveJetWeights i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact_mod_cast d.v0_pos
  · exact div_pos (d.rationalWeight_pos _) (by exact_mod_cast d.base.theta_pos)

lemma curveDegreeWeights_cast (i : Fin (d.m + 1)) :
    (d.curveDegreeWeights i : ℝ) = PiExponentApprox.geometricDegreeWeight d.w0 d.x i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [PiExponentApprox.geometricDegreeWeight]
  · simp [PiExponentApprox.geometricDegreeWeight, d.cast_rationalWeight]

lemma curveJetWeights_cast (i : Fin (d.m + 1)) :
    (d.curveJetWeights i : ℝ) = PiExponentApprox.geometricJetWeight d.v0 d.base.theta d.x i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [PiExponentApprox.geometricJetWeight]
  · simp [PiExponentApprox.geometricJetWeight, d.cast_rationalWeight]

lemma curve_fibre_product_ratio :
    (∏ i : Fin d.m, (d.curveDegreeWeights i.succ : ℝ)) /
      (∏ i : Fin d.m, (d.curveJetWeights i.succ : ℝ)) = (d.base.theta : ℝ) ^ d.m := by
  have hp : (∏ i : Fin d.m, (d.rationalWeight (i.val + 1) : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast ne_of_gt (d.rationalWeight_pos _))
  simp only [curveDegreeWeights_succ, curveJetWeights_succ, Rat.cast_div,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  field_simp [hp]

lemma curve_product_ratio :
    (∏ i : Fin (d.m + 1), (d.curveDegreeWeights i : ℝ)) /
      (∏ i : Fin (d.m + 1), (d.curveJetWeights i : ℝ)) =
      ((d.w0 : ℝ) / d.v0) * (d.base.theta : ℝ) ^ d.m := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_div_mul_comm, d.curve_fibre_product_ratio]
  rfl

lemma curve_volume :
    (d.K : ℝ) * (1 + 3 * (d.sigma : ℝ)) ^ (d.m + 1) *
      (∏ i, (d.curveDegreeWeights i : ℝ)) / (∏ i, (d.curveJetWeights i : ℝ)) < 1 := by
  calc
    _ = (1 + 3 * (d.sigma : ℝ)) ^ (d.m + 1) *
        ((d.K : ℝ) * ((∏ i, (d.curveDegreeWeights i : ℝ)) /
          (∏ i, (d.curveJetWeights i : ℝ)))) := by ring
    _ = (1 + 3 * (d.sigma : ℝ)) ^ (d.m + 1) *
        ((d.K : ℝ) * ((d.w0 : ℝ) / d.v0) * (d.base.theta : ℝ) ^ d.m) := by
      rw [d.curve_product_ratio]
      ring
    _ < 1 := d.sigma_volume

lemma curve_fibre_volume :
    (d.K : ℝ) * (1 + 3 * (d.sigma : ℝ)) ^ d.m *
      (∏ i : Fin d.m, (d.curveDegreeWeights i.succ : ℝ)) /
      (∏ i : Fin d.m, (d.curveJetWeights i.succ : ℝ)) < 1 := by
  calc
    _ = (1 + 3 * (d.sigma : ℝ)) ^ d.m *
        ((d.K : ℝ) * ((∏ i : Fin d.m, (d.curveDegreeWeights i.succ : ℝ)) /
          (∏ i : Fin d.m, (d.curveJetWeights i.succ : ℝ)))) := by ring
    _ = (1 + 3 * (d.sigma : ℝ)) ^ d.m *
        ((d.K : ℝ) * (d.base.theta : ℝ) ^ d.m) := by rw [d.curve_fibre_product_ratio]
    _ < 1 := d.sigma_centers

lemma curve_coordinate_ratio (i : Fin d.m) :
    (1 + (d.sigma : ℝ)) * (d.curveDegreeWeights i.succ : ℝ) <
      (d.curveJetWeights i.succ : ℝ) := by
  simp only [curveDegreeWeights_succ, curveJetWeights_succ, Rat.cast_div]
  apply (lt_div_iff₀ d.base.theta_pos).mpr
  have hi : (0 : ℝ) < d.rationalWeight (i.val + 1) := by exact_mod_cast d.rationalWeight_pos _
  nlinarith [mul_lt_mul_of_pos_right d.sigma_theta hi]

lemma curve_separated_weight_products (A B : Finset (Fin (d.m + 1)))
    (hcard : A.card = B.card) (i : Fin (d.m + 1)) (hi : i ≠ 0)
    (hiA : i ∈ A) (hiB : i ∉ B)
    (hhigh : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) :
    PersistentWeightComparison.comparisonConstant d.m d.sigma *
      (∏ j ∈ B, (d.curveJetWeights j : ℝ)) <
      ∏ j ∈ A, (d.curveDegreeWeights j : ℝ) := by
  classical
  let e : Fin (d.m + 1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hbound (S : Finset (Fin (d.m + 1))) : S.map e ⊆ Finset.range (d.m + 1) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨k, hkB, rfl⟩ := Finset.mem_map.mp hjB
    by_contra hnot
    have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
    have hne : i ≠ k := fun h => hiB (h.symm ▸ hkB)
    have hkA := (hhigh k (lt_of_le_of_ne hik hne)).mpr hkB
    exact hjA (Finset.mem_map.mpr ⟨k, hkA, rfl⟩)
  have hn : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have h := d.separated_weight_products (A.map e) (B.map e)
    (by simpa using hcard) (hbound A) (hbound B) i.val hn
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩)
    (by
      intro hmem
      obtain ⟨a, haB, hai⟩ := Finset.mem_map.mp hmem
      have hai' : a = i := Fin.ext hai
      exact hiB (hai' ▸ haB))
    hbelow
  simpa only [Finset.prod_map, e, Function.Embedding.coeFn_mk,
    ← d.curveJetWeights_cast, ← d.curveDegreeWeights_cast,
    PersistentWeightComparison.comparisonConstant, interpolationSeparationConstant] using h

end
end PiExponent.AdmissibleParameters

end OAI
