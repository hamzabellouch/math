import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.QuadraticBound
import OAI.Geometry.TamingCompatibility.HeatFlow.FlatHeat

namespace OAI

section
section
section
noncomputable section
section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace TamingCompatibility.GeometricHilbert.NormalHeatResidual
open scoped ContDiff RealInnerProductSpace
open FlatHeat (V heat)
open Filter Set
open scoped Topology
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
abbrev End := W →L[ℝ] W
abbrev Principal := Fin 4 → Fin 4 → ℝ
abbrev First := Fin 4 → End (W := W)
def euclideanPrincipal : Principal := fun i j => if i = j then 1 else 0

def residual (a : V → Principal) (b : V → First (W := W))
    (c : V → End (W := W)) (t : ℝ) (z : V) : End (W := W) :=
  (∑ i, ∑ j, ((euclideanPrincipal i j - a z i j) *
    fderiv ℝ (fun y => fderiv ℝ (heat t) y (EuclideanSpace.basisFun (Fin 4) ℝ j)) z
      (EuclideanSpace.basisFun (Fin 4) ℝ i)) • ContinuousLinearMap.id ℝ W) +
  (∑ i, (fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) • b z i) +
    heat t z • c z

lemma residual_bound (a : V → Principal) (b : V → First (W := W))
    (c : V → End (W := W)) {Ca Cb Cc t : ℝ} (ht : 0 < t)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (z : V)
    (ha : ∀ i j, |a z i j - euclideanPrincipal i j| ≤ Ca*‖z‖^2)
    (hb : ∀ i, ‖b z i‖ ≤ Cb*‖z‖) (hc : ‖c z‖ ≤ Cc) :
    ‖residual a b c t z‖ ≤ (2304*Ca + 64*Cb + 4*Cc)*heat (2*t) z := by
  have hH := FlatHeat.heat_nonneg (2*t) z
  have ha' (i j : Fin 4) : ‖((euclideanPrincipal i j - a z i j) *
      fderiv ℝ (fun y => fderiv ℝ (heat t) y (EuclideanSpace.basisFun (Fin 4) ℝ j)) z
        (EuclideanSpace.basisFun (Fin 4) ℝ i)) • ContinuousLinearMap.id ℝ W‖ ≤
      144*Ca*heat (2*t) z := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_sub_comm]
    calc
      _ ≤ (Ca*‖z‖^2) * |fderiv ℝ (fun y => fderiv ℝ (heat t) y
          (EuclideanSpace.basisFun (Fin 4) ℝ j)) z (EuclideanSpace.basisFun (Fin 4) ℝ i)| * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right (ha i j) (abs_nonneg _))
          ContinuousLinearMap.norm_id_le (norm_nonneg _) (by positivity)
      _ = Ca * (‖z‖^2 * |fderiv ℝ (fun y => fderiv ℝ (heat t) y
          (EuclideanSpace.basisFun (Fin 4) ℝ j)) z (EuclideanSpace.basisFun (Fin 4) ℝ i)|) := by ring
      _ ≤ Ca*(144*heat (2*t) z) := mul_le_mul_of_nonneg_left
        (by simpa using (FlatHeat.normal_jet_hessian_bound ht z
          (EuclideanSpace.basisFun (Fin 4) ℝ i) (EuclideanSpace.basisFun (Fin 4) ℝ j))) hCa
      _ = _ := by ring
  have hb' (i : Fin 4) : ‖(fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) • b z i‖ ≤
      16*Cb*heat (2*t) z := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)| * (Cb*‖z‖) :=
        mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
      _ = Cb*(‖z‖ * |fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)|) := by ring
      _ ≤ Cb*(16*heat (2*t) z) := mul_le_mul_of_nonneg_left
        (by simpa using (FlatHeat.normal_jet_gradient_bound ht z
          (EuclideanSpace.basisFun (Fin 4) ℝ i))) hCb
      _ = _ := by ring
  have hc' : ‖heat t z • c z‖ ≤ 4*Cc*heat (2*t) z := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (FlatHeat.heat_nonneg t z)]
    have h := FlatHeat.gaussian_weight_absorption ht z 0
    norm_num only [Nat.mul_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, mul_one] at h
    calc
      _ ≤ (4*heat (2*t) z)*Cc := mul_le_mul h hc (norm_nonneg _) (by positivity)
      _ = _ := by ring
  unfold residual
  calc
    _ ≤ ‖∑ i, ∑ j, ((euclideanPrincipal i j - a z i j) *
        fderiv ℝ (fun y => fderiv ℝ (heat t) y (EuclideanSpace.basisFun (Fin 4) ℝ j)) z
          (EuclideanSpace.basisFun (Fin 4) ℝ i)) • ContinuousLinearMap.id ℝ W‖ +
        ‖∑ i, (fderiv ℝ (heat t) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) • b z i‖ +
        ‖heat t z • c z‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (∑ i : Fin 4, ∑ j : Fin 4, 144*Ca*heat (2*t) z) +
        (∑ i : Fin 4, 16*Cb*heat (2*t) z) + 4*Cc*heat (2*t) z := by
      apply add_le_add _ hc'
      apply add_le_add
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ha' i j))
      · exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb' i)
    _ = _ := by simp; ring

lemma exists_residual_bound (a : V → Principal) (b : V → First (W := W))
    (c : V → End (W := W)) (ha : ContDiffAt ℝ 2 a 0)
    (ha0 : a 0 = euclideanPrincipal) (hda : fderiv ℝ a 0 = 0)
    (hb : ContDiffAt ℝ 1 b 0) (hb0 : b 0 = 0) (hc : ContinuousAt c 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ t : ℝ, 0 < t →
      ∀ z : V, ‖z‖ ≤ r → ‖residual a b c t z‖ ≤ C*heat (2*t) z := by
  obtain ⟨Ca,hCa,ra,hra,ha'⟩ := LocalTaylor.quadratic_bound ha hda
  obtain ⟨Cb,hCb,rb,hrb,hb'⟩ := LocalTaylor.linear_bound hb hb0
  have hce : ∀ᶠ z in nhds (0 : V), ‖c z‖ < ‖c 0‖+1 :=
    hc.norm (isOpen_Iio.mem_nhds (lt_add_one _))
  obtain ⟨rc,hrc,hc'⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hce
  refine ⟨2304*Ca+64*Cb+4*(‖c 0‖+1), by positivity,
    min ra (min rb rc), lt_min hra (lt_min hrb hrc), fun t ht z hz => ?_⟩
  apply residual_bound a b c ht hCa hCb z
  · intro i j
    have h0 := (ha' z (hz.trans (min_le_left _ _))).1
    rw [ha0] at h0
    exact (le_trans (norm_le_pi_norm ((a z-euclideanPrincipal) i) j)
      (norm_le_pi_norm (a z-euclideanPrincipal) i)).trans h0
  · intro i
    exact (norm_le_pi_norm (b z) i).trans (hb' z
      (hz.trans ((min_le_right _ _).trans (min_le_left _ _))))
  · exact (hc' (by simpa using hz.trans ((min_le_right _ _).trans (min_le_right _ _)))).le

def applyOperator (a : V → Principal) (b : V → First (W := W))
    (c : V → End (W := W)) (f : V → W) (z : V) : W :=
  -(∑ i, ∑ j, a z i j • fderiv ℝ (fun y => fderiv ℝ f y
      (EuclideanSpace.basisFun (Fin 4) ℝ j)) z (EuclideanSpace.basisFun (Fin 4) ℝ i)) +
    (∑ i, b z i (fderiv ℝ f z (EuclideanSpace.basisFun (Fin 4) ℝ i))) + c z (f z)

def modelSection (t : ℝ) (u : W) (z : V) : W := heat t z • u

lemma modelSection_fderiv (t : ℝ) (u : W) (z v : V) :
    fderiv ℝ (modelSection t u) z v = fderiv ℝ (heat t) z v • u := by
  have h := ((FlatHeat.heat_hasFDerivAt t z).smul_const u).fderiv
  simpa only [modelSection, ContinuousLinearMap.smulRight_apply,
    (FlatHeat.heat_hasFDerivAt t z).fderiv] using!
    congrArg (fun f : V →L[ℝ] W => f v) h

lemma modelSection_hessian (t : ℝ) (u : W) (z v w : V) :
    fderiv ℝ (fun y => fderiv ℝ (modelSection t u) y v) z w =
      (fderiv ℝ (fun y => fderiv ℝ (heat t) y v) z w) • u := by
  simp_rw [modelSection_fderiv]
  have h := ((FlatHeat.heat_directional_hasFDerivAt t z v).smul_const u).fderiv
  simpa only [ContinuousLinearMap.smulRight_apply,
    (FlatHeat.heat_directional_hasFDerivAt t z v).fderiv] using
    congrArg (fun f : V →L[ℝ] W => f w) h

lemma modelSection_time {t : ℝ} (ht : 0 < t) (u : W) (z : V) :
    deriv (fun s => modelSection s u z) t = FlatHeat.laplacian (heat t) z • u := by
  have h := ((FlatHeat.heat_hasDerivAt_time ht z).smul_const u).deriv
  rw [← FlatHeat.heat_equation ht z, (FlatHeat.heat_hasDerivAt_time ht z).deriv]
  exact h

lemma residual_apply (a : V → Principal) (b : V → First (W := W))
    (c : V → End (W := W)) {t : ℝ} (ht : 0 < t) (z : V) (u : W) :
    deriv (fun s => modelSection s u z) t + applyOperator a b c (modelSection t u) z =
      residual a b c t z u := by
  rw [modelSection_time ht, applyOperator]
  simp_rw [modelSection_hessian, modelSection_fderiv]
  simp only [modelSection, map_smul]
  simp [residual, euclideanPrincipal, FlatHeat.laplacian, Finset.sum_sub_distrib,
    sub_smul, mul_smul, Finset.sum_smul]
  abel

end TamingCompatibility.GeometricHilbert.NormalHeatResidual

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
