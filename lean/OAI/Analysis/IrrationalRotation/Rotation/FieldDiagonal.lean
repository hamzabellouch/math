import OAI.Analysis.IrrationalRotation.Model.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftAlgebra
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)

theorem fieldDiagonal_ae (f : Lp Hilbert 2 μ) :
    fieldDiagonal a C hC ha hm f =ᵐ[μ] fun x => diagonal (a x) (f x) :=
  fieldDiagonalVec_ae a C hC ha hm f

theorem fieldDiagonal_coordinate_ae (f : Lp Hilbert 2 μ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ, fieldDiagonal a C hC ha hm f x k = a x k * f x k := by
  filter_upwards [fieldDiagonal_ae a C hC ha hm f] with x hx k
  exact congrArg (fun v : Hilbert => v k) hx

theorem norm_fieldDiagonal_le : ‖fieldDiagonal a C hC ha hm‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable {a C hC ha hm}

theorem fieldDiagonal_congr
    {b : X → Weight} {D : ℝ} {hD : 0 ≤ D} {hb : ∀ x, ‖b x‖ ≤ D}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ}
    (hab : a =ᵐ[μ] b) :
    fieldDiagonal a C hC ha hm = fieldDiagonal b D hD hb hn := by
  ext f
  filter_upwards [fieldDiagonal_ae a C hC ha hm f,
    fieldDiagonal_ae b D hD hb hn f, hab] with x hx hy hxy
  rw [hx, hy, hxy]

theorem fieldDiagonal_mul_of_coeff_eq
    {b c : X → Weight} {D E : ℝ} {hD : 0 ≤ D} {hE : 0 ≤ E}
    {hb : ∀ x, ‖b x‖ ≤ D} {hc : ∀ x, ‖c x‖ ≤ E}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ}
    {hp : ∀ k, AEStronglyMeasurable (fun x => c x k) μ}
    (heq : ∀ᵐ x ∂μ, ∀ k, c x k = a x k * b x k) :
    fieldDiagonal c E hE hc hp =
      fieldDiagonal a C hC ha hm * fieldDiagonal b D hD hb hn := by
  ext f
  filter_upwards [fieldDiagonal_coordinate_ae c E hE hc hp f,
    fieldDiagonal_coordinate_ae a C hC ha hm (fieldDiagonal b D hD hb hn f),
    fieldDiagonal_coordinate_ae b D hD hb hn f, heq] with x hx hy hz he
  apply lp.ext
  funext k
  change fieldDiagonal c E hE hc hp f x k =
    fieldDiagonal a C hC ha hm (fieldDiagonal b D hD hb hn f) x k
  rw [hx, hy, hz, he, mul_assoc]

theorem fieldDiagonal_eq_one_of_coeff_eq_one
    (heq : ∀ᵐ x ∂μ, ∀ k, a x k = 1) :
    fieldDiagonal a C hC ha hm = 1 := by
  ext f
  filter_upwards [fieldDiagonal_coordinate_ae a C hC ha hm f, heq] with x hx he
  apply lp.ext
  funext k
  change fieldDiagonal a C hC ha hm f x k = f x k
  rw [hx, he, one_mul]

theorem fieldDiagonal_commute
    {b : X → Weight} {D : ℝ} {hD : 0 ≤ D} {hb : ∀ x, ‖b x‖ ≤ D}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ} :
    Commute (fieldDiagonal a C hC ha hm) (fieldDiagonal b D hD hb hn) := by
  change fieldDiagonal a C hC ha hm * fieldDiagonal b D hD hb hn =
    fieldDiagonal b D hD hb hn * fieldDiagonal a C hC ha hm
  ext f
  filter_upwards [fieldDiagonal_coordinate_ae a C hC ha hm (fieldDiagonal b D hD hb hn f),
    fieldDiagonal_coordinate_ae b D hD hb hn f,
    fieldDiagonal_coordinate_ae b D hD hb hn (fieldDiagonal a C hC ha hm f),
    fieldDiagonal_coordinate_ae a C hC ha hm f] with x hab hbx hba hax
  apply lp.ext
  funext k
  change fieldDiagonal a C hC ha hm (fieldDiagonal b D hD hb hn f) x k =
    fieldDiagonal b D hD hb hn (fieldDiagonal a C hC ha hm f) x k
  rw [hab, hbx, hba, hax]
  ring

theorem fieldDiagonal_star_of_eq
    {b : X → Weight} {D : ℝ} {hD : 0 ≤ D} {hb : ∀ x, ‖b x‖ ≤ D}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ}
    (heq : b =ᵐ[μ] fun x => star (a x)) :
    fieldDiagonal b D hD hb hn = star (fieldDiagonal a C hC ha hm) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldDiagonal_ae b D hD hb hn f,
    fieldDiagonal_ae a C hC ha hm g, heq] with x hx hy he
  rw [hx, hy, he, diagonal_star, ContinuousLinearMap.star_eq_adjoint]
  exact (diagonal (a x)).adjoint_inner_left (g x) (f x)

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

theorem fieldShift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ =
      (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  ext f
  filter_upwards [fieldShift_ae (m + n) f,
    fieldShift_ae m ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f),
    fieldShift_ae n f] with x hmn hm hn
  change ((shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x =
    ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f)) x
  rw [hmn, hm, hn]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f x)) (shift_add m n)

theorem fieldShift_zero :
    (shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ = 1 := by
  ext f
  filter_upwards [fieldShift_ae 0 f] with x hx
  change ((shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x = f x
  rw [hx]
  change (shift 0).toLinearIsometry.toContinuousLinearMap (f x) = f x
  rw [shift_zero]
  rfl

theorem fieldDiagonal_shift_covariance
    {b : X → Weight} {D : ℝ} {hD : 0 ≤ D} {hb : ∀ x, ‖b x‖ ≤ D}
    {hn : ∀ k, AEStronglyMeasurable (fun x => b x k) μ}
    (m : ℤ) (heq : b =ᵐ[μ] fun x => translate (a x) m) :
    fieldDiagonal a C hC ha hm *
        (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ =
      (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        fieldDiagonal b D hD hb hn := by
  ext f
  filter_upwards [fieldDiagonal_ae a C hC ha hm
      ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f),
    fieldShift_ae m f, fieldShift_ae m (fieldDiagonal b D hD hb hn f),
    fieldDiagonal_ae b D hD hb hn f, heq] with x hleft hs hright hbval he
  change (fieldDiagonal a C hC ha hm
      ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f)) x =
    ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      (fieldDiagonal b D hD hb hn f)) x
  rw [hleft, hs, hright, hbval, he]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f x))
    (diagonal_shift_covariance (a x) m)

theorem fieldShift_norm_map (m : ℤ) (f : Lp Hilbert 2 μ) :
    ‖(shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ,
      ‖((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x‖ = ‖f x‖ := by
    filter_upwards [fieldShift_ae m f] with x hx
    rw [hx, (shift m).norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldShift_mem_unitary (m : ℤ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  let A := (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  let B := (shift (-m)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hA : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  apply hA.mem_unitary_iff_star_mul_self.mpr
  change ContinuousLinearMap.adjoint A ∘L A = 1
  exact A.norm_map_iff_adjoint_comp_self.mp (fieldShift_norm_map m)

theorem fieldDiagonal_norm_map
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) (f : Lp Hilbert 2 μ) :
    ‖fieldDiagonal a C hC ha hm f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ, ‖fieldDiagonal a C hC ha hm f x‖ = ‖f x‖ := by
    filter_upwards [fieldDiagonal_coordinate_ae a C hC ha hm f, hunit] with x hx hu
    have hcoord : ∀ k, ‖fieldDiagonal a C hC ha hm f x k‖ = ‖f x k‖ := by
      intro k
      rw [hx, norm_mul, hu, one_mul]
    exact le_antisymm (lp.norm_mono (by norm_num) fun k => (hcoord k).le)
      (lp.norm_mono (by norm_num) fun k => (hcoord k).symm.le)
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldDiagonal_mem_unitary
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) :
    fieldDiagonal a C hC ha hm ∈ unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  have hb : ∀ x, ‖star (a x)‖ ≤ C := by simpa using ha
  have hn : ∀ k, AEStronglyMeasurable (fun x => star (a x) k) μ := by
    intro k
    simpa only [lp.coeFn_star, Pi.star_apply] using
      continuous_star.comp_aestronglyMeasurable (hm k)
  have hstar : fieldDiagonal (fun x => star (a x)) C hC hb hn =
      star (fieldDiagonal a C hC ha hm) :=
    fieldDiagonal_star_of_eq (Filter.Eventually.of_forall fun _ => rfl)
  have hunitstar : ∀ᵐ x ∂μ, ∀ k, ‖star (a x) k‖ = 1 := by
    simpa only [lp.coeFn_star, Pi.star_apply, norm_star] using hunit
  apply Unitary.mem_iff.mpr
  constructor
  · change ContinuousLinearMap.adjoint (fieldDiagonal a C hC ha hm) ∘L
      fieldDiagonal a C hC ha hm = 1
    exact ContinuousLinearMap.norm_map_iff_adjoint_comp_self _ |>.mp
      (fieldDiagonal_norm_map hunit)
  · have hh := ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (star (fieldDiagonal a C hC ha hm)) |>.mp (fun f => by
        rw [← hstar]
        exact fieldDiagonal_norm_map hunitstar f)
    change star (star (fieldDiagonal a C hC ha hm)) *
      star (fieldDiagonal a C hC ha hm) = 1 at hh
    simpa only [star_star] using hh

end Invariant233.WeightedShift

end

end OAI
