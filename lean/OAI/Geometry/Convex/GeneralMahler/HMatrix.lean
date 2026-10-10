import OAI.Geometry.Convex.GeneralMahler.MixedField

namespace OAI
/-!
### H_f, A, L from Equation (7) and their growth bounds
-/
noncomputable section
open Set Filter Real Matrix MeasureTheory MeasureTheory.Measure
open scoped Topology ENNReal NNReal RealInnerProductSpace Matrix.Norms.L2Operator MatrixOrder
namespace GeneralMahler
open Layers
variable {m : ℕ}

namespace ProjField
variable (q : ProjField m)

def kerH (f : ℝ → ℝ) (z : ℝ) (x : Rn m) := deriv f z • q.PD z x
def Hmat (f : ℝ → ℝ) (x : Rn m) := ∫ z, q.kerH f z x
def Amat := q.Hmat id
def M (i : Fin m) := ∫ x, x i • q.Amat x ∂normal m
def Lmat (x : Rn m) := ∑ i, x i • q.M i
def Rmat (x : Rn m) := q.Amat x - q.Lmat x
def avgA := ∫ x, q.Amat x ∂normal m
lemma PD_herm (z x) : (q.PD z x).IsHermitian :=
    ((Matrix.isHermitian_one).smul (show IsSelfAdjoint (p z) by simp [IsSelfAdjoint])).sub (q.Pmat_herm _ _)

variable [NeZero m] {f : ℝ→ℝ} (h : PolyBound (deriv f))

lemma H_mixed (h : PolyBound (deriv f)) : mixed (q.kerH f) :=
  q.mixed_PD.product
    (g := fun z (_ : Rn m) => deriv f z)
    (h.comp PolyBound.fst) (fun x y => by
      rw [kerH,norm_smul]; exact le_of_eq (mul_comm ..))

omit [NeZero m] in
lemma H_sm : StronglyMeasurable (q.kerH f).uncurry :=
  ((measurable_deriv f).stronglyMeasurable.comp_measurable measurable_fst).smul q.PD_sm

omit [NeZero m] in
lemma H_ams (y : Rn m) :
    AEStronglyMeasurable (fun x => q.kerH f x y) :=
  ((q.H_sm (f := f)).comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable

include h in
lemma H_poly : PolyBound (q.Hmat f) :=
  poly_integral_left (q.H_mixed h) (q.H_ams)

include h in
lemma H_left_int (y) : Integrable (fun x => q.kerH f x y) :=
  mixed_integrable_left (q.H_mixed h) y (q.H_ams y)

omit [NeZero m] in
lemma H_SM : StronglyMeasurable (q.Hmat f) := (q.H_sm).integral_prod_left

include h in
lemma H_integrable : Integrable (q.Hmat f) (normal m) :=
  (q.H_poly h).gaussian_integrable q.H_SM.aestronglyMeasurable

include h in
lemma H_hermitian (x) : (q.Hmat f x).IsHermitian :=
  hermitian_integral (q.H_left_int h _)
    (ae_of_all _ fun z => (q.PD_herm ..).smul (show IsSelfAdjoint (deriv f z) by simp [IsSelfAdjoint]))

lemma poly_id_der : PolyBound (deriv (id : ℝ → ℝ)) := by
  rw [show deriv (id : ℝ → ℝ) = (fun _ => (1:ℝ)) from funext fun x => deriv_id x] ; exact PolyBound.const 1

lemma A_poly : PolyBound q.Amat := q.H_poly poly_id_der
omit [NeZero m] in
lemma A_SM : StronglyMeasurable q.Amat := q.H_SM
lemma A_integrable : Integrable q.Amat (normal m) := q.H_integrable poly_id_der

def coord (i : Fin m) : Rn m →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).toContinuousLinearMap
omit [NeZero m] in
@[simp] lemma coord_apply (i : Fin m) (x) : coord i x = x i := rfl

lemma A_coord_poly (i : Fin m) : PolyBound (fun x : Rn m => (x i) • q.Amat x) :=
  (PolyBound.clm (coord i)).smul q.A_poly

lemma A_coord_int (i : Fin m) :
    Integrable (fun x : Rn m => x i • q.Amat x) (normal m) := by
  apply (q.A_coord_poly i).gaussian_integrable
  exact (((coord i).continuous.stronglyMeasurable).smul q.A_SM).aestronglyMeasurable

lemma avgA_sym : q.avgA.IsHermitian := hermitian_integral q.A_integrable
  (ae_of_all _ fun _z => q.H_hermitian poly_id_der _)

lemma M_sym (i) : (q.M i).IsHermitian :=
  hermitian_integral (q.A_coord_int i) (ae_of_all _ fun z => (q.H_hermitian poly_id_der _).smul (by simp [IsSelfAdjoint]))

omit [NeZero m] in
lemma L_linear : ∃ l : Rn m →L[ℝ] Mat m, (l : Rn m → Mat m) = q.Lmat := by
  classical
  use ∑ i, (coord i).smulRight (q.M i)
  ext x; simp [Lmat]

omit [NeZero m] in
lemma L_poly : PolyBound q.Lmat := by
  obtain ⟨l,hl⟩ := q.L_linear; rw [← hl]; exact PolyBound.clm _

omit [NeZero m] in
lemma L_cont : Continuous q.Lmat := by
  obtain ⟨l,hl⟩ := q.L_linear; rw [← hl]; exact l.continuous

lemma L_sym (x) : (q.Lmat x).IsHermitian :=
  by
    unfold Matrix.IsHermitian Lmat
    rw [conjTranspose_sum]; exact Finset.sum_congr rfl fun i _ => (q.M_sym i).smul (by simp [IsSelfAdjoint])

end ProjField
end GeneralMahler

end

end OAI
