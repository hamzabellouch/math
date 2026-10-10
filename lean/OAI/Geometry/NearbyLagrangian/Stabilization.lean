import Mathlib
import OAI.Geometry.NearbyLagrangian.JetTopology

namespace OAI

/-! Balanced stabilization, negative fibrations and stable tube classes. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

def sumCoordinates (k l r s : ℕ) :
    Euclidean ((k + r) + (l + s)) ≃L[ℝ] Euclidean (k + l) × Euclidean (r + s) :=
  (EuclideanSpace.finAddEquivProd (n := k+r) (m := l+s)).trans
    (((EuclideanSpace.finAddEquivProd (n := k) (m := r)).prodCongr
      (EuclideanSpace.finAddEquivProd (n := l) (m := s))).trans
    ((ContinuousLinearEquiv.prodProdProdComm ℝ (Euclidean k) (Euclidean r)
      (Euclidean l) (Euclidean s)).trans
    ((EuclideanSpace.finAddEquivProd (n := k) (m := l)).symm.prodCongr
      (EuclideanSpace.finAddEquivProd (n := r) (m := s)).symm)))

theorem norm_sq_split {k r : ℕ} (w : Euclidean (k+r)) :
    ‖w‖ ^ 2 = ‖(EuclideanSpace.finAddEquivProd w).1‖ ^ 2 +
      ‖(EuclideanSpace.finAddEquivProd w).2‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_add]
  rfl

@[simp] theorem standardForm_apply (k l : ℕ) (w : Euclidean (k+l)) :
    standardForm k l w = -‖(EuclideanSpace.finAddEquivProd w).1‖ ^ 2 +
      ‖(EuclideanSpace.finAddEquivProd w).2‖ ^ 2 := rfl

theorem standardForm_sum (k l r s : ℕ) :
    ((standardForm k l).directSum (standardForm r s)).pullback
      (sumCoordinates k l r s) = standardForm (k+r) (l+s) := by
  ext w
  change standardForm k l ((sumCoordinates k l r s w).1) +
    standardForm r s ((sumCoordinates k l r s w).2) = _
  let uv := EuclideanSpace.finAddEquivProd (n := k+r) (m := l+s) w
  let x := EuclideanSpace.finAddEquivProd (n := k) (m := r) uv.1
  let y := EuclideanSpace.finAddEquivProd (n := l) (m := s) uv.2
  have hc : sumCoordinates k l r s w =
      ((EuclideanSpace.finAddEquivProd (n := k) (m := l)).symm (x.1, y.1),
       (EuclideanSpace.finAddEquivProd (n := r) (m := s)).symm (x.2, y.2)) := rfl
  rw [hc]
  simp only [standardForm_apply, ContinuousLinearEquiv.apply_symm_apply]
  change -‖x.1‖ ^ 2 + ‖y.1‖ ^ 2 + (-‖x.2‖ ^ 2 + ‖y.2‖ ^ 2) =
    -‖uv.1‖ ^ 2 + ‖uv.2‖ ^ 2
  have hx : ‖uv.1‖ ^ 2 = ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2 := norm_sq_split uv.1
  have hy : ‖uv.2‖ ^ 2 = ‖y.1‖ ^ 2 + ‖y.2‖ ^ 2 := norm_sq_split uv.2
  linarith

def tubeSum (k l r s : ℕ) : C(Tube k l × Tube r s, Tube (k+r) (l+s)) where
  toFun p := ⟨(p.1.val.directSum p.2.val).pullback (sumCoordinates k l r s), by
    rw [mem_pathComponent_iff]
    have h := ((mem_pathComponent_iff.mp p.1.property).prod
      (mem_pathComponent_iff.mp p.2.property)).map
      ((RegularHomogeneous.continuous_pullback (sumCoordinates k l r s)).comp
        RegularHomogeneous.continuous_directSum)
    change Joined (((standardForm k l).directSum (standardForm r s)).pullback
      (sumCoordinates k l r s)) _ at h
    rw [standardForm_sum] at h
    exact h⟩
  continuous_toFun := (((RegularHomogeneous.continuous_pullback
      (sumCoordinates k l r s)).comp RegularHomogeneous.continuous_directSum).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

def stabilize (m : ℕ) : C(Tube m m, Tube (m+1) (m+1)) :=
  (tubeSum m m 1 1).comp
    ⟨fun f => (f, standardTube 1 1), continuous_id.prodMk continuous_const⟩

@[simp] theorem stabilize_standard (m : ℕ) :
    stabilize m (standardTube m m) = standardTube (m+1) (m+1) := by
  apply Subtype.ext
  exact standardForm_sum m m 1 1

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes

def stabilizeFor (m : ℕ) : (r : ℕ) → C(Tube m m, Tube (m+r) (m+r))
  | 0 => ContinuousMap.id _
  | r+1 => (stabilize (m+r)).comp (stabilizeFor m r)

@[simp] theorem stabilizeFor_standard (m r : ℕ) :
    stabilizeFor m r (standardTube m m) = standardTube (m+r) (m+r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change stabilize (m+r) (stabilizeFor m r (standardTube m m)) = _
    rw [ih]
    exact stabilize_standard (m+r)

variable {B E F : Type*} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace F]

structure FiberwiseHomotopyEquiv (p : C(E, B)) (q : C(F, B)) where
  toFun : C(E, F)
  invFun : C(F, E)
  toFun_over : ∀ e, q (toFun e) = p e
  invFun_over : ∀ f, p (invFun f) = q f
  left : (invFun.comp toFun).Homotopy (ContinuousMap.id E)
  right : (toFun.comp invFun).Homotopy (ContinuousMap.id F)
  left_over : ∀ t e, p (left (t, e)) = p e
  right_over : ∀ t f, q (right (t, f)) = q f

def NegativeTotal {k l : ℕ} (a : C(B, Tube k l)) :=
  {bu : B × Metric.sphere (0 : Euclidean (k+l)) 1 // (a bu.1).val bu.2 ≤ 0}

instance {k l : ℕ} (a : C(B, Tube k l)) : TopologicalSpace (NegativeTotal a) :=
  inferInstanceAs (TopologicalSpace
    {bu : B × Metric.sphere (0 : Euclidean (k+l)) 1 // (a bu.1).val bu.2 ≤ 0})

def negativeProjection {k l : ℕ} (a : C(B, Tube k l)) : C(NegativeTotal a, B) :=
  ⟨fun bu => bu.val.1, continuous_fst.comp continuous_subtype_val⟩

def NegativeTrivial {k l : ℕ} (a : C(B, Tube k l)) : Prop :=
  Nonempty (FiberwiseHomotopyEquiv (negativeProjection a)
    (⟨Prod.fst, continuous_fst⟩ : C(B × Metric.sphere (0 : Euclidean k) 1, B)))

def StableNegativeTrivial {m : ℕ} (a : C(B, Tube m m)) : Prop :=
  ∃ r : ℕ, NegativeTrivial ((stabilizeFor m r).comp a)

def StablyNonNull {m : ℕ} (a : C(B, Tube m m)) : Prop :=
  ∀ r : ℕ, ¬ ((stabilizeFor m r).comp a).Nullhomotopic

def KernelFamilyGoal : Prop :=
  ∃ m : ℕ, 20 ≤ m ∧
    ∃ a : C(Metric.sphere (0 : Euclidean 10) 1, Tube m m),
      StablyNonNull a ∧ StableNegativeTrivial a

end NearbyLagrangian.Tubes

end

end OAI
