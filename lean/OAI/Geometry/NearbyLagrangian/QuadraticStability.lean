import Mathlib
import OAI.Geometry.NearbyLagrangian.BalancedStability
import OAI.Geometry.NearbyLagrangian.SquareCoordinates

namespace OAI

/-! Positive and negative square stabilization of trivial negative fibrations. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes
open scoped Topology

def scalarCoordinate : Euclidean 1 ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ))

@[simp] lemma scalarCoordinate_apply (w : Euclidean 1) : scalarCoordinate w = w 0 := rfl

lemma scalarCoordinate_norm_sq (w : Euclidean 1) : ‖w‖^2 = (scalarCoordinate w)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp

lemma sumCoordinates_norm_sq (k l r s : ℕ) (w : Euclidean ((k+r)+(l+s))) :
    ‖w‖^2 = ‖(sumCoordinates k l r s w).1‖^2 + ‖(sumCoordinates k l r s w).2‖^2 := by
  let uv := EuclideanSpace.finAddEquivProd (n:=k+r) (m:=l+s) w
  let x := EuclideanSpace.finAddEquivProd (n:=k) (m:=r) uv.1
  let y := EuclideanSpace.finAddEquivProd (n:=l) (m:=s) uv.2
  have hc : sumCoordinates k l r s w =
      ((EuclideanSpace.finAddEquivProd (n:=k) (m:=l)).symm (x.1,y.1),
       (EuclideanSpace.finAddEquivProd (n:=r) (m:=s)).symm (x.2,y.2)) := rfl
  have h0 : ‖w‖^2 = ‖uv.1‖^2 + ‖uv.2‖^2 := norm_sq_split w
  have hx : ‖uv.1‖^2 = ‖x.1‖^2+‖x.2‖^2 := norm_sq_split uv.1
  have hy : ‖uv.2‖^2 = ‖y.1‖^2+‖y.2‖^2 := norm_sq_split uv.2
  rw [hc]
  rw [norm_sq_split ((EuclideanSpace.finAddEquivProd (n:=k) (m:=l)).symm (x.1,y.1)),
    norm_sq_split ((EuclideanSpace.finAddEquivProd (n:=r) (m:=s)).symm (x.2,y.2))]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  linarith

def negativeSquareCoordinates (k l : ℕ) : Euclidean ((k+1)+l) ≃L[ℝ] Euclidean (k+l) × ℝ :=
  (sumCoordinates k l 1 0).trans ((ContinuousLinearEquiv.refl ℝ _).prodCongr scalarCoordinate)

def positiveSquareCoordinates (k l : ℕ) : Euclidean (k+(l+1)) ≃L[ℝ] Euclidean (k+l) × ℝ :=
  (sumCoordinates k l 0 1).trans ((ContinuousLinearEquiv.refl ℝ _).prodCongr scalarCoordinate)

lemma negativeSquareCoordinates_norm_sq (k l : ℕ) (w : Euclidean ((k+1)+l)) :
    ‖w‖^2 = ‖(negativeSquareCoordinates k l w).1‖^2+(negativeSquareCoordinates k l w).2^2 := by
  change ‖w‖^2 = ‖(sumCoordinates k l 1 0 w).1‖^2 + (scalarCoordinate (sumCoordinates k l 1 0 w).2)^2
  rw [← scalarCoordinate_norm_sq]
  exact sumCoordinates_norm_sq k l 1 0 w

lemma positiveSquareCoordinates_norm_sq (k l : ℕ) (w : Euclidean (k+(l+1))) :
    ‖w‖^2 = ‖(positiveSquareCoordinates k l w).1‖^2+(positiveSquareCoordinates k l w).2^2 := by
  change ‖w‖^2 = ‖(sumCoordinates k l 0 1 w).1‖^2 + (scalarCoordinate (sumCoordinates k l 0 1 w).2)^2
  rw [← scalarCoordinate_norm_sq]
  exact sumCoordinates_norm_sq k l 0 1 w

lemma standardForm_one_zero (w : Euclidean (1+0)) :
    standardForm 1 0 w = -(scalarCoordinate w)^2 := by
  rw [standardForm_apply]
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one,Fin.sum_univ_zero,add_zero,
    scalarCoordinate_apply]
  rfl

lemma standardForm_zero_one (w : Euclidean (0+1)) :
    standardForm 0 1 w = (scalarCoordinate w)^2 := by
  rw [standardForm_apply]
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one,Fin.sum_univ_zero,neg_zero,zero_add,
    scalarCoordinate_apply]
  rfl

def addNegativeOne (k l : ℕ) : C(Tube k l,Tube (k+1) l) :=
  (tubeSum k l 1 0).comp ⟨fun f => (f,standardTube 1 0),continuous_id.prodMk continuous_const⟩

def addPositiveOne (k l : ℕ) : C(Tube k l,Tube k (l+1)) :=
  (tubeSum k l 0 1).comp ⟨fun f => (f,standardTube 0 1),continuous_id.prodMk continuous_const⟩

@[simp] lemma addNegativeOne_apply (k l : ℕ) (f : Tube k l) (w : Euclidean ((k+1)+l)) :
    (addNegativeOne k l f).val w = f.val (negativeSquareCoordinates k l w).1 -
      (negativeSquareCoordinates k l w).2^2 := by
  change f.val (sumCoordinates k l 1 0 w).1 + standardForm 1 0 (sumCoordinates k l 1 0 w).2 = _
  rw [standardForm_one_zero]
  rfl

@[simp] lemma addPositiveOne_apply (k l : ℕ) (f : Tube k l) (w : Euclidean (k+(l+1))) :
    (addPositiveOne k l f).val w = f.val (positiveSquareCoordinates k l w).1 +
      (positiveSquareCoordinates k l w).2^2 := by
  change f.val (sumCoordinates k l 0 1 w).1 + standardForm 0 1 (sumCoordinates k l 0 1 w).2 = _
  rw [standardForm_zero_one]
  rfl

lemma squareComposition_old (k l : ℕ) (w : Euclidean ((k+1)+(l+1))) :
    (sumCoordinates k l 1 0 (sumCoordinates (k+1) l 0 1 w).1).1 =
      (sumCoordinates k l 1 1 w).1 := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [sumCoordinates_fst_neg]
    change (sumCoordinates (k+1) l 0 1 w).1 ((j.castAdd 1).castAdd l) = _
    rw [sumCoordinates_fst_neg]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp
  · simp only [sumCoordinates_fst_pos]
    apply congrArg (fun i => w i)
    apply Fin.ext
    simp

lemma squareComposition_negative (k l : ℕ) (w : Euclidean ((k+1)+(l+1))) :
    scalarCoordinate (sumCoordinates k l 1 0 (sumCoordinates (k+1) l 0 1 w).1).2 =
      (sumCoordinates k l 1 1 w).2 0 := by
  change (sumCoordinates k l 1 0 (sumCoordinates (k+1) l 0 1 w).1).2 ((0:Fin 1).castAdd 0) =
    (sumCoordinates k l 1 1 w).2 ((0:Fin 1).castAdd 1)
  simp only [sumCoordinates_snd_neg]
  change (sumCoordinates (k+1) l 0 1 w).1 (((0:Fin 1).natAdd k).castAdd l) = _
  rw [sumCoordinates_fst_neg]
  apply congrArg (fun i => w i)
  apply Fin.ext
  simp

lemma squareComposition_positive (k l : ℕ) (w : Euclidean ((k+1)+(l+1))) :
    scalarCoordinate (sumCoordinates (k+1) l 0 1 w).2 =
      (sumCoordinates k l 1 1 w).2 1 := by
  change (sumCoordinates (k+1) l 0 1 w).2 ((0:Fin 1).natAdd 0) =
    (sumCoordinates k l 1 1 w).2 ((0:Fin 1).natAdd 1)
  simp only [sumCoordinates_snd_pos]

lemma standardForm_one_one (w : Euclidean (1+1)) :
    standardForm 1 1 w = -(w 0)^2+(w 1)^2 := by
  rw [standardForm_apply]
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_one]
  rfl

lemma addPositiveNegative_eq_stabilize (m : ℕ) :
    (addPositiveOne (m+1) m).comp (addNegativeOne m m) = stabilize m := by
  apply ContinuousMap.ext
  intro f
  apply Subtype.ext
  apply RegularHomogeneous.ext
  intro w
  change (addPositiveOne (m+1) m (addNegativeOne m m f)).val w = _
  rw [addPositiveOne_apply,addNegativeOne_apply]
  change f.val (sumCoordinates m m 1 0 (sumCoordinates (m+1) m 0 1 w).1).1 -
      (scalarCoordinate (sumCoordinates m m 1 0 (sumCoordinates (m+1) m 0 1 w).1).2)^2 +
      (scalarCoordinate (sumCoordinates (m+1) m 0 1 w).2)^2 =
    f.val (sumCoordinates m m 1 1 w).1 + standardForm 1 1 (sumCoordinates m m 1 1 w).2
  rw [squareComposition_old,squareComposition_negative,squareComposition_positive,standardForm_one_one]
  ring

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes
open Set
open scoped Topology Manifold ContDiff
open RadialTopology
variable {B : Type*} [TopologicalSpace B]

theorem negativeTrivial_iff_sphere {k l : ℕ} (a : C(B,Tube k l)) :
    NegativeTrivial a ↔ Nonempty (FiberwiseHomotopyEquiv
      (negativeSphere (fun b w => (a b).val w)).projection
      (fullSphere B (Euclidean k)).projection) := by
  constructor
  · rintro ⟨h⟩
    let h₀ := h.precomposeHomeomorph
      (p:=(negativeSphere (fun b w => (a b).val w)).projection)
      (negativeTotalInHomeomorph a).symm (fun _ => rfl)
    exact ⟨(h₀.symm.precomposeHomeomorph
      (p:=(fullSphere B (Euclidean k)).projection)
      fullSphereHomeomorph (fun _ => rfl)).symm⟩
  · rintro ⟨h⟩
    let h₀ := h.precomposeHomeomorph (p:=negativeProjection a)
      (negativeTotalInHomeomorph a) (fun _ => rfl)
    exact ⟨(h₀.symm.precomposeHomeomorph
      (p:=(⟨Prod.fst,continuous_fst⟩ : C(B × Metric.sphere (0:Euclidean k) 1,B)))
      fullSphereHomeomorph.symm (fun _ => rfl)).symm⟩

theorem NegativeTrivial.addPositiveOne {k l : ℕ} {a : C(B,Tube k l)}
    (h : NegativeTrivial a) : NegativeTrivial ((NearbyLagrangian.Tubes.addPositiveOne k l).comp a) := by
  obtain ⟨h⟩ := (negativeTrivial_iff_sphere a).mp h
  let hE := positiveSquareCoordinatesEquiv
    (fun b r hr w => (a b).val.homogeneity_nonneg hr w)
    (positiveSquareCoordinates k l) (positiveSquareCoordinates_norm_sq k l)
  have hg : (fun b w => (((NearbyLagrangian.Tubes.addPositiveOne k l).comp a) b).val w) =
      (fun b w => (a b).val (positiveSquareCoordinates k l w).1+
        (positiveSquareCoordinates k l w).2^2) := by
    funext b w
    exact addPositiveOne_apply k l (a b) w
  apply (negativeTrivial_iff_sphere _).mpr
  rw [hg]
  exact ⟨hE.symm.trans h⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B] [CompactSpace B] [T2Space B]

include V in

theorem NegativeTrivial.addNegativeOne {k l : ℕ} (hdim : 0 < k+l) {a : C(B,Tube k l)}
    (h : NegativeTrivial a) : NegativeTrivial ((NearbyLagrangian.Tubes.addNegativeOne k l).comp a) := by
  let : NeZero (k+l) := ⟨by omega⟩
  let : NeZero ((k+1)+l) := ⟨by omega⟩
  obtain ⟨h⟩ := (negativeTrivial_iff_sphere a).mp h
  let f : C(B,RegularHomogeneous (Euclidean (k+l))) :=
    ⟨fun b => (a b).val,continuous_subtype_val.comp a.continuous⟩
  obtain ⟨hE⟩ := RegularHomogeneous.negativeSquare_equiv (V:=V) f
    (negativeSquareCoordinates k l) (negativeSquareCoordinates_norm_sq k l)
  let hS := suspendTrivialization h (positiveSquareCoordinates k 0)
    (positiveSquareCoordinates_norm_sq k 0)
  have hg : (fun b w => (((NearbyLagrangian.Tubes.addNegativeOne k l).comp a) b).val w) =
      (fun b w => (a b).val (negativeSquareCoordinates k l w).1-
        (negativeSquareCoordinates k l w).2^2) := by
    funext b w
    exact addNegativeOne_apply k l (a b) w
  apply (negativeTrivial_iff_sphere _).mpr
  rw [hg]
  exact ⟨hE.symm.trans hS⟩

include V in

theorem NegativeTrivial.stabilize {m : ℕ} (hm : 0 < m) {a : C(B,Tube m m)}
    (h : NegativeTrivial a) : NegativeTrivial ((stabilize m).comp a) := by
  rw [← addPositiveNegative_eq_stabilize]
  exact (h.addNegativeOne (V:=V) (by omega : 0 < m+m)).addPositiveOne

include V in

theorem NegativeTrivial.stabilizeFor {m : ℕ} (hm : 0 < m) {a : C(B,Tube m m)}
    (h : NegativeTrivial a) (r : ℕ) : NegativeTrivial ((stabilizeFor m r).comp a) := by
  induction r with
  | zero => exact h
  | succ r ih =>
    exact ih.stabilize (V:=V) (by omega : 0 < m+r)

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes
open ContinuousMap
open scoped Manifold ContDiff
variable {B V : Type*} [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B] [T2Space B] [CompactSpace B]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B] [T2Space B] [CompactSpace B] in
lemma negativeTrivial_tubeCast_iff {m n : ℕ} (h : m = n) (a : C(B,Tube m m)) :
    NegativeTrivial ((tubeCast h).comp a) ↔ NegativeTrivial a := by
  subst n
  rfl

include V in

theorem StableNegativeTrivial.stabilize {m : ℕ} (hm : 0 < m) {a : C(B,Tube m m)}
    (ha : StableNegativeTrivial a) (r : ℕ) :
    StableNegativeTrivial ((stabilizeFor m r).comp a) := by
  obtain ⟨s,hs⟩ := ha
  have hsr := hs.stabilizeFor (V:=V) (by omega : 0 < m+s) r
  have ht := (negativeTrivial_tubeCast_iff (Nat.add_assoc m s r) _).mpr hsr
  have he₁ : (tubeCast (Nat.add_assoc m s r)).comp
      ((stabilizeFor (m+s) r).comp ((stabilizeFor m s).comp a)) =
      (stabilizeFor m (s+r)).comp a := by
    ext b
    exact congrArg (fun f => f (a b)) (stabilizeFor_comp m s r)
  rw [he₁] at ht
  have ht' : NegativeTrivial ((stabilizeFor m (r+s)).comp a) := by
    exact (Nat.add_comm s r) ▸ ht
  refine ⟨s, (negativeTrivial_tubeCast_iff (Nat.add_assoc m r s) _).mp ?_⟩
  have he₂ : (tubeCast (Nat.add_assoc m r s)).comp
      ((stabilizeFor (m+r) s).comp ((stabilizeFor m r).comp a)) =
      (stabilizeFor m (r+s)).comp a := by
    ext b
    exact congrArg (fun f => f (a b)) (stabilizeFor_comp m r s)
  rw [he₂]
  exact ht'

include V in
theorem StableNegativeTrivial.addBalanced {m : ℕ} (hm : 0 < m) {a : C(B,Tube m m)}
    (ha : StableNegativeTrivial a) (d : ℕ) :
    StableNegativeTrivial ((addBalanced m d).comp a) := by
  rw [addBalanced_eq_stabilizeFor]
  exact ha.stabilize (V:=V) hm d

include V in

theorem StableNegativeTrivial.addBalancedFor {m : ℕ} (hm : 0 < m) {a : C(B,Tube m m)}
    (ha : StableNegativeTrivial a) (d n : ℕ) :
    StableNegativeTrivial ((addBalancedFor m d n).comp a) := by
  induction n with
  | zero => exact ha
  | succ n ih => exact ih.addBalanced (V:=V) (lt_of_lt_of_le hm (le_transportIndex m d n)) d

end NearbyLagrangian.Tubes

end

end OAI
