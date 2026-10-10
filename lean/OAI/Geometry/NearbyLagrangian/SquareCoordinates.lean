import Mathlib
import OAI.Geometry.NearbyLagrangian.FiberHomotopy
import OAI.Geometry.NearbyLagrangian.PositiveSquares

namespace OAI

/-! Split sphere coordinates and equivalences for added quadratic variables. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialTopology
open Set
open scoped Topology
variable {B W U : Type*} [TopologicalSpace B]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def splitDomainHomeomorph (e : U ≃L[ℝ] W × ℝ)
    (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2)
    (P : B → W → ℝ → Prop) :
    {p : B × U // ‖p.2‖ = 1 ∧ P p.1 (e p.2).1 (e p.2).2} ≃ₜ
      {p : SplitSphere B W // P p.val.1 p.val.2.1 p.val.2.2} where
  toFun p := ⟨⟨(p.val.1,e p.val.2),by rw [← he,p.property.1]; norm_num⟩,p.property.2⟩
  invFun p := ⟨(p.val.val.1,e.symm p.val.val.2),by
    constructor
    · have h := he (e.symm p.val.val.2)
      rw [e.apply_symm_apply,p.val.property] at h
      nlinarith [norm_nonneg (e.symm p.val.val.2)]
    · simpa only [e.apply_symm_apply] using p.property⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; apply Subtype.ext; simp
  continuous_toFun := by
    exact ((continuous_fst.comp continuous_subtype_val).prodMk
      (e.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _ |>.subtype_mk _
  continuous_invFun := by
    have h : Continuous (fun p : {p : SplitSphere B W // P p.val.1 p.val.2.1 p.val.2.2} => p.val.val) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (h.fst.prodMk (e.symm.continuous.comp h.snd)).subtype_mk _

def fullSphere (B W : Type*) [NormedAddCommGroup W] : SphereFamily B W where
  carrier := {p | ‖p.2‖ = 1}
  unit _ h := h

omit [TopologicalSpace B] [NormedSpace ℝ W] in
lemma mem_sphere_of_norm_one {w : W} (h : ‖w‖ = 1) : w ∈ Metric.sphere (0:W) 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using h

omit [TopologicalSpace B] [NormedSpace ℝ W] in
lemma norm_one_of_mem_sphere (w : Metric.sphere (0:W) 1) : ‖w.val‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using w.property

def fullSphereHomeomorph : (fullSphere B W).Total ≃ₜ B × Metric.sphere (0:W) 1 where
  toFun p := (p.val.1,⟨p.val.2,mem_sphere_of_norm_one p.property⟩)
  invFun p := ⟨(p.1,p.2.val),norm_one_of_mem_sphere p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

omit [TopologicalSpace B] in
lemma norm_one_of_split (e : U ≃L[ℝ] W × ℝ)
    (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2)
    (w : W × ℝ) (hw : ‖w.1‖^2+‖w.2‖^2 = 1) : ‖e.symm w‖ = 1 := by
  have h := he (e.symm w)
  rw [e.apply_symm_apply] at h
  simp only [Real.norm_eq_abs,sq_abs] at hw
  nlinarith [norm_nonneg (e.symm w)]

omit [TopologicalSpace B] in
lemma full_suspension_condition (e : U ≃L[ℝ] W × ℝ)
    (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2)
    (p : (fullSphere B U).Total) :
    ((e p.val.2).1 = 0 ∨ (p.val.1,NormedSpace.normalize (e p.val.2).1) ∈
      (fullSphere B W).carrier) ∧ ‖(e p.val.2).1‖^2 + ‖(e p.val.2).2‖^2 = 1 := by
  constructor
  · by_cases h : (e p.val.2).1 = 0
    · exact Or.inl h
    · exact Or.inr (NormedSpace.norm_normalize_eq_one_iff.mpr h)
  · simp only [Real.norm_eq_abs,sq_abs]
    rw [← he,(show ‖p.val.2‖ = 1 from p.property)]; norm_num

def suspensionFullSphereHomeomorph (e : U ≃L[ℝ] W × ℝ)
    (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2) :
    (fullSphere B W).Suspension ℝ ≃ₜ (fullSphere B U).Total where
  toFun p := ⟨(p.val.1,e.symm p.val.2),norm_one_of_split e he p.val.2 p.property.2⟩
  invFun p := ⟨(p.val.1,e p.val.2),full_suspension_condition e he p⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp
  continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    (e.symm.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := ((continuous_fst.comp continuous_subtype_val).prodMk
    (e.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

def negativeSquareCoordinateHomeomorph (e : U ≃L[ℝ] W × ℝ)
    (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2) (f : B → W → ℝ) :
    (negativeSphere (fun b u => f b (e u).1 - (e u).2^2)).Total ≃ₜ NegativeSplit f :=
  (Homeomorph.setCongr (by
    ext p
    change (‖p.2‖ = 1 ∧ f p.1 (e p.2).1 - (e p.2).2^2 ≤ 0) ↔
      (‖p.2‖ = 1 ∧ f p.1 (e p.2).1 ≤ (e p.2).2^2)
    rw [sub_nonpos])).trans (splitDomainHomeomorph e he (fun b w z => f b w ≤ z^2))

def positiveSquareCoordinateHomeomorph (e : U ≃L[ℝ] W × ℝ)
    (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2) (f : B → W → ℝ) :
    (negativeSphere (fun b u => f b (e u).1 + (e u).2^2)).Total ≃ₜ PositiveSplit f :=
  splitDomainHomeomorph e he (fun b w z => f b w + z^2 ≤ 0)

end NearbyLagrangian.RadialTopology

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set
open scoped Topology Manifold ContDiff
open RadialTopology
variable {W U : Type*}
  [NormedAddCommGroup W] [NormedSpace ℝ W] [ProperSpace W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def squareExtend (q : RegularHomogeneous ℝ) (e : U ≃L[ℝ] W × ℝ) :
    C(RegularHomogeneous W,RegularHomogeneous U) :=
  ⟨fun f => (f.directSum q).pullback e,
    (continuous_pullback e).comp (continuous_directSum.comp
      (continuous_id.prodMk continuous_const))⟩

@[simp] lemma squareExtend_negative_apply (e : U ≃L[ℝ] W × ℝ)
    (f : RegularHomogeneous W) (u : U) :
    squareExtend (positiveSquare (W:=ℝ)).neg e f u = f (e u).1 - (e u).2^2 := by
  change f (e u).1 + -‖(e u).2‖^2 = _
  simp only [Real.norm_eq_abs,sq_abs,sub_eq_add_neg]

@[simp] lemma squareExtend_positive_apply (e : U ≃L[ℝ] W × ℝ)
    (f : RegularHomogeneous W) (u : U) :
    squareExtend (positiveSquare (W:=ℝ)) e f u = f (e u).1 + (e u).2^2 := by
  change f (e u).1 + ‖(e u).2‖^2 = _
  simp only [Real.norm_eq_abs,sq_abs]

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.RadialTopology
open Set
open scoped Topology
variable {B W U : Type*} [TopologicalSpace B]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

def positiveSquareCoordinatesEquiv {f : B → W → ℝ}
    (hhom : ∀ b r, 0 ≤ r → ∀ w, f b (r • w) = r^2*f b w)
    (e : U ≃L[ℝ] W × ℝ) (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2) :
    Tubes.FiberwiseHomotopyEquiv (negativeSphere f).projection
      (negativeSphere (fun b u => f b (e u).1 + (e u).2^2)).projection :=
  ((positiveSquareEquiv hhom).symm.precomposeHomeomorph
    (positiveSquareCoordinateHomeomorph e he f) (fun _ => rfl)).symm

def suspendTrivialization {A : SphereFamily B W} {W' U' : Type*}
    [NormedAddCommGroup W'] [NormedSpace ℝ W']
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (h : Tubes.FiberwiseHomotopyEquiv A.projection (fullSphere B W').projection)
    (e : U' ≃L[ℝ] W' × ℝ) (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2) :
    Tubes.FiberwiseHomotopyEquiv (A.suspensionProjection (Z:=ℝ))
      (fullSphere B U').projection :=
  ((SphereFamily.suspendFiberwise (Z:=ℝ) h).symm.precomposeHomeomorph
    (suspensionFullSphereHomeomorph e he).symm (fun _ => rfl)).symm

end NearbyLagrangian.RadialTopology

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set
open scoped Topology Manifold ContDiff
open RadialTopology
variable {B V W U : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace B] [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]
  [CompactSpace B] [T2Space B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [Nontrivial W]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Nontrivial U]

omit [FiniteDimensional ℝ V] [T2Space B] [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B] in
lemma exists_uniform_sphere_gradient_lower (f : C(B,RegularHomogeneous W)) :
    ∃ c : ℝ, 0 < c ∧ ∀ b w, ‖w‖ = 1 → c ≤ ‖gradient (f b) w‖ := by
  cases isEmpty_or_nonempty B with
  | inl h => exact ⟨1,by norm_num,fun b => isEmptyElim b⟩
  | inr h =>
    obtain ⟨c,C,hc,_,hb⟩ := uniform_gradient_bounds f.continuous
    exact ⟨c,hc,fun b w hw => by simpa only [hw,mul_one] using (hb b w).1⟩

include V in

theorem negativeSquare_equiv (f : C(B,RegularHomogeneous W))
    (e : U ≃L[ℝ] W × ℝ) (he : ∀ u, ‖u‖^2 = ‖(e u).1‖^2 + (e u).2^2) :
    Nonempty (FiberwiseHomotopyEquiv
      ((negativeSphere (fun b w => f b w)).suspensionProjection (Z:=ℝ))
      (negativeSphere (fun b u => f b (e u).1 - (e u).2^2)).projection) := by
  obtain ⟨g,hfg,hgs,hN⟩ := exists_smooth_negative_equiv (V:=V) f
  obtain ⟨hN⟩ := hN
  change FiberwiseHomotopyEquiv (negativeSphere (fun b w => f b w)).projection
    (negativeSphere (fun b w => g b w)).projection at hN
  let F := squareExtend (positiveSquare (W:=ℝ)).neg e
  have hhom : (F.comp f).Homotopic (F.comp g) := (ContinuousMap.Homotopic.refl F).comp hfg
  have hM₀ := negative_equiv_of_homotopic (V:=V) (F.comp f) (F.comp g) hhom
  have hM : Nonempty (FiberwiseHomotopyEquiv
      (negativeSphere (fun b u => f b (e u).1 - (e u).2^2)).projection
      (negativeSphere (fun b u => g b (e u).1 - (e u).2^2)).projection) := by
    change Nonempty (FiberwiseHomotopyEquiv
      (negativeInProjection {u : U | ‖u‖=1} (fun p : B × U => f p.1 (e p.2).1-(e p.2).2^2))
      (negativeInProjection {u : U | ‖u‖=1} (fun p : B × U => g p.1 (e p.2).1-(e p.2).2^2)))
    have h₀ : (fun p : B × U => (F.comp f) p.1 p.2) =
        (fun p : B × U => f p.1 (e p.2).1-(e p.2).2^2) :=
      funext (fun p => squareExtend_negative_apply e (f p.1) p.2)
    have h₁ : (fun p : B × U => (F.comp g) p.1 p.2) =
        (fun p : B × U => g p.1 (e p.2).1-(e p.2).2^2) :=
      funext (fun p => squareExtend_negative_apply e (g p.1) p.2)
    rw [h₀,h₁] at hM₀
    exact hM₀
  obtain ⟨hM⟩ := hM
  obtain ⟨c,hc,hgrad⟩ := exists_uniform_sphere_gradient_lower g
  obtain ⟨hS⟩ := smooth_negativeSuspension_equiv hgs hc hgrad
  let hS' := (hS.symm.precomposeHomeomorph
    (p:=(negativeSphere (fun b u => g b (e u).1-(e u).2^2)).projection)
    (negativeSquareCoordinateHomeomorph e he (fun b w => g b w)) (fun _ => rfl)).symm
  exact ⟨((SphereFamily.suspendFiberwise hN).trans hS').trans hM.symm⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
