import Mathlib
import OAI.Geometry.NearbyLagrangian.Stabilization

namespace OAI

/-! Negative domains of standard quadratic tubes and their sphere homotopy types. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes

abbrev UnitSphere (k : ℕ) := Metric.sphere (0 : Euclidean k) 1
abbrev UnitBall (l : ℕ) := Metric.closedBall (0 : Euclidean l) 1

def NegativeDomain {k l : ℕ} (f : RegularHomogeneous (Euclidean (k+l))) :=
  {u : UnitSphere (k+l) // f u ≤ 0}

instance {k l : ℕ} (f : RegularHomogeneous (Euclidean (k+l))) :
    TopologicalSpace (NegativeDomain f) := inferInstanceAs
      (TopologicalSpace {u : UnitSphere (k+l) // f u ≤ 0})

@[simp] theorem unitSphere_norm {k : ℕ} (u : UnitSphere k) : ‖(u : Euclidean k)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using u.property

theorem unitSphere_ne_zero {k : ℕ} (u : UnitSphere k) : (u : Euclidean k) ≠ 0 := by
  intro h
  have := unitSphere_norm u
  simp [h] at this

abbrev StandardNegative (k l : ℕ) := NegativeDomain (standardForm k l)

def negativeCoordinates (k l : ℕ) : C(StandardNegative k l, Euclidean k × Euclidean l) :=
  ⟨fun w => EuclideanSpace.finAddEquivProd (w.val : Euclidean (k+l)),
    (EuclideanSpace.finAddEquivProd (n := k) (m := l)).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)⟩

theorem negative_second_le_first {k l : ℕ} (w : StandardNegative k l) :
    ‖(negativeCoordinates k l w).2‖ ≤ ‖(negativeCoordinates k l w).1‖ := by
  have h := w.property
  change standardForm k l (w.val : Euclidean (k+l)) ≤ 0 at h
  rw [standardForm_apply] at h
  change -‖(negativeCoordinates k l w).1‖ ^ 2 +
    ‖(negativeCoordinates k l w).2‖ ^ 2 ≤ 0 at h
  nlinarith [norm_nonneg (negativeCoordinates k l w).1,
    norm_nonneg (negativeCoordinates k l w).2]

theorem negative_first_ne_zero {k l : ℕ} (w : StandardNegative k l) :
    (negativeCoordinates k l w).1 ≠ 0 := by
  intro hx
  have hy := negative_second_le_first w
  rw [hx, norm_zero] at hy
  have hy0 : (negativeCoordinates k l w).2 = 0 := norm_le_zero_iff.mp hy
  have h0 : negativeCoordinates k l w = 0 := Prod.ext hx hy0
  have he := (EuclideanSpace.finAddEquivProd (n := k) (m := l)).injective
    (show EuclideanSpace.finAddEquivProd (w.val : Euclidean (k+l)) =
      EuclideanSpace.finAddEquivProd (0 : Euclidean (k+l)) from by
        simpa only [map_zero, negativeCoordinates, ContinuousMap.coe_mk] using h0)
  exact unitSphere_ne_zero w.val he

def standardNegativeToProduct (k l : ℕ) : C(StandardNegative k l, UnitSphere k × UnitBall l) where
  toFun w :=
    (⟨NormedSpace.normalize (negativeCoordinates k l w).1, by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (negative_first_ne_zero w)⟩,
     ⟨‖(negativeCoordinates k l w).1‖⁻¹ • (negativeCoordinates k l w).2, by
      simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_norm]
      rw [mul_comm, ← div_eq_mul_inv]
      exact (div_le_one (norm_pos_iff.mpr (negative_first_ne_zero w))).mpr
        (negative_second_le_first w)⟩)
  continuous_toFun := by
    have hx := continuous_fst.comp (negativeCoordinates k l).continuous
    have hy := continuous_snd.comp (negativeCoordinates k l).continuous
    have hi := hx.norm.inv₀ (fun w => norm_ne_zero_iff.mpr (negative_first_ne_zero w))
    exact ((hi.smul hx).subtype_mk _).prodMk ((hi.smul hy).subtype_mk _)

def standardNegativeRaw (k l : ℕ) : C(UnitSphere k × UnitBall l, Euclidean (k+l)) :=
  ⟨fun p => (EuclideanSpace.finAddEquivProd (n := k) (m := l)).symm (p.1, p.2),
    (EuclideanSpace.finAddEquivProd (n := k) (m := l)).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))⟩

theorem standardNegativeRaw_ne_zero {k l : ℕ} (p : UnitSphere k × UnitBall l) :
    standardNegativeRaw k l p ≠ 0 := by
  intro h
  have he := congrArg (fun w : Euclidean (k+l) => (EuclideanSpace.finAddEquivProd w).1) h
  exact unitSphere_ne_zero p.1 (by simpa [standardNegativeRaw] using he)

def productToStandardNegative (k l : ℕ) : C(UnitSphere k × UnitBall l, StandardNegative k l) where
  toFun p := ⟨⟨NormedSpace.normalize (standardNegativeRaw k l p), by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        NormedSpace.norm_normalize (standardNegativeRaw_ne_zero p)⟩, by
    change standardForm k l (‖standardNegativeRaw k l p‖⁻¹ • standardNegativeRaw k l p) ≤ 0
    rw [(standardForm k l).homogeneity _
      (inv_pos.mpr (norm_pos_iff.mpr (standardNegativeRaw_ne_zero p)))]
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    simp only [standardForm_apply, standardNegativeRaw, ContinuousMap.coe_mk,
      ContinuousLinearEquiv.apply_symm_apply, unitSphere_norm]
    have hz : ‖(p.2 : Euclidean l)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using p.2.property
    nlinarith [norm_nonneg (p.2 : Euclidean l)]⟩
  continuous_toFun := by
    have hn := (standardNegativeRaw k l).continuous.norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (standardNegativeRaw_ne_zero p))
    exact (((hn.smul (standardNegativeRaw k l).continuous).subtype_mk _).subtype_mk _)

@[simp] theorem negativeCoordinates_productToStandardNegative {k l : ℕ}
    (p : UnitSphere k × UnitBall l) :
    negativeCoordinates k l (productToStandardNegative k l p) =
      ‖standardNegativeRaw k l p‖⁻¹ • ((p.1 : Euclidean k), (p.2 : Euclidean l)) := by
  change EuclideanSpace.finAddEquivProd
    (‖standardNegativeRaw k l p‖⁻¹ • standardNegativeRaw k l p) = _
  rw [map_smul]
  congr 1
  exact (EuclideanSpace.finAddEquivProd (n := k) (m := l)).apply_symm_apply _

@[simp] theorem standardNegativeToProduct_productToStandardNegative {k l : ℕ}
    (p : UnitSphere k × UnitBall l) :
    standardNegativeToProduct k l (productToStandardNegative k l p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    change NormedSpace.normalize (negativeCoordinates k l
      (productToStandardNegative k l p)).1 = _
    rw [negativeCoordinates_productToStandardNegative]
    change NormedSpace.normalize (‖standardNegativeRaw k l p‖⁻¹ • (p.1 : Euclidean k)) = _
    rw [NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr (norm_pos_iff.mpr (standardNegativeRaw_ne_zero p)))]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one (unitSphere_norm p.1)
  · apply Subtype.ext
    change ‖(negativeCoordinates k l (productToStandardNegative k l p)).1‖⁻¹ •
      (negativeCoordinates k l (productToStandardNegative k l p)).2 = _
    rw [negativeCoordinates_productToStandardNegative]
    change ‖‖standardNegativeRaw k l p‖⁻¹ • (p.1 : Euclidean k)‖⁻¹ •
      (‖standardNegativeRaw k l p‖⁻¹ • (p.2 : Euclidean l)) = _
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, unitSphere_norm, mul_one,
      inv_inv, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (standardNegativeRaw_ne_zero p)),
      one_smul]

@[simp] theorem productToStandardNegative_standardNegativeToProduct {k l : ℕ}
    (w : StandardNegative k l) :
    productToStandardNegative k l (standardNegativeToProduct k l w) = w := by
  apply Subtype.ext
  apply Subtype.ext
  change NormedSpace.normalize (standardNegativeRaw k l (standardNegativeToProduct k l w)) = _
  have he : standardNegativeRaw k l (standardNegativeToProduct k l w) =
      ‖(negativeCoordinates k l w).1‖⁻¹ • (w.val : Euclidean (k+l)) := by
    apply (EuclideanSpace.finAddEquivProd (n := k) (m := l)).injective
    change EuclideanSpace.finAddEquivProd
      ((EuclideanSpace.finAddEquivProd (n := k) (m := l)).symm
        (‖(negativeCoordinates k l w).1‖⁻¹ • (negativeCoordinates k l w).1,
         ‖(negativeCoordinates k l w).1‖⁻¹ • (negativeCoordinates k l w).2)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, map_smul]
    rfl
  rw [he, NormedSpace.normalize_smul_of_pos
    (inv_pos.mpr (norm_pos_iff.mpr (negative_first_ne_zero w)))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (unitSphere_norm w.val)

def standardNegativeHomeomorph (k l : ℕ) : StandardNegative k l ≃ₜ UnitSphere k × UnitBall l where
  toFun := standardNegativeToProduct k l
  invFun := productToStandardNegative k l
  left_inv := productToStandardNegative_standardNegativeToProduct
  right_inv := standardNegativeToProduct_productToStandardNegative
  continuous_toFun := (standardNegativeToProduct k l).continuous
  continuous_invFun := (productToStandardNegative k l).continuous

def unitBallContract (l : ℕ) : C(unitInterval × UnitBall l, UnitBall l) where
  toFun tz := ⟨(tz.1 : ℝ) • (tz.2 : Euclidean l), by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg tz.1.property.1]
    have hz : ‖(tz.2 : Euclidean l)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using tz.2.property
    exact (mul_le_mul_of_nonneg_right tz.1.property.2 (norm_nonneg _)).trans
      (by simpa using hz)⟩
  continuous_toFun := ((continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

def standardNegativeSphereEquiv (k l : ℕ) :
    ContinuousMap.HomotopyEquiv (StandardNegative k l) (UnitSphere k) :=
  (standardNegativeHomeomorph k l).toHomotopyEquiv.trans {
    toFun := ⟨Prod.fst, continuous_fst⟩
    invFun := ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩
    left_inv := ⟨{
      toFun := fun tp => (tp.2.1, unitBallContract l (tp.1, tp.2.2))
      continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
        ((unitBallContract l).continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
      map_zero_left := by
        intro p
        apply Prod.ext
        · rfl
        · apply Subtype.ext; simp [unitBallContract]
      map_one_left := by
        intro p
        apply Prod.ext
        · rfl
        · apply Subtype.ext; simp [unitBallContract] }⟩
    right_inv := by apply ContinuousMap.Homotopic.refl }

variable {B : Type*} [TopologicalSpace B]

def constantNegativeTotalHomeomorph (B : Type*) [TopologicalSpace B] (k l : ℕ) :
    NegativeTotal (ContinuousMap.const B (standardTube k l)) ≃ₜ B × StandardNegative k l where
  toFun bu := (bu.val.1, ⟨bu.val.2, bu.property⟩)
  invFun bu := ⟨(bu.1, bu.2.val), bu.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := ((continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _)

variable {A C : Type*} [TopologicalSpace A] [TopologicalSpace C]

def FiberwiseHomotopyEquiv.ofProduct (h : ContinuousMap.HomotopyEquiv A C) :
    FiberwiseHomotopyEquiv (⟨Prod.fst, continuous_fst⟩ : C(B × A, B))
      (⟨Prod.fst, continuous_fst⟩ : C(B × C, B)) where
  toFun := ⟨fun ba => (ba.1, h ba.2), continuous_fst.prodMk (h.continuous.comp continuous_snd)⟩
  invFun := ⟨fun bc => (bc.1, h.invFun bc.2),
    continuous_fst.prodMk (h.invFun.continuous.comp continuous_snd)⟩
  toFun_over _ := rfl
  invFun_over _ := rfl
  left := {
    toFun := fun tba => (tba.2.1, h.left_inv.some (tba.1, tba.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (h.left_inv.some.continuous_toFun.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    map_zero_left := by intro ba; simp
    map_one_left := by intro ba; simp }
  right := {
    toFun := fun tbc => (tbc.2.1, h.right_inv.some (tbc.1, tbc.2.2))
    continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
      (h.right_inv.some.continuous_toFun.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
    map_zero_left := by intro bc; simp
    map_one_left := by intro bc; simp }
  left_over _ _ := rfl
  right_over _ _ := rfl

variable {E F G : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]

def FiberwiseHomotopyEquiv.precomposeHomeomorph {p : C(E, B)} {q : C(F, B)} {r : C(G, B)}
    (h : FiberwiseHomotopyEquiv q r) (e : E ≃ₜ F) (he : ∀ x, q (e x) = p x) :
    FiberwiseHomotopyEquiv p r where
  toFun := h.toFun.comp ⟨e, e.continuous⟩
  invFun := (⟨e.symm, e.symm.continuous⟩ : C(F, E)).comp h.invFun
  toFun_over x := (h.toFun_over (e x)).trans (he x)
  invFun_over x := by
    change p (e.symm (h.invFun x)) = r x
    rw [← he, e.apply_symm_apply]
    exact h.invFun_over x
  left := {
    toFun := fun tx => e.symm (h.left (tx.1, e tx.2))
    continuous_toFun := e.symm.continuous.comp (h.left.continuous_toFun.comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp }
  right := {
    toFun := h.right
    continuous_toFun := h.right.continuous_toFun
    map_zero_left := by intro x; simp
    map_one_left := by intro x; simp }
  left_over t x := by
    change p (e.symm (h.left (t, e x))) = p x
    rw [← he, e.apply_symm_apply, h.left_over, he]
  right_over := h.right_over

theorem negativeTrivial_standard (B : Type*) [TopologicalSpace B] (k l : ℕ) :
    NegativeTrivial (ContinuousMap.const B (standardTube k l)) := by
  exact ⟨(FiberwiseHomotopyEquiv.ofProduct (B := B) (standardNegativeSphereEquiv k l)).precomposeHomeomorph (constantNegativeTotalHomeomorph B k l) (fun _ => rfl)⟩

theorem stableNegativeTrivial_standard (B : Type*) [TopologicalSpace B] (m : ℕ) :
    StableNegativeTrivial (ContinuousMap.const B (standardTube m m)) := by
  refine ⟨0, ?_⟩
  exact negativeTrivial_standard B m m

end NearbyLagrangian.Tubes

end

end OAI
