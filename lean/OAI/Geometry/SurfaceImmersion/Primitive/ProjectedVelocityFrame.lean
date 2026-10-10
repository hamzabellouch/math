import OAI.Geometry.SurfaceImmersion.Primitive.VelocityPlaneRays

namespace OAI

/-! The actual frame formed from the projected tangent and preferred normal. -/
noncomputable section
open Set
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def projectedFirst (X Y C n : Vec) (t : ℝ) : Vec :=
  first (realNormalPart Y C X) (realNormalPart Y C n) t

def projectedSecond (X Y C n : Vec) (t : ℝ) : Vec :=
  unitPerp Y C (projectedFirst X Y C n t)

lemma projected_blend_nonzero {X Y B C n : Vec} {a b t : ℝ}
    (hD : gramDet X Y ≠ 0) (ha : a < 0)
    (hXB : X ⬝ᵥ B = 0) (hYB : Y ⬝ᵥ B = 0)
    (hC : C = a • X + b • Y + B)
    (hXn : X ⬝ᵥ n = 0) (hYn : Y ⬝ᵥ n = 0) (hn : n ⬝ᵥ n = 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hB : t < 1 → B ≠ 0)
    (hanti : t < 1 → normalize B ≠ -n) :
    blend (realNormalPart Y C X) (realNormalPart Y C n) t ≠ 0 := by
  have hn0 : n ≠ 0 := by
    intro hz
    rw [hz] at hn
    norm_num at hn
  have hpn := projected_normal_ne_zero hD ha.ne hXB hYB hC hXn hYn hn0
  have hD' := (velocity_gram_pos hD ha.ne hXB hYB hC).ne'
  apply blend_nonzero_of_not_opposite hpn ht
  · intro ht0 hpX
    have ht1 : t < 1 := by rw [ht0]; norm_num
    have hpb := projected_normal_ne_zero hD ha.ne hXB hYB hC hXB hYB (hB ht1)
    apply hpb
    rw [projected_second_form hD' hC, hpX, smul_zero]
  · intro ht1
    exact projected_tangent_no_opposite_ray hD ha hXB hYB hC hXn hYn
      (no_opposite_ray_of_normalized (hB ht1) hn (hanti ht1))

theorem projected_frame_orthonormal {X Y C n : Vec} {t : ℝ}
    (hD : gramDet Y C ≠ 0)
    (hn : blend (realNormalPart Y C X) (realNormalPart Y C n) t ≠ 0) :
    projectedFirst X Y C n t ⬝ᵥ projectedFirst X Y C n t = 1 ∧
      projectedSecond X Y C n t ⬝ᵥ projectedSecond X Y C n t = 1 ∧
      projectedFirst X Y C n t ⬝ᵥ projectedSecond X Y C n t = 0 ∧
      Y ⬝ᵥ projectedFirst X Y C n t = 0 ∧ C ⬝ᵥ projectedFirst X Y C n t = 0 ∧
      Y ⬝ᵥ projectedSecond X Y C n t = 0 ∧ C ⬝ᵥ projectedSecond X Y C n t = 0 := by
  have hx := realNormalPart_perp Y C X hD
  have hn' := realNormalPart_perp Y C n hD
  exact frame_orthonormal_of_nonzero hD hn hx.1 hn'.1 hx.2 hn'.2

lemma projectedFirst_zero (X Y C n : Vec) :
    projectedFirst X Y C n 0 = normalize (realNormalPart Y C X) := by
  simp [projectedFirst, first, blend]

lemma projectedFirst_one (X Y C n : Vec) :
    projectedFirst X Y C n 1 = normalize (realNormalPart Y C n) := by
  simp [projectedFirst, first, blend]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem projected_frame_smoothOn {X Y C n : E → Vec} {t : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hn : ContDiffOn ℝ ∞ n U) (ht : ContDiffOn ℝ ∞ t U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hblend : ∀ x ∈ U, blend (realNormalPart (Y x) (C x) (X x))
      (realNormalPart (Y x) (C x) (n x)) (t x) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => projectedFirst (X x) (Y x) (C x) (n x) (t x)) U ∧
      ContDiffOn ℝ ∞ (fun x => projectedSecond (X x) (Y x) (C x) (n x) (t x)) U := by
  have hfirst (x : E) (hx : x ∈ U) :
      ContDiffAt ℝ ∞ (fun z => projectedFirst (X z) (Y z) (C z) (n z) (t z)) x := by
    have hy := hY.contDiffAt (hU.mem_nhds hx)
    have hc := hC.contDiffAt (hU.mem_nhds hx)
    exact first_smoothAt_of_nonzero
      (contDiffAt_realNormalPart hy hc (hX.contDiffAt (hU.mem_nhds hx)) (hD x hx))
      (contDiffAt_realNormalPart hy hc (hn.contDiffAt (hU.mem_nhds hx)) (hD x hx))
      (ht.contDiffAt (hU.mem_nhds hx)) (hblend x hx)
  refine ⟨fun x hx => (hfirst x hx).contDiffWithinAt, ?_⟩
  intro x hx
  have hy := hY.contDiffAt (hU.mem_nhds hx)
  have hc := hC.contDiffAt (hU.mem_nhds hx)
  have hpx := realNormalPart_perp (Y x) (C x) (X x) (hD x hx)
  have hpn := realNormalPart_perp (Y x) (C x) (n x) (hD x hx)
  exact (contDiffAt_unitPerp hy hc (hfirst x hx) (hD x hx)
    (normalize_nonzero (hblend x hx))
    (first_perp hpx.1 hpn.1 _) (first_perp hpx.2 hpn.2 _)).contDiffWithinAt

end ClosedSurfaceR4.VelocityFrame

end

end OAI
