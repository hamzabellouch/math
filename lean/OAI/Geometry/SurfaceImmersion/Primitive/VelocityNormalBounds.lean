import OAI.Geometry.SurfaceImmersion.Primitive.VelocityNormalNonvanishing
import OAI.Geometry.Immersion.ClosedSurface.NormalJets

namespace OAI

/-! Smoothness and compact positive lower bounds for the limiting normal component. -/
noncomputable section
open Set
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def leadingNormal (X Y C V : Vec) : Vec :=
  realNormalPart (leadingTangent X Y C V) Y C

def normalSize (X Y C V : Vec) : ℝ :=
  Real.sqrt (leadingNormal X Y C V ⬝ᵥ leadingNormal X Y C V)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X Y C V : E → Vec} {U : Set E}

lemma leadingTangent_smoothOn (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hV : ContDiffOn ℝ ∞ V U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => leadingTangent (X x) (Y x) (C x) (V x)) U := by
  intro x hx
  have hm := hU.mem_nhds hx
  exact (((hX.contDiffAt hm).sub (contDiffAt_realNormalPart
    (hY.contDiffAt hm) (hC.contDiffAt hm) (hX.contDiffAt hm) (hD x hx))).add
      (hV.contDiffAt hm)).contDiffWithinAt

lemma leadingNormal_smoothOn (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hV : ContDiffOn ℝ ∞ V U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hYV : ∀ x ∈ U, Y x ⬝ᵥ V x = 0) (hCV : ∀ x ∈ U, C x ⬝ᵥ V x = 0)
    (hV0 : ∀ x ∈ U, V x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => leadingNormal (X x) (Y x) (C x) (V x)) U := by
  have hT := leadingTangent_smoothOn hU hX hY hC hV hD
  intro x hx
  have hm := hU.mem_nhds hx
  exact (contDiffAt_realNormalPart (hT.contDiffAt hm) (hY.contDiffAt hm)
    (hC.contDiffAt hm) (leading_normal_nondegenerate (hD x hx)
      (hYV x hx) (hCV x hx) (hV0 x hx)).1).contDiffWithinAt

lemma normalSize_positive {X Y C V : Vec} (hD : gramDet Y C ≠ 0)
    (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0) (hV : V ≠ 0) :
    0 < normalSize X Y C V :=
  Real.sqrt_pos.mpr (dot_self_pos (leading_normal_nondegenerate hD hYV hCV hV).2)

/-- Both the normal length and its reciprocal are uniformly controlled on compact data. -/
theorem compact_normalSize_bounds (hU : IsOpen U)
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U)
    (hC : ContDiffOn ℝ ∞ C U) (hV : ContDiffOn ℝ ∞ V U)
    (hD : ∀ x ∈ U, gramDet (Y x) (C x) ≠ 0)
    (hYV : ∀ x ∈ U, Y x ⬝ᵥ V x = 0) (hCV : ∀ x ∈ U, C x ⬝ᵥ V x = 0)
    (hV0 : ∀ x ∈ U, V x ≠ 0) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ c D : ℝ, 0 < c ∧ 0 < D ∧ ∀ x ∈ K,
      c ≤ normalSize (X x) (Y x) (C x) (V x) ∧
      normalSize (X x) (Y x) (C x) (V x) ≤ D ∧
      1 / normalSize (X x) (Y x) (C x) (V x) ≤ 1 / c := by
  let S : E → ℝ := fun x => normalSize (X x) (Y x) (C x) (V x)
  have hN := (leadingNormal_smoothOn hU hX hY hC hV hD hYV hCV hV0).continuousOn
  have hS : ContinuousOn S K := by
    apply ContinuousOn.sqrt
    exact (continuousOn_finsetSum Finset.univ (fun i _ =>
      ((continuous_apply i).comp_continuousOn (hN.mono hKU)).mul
        ((continuous_apply i).comp_continuousOn (hN.mono hKU))))
  have hpos (x : E) (hx : x ∈ K) : 0 < S x :=
    normalSize_positive (hD x (hKU hx)) (hYV x (hKU hx)) (hCV x (hKU hx)) (hV0 x (hKU hx))
  rcases K.eq_empty_or_nonempty with hzero | hne
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
    simp [hzero]
  obtain ⟨xmin, hxmin, hmin⟩ := hK.exists_isMinOn hne hS
  obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isMaxOn hne hS
  refine ⟨S xmin, S xmax, hpos xmin hxmin, hpos xmax hxmax, ?_⟩
  intro x hx
  exact ⟨hmin hx, hmax hx, one_div_le_one_div_of_le (hpos xmin hxmin) (hmin hx)⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
