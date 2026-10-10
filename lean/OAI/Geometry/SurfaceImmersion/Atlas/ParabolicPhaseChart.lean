import OAI.Geometry.SurfaceImmersion.Atlas.CenteredConvexPhase

namespace OAI

/-! An explicit phase chart on an entire half-plane. This supplies one
chart on a disk uniformly over nearby linear phase parameters. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

def parabolicPhaseMap (k : ℝ) (p : Base) : Base :=
  (p.1+(k/2)*(p.1^2+p.2^2),p.2)

def parabolicDiscriminant (k : ℝ) (p : Base) : ℝ :=
  1+2*k*p.1-k^2*p.2^2

def parabolicPhaseInverse (k : ℝ) (p : Base) : Base :=
  ((Real.sqrt (parabolicDiscriminant k p)-1)/k,p.2)

lemma parabolicDiscriminant_map (k : ℝ) (p : Base) :
    parabolicDiscriminant k (parabolicPhaseMap k p) = (1+k*p.1)^2 := by
  simp only [parabolicDiscriminant,parabolicPhaseMap]
  ring

lemma parabolicPhaseMap_smooth (k : ℝ) : ContDiff ℝ ∞ (parabolicPhaseMap k) := by
  unfold parabolicPhaseMap
  fun_prop

lemma parabolicDiscriminant_smooth (k : ℝ) : ContDiff ℝ ∞ (parabolicDiscriminant k) := by
  unfold parabolicDiscriminant
  fun_prop

lemma parabolicPhaseInverse_source {k : ℝ} (hk : k ≠ 0) {p : Base}
    (hp : 0 < parabolicDiscriminant k p) :
    0 < 1+k*(parabolicPhaseInverse k p).1 := by
  have he : 1+k*(parabolicPhaseInverse k p).1 = Real.sqrt (parabolicDiscriminant k p) := by
    dsimp [parabolicPhaseInverse]
    field_simp
    ring
  rw [he]
  exact Real.sqrt_pos.mpr hp

lemma parabolicPhaseInverse_left {k : ℝ} (hk : k ≠ 0) {p : Base}
    (hp : 0 < 1+k*p.1) : parabolicPhaseInverse k (parabolicPhaseMap k p) = p := by
  ext
  · simp only [parabolicPhaseInverse,parabolicDiscriminant_map,Real.sqrt_sq hp.le]
    field_simp
    ring
  · rfl

lemma parabolicPhaseInverse_right {k : ℝ} (hk : k ≠ 0) {p : Base}
    (hp : 0 < parabolicDiscriminant k p) :
    parabolicPhaseMap k (parabolicPhaseInverse k p) = p := by
  have hs := Real.sq_sqrt hp.le
  ext
  · dsimp [parabolicPhaseMap,parabolicPhaseInverse]
    field_simp
    dsimp [parabolicDiscriminant] at hs ⊢
    nlinarith
  · rfl

lemma parabolicPhaseInverse_smooth (k : ℝ) :
    ContDiffOn ℝ ∞ (parabolicPhaseInverse k) {p | 0 < parabolicDiscriminant k p} := by
  apply ContDiffOn.prodMk _ contDiffOn_snd
  exact (((parabolicDiscriminant_smooth k).contDiffOn.sqrt (fun _ hp => ne_of_gt hp)).sub
    contDiffOn_const).div_const k

def parabolicPhaseChart (k : ℝ) (hk : k ≠ 0) : OpenPartialHomeomorph Base Base where
  toFun := parabolicPhaseMap k
  invFun := parabolicPhaseInverse k
  source := {p | 0 < 1+k*p.1}
  target := {p | 0 < parabolicDiscriminant k p}
  map_source' := fun p hp => by
    change 0 < parabolicDiscriminant k (parabolicPhaseMap k p)
    rw [parabolicDiscriminant_map]
    exact sq_pos_of_pos hp
  map_target' := fun _ hp => parabolicPhaseInverse_source hk hp
  left_inv' := fun _ hp => parabolicPhaseInverse_left hk hp
  right_inv' := fun _ hp => parabolicPhaseInverse_right hk hp
  open_source := isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_fst))
  open_target := isOpen_lt continuous_const (parabolicDiscriminant_smooth k).continuous
  continuousOn_toFun := (parabolicPhaseMap_smooth k).continuous.continuousOn
  continuousOn_invFun := (parabolicPhaseInverse_smooth k).continuousOn

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
