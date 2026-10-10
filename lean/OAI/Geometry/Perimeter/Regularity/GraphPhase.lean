import OAI.Geometry.Perimeter.Regularity.GraphExistence

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem full_graph_phaseSupport_iff (hn : 1<n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0≤a) (ha4 : a<1/4)
    (hs : FullSlab E v 8 a) {f : normalPlane v → ℝ}
    (hiff : ∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
      ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y))
    (y : normalPlane v) (hy : ‖y‖<1/4) (t : ℝ) (ht : |t|<1/2) :
    ((y:Euc n)+t•v∈(volume.restrict E).support ↔ t≤f y) := by
  let g : ℝ → Euc n := fun s ↦ (y:Euc n)+s•v
  let K := (volume.restrict E).support
  have hg : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hnorm (s : ℝ) (hss : |s|≤1/2) : ‖g s‖<1 := by
    have hh := norm_add_le (y:Euc n) (s•v)
    rw [norm_smul,Real.norm_eq_abs,hv,mul_one] at hh
    change ‖(y:Euc n)‖<1/4 at hy
    dsimp [g]
    linarith
  have hball (s : ℝ) (hss : |s|≤1/2) : g s∈Metric.ball 0 8 := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hnorm s hss]
  have hleft : g (-(1/2))∈K := hs.lower_phaseSupport ha (hball _ (by norm_num)) (by
    change inner ℝ v ((y:Euc n)+(-(1/2):ℝ)•v) < -a
    rw [normal_fiber_inner hv]; linarith)
  have hright : g (1/2)∉K := hs.upper_not_phaseSupport ha (hball _ (by norm_num)) (by
    change a < inner ℝ v ((y:Euc n)+(1/2:ℝ)•v)
    rw [normal_fiber_inner hv]; linarith)
  have hfront : frontier K=perimeterSupport E := minimizing_frontier_phaseSupport
    (Real.HolderConjugate.conjExponent (by exact_mod_cast hn : 1<(n:ℝ))) hmin
  constructor
  · intro hx
    by_contra! hf
    obtain ⟨z,⟨s,hss,rfl⟩,hz⟩ := connected_crosses_frontier
      (isPreconnected_Icc.image g hg.continuousOn) Measure.isClosed_support
      (mem_image_of_mem g (show t∈Icc t (1/2) from ⟨le_rfl,(abs_lt.mp ht).2.le⟩)) hx
      (mem_image_of_mem g (show (1/2:ℝ)∈Icc t (1/2) from ⟨(abs_lt.mp ht).2.le,le_rfl⟩)) hright
    rw [hfront] at hz
    have hb : |s|≤1/2 := abs_le.mpr ⟨(abs_lt.mp ht).1.le.trans hss.1,hss.2⟩
    have he := (hiff y s hy (hnorm s hb)).mp hz
    linarith [hss.1]
  · intro htf
    by_contra hx
    obtain ⟨z,⟨s,hss,rfl⟩,hz⟩ := connected_crosses_frontier
      (isPreconnected_Icc.image g hg.continuousOn) Measure.isClosed_support
      (mem_image_of_mem g (show (-(1/2):ℝ)∈Icc (-(1/2)) t from ⟨le_rfl,(abs_lt.mp ht).1.le⟩)) hleft
      (mem_image_of_mem g (show t∈Icc (-(1/2)) t from ⟨(abs_lt.mp ht).1.le,le_rfl⟩)) hx
    have hKz : g s∈K := Measure.isClosed_support.frontier_subset hz
    rw [hfront] at hz
    have hb : |s|≤1/2 := abs_le.mpr ⟨hss.1,hss.2.trans (abs_lt.mp ht).2.le⟩
    have he := (hiff y s hy (hnorm s hb)).mp hz
    have hst : s=t := by linarith [hss.2]
    exact hx (hst ▸ hKz)

end RPISingularHarnack

end

end OAI
