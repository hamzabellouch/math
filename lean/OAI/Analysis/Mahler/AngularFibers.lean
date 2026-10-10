import OAI.Analysis.Mahler.ImplicitAngle
import OAI.Analysis.Mahler.SineBound

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

noncomputable def fiberDomain (q : ℝ) : Set ℝ :=
  {r | 0 < r ∧ r < 1 ∧ |q| < radialMap r}

lemma fiberDomain_isOpen (q : ℝ) : IsOpen (fiberDomain q) := by
  apply isOpen_iff_mem_nhds.mpr
  intro r hr
  have hc := (hasDerivAt_radialMap hr.1 hr.2.1).continuousAt
  have hm := hc (Ioi_mem_nhds hr.2.2)
  filter_upwards [Ioo_mem_nhds hr.1 hr.2.1, hm] with s hs hms
  exact ⟨hs.1,hs.2,hms⟩

lemma exists_fiberAngle {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ∃ θ : ℝ, θ ∈ Ioo 0 Real.pi ∧ MahlerConformal.Q r θ = q := by
  have hq := abs_lt.mp hr.2.2
  exact (MahlerConformal.existsUnique_angle hr.1 hr.2.1 hq.1 hq.2).exists

/-- The unique upper-half-disk angle, extended by zero outside its open radial domain. -/
noncomputable def fiberAngle (q r : ℝ) : ℝ := by
  classical
  exact if hr : r ∈ fiberDomain q then Classical.choose (exists_fiberAngle hr) else 0

lemma fiberAngle_spec {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberAngle q r ∈ Ioo 0 Real.pi ∧ MahlerConformal.Q r (fiberAngle q r) = q := by
  unfold fiberAngle
  rw [dite_eq_left hr]
  exact Classical.choose_spec (exists_fiberAngle hr)

/-- Local implicit angles agree with the globally chosen fiber by uniqueness.
Thus the global choice is smooth at every point of its open domain. -/
theorem contDiffAt_fiberAngle {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ContDiffAt ℝ ∞ (fiberAngle q) r := by
  have hs := fiberAngle_spec hr
  obtain ⟨ψ,hψr,hψC,hψQ⟩ := exists_local_angle hr.1 hr.2.1 hs.1.1 hs.1.2
  have hψcont := hψC.continuousAt
  have hψrange : ∀ᶠ s in 𝓝 r, ψ s ∈ Ioo (0 : ℝ) Real.pi := by
    apply hψcont
    rw [hψr]
    exact Ioo_mem_nhds hs.1.1 hs.1.2
  apply hψC.congr_of_eventuallyEq
  filter_upwards [(fiberDomain_isOpen q).mem_nhds hr, hψrange, hψQ] with s hsd hsp hsQ
  have hg := fiberAngle_spec hsd
  have heq : MahlerConformal.Q s (fiberAngle q s) = MahlerConformal.Q s (ψ s) := by
    rw [hg.2, hsQ, hs.2]
  exact (MahlerConformal.Q_strictAntiOn hsd.1 hsd.2.1).injOn
    ⟨hg.1.1.le,hg.1.2.le⟩ ⟨hsp.1.le,hsp.2.le⟩ heq

/-- Measurability of the actual fiber angle, including its zero extension. -/
theorem measurable_fiberAngle (q : ℝ) : Measurable (fiberAngle q) := by
  classical
  have hc : ContinuousOn (fiberAngle q) (fiberDomain q) :=
    fun _ hr => (contDiffAt_fiberAngle hr).continuousAt.continuousWithinAt
  have hmeas := hc.measurable_piecewise continuous_zero.continuousOn
    (fiberDomain_isOpen q).measurableSet
  convert hmeas using 1
  ext r
  by_cases hr : r ∈ fiberDomain q
  · simp [hr]
  · simp [fiberAngle, hr]

/-- Every radius after r0 has a unique fiber angle when M(r0)=|q|. -/
theorem mem_fiberDomain_of_basepoint {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) (hr : r ∈ Ioo r₀ 1) : r ∈ fiberDomain q := by
  have hrpos : 0 < r := hr₀.trans_lt hr.1
  refine ⟨hrpos,hr.2,?_⟩
  rw [← hq]
  exact strictMonoOn_radialMap ⟨hr₀,hr.1.trans hr.2⟩ ⟨hrpos.le,hr.2⟩ hr.1

end SymmetricMahler

end OAI
