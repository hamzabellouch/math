import OAI.Analysis.Mahler.GlobalVerticalGeometry
import OAI.Analysis.Mahler.FiberPreimageEndpoint

namespace OAI

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

theorem fiberDomain_eq_Ioo {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : fiberDomain q = Ioo r₀ 1 := by
  ext r
  constructor
  · intro hr
    refine ⟨?_,hr.2.1⟩
    by_contra h
    have hm := strictMonoOn_radialMap.monotoneOn ⟨hr.1.le,hr.2.1⟩ ⟨hr₀,hr₁⟩ (le_of_not_gt h)
    rw [hq] at hm
    linarith [hr.2.2]
  · exact mem_fiberDomain_of_basepoint hr₀ hq

lemma F_polar_fiberAngle {q r : ℝ} (hr : r ∈ fiberDomain q) :
    F (polar r (fiberAngle q r)) = (q : ℂ) + (fiberHeight q r : ℂ)*I := by
  apply Complex.ext
  · simpa [Q] using (fiberAngle_spec hr).2
  · simp [fiberHeight,S]

/-- The already proved conformal inverse agrees with the actual global polar choice. -/
theorem inverseF_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    inverseF ((q : ℂ) + (fiberHeight q r : ℂ)*I) = polar r (fiberAngle q r) := by
  rw [← F_polar_fiberAngle hr]
  apply inverseF_left
  simpa [norm_polar hr.1.le] using hr.2.1

theorem norm_inverseF_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ‖inverseF ((q : ℂ) + (fiberHeight q r : ℂ)*I)‖ = r := by
  rw [inverseF_fiberHeight hr,norm_polar hr.1.le]

/-- No positive heights are omitted, and no spurious positive heights are added. -/
theorem positive_verticalFiber_eq_image {q r₀ : ℝ} (hqstrip : q ∈ Ioo (-1 : ℝ) 1)
    (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1) (hq : radialMap r₀ = |q|) :
    verticalFiber q ∩ Ioi 0 = fiberHeight q '' Ioo r₀ 1 := by
  ext y
  constructor
  · rintro ⟨hy,hpos⟩
    rw [verticalFiber_eq_images hqstrip hr₀ hr₁ hq] at hy
    rcases hy with ⟨r,hr,he⟩ | ⟨r,hr,he⟩
    · have hlt : r₀ < r := by
        rcases hr.1.eq_or_lt with hz | ht
        · subst r
          rw [fiberHeight_basepoint hq] at he
          exact False.elim (by simp [← he] at hpos)
        · exact ht
      exact ⟨r,⟨hlt,hr.2⟩,he⟩
    · have hn := fiberHeight_nonneg hr₀ hq hr
      dsimp only at he
      change 0 < y at hpos
      linarith
  · rintro ⟨r,hr,rfl⟩
    exact ⟨fiberHeight_mem_verticalFiber (mem_fiberDomain_of_basepoint hr₀ hq hr),
      fiberHeight_pos hr₀ hq hr⟩

theorem fiberHeight_bijOn {q r₀ : ℝ} (hqstrip : q ∈ Ioo (-1 : ℝ) 1)
    (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1) (hq : radialMap r₀ = |q|) :
    BijOn (fiberHeight q) (Ioo r₀ 1) (verticalFiber q ∩ Ioi 0) := by
  rw [positive_verticalFiber_eq_image hqstrip hr₀ hr₁ hq]
  exact ⟨mapsTo_image _ _, (strictMonoOn_fiberHeight hr₀ hq).injOn,
    surjOn_image _ _⟩

/-- The whole integration segment for the vertical primitive belongs to Omega. -/
theorem vertical_segment_mem_Omega {u : ℂ} (hu : u ∈ Omega) {t : ℝ}
    (ht : t ∈ uIcc 0 u.im) : (u.re : ℂ) + (t : ℂ)*I ∈ Omega := by
  have hq : u.re ∈ Ioo (-1 : ℝ) 1 := by
    rw [← image_re_F_disk]
    exact ⟨u,hu,rfl⟩
  have hv := verticalFiber_interval hq
  have hy : u.im ∈ verticalFiber u.re := by
    simpa only [verticalFiber, mem_ofPred_eq, Complex.re_add_im] using hu
  exact hv.2.1.uIcc_subset hv.2.2 hy ht

/-- Global geometry of F, Omega, inverseF and fiberHeight.
The fiber endpoints and parametrization give the geometric prerequisites
for the radial primitive, without asserting its derivative or bound. -/
theorem global_vertical_geometry {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    IsOpen (verticalFiber q) ∧ OrdConnected (verticalFiber q) ∧
    0 ∈ verticalFiber q ∧
    ∃ r₀ ∈ Ico (0 : ℝ) 1, radialMap r₀ = |q| ∧
      fiberDomain q = Ioo r₀ 1 ∧
      StrictMonoOn (fiberHeight q) (Ico r₀ 1) ∧
      BijOn (fiberHeight q) (Ioo r₀ 1) (verticalFiber q ∩ Ioi 0) ∧
      Tendsto (fiberHeight q) (𝓝[>] r₀) (𝓝 0) ∧
      Tendsto (fun r => polar r (fiberAngle q r)) (𝓝[>] r₀)
        (𝓝 (if 0 ≤ q then (r₀ : ℂ) else -(r₀ : ℂ))) ∧
      ∀ r ∈ Ioo r₀ 1, ‖inverseF ((q : ℂ) + (fiberHeight q r : ℂ)*I)‖ = r := by
  obtain ⟨ho,hi,hz⟩ := verticalFiber_interval hq
  obtain ⟨r₀,hr₀,hbase⟩ := exists_radial_basepoint hq
  exact ⟨ho,hi,hz,r₀,hr₀,hbase,
    fiberDomain_eq_Ioo hr₀.1 hr₀.2 hbase,
    strictMonoOn_fiberHeight_basepoint hr₀.1 hr₀.2 hbase,
    fiberHeight_bijOn hq hr₀.1 hr₀.2 hbase,
    fiberHeight_tendsto_basepoint hr₀.1 hr₀.2 hbase,
    fiberPreimage_tendsto_basepoint hr₀.1 hr₀.2 hbase,
    fun r hr => norm_inverseF_fiberHeight (mem_fiberDomain_of_basepoint hr₀.1 hbase hr)⟩

end SymmetricMahler

end

end OAI
