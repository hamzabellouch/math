import OAI.Analysis.Mahler.FiberEndpoint
import OAI.Analysis.Mahler.ConformalInverse
import Mathlib.Topology.Order.LeftRight

namespace OAI

/-! Global vertical intervals of the conformal image. -/

noncomputable section
open Real Complex Set Filter Metric
open scoped Topology
namespace SymmetricMahler
open MahlerConformal

/-- Exact vertical section of the previously constructed conformal image. -/
def verticalFiber (q : ℝ) : Set ℝ := {y | (q : ℂ) + (y : ℂ)*I ∈ Omega}

lemma exists_radial_basepoint {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    ∃ r₀ ∈ Ico (0 : ℝ) 1, radialMap r₀ = |q| := by
  have hqa : |q| < 1 := abs_lt.mpr ⟨by linarith [hq.1],hq.2⟩
  have he := eventually_radius.and (F_real_tendsto_one.eventually (eventually_gt_nhds hqa))
  obtain ⟨r,hr,hqr⟩ := he.exists
  obtain ⟨t,ht,hte⟩ := intermediate_value_Icc hr.1.le (continuousOn_F_real hr.1.le hr.2)
    (show |q| ∈ Icc (F (0 : ℂ)).re (F (r : ℂ)).re by
      simpa [F_zero] using And.intro (abs_nonneg q) hqr.le)
  exact ⟨t,⟨ht.1,ht.2.trans_lt hr.2⟩,hte⟩

lemma fiberHeight_basepoint {q r₀ : ℝ} (hq : radialMap r₀ = |q|) :
    fiberHeight q r₀ = 0 := by
  have hn : r₀ ∉ fiberDomain q := by simp [fiberDomain, hq]
  simp [fiberHeight, fiberAngle, hn, S_zero]

lemma continuousOn_fiberHeight_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : ContinuousOn (fiberHeight q) (Ico r₀ 1) := by
  intro r hr
  rcases hr.1.eq_or_lt with he | hlt
  · subst r
    have hc : ContinuousWithinAt (fiberHeight q) (Ioi r₀) r₀ := by
      rw [ContinuousWithinAt, fiberHeight_basepoint hq]
      exact fiberHeight_tendsto_basepoint hr₀ hr₁ hq
    exact (continuousWithinAt_Ioi_iff_Ici.mp hc).mono (fun _ h => h.1)
  · exact (hasDerivAt_fiberHeight (mem_fiberDomain_of_basepoint hr₀ hq ⟨hlt,hr.2⟩)).continuousAt.continuousWithinAt

lemma strictMonoOn_fiberHeight_basepoint {q r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) : StrictMonoOn (fiberHeight q) (Ico r₀ 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ico _ _)
    (continuousOn_fiberHeight_basepoint hr₀ hr₁ hq)
  intro r hr
  rw [interior_Ico] at hr
  exact deriv_fiberHeight_pos (mem_fiberDomain_of_basepoint hr₀ hq hr)

lemma fiberHeight_pos {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|)
    (hr : r ∈ Ioo r₀ 1) : 0 < fiberHeight q r := by
  have h := strictMonoOn_fiberHeight_basepoint hr₀ (hr.1.trans hr.2) hq
    ⟨le_rfl,hr.1.trans hr.2⟩ ⟨hr.1.le,hr.2⟩ hr.1
  simpa [fiberHeight_basepoint hq] using h

lemma fiberHeight_nonneg {q r₀ r : ℝ} (hr₀ : 0 ≤ r₀) (hq : radialMap r₀ = |q|)
    (hr : r ∈ Ico r₀ 1) : 0 ≤ fiberHeight q r := by
  rcases hr.1.eq_or_lt with he | hlt
  · subst r; rw [fiberHeight_basepoint hq]
  · exact (fiberHeight_pos hr₀ hq ⟨hlt,hr.2⟩).le

lemma zero_mem_verticalFiber {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) : 0 ∈ verticalFiber q := by
  obtain ⟨t,ht,hF⟩ := exists_real_preimage hq
  have hw : (t : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa [Complex.norm_real, abs_lt] using ht
  simpa [verticalFiber] using (show (q : ℂ) ∈ Omega from ⟨t,hw,hF⟩)

lemma fiberHeight_mem_verticalFiber {q r : ℝ} (hr : r ∈ fiberDomain q) :
    fiberHeight q r ∈ verticalFiber q := by
  refine ⟨polar r (fiberAngle q r), ?_, ?_⟩
  · simpa [norm_polar hr.1.le] using hr.2.1
  · apply Complex.ext
    · simpa [Q] using (fiberAngle_spec hr).2
    · simp [fiberHeight, S]

lemma verticalFiber_neg {q y : ℝ} (hy : y ∈ verticalFiber q) : -y ∈ verticalFiber q := by
  have h := Omega_conj hy
  simpa [verticalFiber, map_add, map_mul] using h

lemma angular_height_mem_image {q r₀ r θ : ℝ} (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1)
    (hq : radialMap r₀ = |q|) (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) (hQ : Q r θ = q) :
    S r θ ∈ fiberHeight q '' Ico r₀ 1 := by
  by_cases hz : θ = 0
  · exact ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hz,S_zero,fiberHeight_basepoint hq]⟩
  by_cases hp : θ = Real.pi
  · exact ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hp,S_pi,fiberHeight_basepoint hq]⟩
  have hi : θ ∈ Ioo 0 Real.pi := ⟨lt_of_le_of_ne hθ.1 (Ne.symm hz),lt_of_le_of_ne hθ.2 hp⟩
  have hm := Q_mem_Ioo hr hr1 hi.1 hi.2
  rw [hQ] at hm
  have habs : |q| < radialMap r := abs_lt.mpr hm
  have hrr : r₀ < r := by
    by_contra h
    have hb := strictMonoOn_radialMap.monotoneOn ⟨hr.le,hr1⟩ ⟨hr₀,hr₁⟩ (le_of_not_gt h)
    rw [hq] at hb
    linarith
  have hd : r ∈ fiberDomain q := ⟨hr,hr1,habs⟩
  have hs := fiberAngle_spec hd
  have he := (Q_strictAntiOn hr hr1).injOn ⟨hs.1.1.le,hs.1.2.le⟩ hθ (hs.2.trans hQ.symm)
  exact ⟨r,⟨hrr.le,hr1⟩,by simp only [fiberHeight,he]⟩

/-- Every image height belongs to the global increasing upper fiber or its reflection. -/
theorem verticalFiber_eq_images {q r₀ : ℝ} (hqstrip : q ∈ Ioo (-1 : ℝ) 1)
    (hr₀ : 0 ≤ r₀) (hr₁ : r₀ < 1) (hq : radialMap r₀ = |q|) :
    verticalFiber q = fiberHeight q '' Ico r₀ 1 ∪
      (fun r => -fiberHeight q r) '' Ico r₀ 1 := by
  ext y
  constructor
  · rintro ⟨w,hw,hF⟩
    have hn : ‖w‖ < 1 := by simpa using hw
    have hQw : (F w).re = q := by rw [hF]; simp
    have hSw : (F w).im = y := by rw [hF]; simp
    by_cases hw0 : w = 0
    · have hy : y = 0 := by simpa [hw0,F_zero] using hSw.symm
      exact Or.inl ⟨r₀,⟨le_rfl,hr₁⟩,by rw [hy,fiberHeight_basepoint hq]⟩
    have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have he : polar ‖w‖ w.arg = w := Complex.norm_mul_exp_arg_mul_I w
    by_cases ha : 0 ≤ w.arg
    · have h := angular_height_mem_image hr₀ hr₁ hq hr hn ⟨ha,Complex.arg_le_pi w⟩
        (show Q ‖w‖ w.arg = q by simpa [Q,he] using hQw)
      exact Or.inl (by simpa [S,he,hSw] using h)
    · have har : -w.arg ∈ Icc (0 : ℝ) Real.pi :=
        ⟨by linarith,by linarith [Complex.neg_pi_lt_arg w]⟩
      have hep : polar ‖w‖ (-w.arg) = starRingEnd ℂ w := by rw [polar_neg_angle,he]
      have h := angular_height_mem_image hr₀ hr₁ hq hr hn har
        (show Q ‖w‖ (-w.arg) = q by simpa [Q,hep,F_conj] using hQw)
      obtain ⟨r,hrt,heq⟩ := h
      refine Or.inr ⟨r,hrt,?_⟩
      simpa [S,hep,F_conj,hSw] using congrArg Neg.neg heq
  · intro hy
    have hmem {r : ℝ} (hr : r ∈ Ico r₀ 1) : fiberHeight q r ∈ verticalFiber q := by
      rcases hr.1.eq_or_lt with he | ht
      · subst r; rw [fiberHeight_basepoint hq]; exact zero_mem_verticalFiber hqstrip
      · exact fiberHeight_mem_verticalFiber (mem_fiberDomain_of_basepoint hr₀ hq ⟨ht,hr.2⟩)
    rcases hy with ⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩
    · exact hmem hr
    · exact verticalFiber_neg (hmem hr)

/-- The actual global vertical section is an open interval containing zero. -/
theorem verticalFiber_interval {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    IsOpen (verticalFiber q) ∧ OrdConnected (verticalFiber q) ∧ 0 ∈ verticalFiber q := by
  obtain ⟨r₀,hr₀,hbase⟩ := exists_radial_basepoint hq
  have hc := continuousOn_fiberHeight_basepoint hr₀.1 hr₀.2 hbase
  have hp := isPreconnected_Ico.image (fiberHeight q) hc
  have hn := isPreconnected_Ico.image (fun r => -fiberHeight q r) hc.neg
  have hz : (0 : ℝ) ∈ fiberHeight q '' Ico r₀ 1 ∩ (fun r => -fiberHeight q r) '' Ico r₀ 1 :=
    ⟨⟨r₀,⟨le_rfl,hr₀.2⟩,fiberHeight_basepoint hbase⟩,
     ⟨r₀,⟨le_rfl,hr₀.2⟩,by dsimp only; rw [fiberHeight_basepoint hbase,neg_zero]⟩⟩
  refine ⟨isOpen_Omega.preimage (by fun_prop),?_,zero_mem_verticalFiber hq⟩
  rw [verticalFiber_eq_images hq hr₀.1 hr₀.2 hbase]
  exact (IsPreconnected.union' ⟨0,hz⟩ hp hn).ordConnected

end SymmetricMahler

end

end OAI
