import OAI.Analysis.LienardCycles.ArcEndpoints

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.CanonicalAnalytic
open ScalarArcs ArcEndpoints ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

theorem endpoints (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
    {p : P} {t h : ℝ} (hht : h < t) :
    ContDiffAt ℝ ω (lowerFamily Φ) ((p,t),h) ∧
    ContDiffAt ℝ ω (upperFamily Φ) ((p,t),h) := by
  have hφ (p : P) : ContDiff ℝ 1 (fun x => Φ (p,x)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  obtain ⟨u,a₀,b₀,hu⟩ := entire_arch_exists (hφ p) (show h-1 < t by linarith)
  obtain ⟨a,b,ha,hb,harch⟩ := hu.subarch (hφ p) (show h-1 < h by linarith) hht
  have hV : ContDiffOn ℝ 1 (field Φ) univ := by
    have hd : ContDiff ℝ ω (field Φ) :=
      contDiff_const.prodMk (((hΦ.comp (contDiff_fst.prodMk contDiff_snd.fst)).sub
        contDiff_snd.snd).prodMk contDiff_const)
    exact (hd.of_le (by simp)).contDiffOn
  obtain ⟨w,hwc,hwpeak,hwmatch,hwd,hwe⟩ := peak_family Φ isOpen_univ hV
    (fun x _ => hloc x) hΦ.contDiffAt hu.lower_lt_peak hu.peak_lt_upper
    hu.continuous hu.peak hu.equation (fun _ _ => mem_univ _)
  let A := (a₀+a)/2
  let B := (b+b₀)/2
  have hA : a₀ < A ∧ A < a := by dsimp [A]; constructor <;> linarith
  have hB : b < B ∧ B < b₀ := by dsimp [B]; constructor <;> linarith
  have hsub : Icc A B ⊆ Ioo a₀ b₀ :=
    fun _ hy => ⟨hA.1.trans_le hy.1,hy.2.trans_lt hB.2⟩
  have hwb : IsArch (fun x => Φ (p,x)) (fun y => w ((p,t),y)) h t a b := by
    apply IsArch.of_solution_and_hits (hφ p) (hwc (p,t))
      (fun y hy => (hwe y (hsub ⟨hA.2.le.trans hy.1,hy.2.trans hB.1.le⟩)).self_of_nhds)
      harch.lower_lt_peak harch.peak_lt_upper (hwpeak (p,t))
    · rw [hwmatch a ⟨ha.le,(harch.lower_lt_peak.trans hu.peak_lt_upper).le⟩]
      exact harch.lower
    · rw [hwmatch b ⟨(hu.lower_lt_peak.trans harch.peak_lt_upper).le,hb.le⟩]
      exact harch.upper
  obtain ⟨l,r,hl,hr,_,_,he⟩ := actual_endpoint_families Φ hφ hwc hwpeak
    (fun y hy => hwd y (Ioo_subset_Icc_self (hsub hy)))
    (fun y hy => hwe y (hsub hy)) hwb hA.2 hB.1 hΦ.continuous.continuousAt
  exact canonical_endpoints_contDiffAt Φ hφ hht hl hr
    (he.mono fun q hq => ⟨fun y => w (q.1,y),hq⟩)

end QuinticLienard.CanonicalAnalytic

end OAI
