import OAI.Probability.SLE.Geometry.HalfPlaneUnivalentBounds
import OAI.Probability.SLE.Geometry.HolomorphicFamilyCompactness
import OAI.Probability.SLE.Loewner.UnivalentLocallyUniformLimit
import OAI.Probability.SLE.Geometry.PublishedConformalCompactness

namespace OAI

/-! The half-plane compactness input follows from the disk growth input.
Moving normalization points stay on the prescribed compact semicircle. -/
noncomputable section
open Set Filter Metric Function
open scoped Topology

namespace SLEExactGauge

local instance compactnessFromGrowthLocallyCompact : LocallyCompactSpace upperHalfPlane :=
  isOpen_upperHalfPlane.locallyCompactSpace

theorem halfPlaneUnivalentCompactness_of_diskGrowth
    (hgrowth : PublishedDiskUnivalentGrowth) : PublishedHalfPlaneUnivalentCompactness := by
  classical
  intro f z s m M hs hm hf hi hz hv hd
  let K : Set ℂ := sphere 0 1 ∩ {w | s≤w.im}
  have hK : IsCompact K := (isCompact_sphere (0:ℂ) 1).inter_right
    (isClosed_le continuous_const Complex.continuous_im)
  have hKH : K⊆upperHalfPlane := fun w hw => hs.trans_le hw.2
  have hzK (n : ℕ) : z n∈K := by
    exact ⟨by simpa only [mem_sphere,dist_zero_right] using (hz n).1,(hz n).2⟩
  have hb : ∀ L : Set ℂ, IsCompact L → L⊆upperHalfPlane →
      ∃ C : ℝ, ∀ n, ∀ w∈L, ‖f n w‖≤C := by
    intro L hL hLH
    exact univalent_compact_family_bound hgrowth f z K L M hK hL hKH hLH hzK hf hi hv
      (fun n => (hd n).2)
  obtain ⟨g,φ,hφ,hconv⟩ := holomorphic_halfPlane_family_subsequence f hf hb
  let F : ℂ → ℂ := fun w => if hw : w∈upperHalfPlane then g ⟨w,hw⟩ else 0
  have hlim : TendstoLocallyUniformlyOn (fun n => f (φ n)) F atTop upperHalfPlane := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    apply tendstoLocallyUniformly_iff_forall_isCompact.mpr
    intro L hL
    have h := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hconv L hL
    change TendstoUniformlyOn (fun n (w : upperHalfPlane) => f (φ n) w) g atTop L at h
    change TendstoUniformlyOn (fun n (w : upperHalfPlane) => f (φ n) w)
      (fun w : upperHalfPlane => F w) atTop L
    have he : (fun w : upperHalfPlane => F w)=(g : upperHalfPlane → ℂ) := by
      funext w
      exact dite_eq_left w.property
    rwa [he]
  have hF := hlim.differentiableOn (Eventually.of_forall fun n => hf (φ n)) isOpen_upperHalfPlane
  have hnon : ¬∃ c, ∀ w∈upperHalfPlane, F w=c := by
    rintro ⟨c,hc⟩
    have hzero (w : ℂ) (hw : w∈upperHalfPlane) : deriv F w=0 := by
      have he : F =ᶠ[𝓝 w] (fun _ => c) := by
        filter_upwards [isOpen_upperHalfPlane.mem_nhds hw] with v hv
        exact hc v hv
      rw [he.deriv_eq,deriv_const]
    have hdl := hlim.deriv (Eventually.of_forall fun n => hf (φ n)) isOpen_upperHalfPlane
    have hdu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_upperHalfPlane).mp
      hdl K hKH hK
    obtain ⟨n,hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp hdu) (m/2) (by positivity)).exists
    have hsmall := hn (z (φ n)) (hzK (φ n))
    have hlower := (hd (φ n)).1
    rw [hzero _ (hKH (hzK (φ n)))] at hsmall
    simp only [Function.comp_apply,dist_zero_left] at hsmall
    linarith
  have hconn : IsPreconnected upperHalfPlane :=
    (convex_halfSpace_im_gt (0:ℝ)).isPreconnected
  have hFi := tendstoLocallyUniformlyOn_injOn isOpen_upperHalfPlane hconn
    (fun n => hf (φ n)) (fun n => hi (φ n)) hlim hnon
  exact ⟨φ,F,hφ,hF,hFi,fun w hw => univalent_deriv_ne_zero isOpen_upperHalfPlane hF hFi hw,hlim⟩

end SLEExactGauge

end

end OAI
