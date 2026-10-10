import Mathlib
import OAI.Geometry.Cannon.Topology.CenteredHomeomorph
import OAI.Geometry.Cannon.Beltrami.ContinuousMemLpRestrict
import OAI.Geometry.Cannon.Topology.EquicontinuousCompactBound

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

namespace CannonBeltrami

def mollifier (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ)+1)
  rOut := 2 / ((n : ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply (div_lt_div_iff_of_pos_right (by positivity)).mpr; norm_num

def mollify (μ : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (mollifier n).normed volume ⋆[lsmul ℝ ℝ, volume] μ

lemma locallyIntegrable_bounded {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) : LocallyIntegrable μ volume := by
  apply (show LocallyIntegrable (fun _ : ℂ => k) volume from
    continuous_const.locallyIntegrable).mono hm
  exact .of_forall (fun z => by simpa only [Real.norm_eq_abs,abs_of_nonneg hk] using hb z)

lemma mollify_smooth {μ : ℂ → ℂ} (hm : LocallyIntegrable μ volume) (n : ℕ) :
    ContDiff ℝ ∞ (mollify μ n) :=
  (mollifier n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (mollifier n).contDiff_normed hm

lemma mollify_bound {μ : ℂ → ℂ} (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hb : ∀ z, ‖μ z‖ ≤ k) (n : ℕ) (z : ℂ) :
    ‖mollify μ n z‖ ≤ k := by
  have h := dist_convolution_le (x₀:=z) (z₀:=0) hk
    (mollifier n).support_normed_eq.subset (mollifier n).nonneg_normed
    (mollifier n).integral_normed hm (fun x _ => by simpa using hb x)
  simpa only [dist_zero_right, mollify] using h

lemma mollify_zero {μ : ℂ → ℂ} {R : ℝ} (hs : ∀ z, R ≤ ‖z‖ → μ z=0)
    (n : ℕ) {z : ℂ} (hz : R+2 ≤ ‖z‖) : mollify μ n z=0 := by
  by_contra hh
  have hm : z ∈ support (mollify μ n) := hh
  obtain ⟨x,hx,y,hy,hxy⟩ := support_convolution_subset (lsmul ℝ ℝ) hm
  have hxr : ‖x‖ < 2 := by
    rw [(mollifier n).support_normed_eq] at hx
    have hx' : ‖x‖ < 2 / ((n : ℝ)+1) := by simpa only [mem_ball,dist_zero_right,mollifier] using hx
    exact hx'.trans_le ((div_le_iff₀ (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α:=ℝ) n]))
  have hyr : ‖y‖ < R := by
    by_contra hy'
    exact hy (hs y (le_of_not_gt hy'))
  have htri := norm_add_le x y
  change x+y=z at hxy
  rw [hxy] at htri
  linarith

lemma mollify_compact {μ : ℂ → ℂ} {R : ℝ} (hs : ∀ z, R ≤ ‖z‖ → μ z=0) (n : ℕ) :
    HasCompactSupport (mollify μ n) := by
  apply (isCompact_closedBall (0 : ℂ) (R+2)).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  have hn : ‖z‖ < R+2 := by
    by_contra hh
    exact hz (mollify_zero hs n (le_of_not_gt hh))
  simpa only [mem_closedBall,dist_zero_right] using hn.le

lemma mollify_ae_tendsto {μ : ℂ → ℂ} (hm : LocallyIntegrable μ volume) :
    ∀ᵐ z ∂volume, Tendsto (fun n => mollify μ n z) atTop (𝓝 (μ z)) := by
  apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (K:=2) _ _ hm
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
    simpa [mollifier,div_eq_mul_inv] using h
  · exact .of_forall (fun n => by dsimp [mollifier]; ring_nf; exact le_refl _)

theorem exists_smooth_coefficient_approximation {μ : ℂ → ℂ}
    (hm : AEStronglyMeasurable μ volume) {k R : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) (hs : ∀ z, R ≤ ‖z‖ → μ z=0) :
    ∃ ν : ℕ → SchwartzMap ℂ ℂ,
      (∀ n, HasCompactSupport (ν n : ℂ → ℂ)) ∧
      (∀ n z, ‖ν n z‖ ≤ k) ∧
      (∀ n z, R+2 ≤ ‖z‖ → ν n z=0) ∧
      (∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z))) := by
  let ν (n : ℕ) := (mollify_compact hs n).toSchwartzMap
    (mollify_smooth (locallyIntegrable_bounded hm hk hb) n)
  exact ⟨ν,fun n => mollify_compact hs n,mollify_bound hm hk hb,
    fun n z hz => mollify_zero hs n hz,mollify_ae_tendsto (locallyIntegrable_bounded hm hk hb)⟩

end CannonBeltrami

namespace CannonBeltrami

def globalCutoff (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := (n:ℝ)+1
  rOut := (n:ℝ)+2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem global_smooth_coefficient_approximation {μ : ℂ → ℂ}
    (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ ν : ℕ → SchwartzMap ℂ ℂ,
      (∀ n, HasCompactSupport (ν n : ℂ → ℂ)) ∧
      (∀ n z, ‖ν n z‖ ≤ k) ∧
      (∀ᵐ z ∂volume, Tendsto (fun n => ν n z) atTop (𝓝 (μ z))) := by
  let f : ℕ → ℂ → ℂ := fun n z => (globalCutoff n z:ℂ)*mollify μ n z
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    (Complex.ofRealCLM.contDiff.comp (globalCutoff n).contDiff).mul
      (mollify_smooth (locallyIntegrable_bounded hm hk hb) n)
  have hc (n : ℕ) : HasCompactSupport (f n) :=
    ((globalCutoff n).hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  let ν (n : ℕ) := (hc n).toSchwartzMap (hf n)
  refine ⟨ν,hc,?_,?_⟩
  · intro n z
    change ‖(globalCutoff n z:ℂ)*mollify μ n z‖ ≤ k
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (globalCutoff n).nonneg]
    calc
      globalCutoff n z*‖mollify μ n z‖ ≤ 1*k :=
        mul_le_mul (globalCutoff n).le_one (mollify_bound hm hk hb n z)
          (norm_nonneg _) (by norm_num)
      _ = k := one_mul _
  · filter_upwards [mollify_ae_tendsto (locallyIntegrable_bounded hm hk hb)] with z hz
    apply hz.congr'
    have hev : ∀ᶠ n : ℕ in atTop, ‖z‖ ≤ (n:ℝ)+1 :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖z‖)).mono
        (fun n hn => by linarith)
    filter_upwards [hev] with n hn
    change mollify μ n z=(globalCutoff n z:ℂ)*mollify μ n z
    rw [(globalCutoff n).one_of_mem_closedBall (by simpa [globalCutoff] using hn)]
    simp

end CannonBeltrami

namespace CannonBeltrami
open CannonPlane

theorem global_weak_mrmt (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ H : ℂ ≃ₜ ℂ, H 0=0 ∧ H 1=1 ∧
      ∀ S : Set ℂ, IsCompact S → ∃ a : Lp ℂ 2 (volume.restrict S),
        ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ S →
          (∫ z, H z*partialZ φ z)=-(∫ z in S, a z*φ z) ∧
          (∫ z, H z*partialBar φ z)=-(∫ z in S, a z*(μ z*φ z)) := by
  obtain ⟨ν,hνc,hνb,hνlim⟩ := global_smooth_coefficient_approximation hm hk hb
  choose F hF0 hF1 hF hF' hFe hFD hFD' using
    (fun n => normalized_smooth_beltrami_solution (ν n) (hνc n) hk hk1 (hνb n))
  let K := (1+k)/(1-k)
  have hK : 0 ≤ K := div_nonneg (by linarith) (sub_pos.mpr hk1).le
  obtain ⟨H,σ,hσ,hH0,hH1,hlim,_⟩ := normalized_smooth_qc_subsequence F hF0 hF1
    (fun n => (hF n).of_le (by simp)) (fun n => (hF' n).of_le (by simp)) hK hFD hFD'
  have hr : UniformRelativeControl (fun n z => F n z) := by
    intro ε hε
    obtain ⟨η,hη,h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η,hη,fun n => h (F n) ((hF' n).of_le (by simp)) (hFD' n)⟩
  have hp := normalized_family_pointwise_bound (fun n z => F n z) hF0 hF1 hr
  have he := relative_control_equicontinuous (fun n z => F n z) hr hp
  have hlocal (S : Set ℂ) (hS : IsCompact S) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ S → ‖F (σ n) z‖ ≤ B := by
    obtain ⟨B,hB,hbB⟩ := equicontinuous_compact_bound (fun n z => F n z) he hp hS
    exact ⟨B,hB,fun n => hbB (σ n)⟩
  have hpt (z : ℂ) : Tendsto (fun n => F (σ n) z) atTop (𝓝 (H z)) :=
    (continuous_eval_const z).tendsto (homeomorphMap H) |>.comp hlim
  have hνt : ∀ᵐ z ∂volume, Tendsto (fun n => ν (σ n) z) atTop (𝓝 (μ z)) := by
    filter_upwards [hνlim] with z hz
    exact hz.comp hσ.tendsto_atTop
  refine ⟨H,hH0,hH1,fun S hS => ?_⟩
  exact local_weak_beltrami_limit (fun n => F (σ n)) H (fun n => hF (σ n)) hlocal hpt hK
    (fun n => hFD (σ n)) (fun n => ν (σ n)) μ
    (fun n => (ν (σ n)).continuous.aestronglyMeasurable) hm hk (fun n => hνb (σ n)) hb hνt
    (fun n => hFe (σ n)) hS
end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
