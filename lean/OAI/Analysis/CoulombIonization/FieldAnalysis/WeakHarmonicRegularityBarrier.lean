import Mathlib
import OAI.Analysis.CoulombIonization.Localization.LipschitzMollifier
import OAI.Analysis.CoulombIonization.ThomasFermi.TFNonradialOscillation
import OAI.Analysis.CoulombIonization.FieldAnalysis.BarrierWeakMaxBarrier

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_WeakHarmonicRegularity_barrier_scope

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology Convolution ContDiff

open CoulombAtom CoulombBarrier

lemma packetSmooth_mean (r : ℝ) (v : Space → ℝ) (x : Space) :
    packetSmooth r v x = ∫ z, packetDensity x r z*v z := by
  rw [packetSmooth,convolution_eq_swap]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change packetDensity 0 r (x-z)*v z = packetDensity x r z*v z
    rw [packetDensity_translate x r z]
    exact congrArg (fun a : ℝ => a*v z)
      (packetDensity_radial r (x-z) (z-x) (norm_sub_rev x z))

theorem weak_harmonic_regular_at {u : Space → ℝ} {y : Space} {S : ℝ}
    (hS : 0 < S) (hu : ContinuousOn u (closedBall y S))
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball y S → (∫ x, u x*Δ g x) = 0) :
    ContDiffAt ℝ ∞ u y ∧ Δ u y = 0 := by
  let f : C(closedBall y S,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall y S) : v z = u z :=
    congrArg (fun h : C(closedBall y S,ℝ) => h ⟨z,hz⟩) hv
  have hvw (g : Space → ℝ) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
      (hs : tsupport g ⊆ ball y S) : (∫ x, v x*Δ g x) = 0 := by
    rw [←hw g hg hcg hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hx : Δ g x = 0
      · simp only [hx,mul_zero]
      · change v x*Δ g x = u x*Δ g x
        rw [he x (ball_subset_closedBall (hs (tfLaplacian_support hg hx)))]
  let r := S/4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrS : r < S/2 := by dsimp [r]; linarith
  have hws : ContDiff ℝ ∞ (packetSmooth r v) := packetSmooth_contDiff hr v.continuous
  have heq : packetSmooth r v =ᶠ[𝓝 y] u := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    have hzdist : dist z y < r := hz
    have hsub : ball z (S/2) ⊆ ball y S := by
      intro x hx
      have hd : dist x z < S/2 := hx
      have ht := dist_triangle x z y
      change dist x y < S
      dsimp [r] at hzdist
      linarith
    rw [packetSmooth_mean,weak_harmonic_packet_mean v.continuous z hr hrS
      (fun g hg hcg hs => hvw g hg hcg (hs.trans hsub)),he z]
    exact mem_closedBall.mpr (hzdist.le.trans (by dsimp [r]; linarith))
  have hlap : Δ (packetSmooth r v) y = 0 := by
    let k := packetDensity 0 r
    have hk : ContDiff ℝ 2 k := (packetDensity_smooth 0 r).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
    have hkc : HasCompactSupport k := packetDensity_compact 0 hr
    have hkg : ContDiff ℝ 2 (fun x => k (y-x)) := hk.comp (contDiff_const.sub contDiff_id)
    have hcg : HasCompactSupport (fun x => k (y-x)) :=
      hkc.comp_homeomorph (Homeomorph.subLeft y)
    have hsg : tsupport (fun x => k (y-x)) ⊆ ball y S :=
      (tsupport_sub_left (fun z hz => by
        simpa only [sub_zero] using packetDensity_support 0 hr hz) y).trans
          (closedBall_subset_ball (by dsimp [r]; linarith))
    have htest := hvw _ hkg hcg hsg
    have hflip : k ⋆[newtonMul] (v:Space → ℝ) = (v:Space → ℝ) ⋆[newtonMul] k := by
      simpa only [newtonMul_flip_eq] using (convolution_flip newtonMul (f := (v:Space → ℝ)) (g := k))
    change Δ (k ⋆[newtonMul] (v:Space → ℝ)) y = 0
    rw [hflip,laplacian_convolution v.continuous.locallyIntegrable hkc hk]
    simp_rw [laplacian_sub_left hk] at htest
    exact htest
  exact ⟨hws.contDiffAt.congr_of_eventuallyEq heq.symm,
    (laplacian_congr_nhds heq).eq_of_nhds.symm.trans hlap⟩

end Work_WeakHarmonicRegularity_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

theorem weak_harmonic_bounded_above_constant {u : Space → ℝ} (hu : Continuous u)
    {K : ℝ} (hb : ∀ x, u x ≤ K)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∫ x, u x*Δ g x) = 0) : ∀ x, u x = u 0 := by
  obtain ⟨C,hC,hosc⟩ := exists_weak_harmonic_oscillation_constant
  intro x
  have he (R : ℝ) (hR : 0 < R) (hx : ‖x‖ ≤ R/2) :
      |u x-u 0| ≤ C/R*‖x‖*(K-u 0) := by
    have hh := hosc (fun z => K-u z) R hR (continuous_const.sub hu).continuousOn
      (fun z _ => sub_nonneg.mpr (hb z))
      (fun g hg hcg hsg => weak_harmonic_upper_distance hu K
        (fun φ hφ hcφ _ => hw φ hφ hcφ) hg hcg hsg) x hx
    convert hh using 1
    rw [show K-u x-(K-u 0) = -(u x-u 0) by ring, abs_neg]
  have hlim : Tendsto (fun R : ℝ => C/R*‖x‖*(K-u 0)) atTop (𝓝 0) := by
    simpa only [id_eq,zero_mul] using ((tendsto_const_nhds.div_atTop tendsto_id).mul_const ‖x‖).mul_const (K-u 0)
  have hle : |u x-u 0| ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim (by
    filter_upwards [eventually_gt_atTop (max 1 (2*‖x‖))] with R hR
    exact he R (by linarith [le_max_left 1 (2*‖x‖)])
      (by linarith [le_max_right 1 (2*‖x‖)]))
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hle)

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

lemma compact_source_weak_poisson {ρ : Space → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {g : Space → ℝ} (hg : ContDiff ℝ 2 g)
    (hcg : HasCompactSupport g) :
    (∫ x, tfPotential ρ x*Δ g x) = -(4*Real.pi)*(∫ x, ρ x*g x) := by
  obtain ⟨R,_,hR⟩ := hcρ.isBounded.exists_pos_norm_le
  obtain ⟨S,_,hS⟩ := hcg.isBounded.exists_pos_norm_le
  apply tfPotential_weak_laplacian_ball (hρ.memLp_of_hasCompactSupport hcρ)
    (S := max R S+1) _ hg hcg
  · intro x hx
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (hS x hx)
      (lt_of_le_of_lt (le_max_right R S) (lt_add_one _)))
  · intro x hx
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (hR x (subset_tsupport ρ hx))
      (lt_of_le_of_lt (le_max_left R S) (lt_add_one _)))

theorem compact_laplacian_representation {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (hcu : HasCompactSupport (Δ u)) {K : ℝ} (hb : ∀ x, u x ≤ K) :
    ∃ A : ℝ, ∀ x, u x = A-tfPotential (fun y => Δ u y/(4*Real.pi)) x := by
  let ρ := fun y => Δ u y/(4*Real.pi)
  have hρ : Continuous ρ := (tfLaplacian_continuous hu).div_const _
  have hcρ : HasCompactSupport ρ := hcu.mul_right
  have hp : Continuous (tfPotential ρ) := tfPotential_continuous
    (hρ.integrable_of_hasCompactSupport hcρ) (hρ.memLp_of_hasCompactSupport hcρ)
  obtain ⟨P,hP⟩ := compact_potential_bounded hρ hcρ
  have hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∫ x, (u x+tfPotential ρ x)*Δ g x) = 0 := by
    intro g hg hcg
    have hi₁ : Integrable (fun x => u x*Δ g x) :=
      (hu.continuous.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    have hi₂ : Integrable (fun x => tfPotential ρ x*Δ g x) :=
      (hp.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    simp_rw [add_mul]
    rw [integral_add hi₁ hi₂,compact_laplacian_green hu hg hcg,
      compact_source_weak_poisson hρ hcρ hg hcg]
    have he : (fun x => ρ x*g x) = fun x => (Δ u x*g x)/(4*Real.pi) := by
      funext x
      dsimp [ρ]
      ring
    rw [he,integral_div]
    field_simp
    ring
  have hh := weak_harmonic_bounded_above_constant (hu.continuous.add hp)
    (u := fun x => u x+tfPotential ρ x)
    (K := K+P) (fun x => add_le_add (hb x)
      ((le_abs_self (tfPotential ρ x)).trans (hP x))) hw
  refine ⟨u 0+tfPotential ρ 0,fun x => ?_⟩
  have ht := hh x
  change u x = u 0+tfPotential ρ 0-tfPotential ρ x
  linarith only [ht]

theorem compact_laplacian_uniform_limit {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (hcu : HasCompactSupport (Δ u)) {K : ℝ} (hb : ∀ x, u x ≤ K) :
    ∃ A : ℝ, ∀ ε > 0, ∃ R > 0, ∀ x : Space, R ≤ ‖x‖ → |u x-A| < ε := by
  obtain ⟨A,hA⟩ := compact_laplacian_representation hu hcu hb
  let ρ := fun y => Δ u y/(4*Real.pi)
  have hρ : Continuous ρ := (tfLaplacian_continuous hu).div_const _
  have hcρ : HasCompactSupport ρ := hcu.mul_right
  obtain ⟨S,_,hS⟩ := hcρ.isBounded.exists_pos_norm_le
  refine ⟨A,?_⟩
  intro ε hε
  obtain ⟨R,hR,hdec⟩ := tfPotential_compact_decay
    (hρ.integrable_of_hasCompactSupport hcρ) (hρ.memLp_of_hasCompactSupport hcρ)
    (fun y hy => hS y (subset_tsupport ρ hy)) (ε/2) (by positivity)
  refine ⟨R,hR,fun x hx => ?_⟩
  rw [hA x,sub_sub_cancel_left,abs_neg]
  exact (hdec x hx).trans_lt (by linarith)

end CoulombAnalysis

end

end OAI
