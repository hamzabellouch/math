import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SphericalMeanLimitBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakHarmonicRegularityBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

theorem exterior_harmonic_uniform_constant_local {u : Space → ℝ} {R K : ℝ}
    (hR : 0 < R) (hu : ∀ x, R < ‖x‖ → ContDiffAt ℝ 2 u x)
    (hh : ∀ x, R ≤ ‖x‖ → Δ u x = 0) (hb : ∀ x, R ≤ ‖x‖ → u x ≤ K) :
    ∃ A : ℝ, ∀ ε > 0, ∃ S > 0, ∀ x : Space, S ≤ ‖x‖ → |u x-A| < ε := by
  let b : ContDiffBump (0:Space) := ⟨2*R,4*R,by linarith,by linarith⟩
  let v : Space → ℝ := fun x => (1-b x)*u x
  have hv : ContDiff ℝ 2 v := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < 2*R
    · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      have hb : y ∈ closedBall (0:Space) b.rIn := by
        simpa only [mem_closedBall,dist_zero_right] using hy.le
      simp only [v,b.one_of_mem_closedBall hb,sub_self,zero_mul]
    · exact (contDiffAt_const.sub b.contDiffAt).mul (hu x (by linarith [le_of_not_gt hx]))
  have he (x : Space) (hx : 4*R < ‖x‖) : v =ᶠ[𝓝 x] u := by
    filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hx] with y hy
    simp only [v,b.zero_of_le_dist (by simpa only [dist_zero_right] using hy.le),sub_zero,one_mul]
  have hcv : HasCompactSupport (Δ v) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:Space) (4*R))
    intro x hx
    by_contra hn
    have hxr : 4*R < ‖x‖ := lt_of_not_ge (fun h => hn (mem_closedBall_zero_iff.mpr h))
    apply hx
    rw [(laplacian_congr_nhds (he x hxr)).eq_of_nhds]
    exact hh x (by linarith)
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:Space) (4*R)).exists_bound_of_continuousOn hv.continuous.continuousOn
  have hvb : ∀ x, v x ≤ max B K := by
    intro x
    by_cases hx : ‖x‖ ≤ 4*R
    · exact (le_abs_self (v x)).trans ((hB x (mem_closedBall_zero_iff.mpr hx)).trans (le_max_left _ _))
    · rw [(he x (lt_of_not_ge hx)).eq_of_nhds]
      exact (hb x (by linarith)).trans (le_max_right _ _)
  obtain ⟨A,hA⟩ := compact_laplacian_uniform_limit hv hcv hvb
  refine ⟨A,?_⟩
  intro ε hε
  obtain ⟨S,hS,hdec⟩ := hA ε hε
  refine ⟨max S (4*R+1),hS.trans_le (le_max_left _ _),fun x hx => ?_⟩
  have hsx : S ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hrx : 4*R < ‖x‖ := by linarith [le_trans (le_max_right S (4*R+1)) hx]
  simpa only [(he x hrx).eq_of_nhds] using hdec x hsx

lemma weak_exterior_regular {u : Space → ℝ} {R : ℝ}
    (hu : ContinuousOn u {x | R < ‖x‖})
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0)
    (y : Space) (hy : R < ‖y‖) : ContDiffAt ℝ ∞ u y ∧ Δ u y = 0 := by
  let S := (‖y‖-R)/2
  have hS : 0 < S := by dsimp [S]; linarith
  have hsub : closedBall y S ⊆ {x | R < ‖x‖} := by
    intro x hx
    have hd : dist x y ≤ S := hx
    have ht : ‖y‖ ≤ ‖x‖+dist x y := by
      have hh := norm_le_norm_add_norm_sub x y
      simpa only [dist_eq_norm, norm_sub_rev] using hh
    change R < ‖x‖
    dsimp [S] at hd
    linarith
  exact weak_harmonic_regular_at hS (hu.mono hsub)
    (fun g hg hcg hs => hw g hg hcg (hs.trans (ball_subset_closedBall.trans hsub)))

theorem weak_exterior_mean_uniform_decay {u : Space → ℝ} {R K q : ℝ}
    (hR : 0 < R) (hu : ContinuousOn u {0}ᶜ)
    (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ {x | R < ‖x‖} → (∫ x, u x*Δ g x) = 0)
    (hb : ∀ x, R ≤ ‖x‖ → u x ≤ K)
    (hmean : ∀ p : Space, R < ‖p‖ → sphereMean u p = q/‖p‖) :
    ∀ ε > 0, ∃ S > 0, ∀ x : Space, S ≤ ‖x‖ → |u x| < ε := by
  have huc : ContinuousOn u {x | R < ‖x‖} :=
    hu.mono (fun x hx => norm_pos_iff.mp (hR.trans hx))
  have hreg (x : Space) (hx : R < ‖x‖) : ContDiffAt ℝ 2 u x :=
    (weak_exterior_regular huc hw x hx).1.of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hhi (x : Space) (hx : 2*R ≤ ‖x‖) : Δ u x = 0 :=
    (weak_exterior_regular huc hw x (by linarith)).2
  obtain ⟨A,hA⟩ := exterior_harmonic_uniform_constant_local (by linarith : 0 < 2*R)
    (fun x hx => hreg x (by linarith)) hhi (fun x hx => hb x (by linarith))
  have he : A = 0 := by
    by_contra hn
    have ha : 0 < |A| := abs_pos.mpr hn
    obtain ⟨S,hS,hs⟩ := hA (|A|/4) (by positivity)
    let r := max S (max (R+1) (4*|q|/|A|+1))
    have hSr : S ≤ r := le_max_left _ _
    have hRr : R+1 ≤ r := (le_max_left _ _).trans (le_max_right _ _)
    have hqr : 4*|q|/|A|+1 ≤ r := (le_max_right _ _).trans (le_max_right _ _)
    have hr : 0 < r := hS.trans_le hSr
    let p : Space := r • radialAxis
    have hpn : ‖p‖ = r := TFUnitData.ray_norm hr
    have hp : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hpn]; exact hr.ne')
    have hm := sphereMean_close_to_constant (sphereFunction_integrable
      (fun x hx => hu.continuousAt (isOpen_compl_singleton.mem_nhds hx)) hp)
      (fun x hx => (hs x (by rw [hx,hpn]; exact hSr)).le)
    rw [hmean p (by rw [hpn]; linarith),hpn] at hm
    have hsmall : |q/r| ≤ |A|/4 := by
      rw [abs_div,abs_of_pos hr]
      apply (div_le_iff₀ hr).mpr
      have ht : 4*|q|/|A| ≤ r := by linarith
      have ht' := (div_le_iff₀ ha).mp ht
      nlinarith
    have hh := abs_sub_le (q/r-A) (q/r) 0
    have hab : |A| ≤ |q/r-A|+|q/r| := by
      have h := abs_sub (q/r-A) (q/r)
      rw [show q/r-A-q/r = -A by ring,abs_neg] at h
      exact h
    linarith
  subst A
  simpa only [sub_zero] using hA

end CoulombAnalysis

end

end OAI
