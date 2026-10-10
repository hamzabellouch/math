import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.TFNonradialOscillation

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

open CoulombAtom

lemma exists_global_weak_poisson_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u ρ : Space → ℝ) (R B M : ℝ),
      0 < R → 0 ≤ B → 0 ≤ M → Continuous u → Measurable ρ →
      (∀ z, 0 ≤ ρ z) → (∀ z, ρ z ≤ M) →
      Function.support ρ ⊆ ball 0 R →
      (∀ z ∈ closedBall (0 : Space) R, u z ≤ B) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ z, u z*Δ g z) = 4*Real.pi*(∫ z, ρ z*g z)) →
      ∀ x : Space, ‖x‖ ≤ R/6 →
        |u x-u 0| ≤ C/R*‖x‖*(B+M*R^2+max (-u 0) 0) := by
  obtain ⟨Ch,hCh,harm⟩ := exists_weak_harmonic_oscillation_constant
  let A : ℝ := 1+8*Real.pi
  let C : ℝ := 3*Ch*A+8*Real.pi
  have hA : 0 < A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u ρ R B M hR hB hM hu hm hn hb hs hcap hw x hx
  let P := tfPotential ρ
  have hp := bounded_support_memLp hm hn hb hs (5/3)
  have hP : Continuous P := tfPotential_continuous (bounded_support_integrable hm hn hb hs) hp
  have hPn (z : Space) : 0 ≤ P z := tfPotential_nonneg (Eventually.of_forall hn) z
  have hpb (z : Space) (hz : ‖z‖ ≤ R) : P z ≤ 8*Real.pi*M*R^2 :=
    bounded_density_potential_le hm hM hR hn hb hs z hz
  have hpd : |P x-P 0| ≤ 8*Real.pi*M*R*‖x‖ := by
    simpa only [sub_zero] using bounded_density_potential_difference hm hM hR hn hb hs x 0
      (hx.trans (by linarith)) (by simp; exact hR.le)
  let H : Space → ℝ := fun z => u z+P z
  have hH : Continuous H := hu.add hP
  have hHw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R → (∫ z, H z*Δ g z) = 0 := by
    intro g hg hcg hsg
    have hiu : Integrable (fun z => u z*Δ g z) :=
      (hu.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    have hip : Integrable (fun z => P z*Δ g z) :=
      (hP.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport
        (tfLaplacian_compact hg hcg).mul_left
    have hpot := tfPotential_weak_laplacian_ball hp hs hg hcg hsg
    dsimp only [H]
    simp_rw [add_mul]
    rw [integral_add hiu hip,hw g hg hcg hsg,hpot]
    ring
  let K : ℝ := B+8*Real.pi*M*R^2
  let v : Space → ℝ := fun z => K-H z
  have hvc : Continuous v := continuous_const.sub hH
  have hvn : ∀ z ∈ closedBall (0 : Space) (3*(R/3)), 0 ≤ v z := by
    intro z hz
    have hz' : z ∈ closedBall (0 : Space) R := by convert hz using 1; congr 1; ring
    have ht := hcap z hz'
    have hpz := hpb z (by simpa only [mem_closedBall,dist_zero_right] using hz')
    dsimp [v,K,H]
    linarith
  have hvw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (3*(R/3)) → (∫ z, v z*Δ g z) = 0 := by
    intro g hg hcg hsg
    apply weak_harmonic_upper_distance hH K hHw hg hcg
    convert hsg using 1
    congr 1
    ring
  have hv := harm v (R/3) (by linarith) hvc.continuousOn hvn hvw x (by linarith)
  let Q : ℝ := B+M*R^2+max (-u 0) 0
  have hn0 : 0 ≤ max (-u 0) 0 := le_max_right _ _
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hv0 : v 0 ≤ A*Q := by
    have ht := hPn 0
    have hc := le_max_left (-u 0) 0
    have hmr : 0 ≤ M*R^2 := mul_nonneg hM (sq_nonneg R)
    dsimp [v,K,H,A,Q]
    nlinarith [mul_nonneg (show 0 ≤ 8*Real.pi by positivity) (add_nonneg hB hn0)]
  have hv' : |H x-H 0| ≤ (3*Ch*A)/R*‖x‖*Q := by
    have he : v x-v 0 = -(H x-H 0) := by dsimp [v]; ring
    rw [he,abs_neg] at hv
    apply hv.trans
    calc
      _ ≤ Ch/(R/3)*‖x‖*(A*Q) := mul_le_mul_of_nonneg_left hv0 (by positivity)
      _ = _ := by ring
  have hp' : |P x-P 0| ≤ (8*Real.pi)/R*‖x‖*Q := by
    apply hpd.trans
    calc
      _ = (8*Real.pi)/R*‖x‖*(M*R^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by dsimp [Q]; linarith) (by positivity)
  calc
    |u x-u 0| = |(H x-H 0)-(P x-P 0)| := by dsimp [H]; congr 1; ring
    _ ≤ |H x-H 0|+|P x-P 0| := abs_sub _ _
    _ ≤ (3*Ch*A)/R*‖x‖*Q+(8*Real.pi)/R*‖x‖*Q := add_le_add hv' hp'
    _ = C/R*‖x‖*Q := by dsimp [C]; ring

theorem exists_weak_poisson_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u ρ : Space → ℝ) (R B M : ℝ),
      0 < R → 0 ≤ B → 0 ≤ M → ContinuousOn u (closedBall 0 R) → Measurable ρ →
      (∀ z, 0 ≤ ρ z) → (∀ z, ρ z ≤ M) →
      Function.support ρ ⊆ ball 0 R →
      (∀ z ∈ closedBall (0 : Space) R, u z ≤ B) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ z, u z*Δ g z) = 4*Real.pi*(∫ z, ρ z*g z)) →
      ∀ x : Space, ‖x‖ ≤ R/6 →
        |u x-u 0| ≤ C/R*‖x‖*(B+M*R^2+max (-u 0) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_global_weak_poisson_oscillation_constant
  refine ⟨C,hC,?_⟩
  intro u ρ R B M hR hB hM hu hm hn hb hs hcap hw x hx
  let f : C(closedBall (0 : Space) R,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall (0 : Space) R) : v z = u z :=
    congrArg (fun h : C(closedBall (0 : Space) R,ℝ) => h ⟨z,hz⟩) hv
  have hh := hbound v ρ R B M hR hB hM v.continuous hm hn hb hs
    (fun z hz => by rw [he z hz]; exact hcap z hz) (fun g hg hcg hsg => ?_) x hx
  · simpa only [he x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans (by linarith : R/6 ≤ R)),
      he 0 (mem_closedBall_self hR.le)] using hh
  · rw [←hw g hg hcg hsg]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : Δ g z = 0
      · simp only [hz,mul_zero]
      · change v z*Δ g z = u z*Δ g z
        rw [he z (ball_subset_closedBall (hsg (tfLaplacian_support hg hz)))]

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology ContDiff

open CoulombAtom

theorem exists_local_poisson_oscillation_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (u ρ : Space → ℝ) (y : Space) (R B M : ℝ),
      0 < R → 0 ≤ B → 0 ≤ M → ContinuousOn u (closedBall y R) → Measurable ρ →
      (∀ z ∈ ball y R, 0 ≤ ρ z) → (∀ z ∈ ball y R, ρ z ≤ M) →
      (∀ z ∈ closedBall y R, u z ≤ B) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball y R →
        (∫ z, u z*Δ g z) = 4*Real.pi*(∫ z, ρ z*g z)) →
      ∀ x : Space, ‖x-y‖ ≤ R/6 →
        |u x-u y| ≤ C/R*‖x-y‖*(B+M*R^2+max (-u y) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_weak_poisson_oscillation_constant
  refine ⟨C,hC,?_⟩
  intro u ρ y R B M hR hB hM hu hm hn hb hcap hw x hx
  let v : Space → ℝ := fun z => u (y+z)
  let q : Space → ℝ := (ball 0 R).indicator (fun z => ρ (y+z))
  have hball (z : Space) (hz : z ∈ ball (0 : Space) R) : y+z ∈ ball y R := by
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  have hclosed (z : Space) (hz : z ∈ closedBall (0 : Space) R) : y+z ∈ closedBall y R := by
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hz
  have hv : ContinuousOn v (closedBall 0 R) :=
    hu.comp (continuous_const.add continuous_id).continuousOn hclosed
  have hqm : Measurable q :=
    (hm.comp (measurable_const.add measurable_id)).indicator measurableSet_ball
  have hqn : ∀ z, 0 ≤ q z := indicator_nonneg (fun z hz => hn _ (hball z hz))
  have hqb : ∀ z, q z ≤ M := by
    intro z
    by_cases hz : z ∈ ball (0 : Space) R
    · dsimp only [q]
      rw [indicator_of_mem hz]
      exact hb _ (hball z hz)
    · dsimp only [q]
      rw [indicator_of_notMem hz]
      exact hM
  have hqs : Function.support q ⊆ ball 0 R := support_indicator_subset
  have hvc : ∀ z ∈ closedBall (0 : Space) R, v z ≤ B := fun z hz => hcap _ (hclosed z hz)
  have hvw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 R → (∫ z, v z*Δ g z) = 4*Real.pi*(∫ z, q z*g z) := by
    intro g hg hcg hsg
    let G : Space → ℝ := fun z => g (-y+z)
    have hG : ContDiff ℝ 2 G := hg.comp (contDiff_const.add contDiff_id)
    have hcG : HasCompactSupport G := hcg.comp_homeomorph (Homeomorph.addLeft (-y))
    have hsG : tsupport G ⊆ ball y R := by
      intro z hz
      have ht := hsg (tsupport_translate_subset y hz)
      simpa only [mem_ball,dist_eq_norm,sub_zero,neg_add_eq_sub] using ht
    have ht := hw G hG hcG hsG
    rw [tfLaplacian_translate g (-y)] at ht
    have hi := integral_add_left_eq_self (μ := volume) (fun z => u z*Δ g (-y+z)) y
    have he : (∫ z, v z*Δ g z) = ∫ z, u z*Δ g (-y+z) := by
      simpa only [v,neg_add_cancel_left] using hi
    rw [he,ht]
    congr 1
    have hj := integral_add_left_eq_self (μ := volume) (fun z => ρ z*G z) y
    calc
      _ = ∫ z, ρ (y+z)*g z := by simpa only [G,neg_add_cancel_left] using hj.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun z => by
        by_cases hz : g z = 0
        · simp only [hz,mul_zero]
        · dsimp only [q]
          rw [indicator_of_mem (hsg (subset_tsupport g hz))])
  have hh := hbound v q R B M hR hB hM hv hqm hqn hqb hqs hvc hvw (x-y) hx
  simpa only [v,add_sub_cancel,add_zero] using hh

end CoulombAnalysis

end

end OAI
