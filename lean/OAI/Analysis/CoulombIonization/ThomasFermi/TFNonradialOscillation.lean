import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.NearTFReaction
import OAI.Analysis.CoulombIonization.FieldAnalysis.WeakHarmonicOscillation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Topology ContDiff

namespace CoulombAnalysis
open CoulombAtom

lemma cap_reaction_scale {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R) :
    (A/R^4)^(3/2:ℝ) = A^(3/2:ℝ)/R^6 := by
  rw [Real.div_rpow hA (pow_nonneg hR.le _)]
  congr 1
  rw [←Real.rpow_natCast R 4,←Real.rpow_mul hR.le]
  norm_num

lemma weak_harmonic_upper_distance {H : Space → ℝ} (hH : Continuous H) (K : ℝ)
    {S : ℝ} (hw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 S → (∫ x, H x*Δ g x) = 0)
    {g : Space → ℝ} (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (hsg : tsupport g ⊆ ball 0 S) : (∫ x, (K-H x)*Δ g x) = 0 := by
  have hi : Integrable (fun x => H x*Δ g x) :=
    (hH.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  have hic : Integrable (fun x => K*Δ g x) :=
    (continuous_const.mul (tfLaplacian_continuous hg)).integrable_of_hasCompactSupport (tfLaplacian_compact hg hcg).mul_left
  have he := compact_laplacian_green (f := fun _ : Space => K) contDiff_const hg hcg
  simp only [laplacian_const,Pi.zero_apply,zero_mul,integral_zero] at he
  simp_rw [sub_mul]
  rw [integral_sub hic hi,he,hw g hg hcg hsg,sub_self]

lemma exists_global_weak_tf_oscillation_constant {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space → ℝ) (R : ℝ), 0 < R → Continuous u →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) →
      ∀ x : Space, ‖x‖ ≤ R/12 →
        |u x-u 0| ≤ C/R*‖x‖*(R⁻¹^4+max (-u 0) 0) := by
  obtain ⟨Ch,hCh,harm⟩ := exists_weak_harmonic_oscillation_constant
  let A : ℝ := 256*(80/k)^2
  let E : ℝ := k*A^(3/2:ℝ)
  let K : ℝ := A+E
  let C : ℝ := 6*Ch*(K+1)+E+1
  have hA : 0 < A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hK : 0 ≤ K := add_nonneg hA.le hE
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro u R hR hu hw x hx
  have hcap (z : Space) (hz : ‖z‖ ≤ 3*R/4) : u z ≤ A/R^4 :=
    weak_tf_nonradial_cap hR hk hu.continuousOn hw z hz
  have hB : 0 ≤ A/R^4 := by positivity
  have hbr (z : Space) (hz : z ∈ ball (0 : Space) (R/2)) : u z ≤ A/R^4 :=
    hcap z (by have ht := mem_ball_zero_iff.mp hz; linarith)
  let ρ := nearTFReaction u k (R/2)
  let P := tfPotential ρ
  have hm : Measurable ρ := nearTFReaction_measurable hu k (R/2)
  have hn : ∀ z, 0 ≤ ρ z := nearTFReaction_nonneg u hk.le (R/2)
  have hb : ∀ z, ρ z ≤ k/(4*Real.pi)*(A/R^4)^(3/2:ℝ) := nearTFReaction_bound hk.le hB hbr
  have hs : Function.support ρ ⊆ ball 0 (R/2) := nearTFReaction_support u k (R/2)
  have hP : Continuous P := nearTFReaction_continuous_potential hu hk.le hB hbr
  have hPn (z : Space) : 0 ≤ P z := tfPotential_nonneg (Eventually.of_forall hn) z
  have hM : 0 ≤ k/(4*Real.pi)*(A/R^4)^(3/2:ℝ) := by positivity
  have hpb (z : Space) (hz : ‖z‖ ≤ R/2) : P z ≤ E/R^4 := by
    have hh := bounded_density_potential_le hm hM (by linarith : 0 < R/2) hn hb hs z hz
    apply hh.trans
    calc
      _ = (E/2)/R^4 := by
        rw [cap_reaction_scale hA.le hR]
        dsimp [E]
        field_simp
        ring
      _ ≤ E/R^4 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hR.le _)
  have hpd : |P x-P 0| ≤ E/R^5*‖x‖ := by
    have hh := bounded_density_potential_difference hm hM (by linarith : 0 < R/2) hn hb hs x 0
      (by linarith) (by simp; positivity)
    apply hh.trans_eq
    rw [sub_zero,cap_reaction_scale hA.le hR]
    dsimp [E]
    field_simp
    ring
  let H : Space → ℝ := fun z => u z+P z
  have hH : Continuous H := hu.add hP
  have hHw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (R/2) → (∫ z, H z*Δ g z) = 0 := by
    intro g hg hcg hsg
    exact nearTFReaction_weak_harmonic hu hk.le hB hbr (by linarith : R/2 ≤ R) hw hg hcg hsg
  let v : Space → ℝ := fun z => K/R^4-H z
  have hvc : Continuous v := continuous_const.sub hH
  have hvn : ∀ z ∈ closedBall (0 : Space) (3*(R/6)), 0 ≤ v z := by
    intro z hz
    have ht : ‖z‖ ≤ R/2 := by
      have he : 3*(R/6) = R/2 := by ring
      simpa only [he,mem_closedBall,dist_zero_right] using hz
    have hc := hcap z (by linarith)
    have hp := hpb z ht
    dsimp [v,H,K]
    rw [add_div]
    linarith
  have hvw : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      tsupport g ⊆ ball 0 (3*(R/6)) → (∫ z, v z*Δ g z) = 0 := by
    intro g hg hcg hsg
    apply weak_harmonic_upper_distance hH (K/R^4) hHw hg hcg
    convert hsg using 1
    congr 1
    ring
  have hv := harm v (R/6) (by linarith) hvc.continuousOn hvn hvw x (by linarith)
  have hv0 : v 0 ≤ K/R^4+max (-u 0) 0 := by
    have hp := hPn 0
    have hn0 := le_max_left (-u 0) 0
    dsimp [v,H]
    linarith
  have hneg : 0 ≤ max (-u 0) 0 := le_max_right _ _
  let Q : ℝ := R⁻¹^4+max (-u 0) 0
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb0 : v 0 ≤ (K+1)*Q := by
    apply hv0.trans
    dsimp [Q]
    rw [div_eq_mul_inv,←inv_pow]
    nlinarith [mul_nonneg hK hneg,pow_nonneg (inv_nonneg.mpr hR.le) 4]
  have hv' : |H x-H 0| ≤ (6*Ch*(K+1))/R*‖x‖*Q := by
    have he : v x-v 0 = -(H x-H 0) := by dsimp [v]; ring
    rw [he,abs_neg] at hv
    apply hv.trans
    calc
      _ ≤ Ch/(R/6)*‖x‖*((K+1)*Q) := mul_le_mul_of_nonneg_left hb0 (by positivity)
      _ = _ := by ring
  have hp' : |P x-P 0| ≤ E/R*‖x‖*Q := by
    apply hpd.trans
    calc
      _ = E/R*‖x‖*(R⁻¹^4) := by ring
      _ ≤ E/R*‖x‖*Q := mul_le_mul_of_nonneg_left (by dsimp [Q]; linarith) (by positivity)
  calc
    |u x-u 0| = |(H x-H 0)-(P x-P 0)| := by dsimp [H]; congr 1; ring
    _ ≤ |H x-H 0|+|P x-P 0| := abs_sub _ _
    _ ≤ (6*Ch*(K+1))/R*‖x‖*Q+E/R*‖x‖*Q := add_le_add hv' hp'
    _ ≤ C/R*‖x‖*Q := by
      dsimp [C]
      calc
        _ = (6*Ch*(K+1)+E)/R*‖x‖*Q := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hQ
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply div_le_div_of_nonneg_right _ hR.le
          linarith

theorem exists_weak_tf_oscillation_constant {k : ℝ} (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Space → ℝ) (R : ℝ), 0 < R →
      ContinuousOn u (closedBall 0 R) →
      (∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball 0 R →
        (∫ x, u x*Δ g x) = ∫ x, k*(max (u x) 0)^(3/2:ℝ)*g x) →
      ∀ x : Space, ‖x‖ ≤ R/12 →
        |u x-u 0| ≤ C/R*‖x‖*(R⁻¹^4+max (-u 0) 0) := by
  obtain ⟨C,hC,hbound⟩ := exists_global_weak_tf_oscillation_constant hk
  refine ⟨C,hC,?_⟩
  intro u R hR hu hw x hx
  let f : C(closedBall (0 : Space) R,ℝ) := ⟨_,hu.domRestrict⟩
  obtain ⟨v,hv⟩ := f.exists_restrict_eq isClosed_closedBall
  have he (z : Space) (hz : z ∈ closedBall (0 : Space) R) : v z = u z :=
    congrArg (fun h : C(closedBall (0 : Space) R,ℝ) => h ⟨z,hz⟩) hv
  have hh := hbound v R hR v.continuous (fun g hg hcg hs => ?_) x hx
  · simpa only [he x (by simpa only [mem_closedBall,dist_zero_right] using hx.trans (by linarith : R/12 ≤ R)),
      he 0 (mem_closedBall_self hR.le)] using hh
  · have hleft : (∫ z, v z*Δ g z) = ∫ z, u z*Δ g z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        by_cases hz : Δ g z = 0
        · simp only [hz,mul_zero]
        · change v z*Δ g z = u z*Δ g z
          rw [he z (ball_subset_closedBall (hs (tfLaplacian_support hg hz)))]
    rw [hleft,hw g hg hcg hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : g z = 0
      · simp only [hz,mul_zero]
      · change k*(max (u z) 0)^(3/2:ℝ)*g z = k*(max (v z) 0)^(3/2:ℝ)*g z
        rw [he z (ball_subset_closedBall (hs (subset_tsupport g hz)))]

end CoulombAnalysis

end

end OAI
