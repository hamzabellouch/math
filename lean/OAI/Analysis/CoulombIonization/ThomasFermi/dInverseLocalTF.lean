import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.OutwardBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter Set Metric
open scoped Topology

theorem exists_inverse_local_tf_parameters {k C hi ε : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C) (hhi : C+1 < hi) (hε : 0 < ε) :
    ∃ lo xi : ℝ, 0 < lo ∧ 0 < xi ∧ lo < hi ∧ C+xi < hi ∧
      ∀ {d H μ : ℝ}, 0 < d → 0 ≤ μ →
        InverseComparisonAt d H μ k lo hi xi C →
        |μ-k*(max H 0)^(3/2:ℝ)| < ε/d^6 := by
  let f : ℝ → ℝ := fun t => k*t^(3/2:ℝ)
  have hf : Continuous f := continuous_const.mul
    (continuous_id.rpow_const (fun _ => Or.inr (by norm_num)))
  have huc : UniformContinuousOn f (Icc 0 hi) := isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  let t : ℝ := min δ 1/4
  have ht : 0 < t := div_pos (lt_min hδ (by norm_num)) (by norm_num)
  have ht1 : t ≤ 1/4 := div_le_div_of_nonneg_right (min_le_right δ 1) (by norm_num)
  have htδ : 2*t < δ := by
    have hh := min_le_left δ 1
    dsimp only [t]
    nlinarith [lt_min hδ (by norm_num : (0:ℝ) < 1)]
  have hh : t < hi := by linarith
  have hgap : C+t < hi := by linarith
  refine ⟨t,t,ht,ht,hh,hgap,?_⟩
  intro d H μ hd hμ hinv
  let v := (d^6*μ/k)^(2/3:ℝ)
  have hs := inverse_comparison_density_height hμ hk ht.le hh ht.le hgap hinv
  have hvn : 0 ≤ v := Real.rpow_nonneg (by positivity) _
  have hvhi : v < hi := hs.1
  have humem : max (d^4*H) 0 ∈ Icc 0 hi :=
    ⟨le_max_right _ _,max_le (hinv.1.trans (by linarith)) (by linarith)⟩
  have hdv : dist v (max (d^4*H) 0) < δ := by
    rw [Real.dist_eq]
    exact hs.2.trans_lt (by linarith)
  have he := hδf v ⟨hvn,hvhi.le⟩ _ humem hdv
  have hvpow : f v = d^6*μ := by
    dsimp only [f,v]
    rw [rpow_inverse_three_halves (by positivity)]
    field_simp
  have hscale : max (d^4*H) 0 = d^4*max H 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg hd.le 4),mul_zero]
  have huval : f (max (d^4*H) 0) = d^6*(k*(max H 0)^(3/2:ℝ)) := by
    dsimp only [f]
    rw [hscale,scaled_positive_reaction hd.le (le_max_right H 0)]
    ring
  rw [Real.dist_eq,hvpow,huval,←mul_sub,abs_mul,abs_of_pos (pow_pos hd 6)] at he
  exact (lt_div_iff₀ (pow_pos hd 6)).mpr (by nlinarith)

lemma InverseComparisonAt.mono_tolerance {d H μ k lo hi xi xi' C : ℝ}
    (h : InverseComparisonAt d H μ k lo hi xi C) (hxi : xi ≤ xi') :
    InverseComparisonAt d H μ k lo hi xi' C := by
  refine ⟨h.1,?_,?_⟩
  · intro t ht hm
    linarith [h.2.1 t ht hm]
  · intro t ht hm
    linarith [h.2.2 t ht hm]

 theorem exists_inverse_local_tf_admissible_parameters {k C hi ε : ℝ}
    (hk : 0 < k) (hC : 0 ≤ C) (hhi : C+1 < hi) (hε : 0 < ε) :
    ∃ lo xi : ℝ, 0 < lo ∧ 0 < xi ∧ 16*xi < lo ∧ lo < hi ∧ C+xi < hi ∧
      ∀ {d H μ : ℝ}, 0 < d → 0 ≤ μ →
        InverseComparisonAt d H μ k lo hi xi C →
        |μ-k*(max H 0)^(3/2:ℝ)| < ε/d^6 := by
  obtain ⟨lo,xi,hlo,hxi,hlh,hgap,hTF⟩ := exists_inverse_local_tf_parameters hk hC hhi hε
  let xi' := min xi (lo/32)
  have hxi' : 0 < xi' := lt_min hxi (by positivity)
  have hle : xi' ≤ xi := min_le_left _ _
  have h16 : 16*xi' < lo := by
    have hh : xi' ≤ lo/32 := min_le_right _ _
    linarith
  exact ⟨lo,xi',hlo,hxi',h16,hlh,(by linarith : C+xi' < hi),
    fun hd hμ hinv => hTF hd hμ (hinv.mono_tolerance hle)⟩

end CoulombBarrier

open MeasureTheory Filter Set
open scoped Topology
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local instance] physicalObservationLaw_probability

 theorem exists_actual_annular_localTF_constant {B c ε : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c) (hcL : c < (10*(100000:ℝ))⁻¹) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ G : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] G ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real Gᶜ ≤ C*u^25 ∧
          ∀ q ∈ G, ∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
            |originalQueryDensity (F i) (r₀ i) j c (r₀ i) (s i) q y -
              tfDensityCoefficient*(max
                (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c (r₀ i) (s i) q y) 0)^(3/2:ℝ)|
              < ε/‖y‖^6 := by
  have hcap : 0 ≤ actualInverseCap := by
    have hh := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  obtain ⟨lo,xi,hlo,hxi,hsmall,hlh,hgap,hTF⟩ :=
    exists_inverse_local_tf_admissible_parameters tfDensityCoefficient_pos hcap
      (hi := actualInverseCap+2) (by linarith) hε
  obtain ⟨C,hC,hresult⟩ := exists_actual_fullAnnulus_good_constant hB hc hcL hlh.le hxi hsmall
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs hr hF
  have hgood := hresult hδ hs hr hF
  filter_upwards [hgood,hr] with i hi hri
  intro j hjs
  obtain ⟨G,hG,hprob,hcomp⟩ := hi j hjs
  refine ⟨G,hG,hprob,?_⟩
  intro q hq y hyl hyh
  have hy : 0 < ‖y‖ := (mul_pos (pow_pos (by norm_num) _) hri).trans_le hyl
  exact hTF hy (jointMasterPosterior_nonneg _ _ _ _ _ _ _ _ _) (hcomp q hq y hyl hyh)

end CoulombAtom

end

end OAI
