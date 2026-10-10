import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.FullAnnulusGoodEvent
import OAI.Analysis.CoulombIonization.RadialBounds.ExteriorScreenNumerics

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set
open scoped Topology
open CoulombAtom CoulombAnalysis

def selectedTailThreshold (s : ℝ) : ℝ := (actualScreenConstant+1)*s
lemma selectedTailThreshold_pos {s : ℝ} (hs : 0 < s) : 0 < selectedTailThreshold s :=
  mul_pos (by linarith [actualScreenConstant_nonneg]) hs
lemma selectedTailThreshold_tendsto {ι : Type*} {F : Filter ι} {s : ι → ℝ}
    (hs : Tendsto s F (𝓝 0)) : Tendsto (fun i => selectedTailThreshold (s i)) F (𝓝 0) := by
  simpa only [selectedTailThreshold,mul_zero] using hs.const_mul (actualScreenConstant+1)
lemma selectedTail_ratio {s : ℝ} (hs : 0 < s) :
    (actualScreenConstant*s^2)/selectedTailThreshold s ≤ s := by
  apply (div_le_iff₀ (selectedTailThreshold_pos hs)).mpr
  unfold selectedTailThreshold
  nlinarith only [sq_nonneg s]

lemma selection_budget_eventually {ι : Type*} {F : Filter ι} {s : ι → ℝ}
    (hs : ∀ i, 0 < s i) (hs0 : Tendsto s F (𝓝 0)) (D A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ i in F, ∀ u : ℝ, 0 ≤ u → u ≤ s i →
      5184*(s i)^32+D*(s i)^barrierErrorExponent+
        (actualScreenConstant*(s i)^2)/selectedTailThreshold (s i)+A*u^25 < 1 := by
  have hh : Tendsto (fun i => 5184*(s i)^32+D*(s i)^barrierErrorExponent+s i+A*(s i)^25) F (𝓝 0) := by
    have ha := (hs0.pow 25).const_mul A
    simpa only [zero_pow (by norm_num : (25:ℕ) ≠ 0),mul_zero,add_zero] using
      ((total_barrier_budget_tendsto_zero hs0 D).add hs0).add ha
  filter_upwards [hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hi u hu hus
  have hratio := selectedTail_ratio (hs i)
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hus 25) hA
  linarith

lemma price_scale_inverse {s : ℝ} (hs : 0 < s) : s^(-4:ℝ) = 1/s^4 := by
  rw [Real.rpow_neg hs.le,show (4:ℝ) = (4:ℕ) by norm_num,Real.rpow_natCast,one_div]

end
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

theorem actual_outward_barrier_given_state_eventually {c : ℝ} (hc : 0 < c)
    (hcL : c < (10*(100000:ℝ))⁻¹) :
    ∃ ε B C M D : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < B ∧ 2 < M ∧ 0 ≤ D ∧
      ∀ {ι : Type*} {l : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N K : ι → ℕ),
        (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s l (𝓝 0) →
        Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop →
        (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
        ∀ F : ∀ i, fermionGraph (N i),
          (∀ i, OwnProbabilityTailTiltState (Z i) ((s i)^(-4:ℝ)) (ε*(Z i:ℝ)^(-1/3:ℝ)) (K i)
            (fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*(ε*(Z i:ℝ)^(-1/3:ℝ)))) 1 (F i)) →
          ∀ᶠ i in l, ∀ J : ℕ, J ≤ K i → (2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ)) ≤ s i →
            ∃ a p : (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) → TFSpace → ℝ,
              IsNuclearBarrier (physicalObservationLaw (graphRawLaw (F i)) (K i))
                (originalQueryDensity (F i) (ε*(Z i:ℝ)^(-1/3:ℝ)) J c (ε*(Z i:ℝ)^(-1/3:ℝ)) (s i))
                (Z i:ℝ) tfDensityCoefficient B C ((2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ))) M
                (5184*(s i)^32+D*(s i)^barrierErrorExponent) a p := by
  classical
  obtain ⟨ε,hε,hε1,hed,hq⟩ := exists_barrier_epsilon tfDensityCoefficient
  obtain ⟨B,hB,hBs,hsub⟩ := exists_barrier_B (k := tfDensityCoefficient) hε
  let C := max (max B (32*ε^3)) actualInverseCap
  have hBC : B ≤ C := (le_max_left B _).trans (le_max_left _ _)
  have hCinit : max B (32*ε^3) ≤ C := le_max_left _ _
  have hCcap : actualInverseCap ≤ C := le_max_right _ _
  obtain ⟨M,lam1,lam2,e,ξ,hl,hh,cal,hξ,hhl,hlh⟩ :=
    exists_fullAnnulus_outward_calibration tfDensityCoefficient_pos.le hB hBC hsub
  obtain ⟨A,hA,hgood⟩ := exists_actual_fullAnnulus_good_constant
    (B := 4*M) (by linarith [cal.M_large]) hc hcL hlh hξ hhl
  obtain ⟨Q,hQ,hmoment⟩ := actual_original_posterior_moment
    canonicalRealPacket_smooth.continuous canonicalRealPacket_support hc hcL
  let D := 32*Real.pi/3*Real.sqrt A*Real.sqrt Q
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨ε,B,C,M,D,hε,hε1,hB,cal.M_large,hD,?_⟩
  intro ι l Z s N K hZ hs hs0 hscale hN F hF
  let r : ι → ℝ := fun i => ε*(Z i:ℝ)^(-1/3:ℝ)
  have hZp (i) : 0 < (Z i:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hZ i))
  have hr (i) : 0 < r i := mul_pos hε (Real.rpow_pos_of_pos (hZp i) _)
  obtain ⟨z,hz⟩ := (canonicalRealPacket_smooth.continuous.pow 2).norm.exists_forall_ge_of_hasCompactSupport
    canonicalRealPacket_compact.mul_left.norm
  let G : ℝ := ‖(canonicalRealPacket z)^2‖
  have hG (y : Space) : (canonicalRealPacket y)^2 ≤ G := by
    rw [←Real.norm_of_nonneg (sq_nonneg (canonicalRealPacket y))]
    exact hz y
  have hnum := initial_numerics_eventually Z s (Filter.Eventually.of_forall hZ) (Filter.Eventually.of_forall hs)
    hs0 hscale hε G c 1
  have hgood' := hgood (r₀ := r) (s := s) (Z := fun i => (Z i:ℝ))
    (lam := fun i => (s i)^(-4:ℝ)) (N := N) (K := K) (F := F)
    (by norm_num : (0:ℝ) ≤ 1) hs0 (Filter.Eventually.of_forall hr)
    (Filter.Eventually.of_forall (fun i => ⟨(Nat.cast_nonneg (Z i)),Real.rpow_pos_of_pos (hs i) _,hF i⟩))
  have hc1 : c ≤ 1/2 := by linarith
  filter_upwards [hnum,hgood'] with i hi hgi
  intro J hJK hJs
  obtain ⟨a,p,hinit⟩ := own_state_initial_barrier hi hc hc1 hε hε1.le
    tfDensityCoefficient_pos.le hB hed hq hBs hsub hG (hN i) (hF i)
  have hm (j : ℕ) {v : ℝ} (hv : r i ≤ v) (hvs : v ≤ s i) (y : Space)
      (hy : v ≤ ‖y‖) (hy' : ‖y‖ ≤ 2*v) :
      (∫ q, (originalQueryDensity (F i) (r i) j c (r i) (s i) q y)^2
        ∂physicalObservationLaw (graphRawLaw (F i)) (K i)) ≤ Q*v^(-12-6*masterExponent) :=
    hmoment (Nat.cast_nonneg (Z i)) (Real.rpow_pos_of_pos (hs i) _) (hN i) (F i)
      (hF i).1 (hF i).2.1 (fun k => dyadicObservationWidth (r i) k) j
      (hr i) (hs i) hi.scale_le hv hvs y hy hy'
  obtain ⟨a',p',hnew⟩ := actual_finite_barrier_from_good (Nat.cast_nonneg (Z i))
    (Real.rpow_pos_of_pos (hs i) _) (hr i) (hs i) hi.scale_le hi.radius_scale hc hcL
    (hN i) (hF i).1 (hF i).2.1 cal hCcap hA.le hQ hm (hinit.mono_cap hCinit) hgi J hJK hJs
  refine ⟨a',p',?_⟩
  rw [max_eq_right cal.M_large.le] at hnew
  exact hnew.mono_budget (add_le_add (initial_budget_le_final_radius (hr i).le hi.radius_scale) le_rfl)

end CoulombBarrier

end

end OAI
