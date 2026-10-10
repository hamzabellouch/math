import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.FullAnnulusGoodEvent
import OAI.Analysis.CoulombIonization.RadialBounds.FiniteBarrier

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

theorem actual_outward_barrier_eventually {c : ℝ} (hc : 0 < c)
    (hcL : c < (10*(100000:ℝ))⁻¹) :
    ∃ ε B C M D : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < B ∧ 2 < M ∧ 0 ≤ D ∧
      ∀ {ι : Type*} {l : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N K : ι → ℕ),
        (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s l (𝓝 0) →
        Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop →
        (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
        ∃ F : ∀ i, fermionGraph (N i),
          (∀ i, OwnProbabilityTailTiltState (Z i) ((s i)^(-4:ℝ)) (ε*(Z i:ℝ)^(-1/3:ℝ)) (K i)
            (fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*(ε*(Z i:ℝ)^(-1/3:ℝ)))) 1 (F i)) ∧
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
  intro ι l Z s N K hZ hs hs0 hscale hN
  let r : ι → ℝ := fun i => ε*(Z i:ℝ)^(-1/3:ℝ)
  have hZp (i) : 0 < (Z i:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hZ i))
  have hr (i) : 0 < r i := mul_pos hε (Real.rpow_pos_of_pos (hZp i) _)
  choose F hF using fun i => exists_actual_own_probability_tail_tilt_state
    (Nat.cast_nonneg (Z i)) (hr i) (hN i) (K i)
    (fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*r i))
    (fun j => tinyProbabilityFloor_pos (Nat.cast_nonneg (Z i))
      (mul_pos (pow_pos (by norm_num) _) (hr i)))
    (by norm_num : (0:ℝ) < 1)
  refine ⟨F,hF,?_⟩
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

end

open MeasureTheory Filter Set Metric
open scoped Topology

theorem inverse_height_squeeze {u v lo hi xi C : ℝ}
    (hv : 0 ≤ v) (hlo : 0 ≤ lo) (hlh : lo < hi) (hxi : 0 ≤ xi)
    (hcap : u ≤ C) (hgap : C+xi < hi)
    (hhigh : ∀ h ∈ Icc lo hi, h < v → h-xi ≤ u)
    (hlow : ∀ h ∈ Icc lo hi, v < h → u ≤ h+xi) :
    v < hi ∧ |v-max u 0| ≤ lo+xi := by
  have hvhi : v < hi := by
    by_contra hn
    have hb : max lo (C+xi) < hi := max_lt hlh hgap
    obtain ⟨h,hh₁,hh₂⟩ := exists_between hb
    have hvh : h < v := hh₂.trans_le (le_of_not_gt hn)
    have hh := hhigh h ⟨(le_max_left _ _).trans hh₁.le,hh₂.le⟩ hvh
    have hCh : C+xi < h := (le_max_right _ _).trans_lt hh₁
    linarith
  have hlower : v ≤ max u 0+lo+xi := by
    by_cases hvlo : v ≤ lo
    · linarith [le_max_right u 0]
    · have hvlo' : lo < v := lt_of_not_ge hvlo
      by_cases hvu : v ≤ u+xi
      · linarith [le_max_left u 0]
      · have hmax : max lo (u+xi) < v := max_lt hvlo' (lt_of_not_ge hvu)
        obtain ⟨h,hh₁,hh₂⟩ := exists_between hmax
        have hh := hhigh h ⟨(le_max_left _ _).trans hh₁.le,(hh₂.trans hvhi).le⟩ hh₂
        have huh : u+xi < h := (le_max_right _ _).trans_lt hh₁
        linarith
  have hupper : max u 0 ≤ v+lo+xi := by
    apply max_le _ (by linarith)
    have hu : u ≤ max v lo+xi := by
      by_contra hn
      have hmaxu : max v lo < u-xi := by linarith [lt_of_not_ge hn]
      have hmaxhi : max v lo < hi := max_lt hvhi hlh
      obtain ⟨h,hh₁,hh₂⟩ := exists_between (lt_min hmaxu hmaxhi)
      have hh := hlow h ⟨(le_max_right _ _).trans hh₁.le,(lt_min_iff.mp hh₂).2.le⟩
        ((le_max_left _ _).trans_lt hh₁)
      linarith [(lt_min_iff.mp hh₂).1]
    have hm : max v lo ≤ v+lo := max_le (by linarith) (by linarith)
    linarith
  exact ⟨hvhi,abs_le.mpr ⟨by linarith,by linarith⟩⟩

lemma rpow_inverse_three_halves {x : ℝ} (hx : 0 ≤ x) :
    (x^(2/3:ℝ))^(3/2:ℝ) = x := by
  rw [←Real.rpow_mul hx]
  norm_num

theorem inverse_comparison_density_height {d H μ k lo hi xi C : ℝ}
    (hμ : 0 ≤ μ) (hk : 0 < k)
    (hlo : 0 ≤ lo) (hlh : lo < hi) (hxi : 0 ≤ xi) (hgap : C+xi < hi)
    (hinv : InverseComparisonAt d H μ k lo hi xi C) :
    let v := (d^6*μ/k)^(2/3:ℝ)
    v < hi ∧ |v-max (d^4*H) 0| ≤ lo+xi := by
  let v := (d^6*μ/k)^(2/3:ℝ)
  have hx : 0 ≤ d^6*μ/k := by positivity
  have hv : 0 ≤ v := Real.rpow_nonneg hx _
  have he : k*v^(3/2:ℝ) = d^6*μ := by
    dsimp only [v]
    rw [rpow_inverse_three_halves hx]
    field_simp
  apply inverse_height_squeeze hv hlo hlh hxi hinv.1 hgap
  · intro t ht htv
    apply hinv.2.1 t ht
    rw [←he]
    exact mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow (hlo.trans ht.1) htv (by norm_num)) hk
  · intro t ht hvt
    apply hinv.2.2 t ht
    rw [←he]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hv hvt (by norm_num)) hk

end CoulombBarrier

end

end OAI
