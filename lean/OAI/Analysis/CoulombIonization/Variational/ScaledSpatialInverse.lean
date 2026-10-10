import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.UniformNetErrorsBarrier
import OAI.Analysis.CoulombIonization.Variational.ScaledOriginalCap
import OAI.Analysis.CoulombIonization.RadialBounds.ExpandedAnnulusInverse

namespace OAI

open MeasureTheory Filter Set
open scoped Topology
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem exists_actual_scaled_spatial_inverse_constant {a c₁ lo hi xi : ℝ}
    (ha : 1/2 ≤ a) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        let v := a*u
        ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C*u^37 ∧
          ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
            (∀ y : Space, 11*v/8 ≤ ‖y‖ → ‖y‖ ≤ 13*v/8 → ∀ h ∈ Icc lo hi,
              (localTFResponse h < (localCellRadius y)^6*
                  originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
                h-xi ≤ (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
              ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
                  localTFResponse h →
                (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
            (∀ y : Space, 11*v/8 ≤ ‖y‖ → ‖y‖ ≤ 13*v/8 →
              (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                  16*(tfPatchCapConstant+3)) := by
  classical
  have ha0 : 0 < a := by linarith
  obtain ⟨T,D,L,A,hT,hD,hL,hA,hreg⟩ := exists_actual_scaled_original_regularity_constants ha hc hcL
  obtain ⟨H,hH,hheight⟩ := exists_inverse_height_net hlh hxi hlo
  obtain ⟨eta,heta,hmargin⟩ := exists_uniform_inverse_density_margin hlh hxi hlo
  let B : ℝ := 4096*(tfPatchCapConstant+2)
  let C : ℝ := 1+B+4*(H.card:ℝ)*4913/a^3
  have hB : 0 ≤ B := by dsimp [B]; linarith [tfPatchCapConstant_pos]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ι l r₀ s Z lam N K F δ hδ hs0 hr₀ hstate
  have has0 : Tendsto (fun i => a*s i) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := a)).mul hs0
  have hpoly : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      TailTiltState (Z i) (lam i) (r₀ i) (K i)
        (tailPolynomialThreshold (r₀ i)) δ (F i) := by
    filter_upwards [hr₀,hstate] with i hri hi'
    exact ⟨hi'.1,hi'.2.1,hi'.2.2.to_tailTiltState hri (tailPolynomialThreshold_pos hri)
      (fun _ => tinyProbabilityFloor_le_polynomial hi'.1 (by positivity))⟩
  have hinv : ∀ᶠ i in l, ∀ k ∈ H, ∀ (j : Fin (K i)) (y : Space),
      (2:ℝ)^j.val*r₀ i ≤ s i → ((2:ℝ)^j.val*r₀ i)/2 ≤ ‖y‖ →
      ‖y‖ ≤ (2*a)*((2:ℝ)^j.val*r₀ i) →
      OriginalPointInverseBounds (F i) (Z i) (lam i) (r₀ i) (s i) c₁ k (xi/4) j y := by
    apply (Filter.eventually_all_finset H).mpr
    intro k hk
    exact actual_expandedAnnulus_inverse_uniform_eventually (by linarith : 1 ≤ 2*a) hc hcL (by positivity)
      (by linarith [(hH k hk).1]) hδ hs0 hr₀ hpoly
  have heA := uniform_power_error_eventually (C := A*(16*(tfPatchCapConstant+3)*100000^4+D))
    (show 0 < 1-3*masterExponent by norm_num [masterExponent]) (show 0 < xi/4 by positivity) has0
  have heB := uniform_power_error_eventually (C := A) (a := (1:ℝ)) zero_lt_one zero_lt_one has0
  have heD := uniform_power_error_eventually (C := 64*L+192*D)
    (show 0 < 1-4*masterExponent by norm_num [masterExponent]) heta has0
  filter_upwards [hreg hδ hs0 hr₀ hstate,hinv,heA,heB,heD,hr₀,has0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    hs0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with i hri' hi' hAi hBi hDi hri hasi hsi
  intro j hjs
  let u := (2:ℝ)^j.val*r₀ i
  let v := a*u
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := hjs.trans hsi.le
  have hs : 0 < s i := hu.trans_le hjs
  have hv : 0 < v := mul_pos ha0 hu
  have hvs : v ≤ a*s i := mul_le_mul_of_nonneg_left hjs ha0.le
  have hv1 : v ≤ 1 := hvs.trans hasi.le
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_inverse_band_spatial_net hv hv1
  let E₀ := {z | T/u^3 < observedAnnularCount
    (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (6*a*u) z ∨
    1 < capBandStatistic v (tfPatchCapConstant+2)
      (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)}
  let E₁ := ⋃ k ∈ H, ⋃ x ∈ Q,
    originalLowFailure (F i) (Z i) (lam i) (r₀ i) (s i) c₁ k (xi/4) j x ∪
      originalHighFailure (F i) (Z i) (lam i) (r₀ i) (s i) c₁ k (xi/4) j x
  have hregi := hri' j hjs
  have hE₀ : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E₀ := hregi.1
  have hE₁ : MeasurableSet[observationInformation
      (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E₁ := by
    apply MeasurableSet.biUnion H.countable_toSet
    intro k hk
    apply MeasurableSet.biUnion Q.countable_toSet
    intro x hx
    exact original_inverse_failure_info_measurable (F i) (Z i) (lam i) (r₀ i) (s i) c₁
      k (xi/4) j x hc hri hs
  refine ⟨E₀ ∪ E₁,hE₀.union hE₁,?_,?_⟩
  · have hp₁ : (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E₁ ≤
        4*(H.card:ℝ)*(Q.card:ℝ)*u^40 := by
      apply original_inverse_height_net_union_bound Q H
      intro k hk x hx
      exact hi' k hk j x hjs (by have := (hQ x hx).1; dsimp [v] at this; nlinarith)
        (by have := (hQ x hx).2; dsimp [v] at this; nlinarith)
    have hp₁' : (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E₁ ≤
        (4*(H.card:ℝ)*4913/a^3)*u^37 := by
      apply hp₁.trans
      calc _ ≤ 4*(H.card:ℝ)*(4913/v^3)*u^40 := by gcongr
           _ = _ := by dsimp [v]; field_simp
    have hp40 : u^40 ≤ u^37 := pow_le_pow_of_le_one hu.le hu1 (by omega)
    have hp60 : u^60 ≤ u^37 := pow_le_pow_of_le_one hu.le hu1 (by omega)
    apply (measureReal_union_le _ _).trans
    calc _ ≤ (u^40+B*u^60)+(4*(H.card:ℝ)*4913/a^3)*u^37 := add_le_add hregi.2.1 hp₁'
         _ ≤ (u^37+B*u^37)+(4*(H.card:ℝ)*4913/a^3)*u^37 := by gcongr
         _ = C*u^37 := by dsimp [C]; ring
  · filter_upwards [hregi.2.2] with q hq
    intro hqE
    have hq0 : q ∉ E₀ := fun h => hqE (Or.inl h)
    have hq1 : q ∉ E₁ := fun h => hqE (Or.inr h)
    have hcount : observedAnnularCount
        (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j (u/8) (6*a*u) q ≤ T/u^3 :=
      le_of_not_gt (fun h => hq0 (Or.inl h))
    have hcap : capBandStatistic v (tfPatchCapConstant+2)
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q) ≤ 1 :=
      le_of_not_gt (fun h => hq0 (Or.inr h))
    obtain ⟨hden,hquery,hfield,hcapq⟩ := hq hcount hcap
    refine ⟨?_,fun y hyl hyh => hcapq y (by linarith) (by linarith)⟩
    exact original_spatial_inverse_propagation (F i) (Z i) (lam i) (r₀ i) (s i) c₁ j q
      hv hv1 hxi hlo hD hL hA.le H Q hQ hcover hmargin hheight
      (hAi v hv hvs) (by simpa using hBi v hv hvs) (hDi v hv hvs)
      hden hquery hfield hq1
end CoulombAtom

end

end OAI
