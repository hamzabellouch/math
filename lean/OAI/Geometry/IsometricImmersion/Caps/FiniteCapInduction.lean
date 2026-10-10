import OAI.Geometry.IsometricImmersion.Caps.VaryingCapInduction

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

def lowerCapMetricRequests {bStar : ℝ} : ℕ → LowerCapRectangle bStar →
    List (ℕ × LowerCapRectangle bStar)
  | 0, _ => []
  | k+1, r => (k+8,r.energyOuter)::(k+7,r)::lowerCapMetricRequests k r.energyOuter.expand

def FiniteCapMetricJets {bStar : ℝ} (g : MetricField) (Y : ℝ → ℝ → ℝ)
    (J : CapMetricJetBudget bStar) (L : List (ℕ × LowerCapRectangle bStar)) : Prop :=
  ∀ b ∈ L, ∀ (i j : Fin 2) (n : ℕ), n ≤ b.1+2 →
    ∀ p ∈ b.2.image Y, ‖iteratedFDeriv ℝ n (fun q => g q i j) p‖ ≤ J b.1 b.2

theorem lowerCapMetricRequests_length {bStar : ℝ} (k : ℕ) (r : LowerCapRectangle bStar) :
    (lowerCapMetricRequests k r).length = 2*k := by
  induction k generalizing r with
  | zero => rfl
  | succ k ih => simp only [lowerCapMetricRequests,List.length_cons,ih]; omega

theorem lowerCapMetricRequests_order_le {bStar : ℝ} (k : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapMetricRequests k r) : b.1 ≤ k+7 := by
  induction k generalizing r with
  | zero => simp [lowerCapMetricRequests] at hb
  | succ k ih =>
    simp only [lowerCapMetricRequests,List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · omega
    · omega
    · have h := ih r.energyOuter.expand hb
      omega

theorem lowerCapMetricRequests_full_order_le {bStar : ℝ} (k : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapMetricRequests k r) {n : ℕ} (hn : n ≤ b.1+2) : n ≤ k+9 := by
  have h := lowerCapMetricRequests_order_le k r b hb
  omega

theorem uniform_finite_varying_lowerCap_L2
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) :
    ∀ k : ℕ, ∀ r : LowerCapRectangle bStar,
      (∀ b ∈ lowerCapMetricRequests k r, 0 ≤ J b.1 b.2) → ∃ H : ℝ≥0,
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        FiniteCapMetricJets g Y J (lowerCapMetricRequests k r) → CoordinateL2Bound z (r.image Y) (k+8) H := by
  intro k
  induction k with
  | zero =>
    intro r hJ
    refine ⟨originalC8L2Budget Z, ?_⟩
    intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
    exact hh.original_L2 hU hSU hZ (hf.image_properties r).2.1 (hf.image_subset_square r)
  | succ k ih =>
    intro r hJ
    let T := r.energyOuter
    have hsourceRequest : (k+8,T) ∈ lowerCapMetricRequests (k+1) r := by
      simp [lowerCapMetricRequests,T]
    have hmixedRequest : (k+7,r) ∈ lowerCapMetricRequests (k+1) r := by
      simp [lowerCapMetricRequests]
    have htail : ∀ b, b ∈ lowerCapMetricRequests k T.expand →
        b ∈ lowerCapMetricRequests (k+1) r := by
      intro b hb
      change b ∈ (k+8,T)::(k+7,r)::lowerCapMetricRequests k T.expand
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb)
    obtain ⟨H, hH⟩ := ih T.expand (fun b hb => hJ b (htail b hb))
    obtain ⟨CR, hCR0, hCR⟩ := exists_localized_actualHighRemainder_bound
      G Z (J (k+8) T) hG hZ (hJ (k+8,T) hsourceRequest) hd hc (k+5) (by omega)
    obtain ⟨CP, hCP0, hCP⟩ := exists_same_region_solution_P_jet_bound
      (J (k+7) r) Z (hJ (k+7,r) hmixedRequest) hd hc (k+7)
    let M := heightQuotientJetBound G Z d c
    let B := max 1 ((squareSobolevWeight (flowInteriorRadius M T.margin T.margin)+1)*(H : ℝ))
    have hB : 1 ≤ B := le_max_left _ _
    let Rraw := actualHighRemainderL2Budget CR (heightPFirstBound G Z d c) B H modelSquare (k+5)
    have hRfinite : Rraw < (⊤ : ℝ≥0∞) := actualHighRemainderL2Budget_lt_top CR
      (heightPFirstBound G Z d c) B H modelSquare_isCompact.measure_lt_top (k+5)
    let RB : ℝ≥0 := Rraw.toNNReal
    have hRB : (RB : ℝ≥0∞) = Rraw := ENNReal.coe_toNNReal hRfinite.ne
    let Ccap := lowerCapConstant G Z d c e0 kappa (k+8) r
    have hCcap : 0 < Ccap := lowerCapConstant_pos G Z d c e0 kappa (k+8) r
    let Htop : ℝ≥0 := ⟨Real.sqrt (Ccap*((RB : ℝ)^2+(H : ℝ)^2)), Real.sqrt_nonneg _⟩
    have hTopSq : (Htop : ℝ)^2 = Ccap*((RB : ℝ)^2+(H : ℝ)^2) :=
      Real.sq_sqrt (mul_nonneg hCcap.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    refine ⟨uniformMixedOrderBudget CP B H Htop (k+9), ?_⟩
    intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
    have hlocalTail : FiniteCapMetricJets g Y J (lowerCapMetricRequests k T.expand) :=
      fun b hb => hlocal b (htail b hb)
    have hLarge : CoordinateL2Bound z (T.expand.image Y) (k+8) H := hH g U z Y W hg hU hSU hgB hdet hh hf hlocalTail
    have hT : CoordinateL2Bound z (T.image Y) (k+8) H :=
      hLarge.restrict (T.image_subset_expand Y)
    have hR : CoordinateL2Bound z (r.image Y) (k+8) H :=
      hT.restrict (r.image_subset_energyOuter Y)
    have hlowT0 : CoordinateBound z (T.image Y) (k+6)
        ((squareSobolevWeight (flowInteriorRadius M T.margin T.margin)+1)*(H : ℝ)) := by
      apply CapInductionFlow.pointwise_from_larger_L2 hh hf hG hZ hd hc T
      convert hLarge using 1
    have hlowT : CoordinateBound z (T.image Y) (k+6) B :=
      hlowT0.mono le_rfl (le_max_right _ _)
    obtain ⟨hTcompact, hTmeas, hTfinite, hTO⟩ := hf.image_properties T
    obtain ⟨hRcompact, hRmeas, hRfiniteImage, hRO⟩ := hf.image_properties r
    have hTS : T.image Y ⊆ modelSquare := hTO.trans modelOpenSquare_subset
    have hRS : r.image Y ⊆ modelSquare := hRO.trans modelOpenSquare_subset
    have hTU : T.image Y ⊆ U := hTS.trans hSU
    have hRU : r.image Y ⊆ U := hRS.trans hSU
    have hlowFactors : ∀ n j, n + heightStateBaseOrder j ≤ (k+5)+1 →
        ∀ p ∈ T.image Y, |heightStateFactor z n j p| ≤ B := by
      intro n j hn
      exact coordinateBound_heightFactors hlowT n j (by omega)
    have hL2Factors : ∀ n j, n + heightStateBaseOrder j ≤ (k+5)+3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict (T.image Y)) ≤ (H : ℝ≥0∞) := by
      intro n j hn
      exact hT.heightFactors_of_aestronglyMeasurable n j (by omega)
        (((heightStateFactor_contDiffOn hU hh.smooth n j).continuousOn.mono
          hTU).aestronglyMeasurable hTmeas)
    have hgHighT : ∀ i j n, n ≤ (k+5)+5 → ∀ p ∈ T.image Y,
        ‖iteratedFDeriv ℝ n (fun q => g q i j) p‖ ≤ J (k+8) T := by
      intro i j n hn p hp
      exact hlocal (k+8,T) hsourceRequest i j n (by omega) p hp
    obtain ⟨hsource, _, hsourceMem⟩ := hCR g z U (T.image Y) hg hU hSU hgB hdet
      hh.smooth hh.lowJet hh.denominator hTmeas hTS hTfinite hgHighT B hB H hlowFactors hL2Factors
    have hsourceRB : eLpNorm (actualHighRemainder g z (k+5)) 2
        (volume.restrict (T.image Y)) ≤ (RB : ℝ≥0∞) := by
      rw [hRB]
      exact hsource.trans (actualHighRemainderL2Budget_mono_area CR
        (heightPFirstBound G Z d c) B H (measure_mono hTS) (k+5))
    have hsourceIntegral : (∫ p in T.image Y, (actualHighRemainder g z (k+5) p)^2) ≤ (RB : ℝ)^2 :=
      integral_sq_le_of_eLpNorm_two_le hsourceMem hsourceRB
    have huIntegral : (∫ p in T.image Y, (verticalJet z (k+8) p)^2) ≤ (H : ℝ)^2 := by
      have hu := hT.integral_sq hh.smooth hU hTmeas hTU (List.replicate (k+8) 1) (by simp)
      simpa only [orderedPartial_replicate_y] using hu
    have hcap : (∫ p in r.image Y,
        (coordPartial 0 (verticalJet z (k+8)) p)^2+(verticalJet z (k+9) p)^2) ≤
        Ccap*((∫ p in T.image Y, (actualHighRemainder g z (k+5) p)^2)+
          (∫ p in T.image Y, (verticalJet z (k+8) p)^2)) := by
      simpa only [Nat.add_assoc, show 5+3=8 by omega, show 5+4=9 by omega] using hf.physicalEstimate (k+5) r
    have hgradient : (∫ p in r.image Y,
        (coordPartial 0 (verticalJet z (k+8)) p)^2+(verticalJet z (k+9) p)^2) ≤ (Htop : ℝ)^2 := by
      rw [hTopSq]
      exact hcap.trans (mul_le_mul_of_nonneg_left (add_le_add hsourceIntegral huIntegral) hCcap.le)
    have hxcont : ContinuousOn (coordPartial 0 (verticalJet z (k+8))) (r.image Y) :=
      ((partial_contDiffOn (verticalJet_contDiffOn hU hh.smooth (k+8)) hU 0).continuousOn).mono hRU
    have hycont : ContinuousOn (verticalJet z (k+9)) (r.image Y) :=
      (verticalJet_contDiffOn hU hh.smooth (k+9)).continuousOn.mono hRU
    have hparts := integral_each_sq_le_sum hRcompact hxcont hycont
    have hxTop : eLpNorm (coordPartial 0 (verticalJet z (k+8))) 2
        (volume.restrict (r.image Y)) ≤ (Htop : ℝ≥0∞) :=
      eLpNorm_two_le_of_integral_sq_le (compact_continuous_memLp_two hRcompact hxcont)
        (hparts.1.trans hgradient)
    have hyTop : eLpNorm (verticalJet z (k+9)) 2
        (volume.restrict (r.image Y)) ≤ (Htop : ℝ≥0∞) :=
      eLpNorm_two_le_of_integral_sq_le (compact_continuous_memLp_two hRcompact hycont)
        (hparts.2.trans hgradient)
    have hz2 : CoordinateBound z modelSquare 2 Z :=
      (coordinateBound_five_of_frechet_eight hh.smooth hU hSU hh.lowJet).mono (by norm_num) le_rfl
    have hP : ∀ n ≤ (k+9)-2, ∀ p ∈ r.image Y,
        ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ CP := by
      intro n hn p hp
      exact hCP g z U (r.image Y) hg hU hRU hRS
        (fun i j n hn p hp => hlocal (k+7,r) hmixedRequest i j n hn p hp)
        (hz2.restrict_domain hRS) (fun p hp => hdet p (hRS hp))
        (fun p hp => hh.denominator p (hRS hp)) n (by omega) p hp
    have hlowR : CoordinateBound z (r.image Y) ((k+9)-3) B := by
      intro word hword p hp
      exact hlowT word (by omega) p (r.image_subset_energyOuter Y hp)
    have hPrev : CoordinateL2Bound z (r.image Y) ((k+9)-1) H := by
      convert hR using 1
      omega
    have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
    have hgO : SmoothPositiveOn g modelOpenSquare :=
      ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
    have hDo : ∀ p ∈ modelOpenSquare,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p :=
      fun p hp => hh.darboux p (modelOpenSquare_subset hp)
    have hyyO : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
      fun p hp => LowQuotient.denominator_ne_zero hc hh.denominator p (modelOpenSquare_subset hp)
    have hfinal := coordinateL2Bound_order_step hgO modelOpenSquare_isOpen (hh.smooth.mono hOU)
      hDo hyyO hRmeas hRO hRS (by omega : 7 ≤ k+9) hCP0 hB hP hlowR hPrev hyTop
      (by simpa only [show (k+9)-1=k+8 by omega] using hxTop)
    convert hfinal using 1

end SmoothLocal.Flow

end

end OAI
