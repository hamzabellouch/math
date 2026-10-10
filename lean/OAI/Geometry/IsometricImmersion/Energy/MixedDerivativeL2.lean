import OAI.Geometry.IsometricImmersion.Energy.MixedRemainderL2

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem word_no_x_eq_replicate (ds : List (Fin 2)) (hx : ds.count 0 = 0) :
    ds = List.replicate ds.length 1 := by
  apply List.eq_replicate_iff.mpr
  refine ⟨rfl, ?_⟩
  intro i hi
  fin_cases i
  · have hpos : 0 < ds.count 0 := List.count_pos_iff.mpr hi
    omega
  · rfl

theorem orderedPartial_replicate_y (z : Coord → ℝ) (n : ℕ) :
    iteratedCoordPartial (List.replicate n 1) z = verticalJet z n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, iteratedCoordPartial, verticalJet, ih]

theorem orderedPartial_at_most_one_x_eLpNorm
    {z : Coord → ℝ} {U V : Set Coord} (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} {Htop : ℝ≥0}
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
      (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) (hx : ds.count 0 ≤ 1) :
    eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞) := by
  by_cases hzcount : ds.count 0 = 0
  · rw [word_no_x_eq_replicate ds hzcount, orderedPartial_replicate_y, hlen]
    exact hv
  · have hcount : ds.count 0 = 1 := by omega
    have hmem : (0 : Fin 2) ∈ ds := List.count_pos_iff.mp (by omega)
    have hperm := List.perm_cons_erase hmem
    have herase : (ds.erase 0).count 0 = 0 := by
      rw [List.count_erase_self, hcount]
    have heraseLen : (ds.erase 0).length = N - 1 := by
      have h := hperm.length_eq
      simp only [List.length_cons] at h
      omega
    have he : iteratedCoordPartial ds z =ᵐ[volume.restrict V]
        coordPartial 0 (verticalJet z (N - 1)) := by
      filter_upwards [ae_restrict_mem hV] with p hp
      have h := orderedPartial_perm hz hU hperm p (hVU hp)
      rw [word_no_x_eq_replicate (ds.erase 0) herase, heraseLen] at h
      simpa only [iteratedCoordPartial, orderedPartial_replicate_y] using h
    rw [eLpNorm_congr_ae he]
    exact hxv

theorem principal_mixed_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    |2 * hessianQuotient g z p| ≤
      ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single 4 (1 : ℝ))
  simpa only [sixVariableP_mixed_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

theorem principal_yy_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    |-((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p)| ≤
      ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single 5 (1 : ℝ))
  simpa only [sixVariableP_yy_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

theorem ordered_mixed_eLpNorm_step
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N - 3) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ N - 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) (hx : 2 ≤ ds.count 0) :
    ∃ es : List (Fin 2), es.length + 2 = N ∧
      (es ++ [0, 1]).count 0 < ds.count 0 ∧
      (es ++ [1, 1]).count 0 < ds.count 0 ∧
      eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤
        ‖C‖ₑ * eLpNorm (iteratedCoordPartial (es ++ [0, 1]) z) 2 (volume.restrict V) +
        ‖C‖ₑ * eLpNorm (iteratedCoordPartial (es ++ [1, 1]) z) 2 (volume.restrict V) +
        mixedRemainderL2Budget C B H V (N - 2) := by
  obtain ⟨es, hperm⟩ := word_two_x_permutation ds hx
  have heslen : es.length + 2 = N := by simpa [hlen] using hperm.length_eq.symm
  have hesN : es.length = N - 2 := by omega
  have hes : 5 ≤ es.length := by omega
  have hc := hperm.count_eq (0 : Fin 2)
  obtain ⟨_, _, hxy, hyyc⟩ := mixed_principal_word_orders es
  refine ⟨es, heslen, ?_, ?_, ?_⟩
  · simpa only [hc] using hxy
  · simpa only [hc] using hyyc
  let a : Coord → ℝ := fun p => 2 * hessianQuotient g z p
  let b : Coord → ℝ := fun p =>
    -((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p)
  let f : Coord → ℝ := iteratedCoordPartial (es ++ [0, 1]) z
  let h : Coord → ℝ := iteratedCoordPartial (es ++ [1, 1]) z
  let R : Coord → ℝ := mixedFaaRemainder g z (by omega) (coordinateDirections es)
  have haS : ContinuousOn a U :=
    continuousOn_const.mul (hessianQuotient_contDiffOn hg hU hz hyy).continuousOn
  have hbS : ContinuousOn b U :=
    (((hessianQuotient_contDiffOn hg hU hz hyy).continuousOn.pow 2).add
      ((gaussianCurvature_contDiffOn hg hU).continuousOn.mul
        (darbouxG_contDiffOn hg hU hz hyy).continuousOn)).neg
  have haf : AEStronglyMeasurable (fun p => a p * f p) (volume.restrict V) :=
    ((haS.mul (orderedPartial_contDiffOn hz hU (es ++ [0, 1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hbh : AEStronglyMeasurable (fun p => b p * h p) (volume.restrict V) :=
    ((hbS.mul (orderedPartial_contDiffOn hz hU (es ++ [1, 1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hafB : eLpNorm (fun p => a p * f p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm f 2 (volume.restrict V) :=
    scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (fun p hp =>
      (principal_mixed_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp))).trans
        (hP 1 (by omega) p hp)) haf
  have hbhB : eLpNorm (fun p => b p * h p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm h 2 (volume.restrict V) :=
    scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (fun p hp =>
      (principal_yy_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp))).trans
        (hP 1 (by omega) p hp)) hbh
  have hRB : eLpNorm R 2 (volume.restrict V) ≤ mixedRemainderL2Budget C B H V (N - 2) := by
    have hP' : ∀ n ≤ es.length, ∀ p ∈ V,
        ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C := by
      simpa only [hesN] using hP
    have hlo' : CoordinateBound z V (es.length - 1) B := by
      convert hlow using 1
      omega
    have hh' : ∀ fs : List (Fin 2), fs.length ≤ es.length + 1 →
        eLpNorm (iteratedCoordPartial fs z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
      fun fs hfs => hheight fs (by omega)
    simpa only [hesN] using
      mixedFaaRemainder_eLpNorm_two hg hU hz hyy hV hVU es hes hC hB hP' hlo' hh'
  have he : iteratedCoordPartial ds z =ᵐ[volume.restrict V]
      (fun p => (a p * f p + b p * h p) + R p) := by
    filter_upwards [ae_restrict_mem hV] with p hp
    have he := (orderedPartial_perm hz hU hperm p (hVU hp)).trans
      (actualDarboux_ordered_mixed_elimination hg hU hz hD hyy (hVU hp) es (by omega))
    dsimp only [a, b, f, h, R]
    simpa only [neg_mul, sub_eq_add_neg] using he
  rw [eLpNorm_congr_ae he]
  have he1 := eLpNorm_add_le
    (f := fun point => a point * f point) (g := fun point => b point * h point)
    (μ := volume.restrict V) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he2 := eLpNorm_add_le
    (f := fun point => a point * f point + b point * h point) (g := R)
    (μ := volume.restrict V) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact he2.trans (add_le_add (he1.trans (add_le_add hafB hbhB)) hRB)

def mixedXBudget (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => (Htop : ℝ≥0∞) + R
  | n + 1 => (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n

theorem mixedXBudget_monotone (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) :
    Monotone (mixedXBudget C R Htop) := by
  apply monotone_nat_of_le_succ
  intro n
  have h : (1 : ℝ≥0∞) ≤ 1 + ‖C‖ₑ + ‖C‖ₑ :=
    (le_add_of_nonneg_right (by positivity)).trans (le_add_of_nonneg_right (by positivity))
  calc
    mixedXBudget C R Htop n = 1 * mixedXBudget C R Htop n := (one_mul _).symm
    _ ≤ (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n := mul_le_mul' h le_rfl
    _ = mixedXBudget C R Htop (n + 1) := rfl

theorem mixedXBudget_base_le (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) (n : ℕ) :
    (Htop : ℝ≥0∞) + R ≤ mixedXBudget C R Htop n :=
  mixedXBudget_monotone C R Htop (Nat.zero_le n)

theorem mixedXBudget_step (C : ℝ) (R : ℝ≥0∞) (Htop : ℝ≥0) (n : ℕ)
    {a b : ℝ≥0∞} (ha : a ≤ mixedXBudget C R Htop n)
    (hb : b ≤ mixedXBudget C R Htop n) :
    ‖C‖ₑ * a + ‖C‖ₑ * b + R ≤ mixedXBudget C R Htop (n + 1) := by
  have hR : R ≤ mixedXBudget C R Htop n :=
    (le_add_of_nonneg_left (by positivity)).trans (mixedXBudget_base_le C R Htop n)
  calc
    _ ≤ ‖C‖ₑ * mixedXBudget C R Htop n +
        ‖C‖ₑ * mixedXBudget C R Htop n + mixedXBudget C R Htop n :=
      add_le_add (add_le_add (mul_le_mul' le_rfl ha) (mul_le_mul' le_rfl hb)) hR
    _ = mixedXBudget C R Htop (n + 1) := by rw [mixedXBudget]; ring

theorem mixedXBudget_lt_top (C : ℝ) {R : ℝ≥0∞} (hR : R < (⊤ : ℝ≥0∞))
    (Htop : ℝ≥0) (n : ℕ) : mixedXBudget C R Htop n < (⊤ : ℝ≥0∞) := by
  induction n with
  | zero => simpa only [mixedXBudget] using ENNReal.add_lt_top.mpr ⟨by finiteness, hR⟩
  | succ n ih =>
      change (1 + ‖C‖ₑ + ‖C‖ₑ) * mixedXBudget C R Htop n < (⊤ : ℝ≥0∞)
      exact ENNReal.mul_lt_top (by finiteness) ih

theorem all_orderN_mixed_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N - 3) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ N - 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
      (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) :
    eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤
      mixedXBudget C (mixedRemainderL2Budget C B H V (N - 2)) Htop N := by
  let R := mixedRemainderL2Budget C B H V (N - 2)
  have hind : ∀ j : ℕ, ∀ es : List (Fin 2), es.length = N → es.count 0 = j →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ mixedXBudget C R Htop j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro es hes hecount
      by_cases hj : j ≤ 1
      · exact (orderedPartial_at_most_one_x_eLpNorm hU hz hV hVU hv hxv es hes
          (by omega)).trans ((le_add_of_nonneg_right (by positivity)).trans
            (mixedXBudget_base_le C R Htop j))
      · obtain ⟨fs, hflen, hfc0, hfc1, hstep⟩ := ordered_mixed_eLpNorm_step
          hg hU hz hD hyy hV hVU hN hC hB hP hlow hheight es hes (by omega)
        have hlen0 : (fs ++ [0, 1]).length = N := by simpa using hflen
        have hlen1 : (fs ++ [1, 1]).length = N := by simpa using hflen
        have hb0 := ih ((fs ++ [0, 1]).count 0) (by omega) (fs ++ [0, 1]) hlen0 rfl
        have hb1 := ih ((fs ++ [1, 1]).count 0) (by omega) (fs ++ [1, 1]) hlen1 rfl
        have hb0' := hb0.trans (mixedXBudget_monotone C R Htop (by omega :
          (fs ++ [0, 1]).count 0 ≤ j - 1))
        have hb1' := hb1.trans (mixedXBudget_monotone C R Htop (by omega :
          (fs ++ [1, 1]).count 0 ≤ j - 1))
        have hsum := hstep.trans (mixedXBudget_step C R Htop (j - 1) hb0' hb1')
        simpa only [show j - 1 + 1 = j by omega] using hsum
  exact (hind (ds.count 0) ds hlen rfl).trans
    (mixedXBudget_monotone C R Htop (hlen ▸ List.count_le_length))

theorem all_orderN_mixed_memLp_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V < (⊤ : ℝ≥0∞))
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N - 3) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ N - 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
      (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) :
    MemLp (iteratedCoordPartial ds z) 2 (volume.restrict V) := by
  exact (all_orderN_mixed_eLpNorm_two hg hU hz hD hyy hV hVU hN hC hB hP hlow hheight
    hv hxv ds hlen).trans_lt (mixedXBudget_lt_top C
      (mixedRemainderL2Budget_lt_top C B H hVfinite (N - 2)) Htop N)

end SmoothLocal.HighEquation

end

end OAI
