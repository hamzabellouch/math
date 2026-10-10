import OAI.Geometry.IsometricImmersion.Metrics.SmoothMetricRestriction
import OAI.Geometry.IsometricImmersion.Comparison.ComparisonCoefficientDerivative
import OAI.Geometry.IsometricImmersion.Darboux.QSameStripMargins

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem comparison_segment_direction_bound
    {P z : Coord → ℝ} {U T : Set Coord} {Z0 Z sigma : ℝ}
    (hU : IsOpen U) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hTU : T ⊆ U) (hPZ : CoordinateBound P T 3 Z0) (hzZ : CoordinateBound z T 3 Z)
    {p : Coord} (hp : p ∈ T) (hs : sigma ∈ Icc (0 : ℝ) 1) (j : Fin 2) :
    ‖(1-sigma) • coordPartial j (qSolutionJet P) p +
      sigma • coordPartial j (qSolutionJet z) p‖ ≤ max 1 Z0 + max 1 Z := by
  have h0 := coordPartial_qSolutionJet_norm_bound hU hP hTU hPZ hp j
  have h1 := coordPartial_qSolutionJet_norm_bound hU hz hTU hzZ hp j
  calc
    _ ≤ ‖(1-sigma) • coordPartial j (qSolutionJet P) p‖ +
        ‖sigma • coordPartial j (qSolutionJet z) p‖ := norm_add_le _ _
    _ = (1-sigma)*‖coordPartial j (qSolutionJet P) p‖ +
        sigma*‖coordPartial j (qSolutionJet z) p‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hs.2),abs_of_nonneg hs.1]
    _ ≤ (1-sigma)*max 1 Z0 + sigma*max 1 Z :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hs.2))
        (mul_le_mul_of_nonneg_left h1 hs.1)
    _ ≤ max 1 Z0 + max 1 Z := by
      have hn0 : 0 ≤ max 1 Z0 := zero_le_one.trans (le_max_left _ _)
      have hn1 : 0 ≤ max 1 Z := zero_le_one.trans (le_max_left _ _)
      exact add_le_add (mul_le_of_le_one_left hn0 (by linarith [hs.1]))
        (mul_le_of_le_one_left hn1 hs.2)

theorem exists_uniform_comparison_coefficient_bounds
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P z : Coord → ℝ) (V T : Set Coord),
      IsOpen V → V ⊆ U → ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V → T ⊆ S → T ⊆ V →
      (∀ p ∈ T, ‖p‖ ≤ R) → CoordinateBound P T 3 Z0 → CoordinateBound z T 3 Z →
      (∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator g (qHeightJetSegment P z sigma p)|) →
      ∀ i : Fin 6, ∀ p ∈ T,
        |comparisonCoefficient g P z i p| ≤ C ∧
        ∀ j : Fin 2, |coordPartial j (comparisonCoefficient g P z i) p| ≤
          C*(max 1 Z0+max 1 Z) := by
  classical
  let A := max R (max Z0 Z)
  choose C0 hC0 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 0
  choose C1 hC1 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 1
  let C := 1 + ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i))
  have hnon (i : Fin 6) : 0 ≤ max 0 (C0 i)+max 0 (C1 i) := by positivity
  have hCle : 1 ≤ C := by
    have hs : 0 ≤ ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i)) :=
      Finset.sum_nonneg (fun i _ => hnon i)
    dsimp [C]
    linarith
  have hC0le (i : Fin 6) : C0 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C0 i),le_max_left 0 (C1 i)]
  have hC1le (i : Fin 6) : C1 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C1 i),le_max_left 0 (C0 i)]
  refine ⟨C,hCle,?_⟩
  intro P z V T hV hVU hP hz hTS hTV hpB hPZ hzZ hfloor i p hp
  have hgV : SmoothPositiveOn g V := hg.mono hVU
  have h0 : ‖qSolutionJet P p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hPZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_left _ _))
  have h1 : ‖qSolutionJet z p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hzZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_right _ _))
  have htube (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ qCompactTube g S A c := by
    refine ⟨⟨?_,?_⟩,hfloor p hp sigma hs⟩
    · change statePoint (qHeightJetSegment P z sigma p) ∈ S
      rw [statePoint_qHeightJetSegment]
      exact hTS hp
    · have hb := stateSegment_coord_bound hs
        (fun j => (norm_le_pi_norm (qSolutionJet P p) j).trans h0)
        (fun j => (norm_le_pi_norm (qSolutionJet z p) j).trans h1)
      exact ⟨fun j => (abs_le.mp (hb j)).1,fun j => (abs_le.mp (hb j)).2⟩
  have hseg (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g V := by
    have hd := qCompactTube_subset_domain hSU A hc (htube sigma hs)
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hTV hp,hd.2⟩
  have hval (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      |qFirstCoefficient g i (qHeightJetSegment P z sigma p)| ≤ C := by
    have hb := (hC0 i _ (htube sigma hs)).trans (hC0le i)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb
  have hder (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using (hC1 i _ (htube sigma hs)).trans (hC1le i)
  constructor
  · change ‖∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (qHeightJetSegment P z sigma p)‖ ≤ C
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun sigma => qFirstCoefficient g i (qHeightJetSegment P z sigma p)) (by
        intro sigma hs
        have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
        exact hval sigma ⟨hs0.1.le,hs0.2⟩)
    simpa only [sub_zero,abs_one,mul_one] using hb
  · intro j
    obtain ⟨W,hW,hpW,hWU,hWseg,_⟩ := exists_comparison_coefficient_neighborhood
      hgV hV hP hz isCompact_singleton (singleton_subset_iff.mpr (hTV hp))
      (fun _ hq sigma hs => by simpa only [mem_singleton_iff.mp hq] using hseg sigma hs)
    rw [comparisonCoefficient_partial hgV hV hP hz hW hWU hWseg (hpW (mem_singleton p)) i j,
      ← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C*(max 1 Z0+max 1 Z)) (f := fun sigma =>
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p+sigma • coordPartial j (qSolutionJet z) p)) ?_
    · simpa only [sub_zero,abs_one,mul_one] using hb
    intro sigma hs
    have hs' : sigma ∈ Icc (0 : ℝ) 1 := by
      have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
      exact ⟨hs0.1.le,hs0.2⟩
    exact ((fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)).le_opNorm _).trans
      (mul_le_mul (hder sigma hs')
        (comparison_segment_direction_bound hV hP hz hTV hPZ hzZ hp hs' j)
        (norm_nonneg _) (zero_le_one.trans hCle))

end SmoothLocal.HighEquation

end

end OAI
