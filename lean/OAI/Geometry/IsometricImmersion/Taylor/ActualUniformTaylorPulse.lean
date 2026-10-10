import OAI.Geometry.IsometricImmersion.Caps.ActualOffPulseCauchy
import OAI.Geometry.IsometricImmersion.Pulses.ReferencePulseEdgeInitial
import OAI.Geometry.IsometricImmersion.Taylor.TaylorInitialStateBound
import OAI.Geometry.IsometricImmersion.Taylor.UniformTaylorPulse

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_taylor_pulse
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let z0 := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ z0 (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              z0 ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 z0 ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ P : Polynomial ℝ, P.natDegree ≤ N+1 ∧ ∀ t, P.eval t = z0 ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs z0 ![x,t] 0 0| ∧
                |qResidual gs z0 ![x,t]| ≤ C/(tau : ℝ)^N) := by
  let L := boundedClassWidth kappa M
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let S := shearedModelSquare q0
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hS : IsCompact S := shearedModelSquare_isCompact q0
  have hSVs : S ⊆ Vs := shearedModelSquare_subset_domain hSV q0
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hCauchy⟩ :=
    exists_actual_off_pulse_cauchy_bounds hgStar hV hSV M hG hd hkappa hM hq0
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N
  let K := taylorInitialRequest N (taylorStripJetOrder N)
  obtain ⟨B,hB,hCauchyK⟩ := hCauchy K
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨C,hC,hTaylor⟩ := uniform_taylor_pulse hgs hVs hS hSVs
    (initialShearedStateBudget (M : ℝ) q0) (initialShearedStateBudget_nonneg _ _) hc B hB N
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨tauTaylor,_,hpoly⟩ := hTaylor delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hCauchyK N delta hdelt,hwidth,
    eventually_ge_atTop (max tauTaylor tauRef)] with tau hCauchyTau hwidthTau htau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let a := -delta/(tau : ℝ)
  let zs := heightInShearCoordinates z q0
  let I := Ioo (-(L*r)) (L*r)
  let J := Icc (-(L*r/2)) (L*r/2)
  have htauT : tauTaylor ≤ tau := (le_max_left _ _).trans htau
  have htauR : tauRef ≤ tau := (le_max_right _ _).trans htau
  have htau1 : 1 ≤ tau := htauRef.trans htauR
  have htauPos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau1)
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have habs : |a| ≤ r := by
    dsimp only [a]
    rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htauPos]
    exact hdw
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hcutS (x : ℝ) (hx : x ∈ I) : inverseShearCoordinates q0 ![x,a] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,habs⟩
  have hcutU (x : ℝ) (hx : x ∈ I) : (![x,a] : Coord) ∈ inverseShearCoordinates q0 ⁻¹' U :=
    hSU (hcutS x hx)
  have hzs : ContDiffOn ℝ ∞ zs (inverseShearCoordinates q0 ⁻¹' U) :=
    heightInShearCoordinates_contDiffOn hh.smooth q0
  have hUs := shearedModelDomain_isOpen hU q0
  have hI : IsOpen I := isOpen_Ioo
  have hJI : J ⊆ I := by
    intro x hx
    exact ⟨by linarith [hx.1,mul_pos hL hr],by linarith [hx.2,mul_pos hL hr]⟩
  have hstate (x : ℝ) (hx : x ∈ I) :
      ‖qSolutionJet (linearCauchy a (heightCauchyValue zs a) (heightCauchyVelocity zs a)) ![x,a]‖ ≤
        initialShearedStateBudget (M : ℝ) q0 := by
    apply actual_initial_sheared_state_bound hh.smooth hU hSU (Nat.cast_nonneg M) hh.lowJet
      q0 (-(L*r)) (L*r) a hcutS hx
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change ‖x‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact (abs_le.mpr ⟨hx.1.le,hx.2.le⟩).trans (hLr.trans (by norm_num))
    · change ‖a‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact habs.trans (by linarith)
  have hden := hfloor g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelt htauR hdw happ
  have hBactual := hCauchyTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have h0 := heightCauchyValue_contDiffOn hzs a hcutU
  have h1 := heightCauchyVelocity_contDiffOn hzs hUs a hcutU
  have hregion (x : ℝ) (hx : x ∈ J) (t : ℝ)
      (ht : t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ))) : (![x,t] : Coord) ∈ S :=
    pulseRectangle_mem_shearedModelSquare hL hr hrhalf hLr hq0 hdw (abs_le.mpr hx) ht
  have hresult := hpoly tau htauT (heightCauchyValue zs a) (heightCauchyVelocity zs a) I J hI hJI h0 h1
    (fun x hx => hcutS x hx) hstate hden
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).1)
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).2) hregion
  refine ⟨hresult.1,hresult.2.1,hresult.2.2.1,?_⟩
  intro x hx t ht
  have hh := hresult.2.2.2 x (abs_le.mp hx) t ht
  have he : c/2 = (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) := by dsimp [c]; ring
  exact ⟨he ▸ hh.1,hh.2⟩

end SmoothLocal.Perturbation

end

end OAI
