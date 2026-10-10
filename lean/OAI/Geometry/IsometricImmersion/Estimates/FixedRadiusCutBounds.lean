import OAI.Geometry.IsometricImmersion.Coordinates.ActualFiniteShearedCutBounds

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_lower_cut_bound_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L r : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn gTau U → IsOpen U →
          (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          CapInductionHeight gTau U Z c e0 z →
          CapInductionFlow gTau U G Z d c e0 kappa z Y W →
          |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ ds : List (Fin 2), ds.length ≤ n → ∀ x : ℝ, |x| ≤ L*r →
            |iteratedCoordPartial ds z (inverseShearCoordinates q0 (boxPoint x (-r)))| ≤ C := by
  let m := max 8 (n+3)
  obtain ⟨Bstar,_,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  let R := lowerCutRectangle L r hL hr hrhalf hLr
  let J : CapMetricJetBudget (-r/2) := fun _ _ => Bstar+1
  obtain ⟨C,hC,hheight⟩ := uniform_finite_varying_lowerCap_pointwise
    G Z d c e0 kappa hG hZ hd hc J n R (fun _ _ => by dsimp [J]; linarith)
  refine ⟨C,hC,?_⟩
  intro N delta hdelta
  have hevent : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hevent,eventually_ge_atTop m] with tau hwidth hm
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds x hx
  have htau0 : (0 : ℝ) < tau := zero_lt_one.trans_le hwidth.1
  have htau1 : 1 ≤ tau := by exact_mod_cast hwidth.1
  have herror := metricApproximationAccuracy_le_one htau1
  let Bq := heightQuotientJetBound G Z d c
  have hBq : 0 ≤ Bq := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (p : Coord) (hp : p ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient gTau z) p| ≤ Bq :=
    hf.quotientBound [i] (by norm_num) p hp
  have hlocal : FiniteCapMetricJets gTau Y J (lowerCapPointwiseRequests n R) := by
    intro b hb i j k hk p hp
    have hkM : k ≤ m := lowerCapPointwiseRequests_full_order_le n R b hb hk
    have hpS := hf.image_subset_square b.2 hp
    have heq : testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar :=
      testMetric_eventuallyEq_on_lower_cap hf.quotientSmooth hf.domainOpen hf.squareSubset
        hf.continuous hf.range hf.start hf.ode hh.quotient hBq hL hr hpartial hq0 hcenter
        (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
        (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau0 hwidth.2
        gStar N b.2 hp
    have hhjet := metric_jet_norm_le_of_approximation_locality hgStar hgTau hV hU
      (hSV hpS) (hf.domainSubset (hf.squareSubset hpS)) heq i j k
      (hbase i j k hkM p hpS) (happrox i j k (hkM.trans hm) p hpS)
    exact hhjet.trans (add_le_add le_rfl herror)
  have hbound := hheight gTau U z Y W hgTau hU (hf.squareSubset.trans hf.domainSubset)
    hg4 hdet hh hf hlocal
  exact hbound ds hds _ (actual_lower_cut_in_cap_image hh hf hG hZ hd hc hL hr hrhalf hLr
    hq0 hcenter hrsmall hx)

theorem exists_actual_finite_sheared_lower_cut_bound_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L r : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn gTau U → IsOpen U →
          (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          CapInductionHeight gTau U Z c e0 z →
          CapInductionFlow gTau U G Z d c e0 kappa z Y W →
          |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ ds : List (Fin 2), ds.length ≤ n → ∀ x : ℝ, |x| ≤ L*r →
            |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ C := by
  obtain ⟨C,hC,hcut⟩ := exists_actual_finite_lower_cut_bound_at_radius
    (e0 := e0) (kappa := kappa) hgStar hV hSV hG hZ hd hc hL hq0 hr hrhalf hLr hrsmall n
  refine ⟨(2*(1+|q0|))^n*C,by positivity,?_⟩
  intro N delta hdelt
  filter_upwards [hcut N delta hdelt] with tau hcutTau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happ ds hds x hx
  let S : Set Coord := {p | ∃ t : ℝ, |t| ≤ L*r ∧ p = inverseShearCoordinates q0 (boxPoint t (-r))}
  have hSU : S ⊆ U := by
    rintro p ⟨t,ht,rfl⟩
    exact hf.domainSubset (hf.squareSubset (inverseShear_lower_cut_mem_modelSquare hr hrhalf hLr hq0 ht))
  have hbound : CoordinateBound z S n C := by
    intro es hes p hp
    obtain ⟨t,ht,rfl⟩ := hp
    exact hcutTau gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happ es hes t ht
  exact SmoothLocal.Pulse.CoordinateBound.inverse_shear hbound hh.smooth hU hSU hC q0 ds hds
    (coordinatePoint x (-r)) ⟨x,hx,rfl⟩

end SmoothLocal.Pulse

end

end OAI
