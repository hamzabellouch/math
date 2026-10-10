import OAI.Geometry.IsometricImmersion.Caps.ActualFiniteLowerCutBounds
import OAI.Geometry.IsometricImmersion.Calculus.ShearHeightJets
import OAI.Geometry.IsometricImmersion.Darboux.QInitialEnergy

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem inverseShear_lower_cut_mem_modelSquare
    {q0 L r x : ℝ} (hr : 0 < r) (hrhalf : r < 1/2)
    (hLr : L*r ≤ 1/20) (hq0 : |q0| ≤ 1/20) (hx : |x| ≤ L*r) :
    inverseShearCoordinates q0 (boxPoint x (-r)) ∈ modelSquare := by
  have hx20 : |x| ≤ 1/20 := hx.trans hLr
  have hmul : |q0*x| ≤ (1/20 : ℝ)*(1/20) := by
    rw [abs_mul]
    exact mul_le_mul hq0 hx20 (abs_nonneg x) (by norm_num)
  have hy : |-r-q0*x| ≤ r+(1/20 : ℝ)*(1/20) := by
    calc
      _ ≤ |-r| + |q0*x| := abs_sub _ _
      _ = r + |q0*x| := by rw [abs_neg, abs_of_pos hr]
      _ ≤ _ := add_le_add le_rfl hmul
  have hx3 : |x| ≤ 3 := hx20.trans (by norm_num)
  have hy3 : |-r-q0*x| ≤ 3 := hy.trans (by linarith)
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx3
  obtain ⟨hyl,hyr⟩ := abs_le.mp hy3
  constructor
  · intro i
    fin_cases i
    · simpa [inverseShearCoordinates,boxPoint] using hxl
    · simpa [inverseShearCoordinates,boxPoint] using hyl
  · intro i
    fin_cases i
    · simpa [inverseShearCoordinates,boxPoint] using hxr
    · simpa [inverseShearCoordinates,boxPoint] using hyr

theorem exists_actual_finite_sheared_lower_cut_height_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
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
                |iteratedCoordPartial ds (heightInShearCoordinates z q0)
                  (coordinatePoint x (-r))| ≤ B := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcut⟩ := exists_actual_finite_lower_cut_height_bounds
    (e0 := e0) (kappa := kappa) hgStar hV hSV hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro n
  obtain ⟨C,hC,hCn⟩ := hcut n
  refine ⟨(2*(1+|q0|))^n*C, by positivity, ?_⟩
  intro N delta hdelta
  filter_upwards [hCn N delta hdelta] with tau htau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds x hx
  let S : Set Coord := {p | ∃ t : ℝ, |t| ≤ L*r ∧ p = inverseShearCoordinates q0 (boxPoint t (-r))}
  have hSU : S ⊆ U := by
    rintro _ ⟨t,ht,rfl⟩
    exact hf.domainSubset (hf.squareSubset (inverseShear_lower_cut_mem_modelSquare hr hrhalf hLr hq0 ht))
  have hbound : CoordinateBound z S n C := by
    intro es hes _ hp
    obtain ⟨t,ht,rfl⟩ := hp
    exact htau gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox es hes t ht
  have hshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hbound hh.smooth hU hSU hC q0
  exact hshear ds hds (coordinatePoint x (-r)) ⟨x,hx,rfl⟩

end SmoothLocal.Pulse

end

end OAI
