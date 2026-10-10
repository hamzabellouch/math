import OAI.MeasureTheory.Falconer.Radial.SmallChartWeakRadial
import OAI.MeasureTheory.Falconer.Estimates.BadTripleRelation
import OAI.MeasureTheory.Falconer.Geometry.ChartPairPower

namespace OAI

/-! # Actual original-law radial preparation for the endpoint angular proof -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory NormedSpace
open scoped ENNReal
variable {h : ℕ}

theorem endpoint_radial_preparation (hLW : PublishedFiniteLoomisWhitney)
    {ζ ell a : ℝ} (hζ : 0 < ζ) (hell : (h:ℝ) < ell)
    (hell' : ell < (((h+1:ℕ):ℝ)/((h+1:ℕ)+1))*((h+1:ℕ):ℝ)) (ha : 0 < a) :
    ∃ ε b e c₀ c₁ c₂ : ℝ, 0 < ε ∧ 0 < b ∧ 0 < e ∧ 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (μ : Measure (Space ((h+1)+1))) [IsProbabilityMeasure μ],
      (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
      (∀ x : Space ((h+1)+1), ∀ r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ (ball x r) ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^((h+1:ℕ):ℝ))) →
      (∀ w : Space ((h+1)+1), ‖w‖ = 1 → ∀ v r : ℝ, ((2:ℝ)^N)⁻¹ ≤ r → r ≤ 1 →
        μ {x | |inner ℝ w x-v| ≤ r} ≤ ENNReal.ofReal (((2:ℝ)^N)^ε*r^ζ)) →
      ∃ G : Set (Space ((h+1)+1) × Space ((h+1)+1)), MeasurableSet G ∧
        (∀ p z, (p,z) ∈ G → ((2:ℝ)^N)^(-b) ≤ dist p z) ∧
        (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) ∧
        (∫⁻ A : Fin h → Space (((h+1)+1)+1),
          ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
            (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))) Gᶜ ∂gaussianRows (((h+1)+1)+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₁)) ∧
        (∫⁻ A : Fin h → Space (((h+1)+1)+1),
          ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
            ((gaussianChartSliceMeasure μ A (1/(2:ℝ)^N)).prod
              (gaussianChartSliceMeasure μ A (1/(2:ℝ)^N))))
                (badChartTriples G (2*((2:ℝ)^N)^(-a))) ∂gaussianRows (((h+1)+1)+1) h) ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-c₂)) ∧
        ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space ((h+1)+1),
          μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
            ENNReal.ofReal (((2:ℝ)^N)^e*(3*(1/(2:ℝ)^j))^ell) := by
  obtain ⟨H,hH,b₀,e,hb₀,he,hscale,hgap⟩ := exists_endpoint_radial_losses h hell ha
  let b := min b₀ (1/2)
  have hb : 0 < b := lt_min hb₀ (by norm_num)
  have hb₀' : b ≤ b₀ := min_le_left _ _
  have hb1 : b ≤ 1 := (min_le_right b₀ (1/2)).trans (by norm_num)
  have hscale' : 1/(H:ℝ) < a-2*b := by linarith
  have hgap' : 0 < (ell-h)/(2*(H:ℝ))-2*(h:ℝ)*b-e := by
    have hh := mul_le_mul_of_nonneg_left hb₀' (show 0 ≤ 2*(h:ℝ) by positivity)
    linarith
  have hell0 : 0 ≤ ell := (Nat.cast_nonneg h).trans hell.le
  obtain ⟨ew,cw,hew,hcw,Nw,hw⟩ := small_chart_weak_radial hLW (by omega : 1 ≤ h+1)
    hζ hell0 hell' he
  let q : ℝ := ((h+1:ℕ):ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqb : 0 < q*b/2 := by positivity
  let c₀ := min cw (q*b/2)/2
  have hc₀ : 0 < c₀ := half_pos (lt_min hcw (by positivity))
  have hc₀w : c₀ < cw := by dsimp [c₀]; have := min_le_left cw (q*b/2); linarith
  have hc₀b : c₀ < q*b/2 := by dsimp [c₀]; have := min_le_right cw (q*b/2); linarith
  obtain ⟨Nd,hd⟩ := weak_radial_two_costs (A := 1) (B := 1) (by norm_num) (by norm_num) hc₀w hc₀b
  obtain ⟨ep,cp,hep,hcp,Np,hp⟩ := chart_pair_power (n := (h+1)+1) h
    (q := q) (by dsimp [q]; push_cast; linarith) hc₀
  obtain ⟨ct,hct,Nt,ht⟩ := endpoint_bad_triples (n := (h+1)+1) (h := h)
    H hH hb hell hscale' hgap'
  let ε := min ew (min ep (q*b/4))
  have hε : 0 < ε := lt_min hew (lt_min hep (by positivity))
  have hεw : ε ≤ ew := min_le_left _ _
  have hεp : ε ≤ ep := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ q*b/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,b,e,c₀,cp,ct,hε,hb,he,hc₀,hcp,hct,Nw+Nd+Np+Nt,?_⟩
  intro N hN μ _ hμ hball hslab
  let R : ℝ := (2:ℝ)^N
  have hR1 : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hR : 0 < R := zero_lt_one.trans_le hR1
  have hlossw : R^ε ≤ R^ew := Real.rpow_le_rpow_of_exponent_le hR1 hεw
  have hlossp : R^ε ≤ R^ep := Real.rpow_le_rpow_of_exponent_le hR1 hεp
  obtain ⟨G₀,hG₀,hdiag₀,hcost₀,hcap₀⟩ := hw N (by omega) μ hμ
    (fun x r hr hr1 => (hball x r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hlossw (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
    (fun w hw v r hr hr1 => (hslab w hw v r hr hr1).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hlossw (Real.rpow_nonneg (le_trans (by positivity) hr) _))))
  let G := separatedRadialPairs G₀ (R^(-b))
  have hG : MeasurableSet G := separatedRadialPairs_measurable hG₀ _
  have hsub : G ⊆ G₀ := separatedRadialPairs_subset _ _
  have hsep : ∀ p z, (p,z) ∈ G → R^(-b) ≤ dist p z := fun _ _ hp => hp.2
  have hdiag : ∀ p z, (p,z) ∈ G → z ≠ p := fun p z hp => hdiag₀ p z (hsub hp)
  have hrlo : R⁻¹ ≤ R^(-b) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hrhi : R^(-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith)
  have hnear : ∀ x, μ (ball x (R^(-b))) ≤ ENNReal.ofReal (R^(-(q*b/2))) := by
    intro x
    apply (hball x (R^(-b)) hrlo hrhi).trans
    apply ENNReal.ofReal_le_ofReal
    change R^ε*(R^(-b))^q ≤ _
    rw [← Real.rpow_mul hR.le,← Real.rpow_add hR]
    exact Real.rpow_le_rpow_of_exponent_le hR1 (by nlinarith)
  have hcost : (μ.prod μ) Gᶜ ≤ ENNReal.ofReal (R^(-c₀)) := by
    apply (separatedRadialPairs_cost μ G₀ _ _ hnear).trans
    apply (add_le_add hcost₀ le_rfl).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul] using hd N (by omega))
  have hcap : ∀ p, ∀ j : ℕ, j ≤ N → ∀ u : Space ((h+1)+1),
      μ {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ≤
        ENNReal.ofReal (R^e*(3*(1/(2:ℝ)^j))^ell) := by
    intro p j hj u
    have hsubcap : {z | (p,z) ∈ G ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} ⊆
        {z | (p,z) ∈ G₀ ∧ dist (normalize (z-p)) u < 3*(1/(2:ℝ)^j)} :=
      fun _ hz => ⟨hsub hz.1,hz.2⟩
    exact (measure_mono hsubcap).trans (hcap₀ p j hj u)
  refine ⟨G,hG,hsep,hcost,?_,?_,hcap⟩
  · apply hp N (by omega) μ (by filter_upwards [hμ] with x hx; linarith) Gᶜ hG.compl hcost
    intro x j hj
    have hlo : R⁻¹ ≤ 1/(2:ℝ)^j := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hj)
    have hhi : 1/(2:ℝ)^j ≤ 1 := by
      rw [one_div]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    exact (hball x _ hlo hhi).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hlossp (by positivity)))
  · apply ht N (by omega) μ G (badChartTriples G (2*R^(-a))) (badChartTriples_measurable hG _)
      (badChartTriples_retained G _ _ hsep) hdiag
    exact fun p j hj u _ => hcap p j hj u

end Falconer

end OAI
