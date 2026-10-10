import OAI.Analysis.FreeEntropy.GaussianCrossEntropy

namespace OAI

noncomputable section
open MeasureTheory Filter Finset Set
open scoped Topology
namespace FiniteEntropySeparation
namespace Model
variable (p : ℕ) [NeZero p]
variable {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
  {h R : ℝ} (hR : 0≤R) (hn : ∀k,(diagonalMicrostates (τ p) (X p h) R k (D k)).Nonempty)
  (μ : (k:ℕ) → Measure (MatrixCoordinates (p+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
  (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (τ p) (X p h) R k (D k))
include hD0 hD hR hn hμ in
 theorem matrixHeatLaw_totalSecond_tendsto {s : ℝ} (hs : 0<s) :
    Tendsto (fun k => ∫a,totalSecond (matrixMoment a) ∂matrixHeatLaw (μ k) s) atTop
      (𝓝 (totalSecond (wordMoment (τ p) (heatTuple (X p h) (auxiliaryNoise p) s)))) := by
  have hb k : ∀ᵐa ∂μ k,∀i,matrixOpNorm (hermitianMatrix a i)≤R := (hμ k).mono (fun _ ha => ha.1)
  have hi k i : Integrable (fun a => (matrixMoment a [i,i]).re) (matrixHeatLaw (μ k) s) :=
    (matrixHeatLaw_moment_integrable (hD0 k) (μ k) hR (hb k) hs [i,i]).re
  have ht i := Complex.continuous_re.continuousAt.tendsto.comp (FreeTensor.matrixHeatLaw_moment_tendsto hD0 hD (oldNoise p) (X p h)
    (X_mem_background p h) hR hn (auxiliaryIndex p) (auxiliaryIndex_injective p)
    (auxiliaryIndex_fresh p) μ hμ hs [i,i])
  have he k : (∫a,totalSecond (matrixMoment a) ∂matrixHeatLaw (μ k) s)=
      ∑i : Fin (p+1),(∫a,matrixMoment a [i,i] ∂matrixHeatLaw (μ k) s).re := by
    unfold totalSecond
    rw [integral_finsetSum univ (fun i _ => hi k i)]
    apply sum_congr rfl
    intro i _
    exact integral_re (matrixHeatLaw_moment_integrable (hD0 k) (μ k) hR (hb k) hs [i,i])
  simp_rw [he]
  exact tendsto_finsetSum univ (fun i _ => ht i)
end Model

 theorem chosen_terminal_isotropic {D : ℕ → ℕ} (hD0 : ∀k,0<D k) (hD : Tendsto D atTop atTop)
    {h R δ Δ : ℝ} (hh0 : 0<h) (hh1 : h<1) (hR : 0≤R)
    (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin chosenP,i≠j → Δ≤|equidiscreteAtom chosenP i-equidiscreteAtom chosenP j|)
    (hq : ∀l : Fin chosenP,∀r : ℝ,|r-equidiscreteAtom chosenP l|≤δ → (3:ℝ)/4≤((spectralBasis chosenP l).eval r)^2)
    (hh : spectralGood chosenP δ Δ (wordMoment (Model.τ chosenP) (Model.X chosenP h)))
    (hn : ∀k,(diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)).Nonempty)
    (μ : (k:ℕ) → Measure (MatrixCoordinates (chosenP+1) (D k))) [∀k,IsProbabilityMeasure (μ k)]
    (hμ : ∀k,∀ᵐa ∂μ k,a∈diagonalMicrostates (Model.τ chosenP) (Model.X chosenP h) R k (D k)) :
    ∀ᶠk in atTop,normalizedMatrixEntropy (μ k) chosenTime≤
      ((chosenP+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*(1+h+chosenTime))-(3:ℝ)/2 := by
  let v := 1+h+chosenTime
  have hv : 0<v := by dsimp [v]; linarith [chosenTime_pos]
  have hconv := Model.matrixHeatLaw_totalSecond_tendsto chosenP hD0 hD hR hn μ hμ chosenTime_pos
  have hm := Model.totalSecond_heat_le chosenP chosenP_ge_two hh0.le chosenTime_pos.le
  have hlim : totalSecond (wordMoment (Model.τ chosenP) (heatTuple (Model.X chosenP h) (Model.auxiliaryNoise chosenP) chosenTime))<
      ((chosenP+1:ℕ):ℝ)*v+v/2 := by push_cast; dsimp [v] at *; linarith
  have he := hconv.eventually (gt_mem_nhds hlim)
  have hl := Model.matrixHeatLaw_blocks_eventually chosenP chosenP_ge_two hδ hΔ hδΔ hsep hq hh0 hh1 hh
    chosenTime_pos chosen_time_noise_budget R D hD0 μ hμ
  filter_upwards [he,hl,hD.eventually (eventually_ge_atTop 64)] with k hk hlow hdk
  have hnorm : ∀ᵐa ∂μ k,‖a‖≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R := by
    filter_upwards [hμ k] with a ha
    have hb := microstates_subset_closedBall (Model.τ chosenP) (Model.X chosenP h) R hR k (D k) ((k+1:ℝ)⁻¹) ha
    simpa only [Metric.mem_closedBall,dist_zero_right] using hb
  have hb := normalizedEntropy_event_gaussian (hD0 k) (μ k) chosenTime_pos
    (show 0≤Real.sqrt (((chosenP+1:ℕ):ℝ)*D k)*R by positivity) hnorm hv
    _ (blockEvent_isClosed (hD0 k) _ _).measurableSet hlow (chosen_gaussian_block hdk hh0 hh1)
  have hmoment : (∫a,totalSecond (matrixMoment a) ∂matrixHeatLaw (μ k) chosenTime)/(2*v)≤
      ((chosenP+1:ℕ):ℝ)/2+1/4 := by
    apply (div_le_iff₀ (by positivity : 0<2*v)).mpr
    linarith
  have hdim : (2:ℝ)≤D k := by exact_mod_cast (show 2≤D k by omega)
  have hlogdim : Real.log 2/(D k:ℝ)^2≤(1:ℝ)/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(D k:ℝ)^2)).mpr
    have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    nlinarith
  have hlog : Real.log (2*Real.pi*Real.exp 1*v)=Real.log (2*Real.pi*v)+1 := by
    rw [show 2*Real.pi*Real.exp 1*v=(2*Real.pi*v)*Real.exp 1 by ring,
      Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp]
  change _≤((chosenP+1:ℕ):ℝ)/2*Real.log (2*Real.pi*Real.exp 1*v)-3/2
  rw [hlog]
  linarith
end FiniteEntropySeparation

end

end OAI
