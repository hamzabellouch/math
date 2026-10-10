import OAI.Probability.SLE.Stochastic.PlanarMartingale

namespace OAI

/-! Conditional optional sampling on the finite grids used to localize
planar harmonic tests. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma stopGridIndex_stopping {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun b => (σ b : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime (gridFiltration ℱ n) (fun b => (stopGridIndex n (σ b) : WithTop ℕ)) := by
  intro j
  change MeasurableSet[ℱ (stopGridTime n j)]
    {b | (stopGridIndex n (σ b) : WithTop ℕ) ≤ (j : WithTop ℕ)}
  have he : {b | (stopGridIndex n (σ b) : WithTop ℕ) ≤ (j : WithTop ℕ)}=
      {b | σ b ≤ stopGridTime n j} := by
    ext b
    exact WithTop.coe_le_coe.trans (stopGridIndex_le n j (σ b))
  rw [he]
  simpa only [WithTop.coe_le_coe] using hσ (stopGridTime n j)

lemma measurableSet_stopGridIndex {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime ℱ (fun b => (σ b : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ b, σ b ≤ T) (n : ℕ) (A : Set Ω)
    (hA : MeasurableSet[hσ.measurableSpace] A) :
    MeasurableSet[(stopGridIndex_stopping hσ n).measurableSpace] A := by
  have hAj (j : ℕ) : MeasurableSet[(gridFiltration ℱ n) j]
      (A ∩ {b | (stopGridIndex n (σ b) : WithTop ℕ) ≤ j}) := by
    have he : {b | (stopGridIndex n (σ b) : WithTop ℕ) ≤ (j : WithTop ℕ)}=
        {b | σ b ≤ stopGridTime n j} := by
      ext b
      exact WithTop.coe_le_coe.trans (stopGridIndex_le n j (σ b))
    rw [he]
    change MeasurableSet[ℱ (stopGridTime n j)] (A ∩ {b | σ b ≤ stopGridTime n j})
    simpa only [WithTop.coe_le_coe] using hA.2 (stopGridTime n j)
  have hn (b) : stopGridIndex n (σ b) ≤ stopGridIndex n T :=
    (stopGridIndex_le n _ _).mpr ((hb b).trans (stopGrid_bounds n T).1)
  have hAN : MeasurableSet[(gridFiltration ℱ n) (stopGridIndex n T)] A := by
    have he : {b | (stopGridIndex n (σ b) : WithTop ℕ) ≤ (stopGridIndex n T : ℕ)}=univ := by
      ext b
      simp only [mem_ofPred_eq,mem_univ,iff_true]
      exact WithTop.coe_le_coe.mpr (hn b)
    simpa only [he,inter_univ] using hAj (stopGridIndex n T)
  exact ⟨le_iSup (gridFiltration ℱ n) (stopGridIndex n T) A hAN,hAj⟩

lemma planar_compensated_grid_sampling
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (σ τ : Driver×Driver → ℝ≥0)
    (hσ : IsStoppingTime planarWienerFiltration (fun b => (σ b : WithTop ℝ≥0)))
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (hστ : ∀ b, σ b ≤ τ b) (T : ℝ≥0) (hb : ∀ b, τ b ≤ T)
    (A : Set (Driver×Driver)) (hA : MeasurableSet[hσ.measurableSpace] A) (n : ℕ) :
    (∫ b in A, planarCompensated f (stopGrid n (σ b)) b ∂W.prod W)=
      ∫ b in A, planarCompensated f (stopGrid n (τ b)) b ∂W.prod W := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  let ℱn := gridFiltration planarWienerFiltration n
  let C (j : ℕ) := planarCompensated f (stopGridTime n j)
  have hM : Martingale C ℱn (W.prod W) := by
    have hm := planar_compensated_martingale W hW f hf hc
    exact ⟨fun j => hm.1 _,fun i j hij => hm.2 _ _ (monotone_stopGridTime n hij)⟩
  have hσn := stopGridIndex_stopping hσ n
  have hτn := stopGridIndex_stopping hτ n
  have hle : (fun b => (stopGridIndex n (σ b) : WithTop ℕ)) ≤
      (fun b => (stopGridIndex n (τ b) : WithTop ℕ)) := by
    intro b
    apply WithTop.coe_le_coe.mpr
    exact (stopGridIndex_le n _ _).mpr ((hστ b).trans (stopGrid_bounds n (τ b)).1)
  have hN (b) : (stopGridIndex n (τ b) : WithTop ℕ) ≤ (stopGridIndex n T : ℕ) := by
    apply WithTop.coe_le_coe.mpr
    exact (stopGridIndex_le n _ _).mpr ((hb b).trans (stopGrid_bounds n T).1)
  have hCE := hM.stoppedValue_ae_eq_condExp_of_le hτn hσn hle hN
  have hAn := measurableSet_stopGridIndex hσ T (fun b => (hστ b).trans (hb b)) n A hA
  have hI := integrable_stoppedValue ℕ hτn hM.integrable hN
  have he : (∫ b in A, stoppedValue C (fun b => (stopGridIndex n (σ b) : WithTop ℕ)) b ∂W.prod W)=
      ∫ b in A, stoppedValue C (fun b => (stopGridIndex n (τ b) : WithTop ℕ)) b ∂W.prod W := by
    calc
      _ = ∫ b in A, (W.prod W)[stoppedValue C (fun b => (stopGridIndex n (τ b) : WithTop ℕ)) | hσn.measurableSpace] b ∂W.prod W :=
        integral_congr_ae (ae_restrict_of_ae hCE)
      _ = _ := setIntegral_condExp hσn.measurableSpace_le hI hAn
  exact he

end SLEExactGauge

end

end OAI
