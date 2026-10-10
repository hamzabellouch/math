import OAI.Geometry.SurfaceImmersion.Correction.AnchoredPreparedCorrection
import OAI.Geometry.SurfaceImmersion.Geometry.RescaledReadBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPreparedInitialization
import OAI.Geometry.SurfaceImmersion.Correction.InitialCorrectionStage

namespace OAI

/-! Arbitrarily accurate primitive maps give an actual smooth exact metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes JetPolynomial JetPolynomial.Perturbation
local instance exactFastFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance exactFastFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance exactFastDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance exactFastDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance exactFastSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance exactFastSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Quantitative finite-accuracy data supplied by the actual primitive construction. -/
def GeometricFastFamily (g : SmoothMetric M) (R c b V₀ : ℝ) : Prop :=
  ∀ N : ℕ, ∃ η C Cv : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 ≤ Cv ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ F : M → Space,
        ContMDiff planeModel spaceModel ∞ F ∧
        A.WeightedBound 1 0 V₀ F ∧ A.WeightedBound z 442 Cv F ∧
        A.ShiftedBound 2 440 z (Cv/z^2) F ∧
        A.TensorWeightedBound 1 440 (C*z^(N+1)) (inducedTensor F-g.inner) ∧
        ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
          ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
          c ≤ NormalFrame.gramDet
            (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
            (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
          b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖

/-- Retain a proved property of the actual finite-accuracy approximant. -/
def GeometricFastFamilyWithProperty (g : SmoothMetric M) (R c b V₀ : ℝ) (property : ℝ → (M → Space) → Prop) : Prop :=
  ∀ N : ℕ, ∃ η C Cv : ℝ, 0 < η ∧ 0 ≤ C ∧ 0 ≤ Cv ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ F : M → Space,
        ContMDiff planeModel spaceModel ∞ F ∧ property z F ∧
        A.WeightedBound 1 0 V₀ F ∧ A.WeightedBound z 442 Cv F ∧
        A.ShiftedBound 2 440 z (Cv/z^2) F ∧
        A.TensorWeightedBound 1 440 (C*z^(N+1)) (inducedTensor F-g.inner) ∧
        ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
          ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
          c ≤ NormalFrame.gramDet
            (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
            (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
          b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖

theorem exact_metric_with_property (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c b V₀ : ℝ) (hc : 0 < c) (hb : 0 < b) (hV₀ : 0 ≤ V₀)
    (property : ℝ → (M → Space) → Prop)
    (hfamily : A.GeometricFastFamilyWithProperty g R c b V₀ property) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ζ : ℝ, 0 < ζ → ∀ K : ℝ, 0 < K →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F ∧ property z F ∧ IsSmoothIsometricImmersion M g G ∧
      A.WeightedBound 1 2 (z^8/K) (G-F) ∧
      (∀ i, WeightedEstimates.WeightedBound univ (z^2) 3 B
        (spaceCoordinates ∘ A.vectorPlaneRead i F)) ∧
      ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ := by
  obtain ⟨B,hB,hreads⟩ := A.uniform_rescaled_read_bound V₀ hV₀
  refine ⟨B,hB,?_⟩
  intro ζ hζ
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hprep⟩ :=
    A.anchored_prepared_correction g houter R c B b hc (zero_le_one.trans hB) hb
  let P : ℝ → ℝ := fun x => x^2
  have hP : HasPolynomialBound P := polynomialBound_id.pow 2
  obtain ⟨Budget,EpsInv,hBudget,hEpsInv,hdata⟩ := hprep P P hP hP
  obtain ⟨ν,hν,N,hinit⟩ := ExactCorrection.polynomial_prepared_initialization EpsInv hEpsInv
  obtain ⟨ηf,C,Cv,hηf,hC,hCv,hf⟩ := hfamily N
  obtain ⟨Dg,hDg,hg⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 440 g.contMDiff
  let H := max C Cv
  have hH : 0 ≤ H := hC.trans (le_max_left _ _)
  have hCH : C ≤ H := le_max_left _ _
  have hCvH : Cv ≤ H := le_max_right _ _
  obtain ⟨ηr,hηr,hηr1,hr⟩ := hreads Cv hCv
  obtain ⟨ηb,hηb,_,hbase⟩ := ExactCorrection.positive_power_threshold Cv 2 1 (by norm_num) zero_lt_one
  intro K hK
  obtain ⟨ηi,hηi,hηi1,hi⟩ := hinit H Dg (a/16) D K hH hDg (by positivity) hD hK
  let η := min z₀ (min ηf (min ηr (min ηb (min ηi ζ))))
  have hη : 0 < η := lt_min hz₀ (lt_min hηf (lt_min hηr (lt_min hηb (lt_min hηi hζ))))
  let z := η/2
  have hz : 0 < z := half_pos hη
  have hzη : z < η := half_lt_self hη
  have hzz₀ : z < z₀ := hzη.trans_le (min_le_left _ _)
  have hzf : z < ηf := hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzr : z < ηr := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hzb : z < ηb := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hziζ : z < min ηi ζ := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hzi := hziζ.trans_le (min_le_left _ _)
  have hzζ := hziζ.trans_le (min_le_right _ _)
  have hz1 : z ≤ 1 := hzz₀.le.trans hz₀1
  have hzsq : z^2 ≤ z := by simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 (by norm_num : 1 ≤ 2)
  obtain ⟨F,hF,hproperty,hFzero,hFwb,hFshift,herr,hgeom⟩ := hf z hz hzf
  have hFread := hr z hz hzr F hF hFzero (fun i => (hFwb i).mono_order (by omega))
  have hsmall : Cv*z^2 ≤ 1 := by
    simpa only [Real.rpow_ofNat] using (hbase z hz hzb).le
  have hFbase : A.ShiftedBound 2 0 1 (P ((z^2)⁻¹)) F := by
    intro i j hj x
    have hj0 : j-2 = 0 := by omega
    have hh := hFshift i j (by omega) x
    simp only [hj0,pow_zero,one_mul] at hh ⊢
    apply hh.trans
    change Cv/z^2 ≤ ((z^2)⁻¹)^2
    apply (div_le_iff₀ (pow_pos hz 2)).mpr
    have heq : ((z^2)⁻¹)^2*z^2 = 1/z^2 := by field_simp
    rw [heq]
    exact (le_div_iff₀ (pow_pos hz 2)).mpr hsmall
  obtain ⟨p,hpa,hprho,hpbudget,hpWish,hpε⟩ := hdata (z^2) (pow_pos hz 2)
    (hzsq.trans hzz₀.le)
    F hF hFread hgeom hFbase
  have hρ : p.ρ = z^8/D := by rw [hprho]; congr 1; ring
  have hbudget : 1/z^4 ≤ p.budget := by
    have hPval : P ((z^2)⁻¹) = 1/z^4 := by dsimp [P]; field_simp
    rw [hPval] at hpWish
    linarith [p.budget_pos]
  obtain ⟨htz,ht32,htε,hMB,hHB,hnear,herror,hcontrol⟩ := hi z hz hzi
  have ht : 0 < z^ν := Real.rpow_pos_of_pos hz _
  have ht1 : z^ν ≤ 1 := by linarith
  have hmap : A.ShiftedBound 2 440 z (H/z^2) F := by
    intro i j hj x
    exact (hFshift i j hj x).trans (div_le_div_of_nonneg_right hCvH (sq_nonneg z))
  have hmap0 : A.ShiftedBound 2 0 1 (H/z^2) F := by
    intro i j hj x
    have hj0 : j-2 = 0 := by omega
    simpa only [hj0,pow_zero,one_mul] using hmap i j (by omega) x
  have hmetric0 : A.TensorWeightedBound 1 0 Dg g.inner := fun i => (hg i).mono_order (by omega)
  have herror' : A.TensorWeightedBound (z^ν) 440 (((z^ν)^(10 : ℝ))^2*(a/16))
      (inducedTensor F-g.inner) := by
    intro i
    apply ((herr i).shrink_scale ht.le ht1).mono_const
    exact (mul_le_mul_of_nonneg_right hCH (pow_nonneg hz.le _)).trans herror
  obtain ⟨seed,hseed⟩ := p.initial_stage_of_scaled_bounds hF ht ht32
    (htε _ (p.ε_pos 0) hpε) hz htz (by positivity) (by positivity) hDg (by positivity)
    hmap0 hmap hmetric0 hg herror' (hMB.trans hbudget) (hHB.trans hbudget)
    (by rwa [hρ]) (by rw [hpa]; linarith)
  obtain ⟨G,hG,hclose⟩ := p.exact_correction_initial_displacement hF ht ht32
    (by positivity) hmap0 seed hseed
  rw [hρ] at hclose
  exact ⟨z,hz,hzζ,hz1,F,G,hF,hproperty,hG,(fun i => (hclose i).mono_const hcontrol),hFread,hgeom⟩

/-- The original geometric conclusion, with no extra property requested. -/
theorem exact_metric_from_fast_family (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c b V₀ : ℝ) (hc : 0 < c) (hb : 0 < b) (hV₀ : 0 ≤ V₀)
    (hfamily : A.GeometricFastFamily g R c b V₀) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ζ : ℝ, 0 < ζ → ∀ K : ℝ, 0 < K →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F ∧ IsSmoothIsometricImmersion M g G ∧
      A.WeightedBound 1 2 (z^8/K) (G-F) ∧
      (∀ i, WeightedEstimates.WeightedBound univ (z^2) 3 B
        (spaceCoordinates ∘ A.vectorPlaneRead i F)) ∧
      ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ := by
  have hdecorated : A.GeometricFastFamilyWithProperty g R c b V₀ (fun _ _ => True) := by
    intro N
    obtain ⟨η,C,Cv,hη,hC,hCv,hf⟩ := hfamily N
    refine ⟨η,C,Cv,hη,hC,hCv,?_⟩
    intro z hz hzη
    obtain ⟨F,hF,hFzero,hFwb,hFshift,herr,hgeom⟩ := hf z hz hzη
    exact ⟨F,hF,trivial,hFzero,hFwb,hFshift,herr,hgeom⟩
  obtain ⟨B,hB,hall⟩ := A.exact_metric_with_property g houter R c b V₀ hc hb hV₀
    (fun _ _ => True) hdecorated
  refine ⟨B,hB,?_⟩
  intro ζ hζ K hK
  obtain ⟨z,hz,hzζ,hz1,F,G,hF,_,hG,hclose,hread,hgeom⟩ := hall ζ hζ K hK
  exact ⟨z,hz,hzζ,hz1,F,G,hF,hG,hclose,hread,hgeom⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
