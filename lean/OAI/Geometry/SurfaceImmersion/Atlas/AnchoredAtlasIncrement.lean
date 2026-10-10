import OAI.Geometry.SurfaceImmersion.Atlas.SelectedGridGeometry
import OAI.Geometry.SurfaceImmersion.Atlas.GridGeometricIncrement

namespace OAI

/-! Actual polynomial increments selected uniformly near a fast atlas map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes
lemma phaseCatalog_inverse_bound (V : Finset Base) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ ξ ∈ V, ∀ hξ : ξ ≠ 0,
      ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ D := by
  classical
  let f := fun ξ : Base => if hξ : ξ ≠ 0 then ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ else 0
  have hf (ξ : Base) : 0 ≤ f ξ := by dsimp [f]; split_ifs <;> positivity
  refine ⟨1+∑ ξ ∈ V, f ξ,le_add_of_nonneg_right (Finset.sum_nonneg (fun ξ _ => hf ξ)),?_⟩
  intro ξ hξ hn
  have hh := Finset.single_le_sum (fun η (_ : η ∈ V) => hf η) hξ
  have he : f ξ = ‖(phaseEquiv ξ hn).symm.toContinuousLinearMap‖ := dite_eq_left hn
  rw [he] at hh
  linarith
end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry PhaseGrid
local instance anchoredIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance anchoredIncrementSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredIncrementSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem anchored_atlas_increment (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ r : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < r ∧
    ∀ FJ Y : ℕ → ℝ → ℝ,
      (∀ m, HasPolynomialBound (FJ m)) → (∀ m, HasPolynomialBound (Y m)) →
      (∀ m x, 1 ≤ x → 1 ≤ FJ m x) → (∀ m x, 1 ≤ x → 1 ≤ Y m x) → ∀ q : ℕ,
    ∃ e : ℕ, ∃ E : ℝ, ∃ P Q : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (Q m)) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
    ∀ G : M → Space, A.ReadJetBall z F G →
    ∀ (τ : ℝ) (s : ℝ≥0), 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ i m l, l ≤ m+3 → WeightedEstimates.WeightedBound univ 1 l
        (FJ m z⁻¹/(s : ℝ)^(l-2)) (spaceCoordinates ∘ A.vectorPlaneRead i G)) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*(z⁻¹)^e))) →
    ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v v', f y v v' = f y v' v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode g.inner y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m z⁻¹) f) →
    ∀ δ : ℝ, 0 < δ → δ ≤ τ →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound τ m (P m z⁻¹*(δ*τ)) U) ∧
        (∀ m, A.TensorWeightedBound τ m (Q m z⁻¹*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (G+U)-inducedTensor G-δ^2 • f)) := by
  classical
  obtain ⟨stock,weights,z₀,K,C,ε,W,κ,hz₀,hz₀1,hK,hC,hε,hW,hκ,hselect⟩ :=
    A.anchored_atlas_phases g houter R c B b hc hB hb
  obtain ⟨_,H,_,_,_,hH,_,hHnorm,_⟩ := A.metric_plane_read_bounds g
  let V : Finset SmallModes.Base := stock.biUnion (fun P =>
    Finset.univ.biUnion (fun j : Fin 3 => weights.image (fun w => w • P.ξ j)))
  obtain ⟨D₁,hD₁,hDinv⟩ := phaseCatalog_inverse_bound V
  let D := 1+4/c+8/(ε*b)
  have hD : 0 < D := by dsimp [D]; positivity
  have hgramD : 4/c ≤ D := by
    have hh : 0 ≤ 8/(ε*b) := by positivity
    dsimp [D]; linarith
  have hnormalD : 8/(ε*b) ≤ D := by
    have hh : 0 ≤ 4/c := by positivity
    dsimp [D]; linarith
  obtain ⟨r,hr,hstep⟩ := A.grid_geometric_increment g V houter
    (by positivity : 0 < ε/4) hκ (half_pos hb) (half_pos hε)
    (zero_le_one.trans hC) (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans hH)) hK.le hD
  refine ⟨z₀,r,hz₀,hz₀1,hr,?_⟩
  intro FJ Y hFJ hY hFJ1 hY1 q
  let M₀ := 1+2*D+C+W*C+D₁
  have hM₀ : 0 ≤ M₀ := by dsimp [M₀]; positivity
  let J := fun m x => FJ m x+M₀
  have hJ (m : ℕ) : HasPolynomialBound (J m) := (hFJ m).add (polynomialBound_const hM₀)
  have hJ1 (m : ℕ) (x : ℝ) (hx : 1 ≤ x) : 1 ≤ J m x := by
    have hh := hFJ1 m x hx
    dsimp [J]; linarith
  obtain ⟨e,E,P,Q,hE,hP,hQ,hbuild⟩ := hstep J Y hJ hY hJ1 hY1 q
  refine ⟨e,E,P,Q,hE,hP,hQ,?_⟩
  intro z hz hzsmall F hF hFb hFm G hG τ s hτ hs hτs hs1 hjets hsmall f hf hsym hnear hfsize δ hδ hδτ
  obtain ⟨a,Pa,ξ,w,hstock,hweights,hcard,hcover,hPa,hw,hpoint,hpairs⟩ :=
    hselect z hz hzsmall F hF hFb hFm
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  have hpt : A.SelectedGridPointMargins g z a Pa G c b ε := hpoint G hG
  have hV (l : A.GridPhaseIndex a) : w (A.gridPhaseLabel l) • ξ (A.gridPhaseLabel l) ∈ V := by
    rcases l with ⟨i,k,j⟩
    change w (i,k.val,j) • ξ (i,k.val,j) ∈ V
    rw [(hPa i k j).1]
    exact Finset.mem_biUnion.mpr ⟨Pa i k,hstock i k,
      Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨w (i,k.val,j),hweights _,rfl⟩⟩⟩
  have hgeom := A.selected_grid_cover_geometry hz hc hcover hpt
  have hcell := A.selected_grid_cell_geometry hε hb (zero_le_one.trans hC) w hpt
    (fun i k j => (hPa i k j).2.1) hw
  have hJbig (m : ℕ) : 2*D ≤ J m z⁻¹ ∧ C ≤ J m z⁻¹ ∧ W*C ≤ J m z⁻¹ ∧ D₁ ≤ J m z⁻¹ := by
    have hj := hFJ1 m z⁻¹ hx
    have hd0 := hD.le
    have hc0 := zero_le_one.trans hC
    have hwc := mul_nonneg hW.le hc0
    have hdi := zero_le_one.trans hD₁
    dsimp [J,M₀]
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  apply hbuild z hz (hzsmall.trans hz₀1) a hcard hcover Pa ξ w
    (fun i k j => (hPa i k j).1) (fun l => (hw l).1) hV
    (fun i k j => (hPa i k j).2.2)
    (fun i k j y => by
      calc
        (Pa i k).Q j (A.tensorPlaneRead i g.inner y) ≤
            ‖(Pa i k).Q j (A.tensorPlaneRead i g.inner y)‖ := Real.le_norm_self _
        _ ≤ ‖(Pa i k).Q j‖*‖A.tensorPlaneRead i g.inner y‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C*H := mul_le_mul (hPa i k j).2.2 (hHnorm i y)
          (norm_nonneg _) (zero_le_one.trans hC))
    (fun i k j y hy => (hcell i k j y hy).1) G hG.1
    (A.selected_grid_pure_geometry hc hb houter ξ (fun i k j => (hPa i k j).1) hpt)
    (hpairs G hG) (fun i y hy => (hgeom i y hy).1)
    (fun i y hy => (hgeom i y hy).2.1)
    (fun i y hy => (hgeom i y hy).2.2.trans hgramD)
    (fun i k j y hy => ⟨(hcell i k j y hy).2.1,(hcell i k j y hy).2.2.1.trans hnormalD⟩)
    τ s hτ hs hτs hs1 (fun m => ⟨(hJbig m).1,(hJbig m).2.1⟩)
    (fun i k j m => ⟨?_,?_⟩) (fun i m l hl => ?_) hsmall f hf hsym hnear hfsize δ hδ hδτ
  · have hw0 : 0 ≤ w (i,k.val,j) := zero_le_one.trans (hw _).1
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hw0]
    exact ((mul_le_mul_of_nonneg_left (hPa i k j).2.1 hw0).trans
      (mul_le_mul_of_nonneg_right (hw _).2 (zero_le_one.trans hC))).trans (hJbig m).2.2.1
  · intro hn
    have hv := hV ⟨i,k,j⟩
    change w (i,k.val,j) • ξ (i,k.val,j) ∈ V at hv
    rw [(hPa i k j).1] at hv
    exact (hDinv _ hv hn).trans (hJbig m).2.2.2
  · apply (hjets i m l hl).mono_const
    apply div_le_div_of_nonneg_right _ (pow_nonneg hs.le _)
    dsimp [J]
    linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
