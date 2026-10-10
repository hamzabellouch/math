import OAI.Geometry.SurfaceImmersion.Geometry.AnchoredFixedOrderStep
import OAI.Geometry.SurfaceImmersion.Geometry.ExactInputRecurrence
import OAI.Geometry.SurfaceImmersion.Geometry.InputSize

namespace OAI

/-! The full next-input recurrence with polynomial fast-family constants. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry
local instance anchoredInputFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredInputFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredInputDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredInputDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance anchoredInputSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredInputSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem anchored_input_step (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ Base : ℝ → ℝ, HasPolynomialBound Base →
    ∃ A₀ : ℝ → ℝ, HasPolynomialBound A₀ ∧
    ∀ Budget : ℝ → ℝ, HasPolynomialBound Budget → ∀ k : ℕ, 10 ≤ k →
    ∃ ε L : ℝ → ℝ, ∃ N : ℕ → ℝ → ℝ,
      HasPolynomialBound (fun x => (ε x)⁻¹) ∧ HasPolynomialBound L ∧
      (∀ m, HasPolynomialBound (N m)) ∧
      (∀ x, 1 ≤ x → 0 < ε x ∧ ε x ≤ 1) ∧
    ∀ z : ℝ, 0 < z → z ≤ z₀ → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F →
      (∀ i, WeightedEstimates.WeightedBound univ z 3 B (spaceCoordinates ∘ A.vectorPlaneRead i F)) →
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖) →
      A.ShiftedBound 2 0 1 (Base z⁻¹) F →
    ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε z⁻¹ → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      A.InputBound t (40*(k+1)) (Budget z⁻¹) G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
      A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
      (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m ≤ k/2, A.WeightedBound 1 m ((z^4/D)*t) U) ∧
        A.TensorWeightedBound (t^(6/5 : ℝ)) 0 (L z⁻¹*(1+2*Budget z⁻¹)*t^(1/5 : ℝ))
          (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) ∧
        ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
          A.InputBound (t^(6/5 : ℝ)) m (A₀ z⁻¹+N m z⁻¹*t^(1/5 : ℝ)*(1+C))
            (G+U) (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)) := by
  classical
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hall⟩ := A.anchored_fixed_order_step g houter R c B b hc hB hb
  choose Pg hPg hgb using fun m => A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain m g.contMDiff
  refine ⟨z₀,a,D,hz₀,hz₀1,ha,hD,?_⟩
  intro Base hBase
  let A₀ := fun x => Base x+1+Pg 0
  have hA₀ : HasPolynomialBound A₀ := ((hBase.add (polynomialBound_const zero_le_one)).add
    (polynomialBound_const (hPg 0)))
  refine ⟨A₀,hA₀,?_⟩
  intro Budget hBudget k hk
  obtain ⟨ε,P,L,hε,hP,hL,hεp,hstep⟩ := hall k hk Budget hBudget
  let N := fun m x => Pg m+P (m+2) x+L m x*(1+Budget x)+1+L m x
  have hN (m : ℕ) : HasPolynomialBound (N m) :=
    ((((polynomialBound_const (hPg m)).add (hP (m+2))).add
      ((hL m).mul ((polynomialBound_const zero_le_one).add hBudget))).add
      (polynomialBound_const zero_le_one)).add (hL m)
  refine ⟨ε,L 0,N,hε,hL 0,hN,hεp,?_⟩
  intro z hz hzsmall F hF hFb hFm hbase G hG t ht htε j hkj hjk hinput hnear hmetric
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  have hBaseN := hBase.nonneg hx
  have ht1 : t ≤ 1 := htε.le.trans (hεp z⁻¹ hx).2
  obtain ⟨U,hU,hUB,hsmall,herror⟩ := hstep z hz hzsmall F hF hFb hFm G hG t ht htε j hkj hjk hinput hnear hmetric
  have hbase' : A.WeightedBound 1 2 (Base z⁻¹) F := by
    intro i l hl x _
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hbase i l (by omega) x
  have hsum := A.weightedBound_add hF (hG.sub hF) zero_le_one hbase' hnear
  change A.WeightedBound 1 2 (Base z⁻¹+(z^4/D)/4) (F+(G-F)) at hsum
  have heG : F+(G-F) = G := by abel
  rw [heG] at hsum
  have hρ1 : (z^4/D)/4 ≤ 1 := by
    have hz1 := hzsmall.trans hz₀1
    have hz4 : z^4 ≤ 1 := pow_le_one₀ hz.le hz1
    have hd0 : 0 < D := zero_lt_one.trans_le hD
    have hh : z^4/D ≤ 1 := (div_le_one hd0).mpr (hz4.trans hD)
    linarith
  have hGbase : A.WeightedBound 1 2 (Base z⁻¹+1) G :=
    fun i => (hsum i).mono_const (by linarith)
  have hbaseline : A.ShiftedBound 2 0 t (Base z⁻¹+1) G := by
    intro i l hl x
    have hl2 : l ≤ 2 := by omega
    have hh := hGbase i l hl2 x (mem_univ x)
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,Nat.sub_eq_zero_of_le hl2,pow_zero] using hh
  refine ⟨U,hU,hsmall,?_,?_⟩
  · have hi0 := A.inputBound_mono_order hinput (show 0 ≤ 40*(k+1) from Nat.zero_le _)
    simpa only [show 1+Budget z⁻¹+Budget z⁻¹ = 1+2*Budget z⁻¹ by ring] using
      herror 0 (Budget z⁻¹) (hBudget.nonneg hx) hi0
  · intro m C hC hCm
    have hUB' : A.WeightedBound (t^(6/5 : ℝ)) (2+m)
        (P (m+2) z⁻¹*(t^(k : ℝ)*t^(6/5 : ℝ))) U := by
      simpa only [Nat.add_comm] using hUB (m+2)
    exact A.exact_scale_input_recurrence hG hU ht ht1 hk
      (by positivity) (hPg 0) (hPg m) ((hP (m+2)).nonneg hx) hC ((hL m).nonneg hx)
      (hBudget.nonneg hx) hbaseline hCm.1 hUB' (hgb 0) (hgb m) (herror m C hC hCm)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
