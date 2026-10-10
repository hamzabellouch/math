import OAI.Geometry.SurfaceImmersion.Geometry.AnchoredActualStep
import OAI.Geometry.SurfaceImmersion.Geometry.GeometricScaleThreshold
import OAI.Geometry.SurfaceImmersion.Geometry.UniformRadiusFixedOrderStep

namespace OAI

/-! Polynomial fixed-order thresholds for the actual anchored correction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes PhaseGeometry MetricGoodPhaseData
local instance anchoredFixedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance anchoredFixedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance anchoredFixedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance anchoredFixedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance anchoredFixedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance anchoredFixedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem anchored_fixed_order_step (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c B b : ℝ) (hc : 0 < c) (hB : 0 ≤ B) (hb : 0 < b) :
    ∃ z₀ a D : ℝ, 0 < z₀ ∧ z₀ ≤ 1 ∧ 0 < a ∧ 1 ≤ D ∧
    ∀ k : ℕ, 10 ≤ k → ∀ Budget : ℝ → ℝ, HasPolynomialBound Budget →
    ∃ ε : ℝ → ℝ, ∃ P L : ℕ → ℝ → ℝ,
      HasPolynomialBound (fun x => (ε x)⁻¹) ∧
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (L m)) ∧
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
    ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
    ∀ t : ℝ, 0 < t → t < ε z⁻¹ → ∀ j : ℕ, k ≤ j → j ≤ k+1 →
      A.InputBound t (40*(k+1)) (Budget z⁻¹) G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
      A.WeightedBound 1 2 ((z^4/D)/4) (G-F) →
      (∀ x, ‖A.tensorEncode (normalizedTensorDefect g.inner (t^(k : ℝ)) G) x-A.tensorEncode g.inner x‖ ≤ a/8) →
      ∃ U : M → Space, ContMDiff planeModel spaceModel ∞ U ∧
        (∀ m, A.WeightedBound (t^(6/5 : ℝ)) m (P m z⁻¹*(t^(k : ℝ)*t^(6/5 : ℝ))) U) ∧
        (∀ m ≤ k/2, A.WeightedBound 1 m ((z^4/D)*t) U) ∧
        ∀ m C, 0 ≤ C → A.InputBound t m C G (normalizedTensorDefect g.inner (t^(k : ℝ)) G) →
          A.TensorWeightedBound (t^(6/5 : ℝ)) m (L m z⁻¹*(1+Budget z⁻¹+C)*t^(1/5 : ℝ))
            (normalizedTensorDefect g.inner (t^((6/5 : ℝ)*(j : ℝ))) (G+U)-g.inner) := by
  classical
  obtain ⟨z₀,a,D,K,hz₀,hz₀1,ha,hD,hK,hall⟩ := A.anchored_actual_step g houter R c B b hc hB hb
  refine ⟨z₀,a,D,hz₀,hz₀1,ha,hD,?_⟩
  intro k hk Budget hBudget
  let r := 40*(k+1)
  obtain ⟨T,hT,hr⟩ := hall r
  obtain ⟨e,E,P,Q,Dm,Em,hE,hP,hQ,hDm,hEm,hbuild⟩ := hr r Budget hBudget
  let ρ := fun x : ℝ => 1/(D*x^4)
  let η := ExactCorrection.geometricScaleThreshold a E e
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hE0 : 0 < E := zero_lt_one.trans_le hE
  have hρ (x : ℝ) (hx : 1 ≤ x) : 0 < ρ x := by
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    dsimp [ρ]; positivity
  have hη (x : ℝ) (hx : 1 ≤ x) : 0 < η x := ExactCorrection.geometricScaleThreshold_pos ha hE0 e hx
  let ε := fun x => ExactCorrection.fixedOrderThreshold k (ρ x) a (η x) T (Budget x) K (fun m => P m x)
  have hε (x : ℝ) (hx : 1 ≤ x) := ExactCorrection.fixedOrderThreshold_spec k hk
    (ρ x) a (η x) T (Budget x) K (hρ x hx) ha (hη x hx) hT (hBudget.nonneg hx) hK (fun m => P m x)
  have hρinv : HasPolynomialBound (fun x => (ρ x)⁻¹) := by
    have hp := (polynomialBound_const hD0.le).mul (polynomialBound_id.pow 4)
    simpa only [ρ,one_div,inv_inv] using hp
  have hηinv : HasPolynomialBound (fun x => (η x)⁻¹) :=
    ExactCorrection.geometricScaleThreshold_inverse_polynomial ha hE0 e
  have hεpoly : HasPolynomialBound (fun x => (ε x)⁻¹) :=
    ExactCorrection.fixedOrderThreshold_inverse_polynomial k ρ (fun _ => a) η
      (fun _ => T) Budget (fun _ => K) P (fun x => (ρ x)⁻¹) (fun _ => a⁻¹) (fun x => (η x)⁻¹)
      (polynomialBound_const hT) hBudget (polynomialBound_const hK) hP hρinv
      (polynomialBound_const (inv_nonneg.mpr ha.le)) hηinv hρ (fun _ _ => ha) hη
      (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  let L := fun m x => Dm m*tailConstant r+Em m*P (m+1) x*(Dm m*tailConstant r)+2*Q m x
  have hL (m : ℕ) : HasPolynomialBound (L m) := by
    exact ((polynomialBound_const (mul_nonneg (hDm m) (tailConstant_nonneg r))).add
      (((polynomialBound_const (hEm m)).mul (hP (m+1))).mul
        (polynomialBound_const (mul_nonneg (hDm m) (tailConstant_nonneg r))))).add
      ((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul (hQ m))
  refine ⟨ε,P,L,hεpoly,hP,hL,fun x hx => ⟨(hε x hx).1,(hε x hx).2.1⟩,?_⟩
  intro z hz hzsmall F hF hFb hFm G hG t ht htε j hkj hjk hinput hnear hmetric
  have hx : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr (hzsmall.trans hz₀1)
  have hρform : ρ z⁻¹ = z^4/D := by
    dsimp [ρ]
    rw [inv_pow]
    field_simp
  have ht1 : t ≤ 1 := htε.le.trans (hε z⁻¹ hx).2.1
  obtain ⟨hτη,htail,hratio,hlow,hδ'δ,hmin⟩ := (hε z⁻¹ hx).2.2 t ht htε j hkj hjk
  rw [hρform] at htail hlow
  obtain ⟨hminpos,hδ,hτ,hs⟩ := ExactCorrection.exact_scale_positive ht k
  have hδ' : 0 < t^((6/5 : ℝ)*(j : ℝ)) := Real.rpow_pos_of_pos ht _
  obtain ⟨_,hδτ,hτs,hst⟩ := ExactCorrection.exact_scale_order ht ht1 hk
  obtain ⟨U,hU,hUB,herror⟩ := hbuild z hz hzsmall F hF hFb hFm G hG (t^(k : ℝ))
    (t^((6/5 : ℝ)*(j : ℝ))) t (t^(11/10 : ℝ)) (t^(6/5 : ℝ))
    hδ hδ' hδ'δ ht ht1 hs hst hτ hτs hδτ hτη hinput hnear hmetric htail hratio
  refine ⟨U,hU,hUB,?_,?_⟩
  · intro m hm i j hj x hx'
    have hb' := (hUB j i).deriv_le hτ (le_refl j) hx'
    have hh := hb'.trans (hlow j (hj.trans hm))
    simpa only [one_pow,one_mul] using hh
  · intro m C hC hCm i
    apply (herror m C hC hCm i).mono_const
    have he : normalizedStepBound r r (Budget z⁻¹) (Dm m) (Em m) ((P (m+1) z⁻¹)) ((Q m z⁻¹)) C
        (t^(k : ℝ)) (t^((6/5 : ℝ)*(j : ℝ)))
        (t^(6/5 : ℝ)) (t^(11/10 : ℝ)) t =
      ((t^((6/5 : ℝ)*(j : ℝ)))^2)⁻¹ *
        (((t^(k : ℝ))^2 + Em m*(P (m+1) z⁻¹)*t^(k : ℝ)) * (Dm m*tailConstant r) *
          ((Budget z⁻¹)*(t^(11/10 : ℝ)/t)^r+C*(t^(6/5 : ℝ)/t)^r) +
          (Q m z⁻¹)*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(r+1)+
            (t^(k : ℝ))^3/t^(6/5 : ℝ))) := by
      unfold normalizedStepBound
      field_simp [hτ.ne']
    rw [he]
    have hden : ((t^((6/5 : ℝ)*(j : ℝ)))^2)⁻¹ ≤
        ((t^((6/5 : ℝ)*((k : ℝ)+1)))^2)⁻¹ := by
      apply (inv_le_inv₀ (sq_pos_of_pos hδ') (sq_pos_of_pos hminpos)).mpr
      nlinarith
    have hdm := hDm m
    have hem := hEm m
    have hbm := ((hP (m+1)).nonneg hx)
    have htm := ((hQ m).nonneg hx)
    have htc := tailConstant_nonneg r
    have hB₀ := hBudget.nonneg hx
    have hnum : 0 ≤
        (((t^(k : ℝ))^2 + Em m*(P (m+1) z⁻¹)*t^(k : ℝ)) * (Dm m*tailConstant r) *
          ((Budget z⁻¹)*(t^(11/10 : ℝ)/t)^r+C*(t^(6/5 : ℝ)/t)^r) +
          (Q m z⁻¹)*(t^(k : ℝ)*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(r+1)+
            (t^(k : ℝ))^3/t^(6/5 : ℝ))) := by positivity
    exact (mul_le_mul_of_nonneg_right hden hnum).trans
      (ExactCorrection.normalized_step_envelope_nat_succ ht ht1 hk (hBudget.nonneg hx) hC
        (mul_nonneg (hDm m) (tailConstant_nonneg r)) (hEm m) (((hP (m+1)).nonneg hx)) (((hQ m).nonneg hx)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
