import OAI.Geometry.SurfaceImmersion.Correction.MetricPolynomialIncrement
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveUpdate
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveSlowErrorProfiles
import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds

namespace OAI

/-! One uniform step of the finite slow-map construction. The derivative
profiles and the small parameter threshold precede the nearby map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PrimitiveRealization
local instance slowPolynomialFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance slowPolynomialFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance slowPolynomialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance slowPolynomialDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance slowPolynomialSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance slowPolynomialSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace MetricGoodPhaseData
variable {g : SmoothMetric M} {F : M → Space}

/-- An actual primitive update improves the amplitude exponent and retains
uniform all-order profiles. The fixed loss is chosen before every scale. -/
theorem polynomial_slow_step (data : MetricGoodPhaseData g F)
    {n : data.A.centers → ℕ}
    (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ loss : ℕ, ∀ (b b' d d' a u : ℝ), 0 ≤ b → b < b' → b'*(loss : ℝ) < 1 →
      2*b' < d → d < d' → 2*d' < 3*d-b' → 0 < a → 0 < u →
    ∀ (P D : ℕ → ℝ) (L : ℝ), (∀ m, 0 ≤ P m) → (∀ m, 0 ≤ D m) → 0 ≤ L →
      (∀ m, data.A.ShiftedBound 2 m 1 (P m) F) →
    ∃ (a' η L' : ℝ) (P' D' : ℕ → ℝ), 0 < a' ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ L' ∧
      (∀ m, 0 ≤ P' m) ∧ (∀ m, 0 ≤ D' m) ∧
    ∀ z : ℝ, 0 < z → z < η → ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G →
      data.A.WeightedBound 1 3 (L*z^u) (G-F) →
      (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) →
      (∀ m, data.A.TensorWeightedBound (z^b) m (D m*z^a)
        (data.A.normalizedPolynomialDefect Pol z (z^d) g.inner G)) →
      ∃ G' : M → Space, ContMDiff planeModel spaceModel ∞ G' ∧
        data.A.WeightedBound 1 3 (L'*z^(min u (d-2*b'))) (G'-F) ∧
        (∀ m, data.A.ShiftedBound 2 m (z^b') (P' m) G') ∧
        (∀ m, data.A.TensorWeightedBound (z^b') m (D' m*z^a')
          (data.A.normalizedPolynomialDefect Pol z (z^d') g.inner G')) := by
  classical
  obtain ⟨loss,hstep⟩ := data.polynomial_small_increment Pol hPol hF
  refine ⟨loss,?_⟩
  intro b b' d d' a u hb hbb hloss hbd2 hdd hcubic ha hu P D L hP hD hL hPF
  have hbd : b' < d := by linarith
  let κ : ℝ := min (b'-b) (1-b'*(loss : ℝ))
  have hκ : 0 < κ := lt_min (sub_pos.mpr hbb) (sub_pos.mpr hloss)
  obtain ⟨q,hq⟩ := exists_nat_gt ((2*d'-d)/κ)
  have hlinear : 0 < d+κ*(q+1)-2*d' := by
    have hh := (div_lt_iff₀ hκ).mp hq
    nlinarith
  let a' := min (d+κ*(q+1)-2*d') (3*d-b'-2*d')
  have ha' : 0 < a' := lt_min hlinear (by linarith)
  choose K hK hKg using fun m => data.A.exists_bundle_bound data.A.tensorTriv
    data.A.tensorTriv_domain m g.contMDiff
  let C : ℕ → ℝ := fun m => 1+2*K m+D m
  have hC (m : ℕ) : 1 ≤ C m := by
    dsimp [C]
    linarith [hK m,hD m]
  obtain ⟨r,hr,hprof⟩ := hstep P hP hPF q
  obtain ⟨ρ,η₀,B,T,hρ,hη₀,hη₀1,hB,hT,hsolve⟩ := hprof C hC
  obtain ⟨η₁,hη₁,_,h₁⟩ := ExactCorrection.positive_power_threshold L u ρ hu hρ
  obtain ⟨η₂,hη₂,_,h₂⟩ := ExactCorrection.positive_power_threshold (D 0) a (r/4) ha (by positivity)
  obtain ⟨η₃,hη₃,_,h₃⟩ := ExactCorrection.positive_power_threshold (K 0) (2*d'-2*d)
    (r/4) (by linarith) (by positivity)
  obtain ⟨η₄,hη₄,_,h₄⟩ := ExactCorrection.positive_power_threshold 2 κ η₀ hκ hη₀
  let η := min 1 (min η₁ (min η₂ (min η₃ η₄)))
  have hη : 0 < η := lt_min zero_lt_one (lt_min hη₁ (lt_min hη₂ (lt_min hη₃ hη₄)))
  let P' : ℕ → ℝ := fun m => P 0+P m+B (2+m)
  let D' : ℕ → ℝ := fun m => T m*(2^(q+1)+1)
  refine ⟨a',η,L+B 3,P',D',ha',hη,min_le_left _ _,add_nonneg hL (hB 3),
    fun m => add_nonneg (add_nonneg (hP 0) (hP m)) (hB (2+m)),
    fun m => mul_nonneg (hT m) (by positivity),?_⟩
  intro z hz hzη G hG hclose hmap hdefect
  have hclose2 : data.A.WeightedBound 1 2 (L*z^u) (G-F) :=
    fun i => (hclose i).mono_order (by omega)
  have hz1 : z ≤ 1 := hzη.le.trans (min_le_left _ _)
  have hzη₁ : z < η₁ := hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzη₂ : z < η₂ := hzη.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hzη₃ : z < η₃ := hzη.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hzη₄ : z < η₄ := hzη.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hs : 0 < z^b := Real.rpow_pos_of_pos hz _
  have hτ : 0 < z^b' := Real.rpow_pos_of_pos hz _
  have hδ : 0 < z^d := Real.rpow_pos_of_pos hz _
  have hδ' : 0 < z^d' := Real.rpow_pos_of_pos hz _
  have hs1 : z^b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  have hτs : z^b' ≤ z^b := Real.rpow_le_rpow_of_exponent_ge hz hz1 hbb.le
  have hτ1 : z^b' ≤ 1 := hτs.trans hs1
  have hδτ : z^d ≤ z^b' := Real.rpow_le_rpow_of_exponent_ge hz hz1 hbd.le
  have hδδ : z^d' ≤ z^d := Real.rpow_le_rpow_of_exponent_ge hz hz1 hdd.le
  have hza : z^a ≤ 1 := Real.rpow_le_one hz.le hz1 ha.le
  let H := data.A.polynomialMeanTarget Pol z (z^d) (z^d') g.inner G
  have hH := data.A.polynomialMeanTarget_smooth (ε := z) (δ := z^d) (δ' := z^d') hPol g.contMDiff hG
  have hHs : ∀ x v w, H x v w = H x w v := by
    intro x v w
    change ((z^d)^2)⁻¹*(g.inner x v w-data.A.atlasPolynomialMetric Pol z G x v w-
      (z^d')^2*g.inner x v w) =
      ((z^d)^2)⁻¹*(g.inner x w v-data.A.atlasPolynomialMetric Pol z G x w v-
        (z^d')^2*g.inner x w v)
    rw [g.symm x v w,data.A.atlasPolynomialMetric_symmetric Pol z G x v w]
  have hHbound (m : ℕ) : data.A.TensorWeightedBound (z^b) m (C m) H := by
    have hbase : data.A.TensorWeightedBound (z^b) m (K m) g.inner :=
      fun i => (hKg m i).shrink_scale hs.le hs1
    have hd := data.A.polynomialMeanTarget_bound hPol hδ hδ'.le hδδ hs.le (hK m)
      g.contMDiff hG hbase (hdefect m)
    intro i
    apply (hd i).mono_const
    dsimp [C]
    have hh := mul_le_of_le_one_right (hD m) hza
    linarith
  have hratio : (z^d')^2/(z^d)^2 = z^(2*d'-2*d) := by
    rw [← Real.rpow_mul_natCast hz.le,← Real.rpow_mul_natCast hz.le,← Real.rpow_sub hz]
    congr 1
    ring
  have hHnear (x : JetPolynomial.Base) :
      ‖data.A.tensorEncode H x-data.A.tensorEncode g.inner x‖ ≤ r/2 := by
    have hnorm := (data.A.tensorEncode_bound
      (data.A.normalizedPolynomialDefect_smooth (ε := z) (δ := z^d) hPol g.contMDiff hG)
      hs (mul_nonneg (hD 0) (Real.rpow_nonneg hz.le _)) (hdefect 0)).norm_le (mem_univ x)
    have hnormg := (data.A.tensorEncode_bound g.contMDiff zero_lt_one (hK 0) (hKg 0)).norm_le (mem_univ x)
    have hh := data.A.polynomialMeanTarget_distance Pol z (z^d) (z^d') g.inner G x hnorm hnormg
    rw [hratio] at hh
    dsimp [H]
    exact hh.trans (by
      have hd := h₂ z hz hzη₂
      have hg := h₃ z hz hzη₃
      nlinarith)
  let ratio := z^b'/z^b+z/(z^b')^loss
  have hratio0 : 0 ≤ ratio := add_nonneg (div_nonneg hτ.le hs.le)
    (div_nonneg hz.le (pow_nonneg hτ.le _))
  have hratioB : ratio ≤ 2*z^κ := slow_parameter_bound_of_exponents hz hz1
  have hratioη : ratio ≤ η₀ := hratioB.trans (h₄ z hz hzη₄).le
  obtain ⟨X,hX,hXb,hXe⟩ := hsolve G hG (L*z^u)
    (mul_nonneg hL (Real.rpow_nonneg hz.le _)) (h₁ z hz hzη₁) hclose2
    ⟨z^b,hs.le⟩ hs hs1 hmap H hH hHs hHnear hHbound
    (z^b') (z^d) z hτ hτs hz.le hz1 hratioη hδ hδτ
  have hprop := data.A.polynomial_increment_propagation hPol g.contMDiff hF hG hX
    hs hτ hτs hτ1 hδ hδ' P B
    (fun m => T m*(z^d*ratio^(q+1)+(z^d)^3/z^b')) hP hB hclose2 hmap hXb hXe
  have hX3 := data.A.weighted_increment_unscaled hτ hτ1
    (mul_nonneg (hB 3) (mul_nonneg hδ.le hτ.le)) (hXb 3)
  have hX3' : data.A.WeightedBound 1 3 (B 3*z^(d-2*b')) X := by
    have heq : B 3*(z^d*z^b')/(z^b')^3 = B 3*z^(d-2*b') := by
      rw [← Real.rpow_mul_natCast hz.le,← Real.rpow_add hz, mul_div_assoc,← Real.rpow_sub hz]
      congr 2
      ring
    simpa only [heq] using hX3
  have hclose3 := data.A.weightedBound_add (hG.sub hF) hX zero_le_one hclose hX3'
  change data.A.WeightedBound 1 3 (L*z^u+B 3*z^(d-2*b')) ((G-F)+X) at hclose3
  have hadd : (G-F)+X = G+X-F := by abel
  rw [hadd] at hclose3
  refine ⟨G+X,hG.add hX,?_,?_,?_⟩
  · intro i
    apply (hclose3 i).mono_const
    have hu' := Real.rpow_le_rpow_of_exponent_ge hz hz1 (min_le_left u (d-2*b'))
    have hd' := Real.rpow_le_rpow_of_exponent_ge hz hz1 (min_le_right u (d-2*b'))
    exact (add_le_add (mul_le_mul_of_nonneg_left hu' hL)
      (mul_le_mul_of_nonneg_left hd' (hB 3))).trans_eq (by ring)
  · intro m i j hj x
    apply (hprop.2.1 m i j hj x).trans
    change P 0+P m+B (2+m)*z^d/z^b' ≤ P 0+P m+B (2+m)
    rw [mul_div_assoc,← Real.rpow_sub hz]
    have hh := Real.rpow_le_one hz.le hz1 (sub_nonneg.mpr hbd.le)
    linarith [mul_le_of_le_one_right (hB (2+m)) hh]
  · intro m i
    apply (hprop.2.2 m i).mono_const
    exact normalized_slow_error_profile hz hz1 (hT m) hratio0 hratioB
      (by simpa only [Nat.cast_add,Nat.cast_one] using
        (min_le_left (d+κ*(q+1)-2*d') (3*d-b'-2*d')))
      (min_le_right _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
