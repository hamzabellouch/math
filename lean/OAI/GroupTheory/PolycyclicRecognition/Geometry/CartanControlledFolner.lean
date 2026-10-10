import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoverMetricProducts
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoverBoxRadius
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledProductPairs
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxNeighborhood
import OAI.GroupTheory.PolycyclicRecognition.Analysis.HaarBoxRadius
import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialBallScales

namespace OAI

/-! # Concrete controlled Følner pairs on the Cartan semidirect cover

Exponentially large nilpotent boxes are paired with good-volume Cartan balls.
Right multiplication by a metric ball enlarges the box radius by a constant,
and the Cartan ball radius by at most three. Both volume ratios are bounded.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped Manifold ENNReal

attribute [local instance] semidirectProductTopology semidirectProductMeasurableSpace
  semidirectProduct_borelSpace

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (M : CartanWordModel H) (hExp : IsGroupExponential Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (hπcont : Continuous (fun g => (π g).toAdd))

include T M hExp hunimod hπExp hπcont in
theorem cartan_cover_controlled_pairs
    [SecondCountableTopology F.N.carrier] [SecondCountableTopology F.D.carrier]
    (dS : ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier))
    (dD : ProperChainMetric F.D.carrier)
    (μN : Measure F.N.carrier) [μN.IsHaarMeasure]
    (μD : Measure F.D.carrier) [μD.IsHaarMeasure] :
    letI := dS.compatibleMetric
    Nonempty (ControlledMetricFolnerPairs (semidirectProductMeasure F.action μN μD)) := by
  let := dS.compatibleMetric
  let := dD.compatibleMetric
  let : IsTopologicalGroup (F.N.carrier ⋊[F.action] F.D.carrier) := F.semidirect_topologicalGroup
  let : IsTopologicalGroup F.D.carrier := topologicalGroup_of_lieGroup (𝓘(ℝ, F.D.modelSpace)) ⊤
  let : IsIsometricSMul (F.N.carrier ⋊[F.action] F.D.carrier)
      (F.N.carrier ⋊[F.action] F.D.carrier) := dS.isometric_compatibleMetric
  let : IsIsometricSMul F.D.carrier F.D.carrier := dD.isometric_compatibleMetric
  let : ProperSpace (F.N.carrier ⋊[F.action] F.D.carrier) := dS.proper_compatibleMetric
  let : ProperSpace F.D.carrier := dD.proper_compatibleMetric
  let : LocallyCompactSpace F.N.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, F.N.modelSpace))
  have nilp := nilpotentPublishedInputs
  have hNnil := cartanRootIdeal_nilpotent H T
  have haarN := nilp.haar _ F.N
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN (F.N.tangent_nilpotent hNnil)
  let b₀ := finBasis ℝ (cartanRootIdeal H)
  let E := M.samplingPolytope T hunimod eW
  obtain ⟨β, hβ⟩ := exists_maximizing_wordBasis M.letter M.wordList b₀
    (M.boxCost T hunimod eW E)
  obtain ⟨A, hA, haction⟩ := M.exists_cover_metric_action_box_bound T F hExp hunimod eW
    π hπExp hπcont dS dD b₀ β hβ
  obtain ⟨P, hP, hprod⟩ := M.exists_groupBox_product_bound T hunimod eW F.N.equiv
    F.ExpN F.isExpN (nilp.dynkin _ F.N) b₀
  let R := max (P * 3 ^ M.bound * 2 ^ M.bound) 1
  have hR : 1 ≤ R := le_max_right _ _
  obtain ⟨K, B, hK, hB, hprojection⟩ := continuousHom_coarseLipschitz dS.chains_compatibleMetric
    (SemidirectProduct.rightHom : (F.N.carrier ⋊[F.action] F.D.carrier) →* F.D.carrier)
    (continuous_semidirect_right F.action)
  obtain ⟨KI, BI, hKI, hBI, hinr⟩ := continuousHom_coarseLipschitz dD.chains_compatibleMetric
    (SemidirectProduct.inr : F.D.carrier →* F.N.carrier ⋊[F.action] F.D.carrier)
    (continuous_semidirect_inr F.action)
  obtain ⟨t, V, ht, htlim, hV, htvol⟩ := nilpotent_closedBall_tripling_scales_above μD
    dD.chains_compatibleMetric (nilp.dynkin _ F.D) (nilp.haar _ F.D) F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance) B
  have ht1 (n : ℕ) : 1 ≤ t n := (le_max_right B 1).trans (ht n)
  have htB (n : ℕ) : B ≤ t n := (le_max_left B 1).trans (ht n)
  let c := 2 * (K + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : 2 ≤ c := by dsimp [c]; linarith
  have hcK : 2 * K ≤ c := by dsimp [c]; linarith
  let scale := fun n => t n / c
  have hscale (n : ℕ) : 0 < scale n := div_pos (by linarith [ht1 n]) hc
  have hlim : Tendsto scale atTop atTop := htlim.atTop_div_const hc
  let small := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (A * t n) 1
  let large := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (A * t n) R
  let b := fun n => M.boxBasis T hunimod eW E β (A * t n)
  have hsmall (n : ℕ) : IsCompact (small n) :=
    isCompact_exponentialCoordinateBox F.N.equiv.toLinearEquiv F.ExpN chartN hchartN
      (b n) 1 zero_le_one
  have hlarge (n : ℕ) : IsCompact (large n) :=
    isCompact_exponentialCoordinateBox F.N.equiv.toLinearEquiv F.ExpN chartN hchartN
      (b n) R (by linarith)
  let s := (M.supportIn T hunimod eW).weightSupport E
  let U := ∑ i, s i
  have hs (i : Fin M.letterCount) : 0 < s i := M.sampling_weightSupport_pos T hunimod eW i
  have hU : 0 ≤ U := Finset.sum_nonneg (fun i _ => (hs i).le)
  have hsi (i : Fin M.letterCount) : s i ≤ U :=
    Finset.single_le_sum (fun i _ => (hs i).le) (Finset.mem_univ i)
  obtain ⟨CN, hCN, hboxrad⟩ := exists_semidirect_box_metric_bound T F M hExp dS b₀ 1 hU
  let radius := c * (CN * (1 + A) + KI + BI)
  have hradius : 0 ≤ radius := by dsimp [radius]; positivity
  refine ⟨controlledMetricFolnerPairs_of_product_sets (semidirectProductHomeomorph F.action)
    μN μD scale hscale hlim small large (fun n => closedBall 1 (t n))
    (fun n => closedBall 1 (3 * t n)) hsmall hlarge
    (fun _ => isCompact_closedBall _ _) (fun _ => isCompact_closedBall _ _)
    (fun n => exponentialCoordinateBox_nonempty F.N.equiv F.ExpN (b n) zero_le_one)
    (fun n => ⟨1, by simp only [mem_closedBall, dist_self]; linarith [ht1 n]⟩)
    (fun n => exponentialCoordinateBox_measureReal_pos F.N.equiv F.ExpN F.isExpN
      chartN hchartN (b n) μN zero_lt_one)
    (fun n => closedBall_measureReal_pos μD (by linarith [ht1 n]))
    (R := radius) (CN := R ^ finrank ℝ (cartanRootIdeal H)) (CD := V)
    hradius (pow_nonneg (by linarith) _) hV ?_ ?_ ?_ htvol⟩
  · intro n x hx
    have ht0 : 0 ≤ t n := (zero_le_one.trans (ht1 n))
    have hA0 : 0 ≤ A := zero_le_one.trans hA
    obtain ⟨v, hv, hvb⟩ := hx.1
    change F.ExpN (F.N.equiv v) = x.left at hv
    have hn := hboxrad s hsi β hβ (A * t n) (by positivity) v hvb
    rw [hv] at hn
    have hd := hinr 1 x.right
    simp only [map_one] at hd
    have hxd : dist 1 x.right ≤ t n := by
      have hm : x.right ∈ closedBall 1 (t n) := hx.2
      change dist x.right 1 ≤ t n at hm
      rwa [dist_comm] at hm
    have hd' := hd.trans (add_le_add (mul_le_mul_of_nonneg_left hxd hKI) le_rfl)
    have htotal := (dist_one_mul_le
      (SemidirectProduct.inl x.left) (SemidirectProduct.inr x.right)).trans (add_le_add hn hd')
    rw [SemidirectProduct.inl_left_mul_inr_right] at htotal
    apply htotal.trans
    dsimp only [radius, scale]
    have he : c * (CN * (1 + A) + KI + BI) * (t n / c) =
        (CN * (1 + A) + KI + BI) * t n := by field_simp
    rw [he]
    nlinarith [mul_nonneg hCN (sub_nonneg.mpr (ht1 n)),
      mul_nonneg hBI (sub_nonneg.mpr (ht1 n))]
  · intro n x hx y hy
    have ht0 : 0 ≤ t n := by linarith [ht1 n]
    have h2scale : 2 * scale n ≤ t n := by
      dsimp only [scale]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hc).mpr
      nlinarith
    have hyt : dist 1 y ≤ t n := hy.trans h2scale
    have hxd : dist 1 x.right ≤ t n := by
      have hm : x.right ∈ closedBall 1 (t n) := hx.2
      change dist x.right 1 ≤ t n at hm
      rwa [dist_comm] at hm
    have ha := haction (t n) (ht1 n) x.right hxd y hyt
    have hmul := hprod E β hβ (A * t n) (by positivity) 2 1 zero_le_one
      ![x.left, F.action x.right y.left] (by
        intro i
        fin_cases i
        · exact hx.1
        · exact ha)
    have hmul' : x.left * F.action x.right y.left ∈ large n := by
      obtain ⟨v, hv, hvb⟩ := hmul
      have hRadius : P * (1 + (2 : ℝ)) ^ M.bound * (1 + 1) ^ M.bound ≤ R := by
        convert (le_max_left (P * 3 ^ M.bound * 2 ^ M.bound) 1) using 1; norm_num
      refine ⟨v, ?_, hvb.trans hRadius⟩
      simpa [List.ofFn_succ] using hv
    refine ⟨hmul', ?_⟩
    have hpy := hprojection 1 y
    simp only [map_one] at hpy
    change dist 1 y.right ≤ K * dist 1 y + B at hpy
    have hkScale : K * (2 * scale n) ≤ t n := by
      dsimp only [scale]
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply (div_le_iff₀ hc).mpr
      nlinarith
    have hpy' : dist 1 y.right ≤ 2 * t n := by
      have h := hpy.trans (add_le_add (mul_le_mul_of_nonneg_left hy hK) le_rfl)
      linarith [htB n]
    change x.right * y.right ∈ closedBall 1 (3 * t n)
    rw [mem_closedBall, dist_comm]
    exact (dist_one_mul_le x.right y.right).trans (by linarith)
  · intro n
    exact le_of_eq (haar_exponential_box_radius_real haarN F.N.equiv hNnil F.ExpN
      F.isExpN b₀ (b n) μN (by linarith))

end PolycyclicRecognition

end

end OAI
