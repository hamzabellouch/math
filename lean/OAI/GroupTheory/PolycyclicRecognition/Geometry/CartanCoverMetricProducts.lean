import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoverWordBoxes
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricChainWords

namespace OAI

/-! # Absorbing metric products in a fixed exponential Cartan box -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set Metric
open scoped Manifold

attribute [local instance] semidirectProductTopology

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

include T hExp hπExp hπcont in
theorem CartanWordModel.exists_cover_metric_action_box_bound
    (dS : ProperChainMetric (F.N.carrier ⋊[F.action] F.D.carrier))
    (dD : ProperChainMetric F.D.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW)) β.val) :
    letI := dS.compatibleMetric
    letI := dD.compatibleMetric
    ∃ A : ℝ, 1 ≤ A ∧ ∀ r : ℝ, 1 ≤ r → ∀ d : F.D.carrier, dist 1 d ≤ r →
      ∀ q : F.N.carrier ⋊[F.action] F.D.carrier, dist 1 q ≤ r →
      F.action d q.left ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (M.samplingPolytope T hunimod eW) β (A * r) 1 := by
  let := dS.compatibleMetric
  let := dD.compatibleMetric
  let : IsIsometricSMul (F.N.carrier ⋊[F.action] F.D.carrier)
      (F.N.carrier ⋊[F.action] F.D.carrier) := dS.isometric_compatibleMetric
  let : IsIsometricSMul F.D.carrier F.D.carrier := dD.isometric_compatibleMetric
  let : ProperSpace (F.N.carrier ⋊[F.action] F.D.carrier) := dS.proper_compatibleMetric
  let : ProperSpace F.D.carrier := dD.proper_compatibleMetric
  let cS := dS.chains_compatibleMetric
  let cD := dD.chains_compatibleMetric
  let e := semidirectProductHomeomorph F.action
  let K : Set (F.N.carrier × F.D.carrier) :=
    e '' closedBall 1 cS.step ∪ (fun d : F.D.carrier => ((1 : F.N.carrier), d)) '' closedBall 1 cD.step
  have hK : IsCompact K := (isCompact_closedBall 1 cS.step).image e.continuous |>.union
    ((isCompact_closedBall 1 cD.step).image (continuous_const.prodMk continuous_id))
  obtain ⟨A, hA, hword⟩ := M.exists_compact_cover_list_box_bound T F hExp hunimod eW
    π hπExp hπcont b₀ β hβ hK
  let L := A * (1 + cD.slope + cD.error + cS.slope + cS.error)
  have hL : 1 ≤ L := by
    have h1 : 1 ≤ 1 + cD.slope + cD.error + cS.slope + cS.error := by
      linarith [cD.slope_nonneg, cD.error_nonneg, cS.slope_nonneg, cS.error_nonneg]
    simpa only [one_mul] using (mul_le_mul hA h1 zero_le_one (by linarith))
  refine ⟨L, hL, ?_⟩
  intro r hr d hd q hq
  obtain ⟨u, hu, heU, hnU⟩ := cD.wordFactorization d
  obtain ⟨v, hv, heV, hnV⟩ := cS.wordFactorization q
  let w := u.map (SemidirectProduct.inr : F.D.carrier →* F.N.carrier ⋊[F.action] F.D.carrier) ++ v
  have hw : ∀ x ∈ w, (x.left, x.right) ∈ K := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hx
      exact Or.inr ⟨d', hu d' hd', rfl⟩
    · exact Or.inl ⟨x, hv x hx, rfl⟩
  have hp : w.prod = SemidirectProduct.inr d * q := by
    simp only [w, List.prod_append, ← map_list_prod, heU, heV]
  have hb := hword w hw
  rw [hp, SemidirectProduct.mul_left, SemidirectProduct.left_inr, one_mul,
    SemidirectProduct.right_inr] at hb
  have hlen : A * (1 + (w.length : ℝ)) ≤ L * r := by
    have hU := hnU.trans (add_le_add (mul_le_mul_of_nonneg_left hd cD.slope_nonneg) le_rfl)
    have hV := hnV.trans (add_le_add (mul_le_mul_of_nonneg_left hq cS.slope_nonneg) le_rfl)
    have he : (w.length : ℝ) = u.length + v.length := by
      simp only [w, List.length_append, List.length_map, Nat.cast_add]
    have h0 : 1 + (w.length : ℝ) ≤
        (1 + cD.slope + cD.error + cS.slope + cS.error) * r := by
      rw [he]
      nlinarith [mul_nonneg cD.error_nonneg (sub_nonneg.mpr hr),
        mul_nonneg cS.error_nonneg (sub_nonneg.mpr hr)]
    exact (mul_le_mul_of_nonneg_left h0 (by linarith)).trans_eq (by dsimp [L]; ring)
  obtain ⟨x, hx, hxb⟩ := hb
  refine ⟨x, hx, ?_⟩
  exact (norm_exponentialRescaleBasis_mono _ _
    (fun j => (bracketWordExponent_pos _ (M.sampling_weightSupport_pos T hunimod eW)
      (β.val j)).le) hlen x).trans hxb

end PolycyclicRecognition

end

end OAI
