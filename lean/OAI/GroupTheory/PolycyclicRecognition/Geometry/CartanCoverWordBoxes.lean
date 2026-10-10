import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUnitarySublinear
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCoverGeometry
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledBasisMonotone

namespace OAI

/-! # Exponential box bounds for all compact words in the cover

Bounded Cartan increments have linearly bounded height. The finite Dynkin
estimate gives a polynomial box radius, which is absorbed by increasing the
exponential scale by a fixed factor.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Set
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
theorem CartanWordModel.exists_compact_cover_word_box_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW)) β.val)
    {K : Set (F.N.carrier × F.D.carrier)} (hK : IsCompact K) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (m : ℕ) (u : ℕ → F.N.carrier) (v : ℕ → F.D.carrier),
      (∀ i < m, (u i, v i) ∈ K) →
      (wordPrefix (fun i => (⟨u i, v i⟩ : F.N.carrier ⋊[F.action] F.D.carrier)) m).left ∈
        M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
          (M.samplingPolytope T hunimod eW) β (A * (1 + (m : ℝ))) 1 := by
  have nilp := nilpotentPublishedInputs
  have haarN := nilp.haar _ F.N
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨⟨chartD, hchartD⟩, _⟩ := (nilp.haar _ F.D).2 F.ExpD F.isExpD
    (F.D.tangent_nilpotent inferInstance)
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨C, p, hC, hbound⟩ := M.exists_compact_semidirect_word_bound T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN (nilp.dynkin _ F.N)
    F.D.equiv F.ExpD F.isExpD chartD hchartD (nilp.dynkin _ F.D) F.action b₀ β hK
    (fun d => cartan_action_eq_adjoint_of_published_realization T M F hExp
      exponentialLinearRealizationInput_intrinsic hbijN hbijD (nilp.dynkin _ F.N) d)
  let E := M.samplingPolytope T hunimod eW
  have hE : IsCompact E := M.isCompact_samplingPolytope T hunimod eW
  have hball : Metric.closedBall (0 : W) 1 ⊆ E := closedBall_subset_weightSamplingPolytope _
  have hne : E.Nonempty := ⟨0, hball (by simp)⟩
  let s := (M.supportIn T hunimod eW).weightSupport E
  obtain ⟨lo, _, hlo, _, hcost⟩ := exists_positive_wordExponent_bounds s
    (M.sampling_weightSupport_pos T hunimod eW) M.wordList
  obtain ⟨A, B, hA, hB, habsorb⟩ := exists_affine_scale_absorbing_polynomial
    (WordBasisSelections.basis M.letter M.wordList β)
    (fun j => M.boxCost T hunimod eW E (β.val j)) hlo
    (fun j => (hcost (β.val j)).1) hC p
  have hc : Continuous (fun z : F.N.carrier × F.D.carrier => (π (F.inclusionD z.2)).toAdd) :=
    hπcont.comp (F.closedD.continuous.comp continuous_snd)
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  let D := max R 1
  have hD : 1 ≤ D := le_max_right _ _
  let L := max (A * D + B) 1
  refine ⟨L, le_max_right _ _, ?_⟩
  intro m u v huv
  let r := D * (1 + (m : ℝ))
  have hr : 0 < r := mul_pos (lt_of_lt_of_le zero_lt_one hD) (by positivity)
  have hm : (m : ℝ) ≤ r := by dsimp [r]; nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hh (i : ℕ) (hi : i < m) : ∃ w ∈ E,
      eW (heightProjection T.character (cartanLog H F.D.equiv F.ExpD hbijD
        (wordPrefix v i) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) = r • w := by
    let ψ := π.comp F.inclusionD
    let z : W := (ψ (wordPrefix v i)).toAdd
    have hn : ‖z‖ ≤ r := by
      have hb := norm_height_wordPrefix_le ψ v i (R := D) (fun j hj =>
        (hR (u j, v j) (huv j (hj.trans hi))).trans (le_max_left _ _))
      have him : (i : ℝ) ≤ m := by exact_mod_cast hi.le
      exact hb.trans (by dsimp [r]; nlinarith)
    refine ⟨r⁻¹ • z, hball ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hr, ← div_eq_inv_mul]
      exact (div_le_one hr).mpr hn
    · rw [← F.inclusionD_height T eW π hπExp hbijD]
      change z = r • (r⁻¹ • z)
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  obtain ⟨x, hx, hxb⟩ := hbound hE hne β hβ r hr.le m u v huv hh
  have hxpoly : ‖(M.boxBasis T hunimod eW E β r).equivFun x‖ ≤ C * (1 + r) ^ p :=
    hxb.trans (mul_le_mul_of_nonneg_left (by gcongr) hC)
  have hx1 := habsorb r hr.le x hxpoly
  refine ⟨x, hx, ?_⟩
  have ht : A * r + B ≤ L * (1 + (m : ℝ)) := by
    have hAB : A * D + B ≤ L := le_max_left _ _
    dsimp only [r]
    nlinarith [mul_nonneg hB (Nat.cast_nonneg m),
      mul_le_mul_of_nonneg_right hAB (show 0 ≤ 1 + (m : ℝ) by positivity)]
  exact (norm_exponentialRescaleBasis_mono _ _
    (fun j => hlo.le.trans (hcost (β.val j)).1) ht x).trans hx1

include T hExp hπExp hπcont in
theorem CartanWordModel.exists_compact_cover_list_box_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW (M.samplingPolytope T hunimod eW)) β.val)
    {K : Set (F.N.carrier × F.D.carrier)} (hK : IsCompact K) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ l : List (F.N.carrier ⋊[F.action] F.D.carrier),
      (∀ x ∈ l, (x.left, x.right) ∈ K) →
      l.prod.left ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (M.samplingPolytope T hunimod eW) β (A * (1 + (l.length : ℝ))) 1 := by
  classical
  obtain ⟨A, hA, hb⟩ := M.exists_compact_cover_word_box_bound T F hExp hunimod
    eW π hπExp hπcont b₀ β hβ hK
  refine ⟨A, hA, ?_⟩
  intro l hl
  let u : ℕ → F.N.carrier ⋊[F.action] F.D.carrier :=
    fun i => if h : i < l.length then l[i] else 1
  have hu (i : ℕ) (hi : i < l.length) : ((u i).left, (u i).right) ∈ K := by
    simpa only [u, dite_eq_left hi] using hl l[i] (List.getElem_mem hi)
  have he : wordPrefix u l.length = l.prod := by
    rw [wordPrefix, show List.ofFn (fun i : Fin l.length => u i.val) = l from ?_]
    simpa only [u, dite_eq_left, Fin.isLt] using (List.ofFn_getElem (xs := l))
  have h := hb l.length (fun i => (u i).left) (fun i => (u i).right) hu
  have hu' : (fun i => (⟨(u i).left, (u i).right⟩ :
      F.N.carrier ⋊[F.action] F.D.carrier)) = u := by
    funext i
    exact SemidirectProduct.ext rfl rfl
  rwa [hu', he] at h

end PolycyclicRecognition

end

end OAI
