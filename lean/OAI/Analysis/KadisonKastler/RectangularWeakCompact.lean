import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! Weak operator compactness for the rectangular operators in a fixed
factorization. The source and target Hilbert spaces may differ. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
theorem exists_weak_rectangular_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (R : ι → H →L[ℂ] K) (d : ℝ) (hd : 0 ≤ d) (hR : ∀ i, ‖R i‖ ≤ d) :
    ∃ T : H →L[ℂ] K, ‖T‖ ≤ d ∧ ∀ ξ η,
      Tendsto (fun i => inner ℂ η (R i ξ)) (ω : Filter ι) (𝓝 (inner ℂ η (T ξ))) := by
  have h (ξ : H) := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => R i ξ) (d * ‖ξ‖) (fun i => (R i).le_of_opNorm_le (hR i) ξ)
  choose v hv ht using h
  have ha (ξ ζ : H) : v (ξ + ζ) = v ξ + v ζ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (ξ + ζ) η)
    simpa only [map_add, inner_add_right] using (ht ξ η).add (ht ζ η)
  have hs (z : ℂ) (ξ : H) : v (z • ξ) = z • v ξ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • ξ) η)
    simpa only [map_smul, inner_smul_right] using (ht ξ η).const_mul z
  let T : H →L[ℂ] K := LinearMap.mkContinuous
    { toFun := v, map_add' := ha, map_smul' := hs } d hv
  exact ⟨T, T.opNorm_le_bound hd hv, ht⟩

def weakRectangularBall (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (d : ℝ) : Set (H →WOT[ℂ] K) :=
  {R | ‖R.toCLM‖ ≤ d}

omit [CompleteSpace H] in
theorem isCompact_weakRectangularBall {d : ℝ} (hd : 0 ≤ d) :
    IsCompact (weakRectangularBall H K d) := by
  classical
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro ω hω
  let R : (H →WOT[ℂ] K) → H →L[ℂ] K := fun T =>
    if ‖T.toCLM‖ ≤ d then T.toCLM else 0
  have hR (T : H →WOT[ℂ] K) : ‖R T‖ ≤ d := by
    dsimp [R]
    split_ifs with h
    · exact h
    · simpa only [norm_zero] using hd
  obtain ⟨T, hT, ht⟩ := exists_weak_rectangular_operator_ultralimit ω R d hd hR
  refine ⟨ContinuousLinearMapWOT.ofCLM T, hT, ?_⟩
  have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (R U))
      (ω : Filter (H →WOT[ℂ] K)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
  have he : (fun U => ContinuousLinearMapWOT.ofCLM (R U)) =ᶠ[ω] id := by
    filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] K)),
      U ∈ weakRectangularBall H K d from hω] with U hU
    simp only [weakRectangularBall, Set.mem_ofPred_eq] at hU
    simp only [R, ite_eq_left hU, ContinuousLinearMapWOT.ofCLM_toCLM, id_eq]
  exact hl.congr' he

end

end KadisonKastler

end OAI
