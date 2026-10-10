import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! Weak operator compactness for bounded operators between the two Hilbert
spaces of a completely bounded factorization. -/

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem exists_rectangular_weak_ultralimit {I : Type*} (ω : Ultrafilter I)
    (a : I → H →L[ℂ] K) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ T : H →L[ℂ] K, ‖T‖ ≤ C ∧ ∀ x y,
      Tendsto (fun i => inner ℂ y (a i x)) (ω : Filter I) (𝓝 (inner ℂ y (T x))) := by
  have h (x : H) := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => a i x) (C * ‖x‖) (fun i => (a i).le_of_opNorm_le (ha i) x)
  choose v hv ht using h
  have hadd (x z : H) : v (x + z) = v x + v z := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x + z) y)
    simpa only [map_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : H) : v (c • x) = c • v x := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, inner_smul_right] using (ht x y).const_mul c
  let T : H →L[ℂ] K := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨T, T.opNorm_le_bound hC hv, ht⟩

def rectangularWeakBall (C : ℝ) : Set (H →WOT[ℂ] K) := {T | ‖T.toCLM‖ ≤ C}

theorem rectangularWeakBall_isCompact (C : ℝ) :
    IsCompact (rectangularWeakBall (H := H) (K := K) C) := by
  classical
  by_cases hC : 0 ≤ C
  · apply isCompact_iff_ultrafilter_le_nhds'.mpr
    intro ω hω
    let a : (H →WOT[ℂ] K) → H →L[ℂ] K := fun T =>
      if T ∈ rectangularWeakBall C then T.toCLM else 0
    have ha (T : H →WOT[ℂ] K) : ‖a T‖ ≤ C := by
      dsimp [a]
      split_ifs with h
      · exact h
      · simpa only [norm_zero] using hC
    obtain ⟨T, hT, ht⟩ := exists_rectangular_weak_ultralimit ω a hC ha
    refine ⟨ContinuousLinearMapWOT.ofCLM T, hT, ?_⟩
    have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (a U))
        (ω : Filter (H →WOT[ℂ] K)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
      ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
    have he : (fun U => ContinuousLinearMapWOT.ofCLM (a U)) =ᶠ[ω] id := by
      filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] K)),
        U ∈ rectangularWeakBall C from hω] with U hU
      simp only [a, ite_eq_left hU, ContinuousLinearMapWOT.ofCLM_toCLM, id_eq]
    exact hl.congr' he
  · have he : rectangularWeakBall (H := H) (K := K) C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro T hT
      exact hC ((norm_nonneg _).trans hT)
    rw [he]
    exact isCompact_empty

theorem rectangularWeakBall_isClosed (C : ℝ) :
    IsClosed (rectangularWeakBall (H := H) (K := K) C) :=
  (rectangularWeakBall_isCompact C).isClosed

end BoundedHochschild.KadisonRingrose

end

end OAI
