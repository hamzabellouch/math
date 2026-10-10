import OAI.Analysis.BoundedHochschild.RepresentedAveragingOrbit

namespace OAI

/-! Convexity of the lifted averaging orbit. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

variable {M I J H K : Type*} [CStarAlgebra M] [Fintype I] [Fintype J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma representedRightAverage_real_smul (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (r : ℝ) (W : H →L[ℂ] K) :
    representedRightAverage π σ (fun i => r • m i) W =
      (r * r) • representedRightAverage π σ m W := by
  have hπ (a : M) : π (r • a) = r • π a :=
    (π.toLinearMap.restrictScalars ℝ).map_smul r a
  have hσ (a : M) : σ (r • a) = r • σ a :=
    (σ.toLinearMap.restrictScalars ℝ).map_smul r a
  have hW (x : H) : W (r • x) = r • W x := (W.restrictScalars ℝ).map_smul r x
  have hA (a : M) (x : K) : π a (r • x) = r • π a x :=
    ((π a).restrictScalars ℝ).map_smul r x
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, hπ, hσ,
    ← ContinuousLinearMap.star_eq_adjoint, star_smul, star_trivial,
    smul_apply, hW, hA, smul_smul, Finset.smul_sum]

lemma representedRightAverage_sum (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (n : J → M) (W : H →L[ℂ] K) :
    representedRightAverage π σ (Sum.elim m n) W =
      representedRightAverage π σ m W + representedRightAverage π σ n W := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [representedRightAverage, operatorRowAverage_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, add_apply]

lemma representedRightAverage_convex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M) (n : J → M)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (W : H →L[ℂ] K) :
    representedRightAverage π σ
      (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • n j)) W =
      r • representedRightAverage π σ m W + s • representedRightAverage π σ n W := by
  rw [representedRightAverage_sum, representedRightAverage_real_smul,
    representedRightAverage_real_smul, Real.mul_self_sqrt hr, Real.mul_self_sqrt hs]

theorem representedAveragingOrbit_convex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    Convex ℝ (representedAveragingOrbit π σ W) := by
  rintro U ⟨n, m, hm, rfl⟩ V ⟨k, v, hv, rfl⟩ r s hr hs hrs
  have he := congrArg ContinuousLinearMapWOT.ofCLM
    (representedRightAverage_convex π σ m v hr hs W.toCLM)
  change weakRepresentedRightAverage π σ
    (Sum.elim (fun i => Real.sqrt r • m i) (fun j => Real.sqrt s • v j)) W =
    r • weakRepresentedRightAverage π σ m W + s • weakRepresentedRightAverage π σ v W at he
  rw [← he]
  exact weakRepresentedRightAverage_mem_orbit π σ _
    (rightAverage_convex_normalized m v hm hv hr hs hrs) W

theorem closedRepresentedAveragingOrbit_convex (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (W : H →WOT[ℂ] K) :
    Convex ℝ (closedRepresentedAveragingOrbit π σ W) :=
  (representedAveragingOrbit_convex π σ W).closure

end BoundedHochschild.KadisonRingrose

end

end OAI
