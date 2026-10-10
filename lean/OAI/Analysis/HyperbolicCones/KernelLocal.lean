import OAI.Analysis.HyperbolicCones.GramProjection

namespace OAI

noncomputable section

open scoped ContDiff RealInnerProductSpace
open Set ContinuousLinearMap

universe u v

namespace Paper256

theorem exists_smooth_kernel_extension
    {W : Type u} {F : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (S : Set W) (hne : S.Nonempty) (A : W → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hs : ∀ u ∈ S, IsSelfAdjoint (A u)) :
    ∃ v ∈ S, ∃ (U : Set W) (P : W → F →L[ℝ] F),
      IsOpen U ∧ v ∈ U ∧ ContDiffOn ℝ ∞ P U ∧
      ∀ u ∈ U, u ∈ S → P u = (A u).ker.starProjection := by
  let ranks : Set ℕ := (fun u => Module.finrank ℝ (A u).range) '' S
  have hfin : ranks.Finite := Set.finite_iff_bddAbove.mpr ⟨Module.finrank ℝ F, by
    rintro _ ⟨u, _, rfl⟩
    exact Submodule.finrank_le _⟩
  obtain ⟨r, hr, hmax⟩ := Set.exists_max_image ranks id hfin (hne.image _)
  obtain ⟨v, hv, rfl⟩ := hr
  let R : Submodule ℝ F := (A v).range
  let T : W → R →L[ℝ] F := fun u => (A u).comp R.subtypeL
  have hTv : Function.Injective (T v) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change A v (x : F) = 0 at hx
    have hxo : (x : F) ∈ Rᗮ := by
      change (x : F) ∈ (A v).rangeᗮ
      rw [(A v).orthogonal_range, (hs v hv).adjoint_eq]
      exact hx
    apply Subtype.ext
    exact inner_self_eq_zero.mp (hxo x x.property)
  have ht : ContDiff ℝ ∞ T := hA.clm_comp contDiff_const
  have hadj : ContDiff ℝ ∞ (fun B : R →L[ℝ] F => B.adjoint) :=
    (ContinuousLinearMap.adjoint : (R →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] R)).contDiff
  let G : W → R →L[ℝ] R := fun u => (T u).adjoint.comp (T u)
  have hg : ContDiff ℝ ∞ G := (hadj.comp ht).clm_comp ht
  let U : Set W := {u | IsUnit (G u)}
  have huopen : IsOpen U := by
    change IsOpen (G ⁻¹' {K : R →L[ℝ] R | IsUnit K})
    apply IsOpen.preimage hg.continuous
    exact Units.isOpen (R := R →L[ℝ] R)
  have hvu : v ∈ U := gram_isUnit_of_injective (T v) hTv
  refine ⟨v, hv, U, fun u => 1 - gramProjection (T u), huopen, hvu, ?_, ?_⟩
  · exact contDiffOn_const.sub (contDiffOn_gramProjection T U ht.contDiffOn (fun _ hu => hu))
  · intro u hu hus
    have hTu : Function.Injective (T u) := by
      have hGi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
      intro x y hxy
      apply hGi
      exact congrArg (T u).adjoint hxy
    have hrange : (T u).range = (A u).range := by
      apply Submodule.eq_of_le_of_finrank_le
      · rintro _ ⟨x, rfl⟩
        exact ⟨(x : F), rfl⟩
      · rw [LinearMap.finrank_range_of_inj hTu]
        exact hmax _ ⟨u, hus, rfl⟩
    exact one_sub_gramProjection_eq_kernel (T u) hu (A u) (hs u hus) hrange

end Paper256

end

end OAI
