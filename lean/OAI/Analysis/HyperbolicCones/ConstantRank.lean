import OAI.Analysis.HyperbolicCones.KernelSmooth

namespace OAI

noncomputable section

open scoped ContDiff RealInnerProductSpace
open Set ContinuousLinearMap

universe u v

namespace Paper256

theorem exists_constant_rank_neighborhood
    {W : Type u} {F : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (S : Set W) (hne : S.Nonempty) (A : W → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (hs : ∀ u ∈ S, IsSelfAdjoint (A u)) :
    ∃ v ∈ S, ∃ U : Set W, IsOpen U ∧ v ∈ U ∧
      (∀ u ∈ S, Module.finrank ℝ (A u).range ≤ Module.finrank ℝ (A v).range) ∧
      ∀ u ∈ U, u ∈ S → Module.finrank ℝ (A u).range = Module.finrank ℝ (A v).range := by
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
  refine ⟨v, hv, U, huopen, hvu, ?_, ?_⟩
  · intro u hu
    exact hmax _ ⟨u, hu, rfl⟩
  · intro u hu hus
    have hTu : Function.Injective (T u) := by
      have hGi := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).1
      intro x y hxy
      apply hGi
      exact congrArg (T u).adjoint hxy
    apply le_antisymm (hmax _ ⟨u, hus, rfl⟩)
    have hrange : (T u).range ≤ (A u).range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨(x : F), rfl⟩
    calc
      Module.finrank ℝ (A v).range = Module.finrank ℝ (T u).range :=
        (LinearMap.finrank_range_of_inj hTu).symm
      _ ≤ Module.finrank ℝ (A u).range := Submodule.finrank_mono hrange

theorem kernel_rank_constant_neighborhood (c : ℕ) (E : Sym 4 →ₗ[ℝ] Sym c) :
    ∃ (v : Vec 4) (U : Set (Vec 4)), ‖v‖ = 1 ∧ v 0 ≠ 0 ∧ IsOpen U ∧ v ∈ U ∧
      (∀ u : Vec 4, ‖u‖ = 1 → u 0 ≠ 0 →
        Module.finrank ℝ (symmetricOperatorLinear c (E (1 - outerSym u))).range ≤
        Module.finrank ℝ (symmetricOperatorLinear c (E (1 - outerSym v))).range) ∧
      ∀ u ∈ U, ‖u‖ = 1 → u 0 ≠ 0 →
        Module.finrank ℝ (symmetricOperatorLinear c (E (1 - outerSym u))).range =
        Module.finrank ℝ (symmetricOperatorLinear c (E (1 - outerSym v))).range := by
  let S : Set (Vec 4) := {u | ‖u‖ = 1 ∧ u 0 ≠ 0}
  have hne : S.Nonempty := ⟨PiLp.single 2 0 1, by simp [S]⟩
  obtain ⟨v, hv, U, hU, hvU, hmax, hrank⟩ := exists_constant_rank_neighborhood S hne
    (fun u => symmetricOperatorLinear c (E (1 - outerSym u)))
    (contDiff_kernelFamily c E) (fun u _ => kernelFamily_isSelfAdjoint c E u)
  exact ⟨v, U, hv.1, hv.2, hU, hvU, fun u hu hu0 => hmax u ⟨hu, hu0⟩,
    fun u hu hunit hu0 => hrank u hu ⟨hunit, hu0⟩⟩

end Paper256

end

end OAI
