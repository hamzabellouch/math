import OAI.Analysis.KadisonKastler.ReducingCommutantCorner

namespace OAI

/-! # Lifting a spatial split through a faithful reducing restriction -/

namespace KadisonKastler

noncomputable section

open Generator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]
  (M : VonNeumannAlgebra H) (hE : E.starProjection ∈ M.commutant)
  (R : VonNeumannAlgebra E) (e : Algebra M ≃⋆ₐ[ℂ] Algebra R)
  (he : ∀ a : Algebra M, (e a).val = cornerCompression E a.val)

include hE he

theorem reducing_commutator_identity
    (T : H →L[ℂ] H) (hTE : E.starProjection * T = T * E.starProjection)
    (a : Algebra M) :
    cornerCompression E (T * a.val - a.val * T) =
      cornerCompression E T * (e a).val - (e a).val * cornerCompression E T := by
  rw [map_sub, cornerCompression_mul_of_invariant E T a.val
      (invariant_of_commutes_starProjection E a.val
        (VonNeumannAlgebra.mem_commutant_iff.mp hE a.val a.property).symm),
    cornerCompression_mul_of_invariant E a.val T
      (invariant_of_commutes_starProjection E T hTE), he]

theorem reducing_spatial_preserves
    (T : H →L[ℂ] H) (hTE : E.starProjection * T = T * E.starProjection)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∀ b ∈ R, cornerCompression E T * b - b * cornerCompression E T ∈ R := by
  intro b hb
  obtain ⟨a, ha⟩ := e.surjective ⟨b, hb⟩
  have hv : (e a).val = b := congrArg Subtype.val ha
  rw [← hv, ← reducing_commutator_identity E M hE R e he T hTE a]
  rw [← he ⟨T * a.val - a.val * T, hT a.val a.property⟩]
  exact (e ⟨T * a.val - a.val * T, hT a.val a.property⟩).property

theorem lift_reducing_spatial_split
    (T : H →L[ℂ] H) (hTE : E.starProjection * T = T * E.starProjection)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M)
    (c : E →L[ℂ] E) (hc : c ∈ R) (hcsa : IsSelfAdjoint c)
    (hTc : cornerCompression E T - c ∈ R.commutant) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ = ‖c‖ ∧ T - a ∈ M.commutant := by
  let a : Algebra M := e.symm ⟨c, hc⟩
  have hac : (e a).val = c := congrArg Subtype.val (e.apply_symm_apply ⟨c, hc⟩)
  have hn : ‖a.val‖ = ‖c‖ := by
    have hi := NonUnitalStarAlgHom.norm_map e.toStarAlgHom e.injective a
    change ‖e a‖ = ‖a‖ at hi
    change ‖a‖ = ‖c‖
    rw [← hi]
    change ‖(e a).val‖ = ‖c‖
    rw [hac]
  have hasa : IsSelfAdjoint a.val := by
    have hh : e.toStarAlgHom (star a) = e.toStarAlgHom a := by
      rw [map_star]
      apply Subtype.ext
      change star (e a).val = (e a).val
      rw [hac, hcsa.star_eq]
    exact congrArg Subtype.val (e.injective hh)
  refine ⟨a.val, a.property, hasa, hn, ?_⟩
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  let y : Algebra M := ⟨b, hb⟩
  let d : Algebra M := ⟨(T * b - b * T) - (a.val * b - b * a.val),
    M.sub_mem (hT b hb) (M.sub_mem (M.mul_mem a.property hb) (M.mul_mem hb a.property))⟩
  have hd : e d = 0 := by
    apply Subtype.ext
    rw [he]
    change cornerCompression E ((T * b - b * T) - (a.val * b - b * a.val)) = 0
    rw [map_sub, reducing_commutator_identity E M hE R e he T hTE y, map_sub,
      cornerCompression_mul_of_invariant E a.val b
        (invariant_of_commutes_starProjection E b
          (VonNeumannAlgebra.mem_commutant_iff.mp hE b hb).symm),
      cornerCompression_mul_of_invariant E b a.val
        (invariant_of_commutes_starProjection E a.val
          (VonNeumannAlgebra.mem_commutant_iff.mp hE a.val a.property).symm),
      ← he a, ← he y, hac]
    apply sub_eq_zero.mpr
    have hh := VonNeumannAlgebra.mem_commutant_iff.mp hTc (e y).val (e y).property
    change (e y).val * (cornerCompression E T - c) =
      (cornerCompression E T - c) * (e y).val at hh
    rw [mul_sub, sub_mul] at hh
    simpa only [neg_sub] using congrArg Neg.neg (sub_eq_sub_iff_sub_eq_sub.mp hh)
  have hz : d = 0 := e.injective (hd.trans (map_zero e.toStarAlgHom).symm)
  have hzv := congrArg Subtype.val hz
  change (T * b - b * T) - (a.val * b - b * a.val) = 0 at hzv
  change b * (T - a.val) = (T - a.val) * b
  rw [mul_sub, sub_mul]
  exact (sub_eq_sub_iff_sub_eq_sub.mp (sub_eq_zero.mp hzv)).symm

end

end KadisonKastler

end OAI
