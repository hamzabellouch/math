import OAI.Analysis.SeparableQuotients.Complexification

namespace OAI

noncomputable section

namespace SeparableQuotient
open Set TopologicalSpace Singular
open scoped Classical
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X Y : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

@[reducible] local instance fsDualGroup (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
    NormedAddCommGroup (StrongDual 𝕜 Z) := inferInstance
@[reducible] local instance fsDualSpace (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] :
    NormedSpace 𝕜 (StrongDual 𝕜 Z) := inferInstance

omit [CompleteSpace Y] in
lemma hasSQ_of_adjoint_not_SS (a : X →L[𝕜] Y)
    (F : Submodule 𝕜 (StrongDual 𝕜 Y)) (hF : IsClosed (F : Set (StrongDual 𝕜 Y)))
    (hsep : IsSeparable (range (subspaceEvaluation F)))
    (hT : ¬ StrictlySingular ((ContinuousLinearMap.precomp 𝕜 a).comp F.subtypeL)) :
    HasSeparableQuotient 𝕜 X := by
  let : CompleteSpace F := hF.completeSpace_coe
  obtain ⟨H,hH,hHi,U,hU⟩ := exists_lift_of_not_strictlySingular _ hT
  let := hH
  apply hasSeparableQuotient_of_separable_evaluation H hHi
  let A : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 H := ContinuousLinearMap.precomp 𝕜 U
  apply (hsep.image A.continuous).mono
  rintro _ ⟨x,rfl⟩
  refine ⟨subspaceEvaluation F (a x), mem_range_self _, ?_⟩
  ext h
  exact congrArg (fun f : StrongDual 𝕜 X => f x) (hU h)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma norm_dual_prod_le (f : StrongDual 𝕜 (X × Y)) :
    ‖f‖ ≤ ‖f.comp (ContinuousLinearMap.inl 𝕜 X Y)‖ +
      ‖f.comp (ContinuousLinearMap.inr 𝕜 X Y)‖ := by
  apply f.opNorm_le_bound (by positivity)
  intro z
  have he : z = (z.1,0) + (0,z.2) := by ext <;> simp
  calc
    ‖f z‖ = ‖f (z.1,0) + f (0,z.2)‖ := by rw [← map_add,← he]
    _ ≤ ‖f (z.1,0)‖ + ‖f (0,z.2)‖ := norm_add_le _ _
    _ ≤ ‖f.comp (ContinuousLinearMap.inl 𝕜 X Y)‖ * ‖z.1‖ +
        ‖f.comp (ContinuousLinearMap.inr 𝕜 X Y)‖ * ‖z.2‖ := add_le_add
          ((f.comp (ContinuousLinearMap.inl 𝕜 X Y)).le_opNorm z.1)
          ((f.comp (ContinuousLinearMap.inr 𝕜 X Y)).le_opNorm z.2)
    _ ≤ ‖f.comp (ContinuousLinearMap.inl 𝕜 X Y)‖ * ‖z‖ +
        ‖f.comp (ContinuousLinearMap.inr 𝕜 X Y)‖ * ‖z‖ := add_le_add
          (mul_le_mul_of_nonneg_left (norm_fst_le z) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (norm_snd_le z) (norm_nonneg _))
    _ = _ := by ring

omit [CompleteSpace X] [CompleteSpace Y] in
lemma top_infinite (hX : ¬ FiniteDimensional 𝕜 X) :
    ¬ FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 X) := by
  intro h
  let := h
  exact hX (FiniteDimensional.of_surjective (⊤ : Submodule 𝕜 X).subtype
    (fun x => ⟨⟨x,trivial⟩,rfl⟩))

/-- The separable quotient dichotomy for a product, via the evaluation criterion. -/
theorem hasSQ_prod_cases (h : HasSeparableQuotient 𝕜 (X × Y)) :
    HasSeparableQuotient 𝕜 X ∨ HasSeparableQuotient 𝕜 Y := by
  obtain ⟨F,hF,hFi,hsep⟩ := separable_evaluation_of_hasSeparableQuotient h
  let : CompleteSpace F := hF.completeSpace_coe
  let p₁ : F →L[𝕜] StrongDual 𝕜 X :=
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.inl 𝕜 X Y)).comp F.subtypeL
  let p₂ : F →L[𝕜] StrongDual 𝕜 Y :=
    (ContinuousLinearMap.precomp 𝕜 (ContinuousLinearMap.inr 𝕜 X Y)).comp F.subtypeL
  by_cases h₁ : StrictlySingular p₁
  · right
    apply hasSQ_of_adjoint_not_SS (ContinuousLinearMap.inr 𝕜 X Y) F hF hsep
    obtain ⟨G,_hG,hGc,hGi,hsmall⟩ := StrictlySingular.exists_small_restriction p₁ h₁
      (⊤ : Submodule 𝕜 F) isClosed_univ (top_infinite hFi) (1/2) (by norm_num)
    apply (not_strictlySingular_iff p₂).mpr
    refine ⟨G,hGc,hGi,1/2,by norm_num,?_⟩
    intro g
    have hn := norm_dual_prod_le (g.val : StrongDual 𝕜 (X × Y))
    have hs := hsmall g.val g.property
    change ‖(g : F)‖ ≤ ‖p₁ g‖ + ‖p₂ g‖ at hn
    change ‖p₁ g‖ ≤ (1/2 : ℝ)*‖g‖ at hs
    change (1/2 : ℝ)*‖g‖ ≤ ‖p₂ g‖
    change ‖g‖ ≤ ‖p₁ g‖ + ‖p₂ g‖ at hn
    linarith
  · exact Or.inl (hasSQ_of_adjoint_not_SS (ContinuousLinearMap.inl 𝕜 X Y) F hF hsep h₁)

end SeparableQuotient

end

end OAI
