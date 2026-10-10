import OAI.Analysis.KadisonKastler.TomitaCoreCoordinates

namespace OAI

/-! # The domain of the closed Tomita operator

The polar graph coordinates parametrize the full closed graph, not only
its algebraic core. Thus the first coordinate has exactly the range of
the positive graph square root as its domain.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hsep hcyc

theorem tomitaClosedLinearOperator_root_graph (a : H) :
    (tomitaGraphRoot (M := M) J Ω a,
      J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a))) ∈
      (tomitaClosedLinearOperator M J Ω 1).graph := by
  rw [tomitaClosedLinearOperator_graph J Ω 1 hsep]
  let v := tomitaPolarCoordinates J Ω hsep hcyc a
  have he : tomitaProductCoordinates v.val =
      (tomitaGraphRoot (M := M) J Ω a,
        J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a))) := by
    apply Prod.ext
    · exact tomitaPolarCoordinates_first J Ω hsep hcyc a
    · exact tomitaPolarCoordinates_second J Ω hsep hcyc a
  rw [← he]
  change tomitaProductCoordinates.symm (tomitaProductCoordinates v.val) ∈
    rescaledGraphSubspace M J Ω 1
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact v.property

theorem tomitaClosedLinearOperator_graph_iff (x y : H) :
    (x, y) ∈ (tomitaClosedLinearOperator M J Ω 1).graph ↔
      ∃ a : H, tomitaGraphRoot (M := M) J Ω a = x ∧
        J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a)) = y := by
  constructor
  · intro hxy
    rw [tomitaClosedLinearOperator_graph J Ω 1 hsep] at hxy
    let v : rescaledGraphSubspace M J Ω 1 := ⟨tomitaProductCoordinates.symm (x, y), hxy⟩
    let a := (tomitaPolarCoordinates J Ω hsep hcyc).symm v
    have he : tomitaPolarCoordinates J Ω hsep hcyc a = v :=
      (tomitaPolarCoordinates J Ω hsep hcyc).apply_symm_apply v
    refine ⟨a, ?_, ?_⟩
    · have h := congrArg (fun w : rescaledGraphSubspace M J Ω 1 => w.val 0) he
      rw [tomitaPolarCoordinates_first] at h
      exact h
    · have h := congrArg (fun w : rescaledGraphSubspace M J Ω 1 => w.val 1) he
      rw [tomitaPolarCoordinates_second] at h
      exact h
  · rintro ⟨a, rfl, rfl⟩
    exact tomitaClosedLinearOperator_root_graph J Ω hsep hcyc a

theorem tomitaClosedLinearOperator_domain_eq_range :
    ((tomitaClosedLinearOperator M J Ω 1).domain : Set H) =
      Set.range (tomitaGraphRoot (M := M) J Ω) := by
  ext x
  change x ∈ (tomitaClosedLinearOperator M J Ω 1).domain ↔
    x ∈ Set.range (tomitaGraphRoot (M := M) J Ω)
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hxy⟩
    obtain ⟨a, ha, _⟩ := (tomitaClosedLinearOperator_graph_iff J Ω hsep hcyc x y).mp hxy
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    exact ⟨_, tomitaClosedLinearOperator_root_graph J Ω hsep hcyc a⟩

theorem tomitaClosedLinearOperator_root_mem (a : H) :
    tomitaGraphRoot (M := M) J Ω a ∈ (tomitaClosedLinearOperator M J Ω 1).domain :=
  LinearPMap.mem_domain_of_mem_graph (tomitaClosedLinearOperator_root_graph J Ω hsep hcyc a)

theorem tomitaClosedLinearOperator_apply_root (a : H) :
    tomitaClosedLinearOperator M J Ω 1
      ⟨tomitaGraphRoot (M := M) J Ω a, tomitaClosedLinearOperator_root_mem J Ω hsep hcyc a⟩ =
      J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc a)) :=
  (tomitaClosedLinearOperator M J Ω 1).mem_graph_snd_inj
    (LinearPMap.mem_graph _ _) (tomitaClosedLinearOperator_root_graph J Ω hsep hcyc a) rfl

end

end KadisonKastler

end OAI
