import OAI.RepresentationTheory.FoulkesHowe.SymmetricLift

namespace OAI

noncomputable section
universe u v w
namespace Problem346

/-- Descend a separately symmetric multilinear pairing in both blocks. -/
theorem exists_symPow_bilinear_lift (n m : ℕ) (V : Type u) (W : Type v)
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Q : MultilinearMap ℂ (fun _ : Fin n => V)
      (MultilinearMap ℂ (fun _ : Fin m => W) ℂ))
    (hleft : ∀ (σ : Equiv.Perm (Fin n)) x,
      Q (fun i => x (σ i)) = Q x)
    (hright : ∀ x (σ : Equiv.Perm (Fin m)) y,
      Q x (fun i => y (σ i)) = Q x y) :
    ∃ B : SymPow n V →ₗ[ℂ] Module.Dual ℂ (SymPow m W),
      ∀ x y, B (symMonomial n V x) (symMonomial m W y) = Q x y := by
  classical
  choose G hG using fun x => exists_symPow_lift (Q x) (hright x)
  let F : MultilinearMap ℂ (fun _ : Fin n => V) (Module.Dual ℂ (SymPow m W)) :=
    { toFun := G
      map_update_add' := by
        intro _ x i a b
        apply SymmetricLift.linearMap_ext
        intro y
        simp only [LinearMap.add_apply, hG]
        exact congrArg (fun T : MultilinearMap ℂ (fun _ : Fin m => W) ℂ => T y)
          (Q.map_update_add x i a b)
      map_update_smul' := by
        intro _ x i c a
        apply SymmetricLift.linearMap_ext
        intro y
        simp only [LinearMap.smul_apply, hG]
        exact congrArg (fun T : MultilinearMap ℂ (fun _ : Fin m => W) ℂ => T y)
          (Q.map_update_smul x i c a) }
  have hF : ∀ (σ : Equiv.Perm (Fin n)) x, F (fun i => x (σ i)) = F x := by
    intro σ x
    apply SymmetricLift.linearMap_ext
    intro y
    change G (fun i => x (σ i)) (symMonomial m W y) = G x (symMonomial m W y)
    rw [hG, hG, hleft]
  obtain ⟨B, hB⟩ := exists_symPow_lift F hF
  refine ⟨B, ?_⟩
  intro x y
  rw [hB]
  exact hG x y

end Problem346

end

end OAI
