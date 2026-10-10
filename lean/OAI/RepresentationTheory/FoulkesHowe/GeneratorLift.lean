import OAI.RepresentationTheory.FoulkesHowe.SpanningAgreement
import OAI.RepresentationTheory.FoulkesHowe.SymmetricLift
import OAI.RepresentationTheory.FoulkesHowe.Spanning

namespace OAI

noncomputable section
namespace Problem346

/-- A separately linearly extendible symmetric formula on spanning generators
induces a linear map out of the homogeneous symmetric power. -/
theorem exists_symPow_lift_on_spanning
    {n : ℕ} {X V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (s : X → V) (hs : Submodule.span ℂ (Set.range s) = ⊤)
    (F : (Fin n → X) → W)
    (hlinear : ∀ x : Fin n → X, ∀ i : Fin n,
      ∃ L : V →ₗ[ℂ] W, ∀ y, L (s y) = F (Function.update x i y))
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → X),
      F (fun i => x (σ i)) = F x) :
    ∃ L : SymPow n V →ₗ[ℂ] W, ∀ x : Fin n → X,
      L (symMonomial n V (fun i => s (x i))) = F x := by
  classical
  obtain ⟨G, hG⟩ := exists_multilinear_extension_of_spanning
    (fun _ : Fin n => s) (fun _ => hs) F hlinear
  have hGs : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V),
      G (fun i => v (σ i)) = G v := by
    intro σ
    have h : G.domDomCongr σ = G := by
      apply multilinear_ext_of_span hs n
      intro v hv
      choose x hx using hv
      have he : v = fun i => s (x i) := funext (fun i => (hx i).symm)
      subst v
      change G (fun i => s (x (σ i))) = G (fun i => s (x i))
      rw [← hG, ← hG, hsym]
    intro v
    exact congrArg (fun G : MultilinearMap ℂ (fun _ : Fin n => V) W => G v) h
  obtain ⟨L, hL⟩ := exists_symPow_lift G hGs
  exact ⟨L, fun x => (hL _).trans (hG x).symm⟩

end Problem346

end

end OAI
