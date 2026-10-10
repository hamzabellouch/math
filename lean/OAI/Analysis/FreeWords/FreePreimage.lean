import Mathlib
import OAI.Analysis.FreeWords.FreeSurjectiveImage

namespace OAI

noncomputable section

namespace KKVariableUltra

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem unitary_map_zpow (φ : A →⋆ₐ[ℂ] B) (u : unitary A) (k : ℤ) :
    φ ((u^k).val)=((Unitary.map (StarMonoidHom.ofClass φ) u)^k).val := by
  exact congrArg Subtype.val (map_zpow (Unitary.map (StarMonoidHom.ofClass φ)) u k)

theorem unitary_map_word (φ : A →⋆ₐ[ℂ] B) (u : unitary A) (w : List (ℤ × A)) :
    φ ((w.map (fun z => (u^z.1).val*z.2)).prod)=
      ((w.map (fun z => (z.1,φ z.2))).map
        (fun z => ((Unitary.map (StarMonoidHom.ofClass φ) u)^z.1).val*z.2)).prod := by
  simp only [map_list_prod,List.map_map,Function.comp_def,map_mul,unitary_map_zpow]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_free_preimage (M : VonNeumannAlgebra H)
    (τ : FaithfulNormalTrace M) (hF : IsFactor M) (hD : IsDiffuse M)
    (φ : A →⋆ₐ[ℂ] ConcreteAlgebra M) (hsur : Function.Surjective φ)
    (T : A → ℂ) (he : ∀ x, τ.map (φ x)=T x)
    (K : Finset ℤ) (F : Finset (List (ℤ × A)))
    (hFne : ∀ w∈F, w≠[]) (hcenter : ∀ w∈F, ∀ z∈w, z.1≠0 ∧ T z.2=0)
    (ε : ℝ) (hε : 0<ε) :
    ∃ v : unitary A,
      (∀ k∈K, k≠0 → ‖T ((v^k).val)‖<ε) ∧
      (∀ w∈F, ‖T ((w.map (fun z => (v^z.1).val*z.2)).prod)‖<ε) := by
  classical
  let wf : List (ℤ × A) → List (ℤ × ConcreteAlgebra M) :=
    List.map (fun z => (z.1,φ z.2))
  have hn : ∀ w∈F.image wf, w≠[] := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    intro hz
    exact hFne v hv (List.map_eq_nil_iff.mp hz)
  have hc : ∀ w∈F.image wf, ∀ z∈w, z.1≠0 ∧ τ.map z.2=0 := by
    intro w hw z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
    exact ⟨(hcenter v hv a ha).1,(he a.2).trans (hcenter v hv a ha).2⟩
  obtain ⟨v,hvK,hvF⟩ := finite_free_in_surjective_image M τ hF hD φ hsur
    K (F.image wf) hn hc ε hε
  refine ⟨v,?_,?_⟩
  · intro k hk hk0
    rw [← he,unitary_map_zpow]
    exact hvK k hk hk0
  · intro w hw
    rw [← he,unitary_map_word]
    exact hvF (wf w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)

end

end KKVariableUltra
end

end OAI
