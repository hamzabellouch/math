import Mathlib
import OAI.Analysis.FreeWords.AmplifiedModel
import OAI.Analysis.FreeWords.HaarFiniteEndpointsDefinitions

namespace OAI

noncomputable section

namespace KKFreeLiftFrontier

open KKTraceTransfer KKMatrixExpectation KKHaarEndpoints

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def FullMatrixUnitary {M : VonNeumannAlgebra H} (n : ℕ) (U : unitary (MatrixAlgebra n M)) : Prop :=
  ∃d:ℕ,0<d ∧ ∃ρ:Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
    Function.Injective ρ ∧ ∀i j,U.val i j∈ρ.range

theorem finite_amplified_cyclic_approx (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hfac : IsFactor M) (hdiff : IsDiffuse M) {n:ℕ} (hn:0<n) :
    FiniteCyclicApprox (matrixTraceMap τ.map n)
      (numericalHom (A := ConcreteAlgebra M) n).range.toSubalgebra (FullMatrixUnitary n) := by
  classical
  intro K F hF ε hε
  let ιB := numericalHom (A := ConcreteAlgebra M) n
  let liftB (b : MatrixAlgebra n M) : Matrix (Fin n) (Fin n) ℂ :=
    if h : b∈ιB.range then h.choose else 0
  have hlift (b : MatrixAlgebra n M) (hb : b∈ιB.range) : ιB (liftB b)=b := by
    simp only [liftB,dite_eq_left hb]
    exact hb.choose_spec
  let liftW (w : List (ℤ×MatrixAlgebra n M)) := w.map (fun z => (z.1,liftB z.2))
  let F₀ := F.image liftW
  have hnonempty : ∀w∈F₀,w≠[] := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    simpa [liftW] using (hF v hv).1
  have hcentered : ∀w∈F₀,∀z∈w,z.1≠0 ∧ Matrix.trace z.2=0 := by
    intro w hw z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    have hc := (hF v hv).2 t ht
    refine ⟨hc.1,?_⟩
    have hh := hc.2.2
    rw [← hlift t.2 hc.2.1,matrixTraceMap_numerical τ.map τ.normalized n] at hh
    have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hn0)
  obtain ⟨d,hd,ρ,hρ,U,hU,hK,hF₀⟩ := finite_amplified_numerical_model M τ hfac hdiff n hn K F₀
    hnonempty hcentered ε hε
  refine ⟨U,⟨d,hd,ρ,hρ,hU⟩,hK,?_⟩
  intro w hw
  have hh := hF₀ (liftW w) (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
  have he : ((liftW w).map (fun z => (U^z.1).val*ιB z.2)).prod=powerWord U w := by
    dsimp [powerWord,liftW]
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro z hz
    rw [Function.comp_apply,hlift z.2 ((hF w hw).2 z hz).2.1]
  change ‖matrixTrace τ n (((liftW w).map (fun z => (U^z.1).val*ιB z.2)).prod)‖<ε at hh
  rw [he] at hh
  exact hh

end

end KKFreeLiftFrontier
end

end OAI
