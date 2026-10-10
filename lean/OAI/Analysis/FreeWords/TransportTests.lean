import Mathlib
import OAI.Analysis.FreeWords.AmplifiedBlockModel
import OAI.Analysis.FreeWords.MatrixExpectationContinuous
import OAI.Analysis.FreeWords.RelativeFiniteEndpoints
import OAI.Analysis.FreeWords.TransportTestsDefinitions

namespace OAI

noncomputable section

namespace KKFiniteTransport

noncomputable section

open KKTraceTransfer KKFreeLiftFrontier KKMatrixExpectation KKControlledConjugation KKRelativeEndpoints

variable {H:Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {M:VonNeumannAlgebra H}

theorem transportPair_conj (τ:FaithfulNormalTrace M) {n:ℕ} (u:unitary (ConcreteAlgebra M))
    (U:unitary (MatrixAlgebra n M)) (w:RelWord τ n) :
    transportPair τ (conjUnitary u U) w=relativePair u (modelWord τ U w) := by
  simp only [transportPair,relativePair,modelWord,List.map_map,Function.comp_def,blockCenter_conj]

theorem modelWord_centered (τ:FaithfulNormalTrace M) {n:ℕ} (U:unitary (MatrixAlgebra n M))
    (w:RelWord τ n) : ∀z∈modelWord τ U w,∀a b,τ.map (z.1 a b)=0 ∧ τ.map (z.2 a b)=0 := by
  intro z hz
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hz
  intro a b
  exact ⟨trace_center_entry τ n _ a b,(matrixExpectation_zero_iff τ n c.2.val).1 c.2.property a b⟩

theorem finite_transport_tests : FiniteTransportTests (H := H) := by
  classical
  intro M τ hfac hdiff n hn L ε hε
  let K:Finset ℤ := L.biUnion fun t => match t with
    | .haar k _ => {k}
    | _ => ∅
  let E:Finset (List (ℤ×MatrixAlgebra n M)×ℤ) := L.biUnion fun t => match t with
    | .block b _ _ => {b.val}
    | _ => ∅
  have hE : ∀z∈E,KKHaarEndpoints.CenteredPowerWord (matrixTraceMap τ.map n)
      (numericalHom n).range.toSubalgebra z.1 ∧ z.2≠0 := by
    intro z hz
    obtain ⟨t,ht,hz⟩ := Finset.mem_biUnion.mp hz
    cases t with
    | block b i j => have he := Finset.mem_singleton.mp hz; subst z; exact b.property
    | _ => simp at hz
  obtain ⟨d,hd,ρ,hρ,V,hentry,hK,_,hEsmall⟩ :=
    finite_amplified_block_model M τ hfac hdiff n hn K ∅ E (by simp) hE ε hε
  let F:Finset (List (MatrixAlgebra n M×MatrixAlgebra n M)) := L.biUnion fun t => match t with
    | .cyclic w _ _ _ => {modelWord τ V w}
    | _ => ∅
  let G:Finset (List (MatrixAlgebra n M×MatrixAlgebra n M)×MatrixAlgebra n M) :=
    L.biUnion fun t => match t with
    | .endpoint w b _ _ => {(modelWord τ V w,blockCenter τ V b)}
    | _ => ∅
  have hF : ∀w∈F,w≠[] ∧ ∀z∈w,∀a b,τ.map (z.1 a b)=0 ∧ τ.map (z.2 a b)=0 := by
    intro w hw
    obtain ⟨t,ht,hw⟩ := Finset.mem_biUnion.mp hw
    cases t with
    | cyclic v hv i j =>
      have he := Finset.mem_singleton.mp hw
      subst w
      exact ⟨by simpa [modelWord] using hv,modelWord_centered τ V v⟩
    | _ => simp at hw
  have hG : ∀z∈G,(∀c∈z.1,∀a b,τ.map (c.1 a b)=0 ∧ τ.map (c.2 a b)=0) ∧
      ∀a b,τ.map (z.2 a b)=0 := by
    intro z hz
    obtain ⟨t,ht,hz⟩ := Finset.mem_biUnion.mp hz
    cases t with
    | endpoint w b i j =>
      have he := Finset.mem_singleton.mp hz
      subst z
      exact ⟨modelWord_centered τ V w,trace_center_entry τ n _⟩
    | _ => simp at hz
  obtain ⟨u,huF,huG⟩ := relative_finite_endpoints M τ hfac hdiff n F G hF hG ε hε
  refine ⟨conjUnitary u V,conjUnitary_good u V ⟨d,hd,ρ,hρ,hentry⟩,?_⟩
  intro t ht
  cases t with
  | haar k hk =>
    have hkm : k∈K := Finset.mem_biUnion.mpr ⟨.haar k hk,ht,by simp⟩
    have hh := hK k hkm hk
    change ‖matrixTraceMap τ.map n (V^k).val‖<ε at hh
    simpa only [testValue,conjUnitary_zpow,amplifyConj_trace τ.map τ.tracial] using hh
  | block b i j =>
    have hbm : b.val∈E := Finset.mem_biUnion.mpr ⟨.block b i j,ht,by simp⟩
    change ‖τ.map (blockValue (conjUnitary u V) b i j)‖<ε
    rw [blockValue_conj]
    simpa only [amplifyConj_apply,conj_trace τ.map τ.tracial,blockValue] using hEsmall b.val hbm i j
  | cyclic w hw i j =>
    have hwm : modelWord τ V w∈F := Finset.mem_biUnion.mpr ⟨.cyclic w hw i j,ht,by simp⟩
    simpa only [testValue,transportPair_conj] using huF _ hwm i j
  | endpoint w b i j =>
    have hwm : (modelWord τ V w,blockCenter τ V b)∈G :=
      Finset.mem_biUnion.mpr ⟨.endpoint w b i j,ht,by simp⟩
    simpa only [testValue,transportPair_conj,blockCenter_conj] using huG _ hwm i j

end

end KKFiniteTransport
end

end OAI
