import Mathlib
import OAI.Analysis.Commutator.StrongDenseTests

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped Topology

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem exists_countable_strong_contraction_tests (P : VonNeumannAlgebra H) :
    ∃ test : ℕ → H →L[ℂ] H,(∀ n,test n∈P ∧ ‖test n‖≤1) ∧
      ∀ A : H →L[ℂ] H,A∈P → ‖A‖≤1 →
        ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) ξ) atTop (𝓝 (A ξ)) := by
  let v : ℕ → H := TopologicalSpace.denseSeq H
  let S : Set (ℕ → H) := {f | ∃ A : H →L[ℂ] H,A∈P ∧ ‖A‖≤1 ∧ ∀ j,f j=A (v j)}
  have hS : S.Nonempty := ⟨fun _ => 0,0,P.zero_mem,by simp,by simp⟩
  let : Nonempty S := hS.to_subtype
  let s : ℕ → S := TopologicalSpace.denseSeq S
  choose test hP hb ht using (fun n => (s n).property)
  refine ⟨test,fun n => ⟨hP n,hb n⟩,?_⟩
  intro A hA hnA
  let f : S := ⟨fun j => A (v j),A,hA,hnA,fun _ => rfl⟩
  have hd : DenseRange s := TopologicalSpace.denseRange_denseSeq S
  obtain ⟨u,hu,hl⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose k hk using hu
  have hlim : Tendsto (fun n => s (k n)) atTop (𝓝 f) := by
    have he : (fun n => s (k n))=u := funext hk
    rwa [he]
  have hj (j : ℕ) : Tendsto (fun n => test (k n) (v j)) atTop (𝓝 (A (v j))) := by
    have hv := (continuous_apply j |>.comp continuous_subtype_val).tendsto f |>.comp hlim
    change Tendsto (fun n => (s (k n)).val j) atTop (𝓝 (A (v j))) at hv
    simpa only [ht] using hv
  exact ⟨k,strong_tendsto_of_dense_tests v (TopologicalSpace.denseRange_denseSeq H)
    (fun n => test (k n)) A (fun n => hb (k n)) hnA hj⟩

end Kadison

end

end
end

end OAI
