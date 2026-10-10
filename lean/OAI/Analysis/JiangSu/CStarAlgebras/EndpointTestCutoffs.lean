import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.TwoParameterPartition

namespace OAI

section

noncomputable section
namespace EndpointPartition
variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [NormedAddCommGroup E]

theorem exists_endpoint_cutoffs {ι : Type*} [Fintype ι] (x0 x1 : X) (h01 : x0≠x1)
    (f : ι → C(X,E)) {δ : ℝ} (hδ : 0<δ) :
    ∃ a b : C(X,ℝ),a x0=1 ∧ a x1=0 ∧ b x0=0 ∧ b x1=1 ∧
      (∀ x,a x≠0 → ∀ i,‖f i x-f i x0‖<δ) ∧
      (∀ x,b x≠0 → ∀ i,‖f i x-f i x1‖<δ) := by
  classical
  obtain ⟨T,ρ,hρ,hs,h0,h1,hf⟩ := exists_weights x0 x1 f hδ
  have hx (x : X) (hx : ∀ t : T,t.val≠x → ρ t x=0) : x∈T := by
    by_contra h
    have hz : ∑ t : T,ρ t x=0 := Finset.sum_eq_zero (fun t _ => hx t (fun e => h (e ▸ t.property)))
    rw [hs] at hz
    norm_num at hz
  let t0 : T := ⟨x0,hx x0 h0⟩
  let t1 : T := ⟨x1,hx x1 h1⟩
  have hv (t : T) (ht : ∀ u : T,u.val≠t.val → ρ u t.val=0) : ρ t t.val=1 := by
    rw [←hs t.val]
    symm
    apply Finset.sum_eq_single t
    · intro u _ hu
      exact ht u (fun he => hu (Subtype.ext he))
    · simp
  refine ⟨ρ t0,ρ t1,hv t0 h0,h1 t0 h01,h0 t1 h01.symm,hv t1 h1,?_,?_⟩
  · intro x ha i
    exact hf t0 x ha i
  · intro x hb i
    exact hf t1 x hb i

end EndpointPartition

end
end

end OAI
