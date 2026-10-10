import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.EndpointPartition

namespace OAI

section

noncomputable section
namespace EndpointPartition
variable {X Y E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [NormedAddCommGroup E]

lemma exists_weights {ι : Type*} [Fintype ι] (a b : X) (f : ι → C(X,E))
    {δ : ℝ} (hδ : 0<δ) :
    ∃ T : Finset X,∃ ρ : T → C(X,ℝ),
      (∀ t x,0≤ρ t x) ∧ (∀ x,∑ t,ρ t x=1) ∧
      (∀ t,t.val≠a → ρ t a=0) ∧ (∀ t,t.val≠b → ρ t b=0) ∧
      (∀ t x,ρ t x≠0 → ∀ l,‖f l x-f l t.val‖<δ) := by
  obtain ⟨T,ρ,g,hρ,hs,hg,h0,h1,hg1,hf⟩ := exists_partition a b f hδ
  refine ⟨T,ρ,fun t x => (hρ t x).1,hs,?_,?_,hf⟩
  · intro t ht
    by_contra hn
    have h := hg1 t a hn
    rw [h0 t ht] at h
    norm_num at h
  · intro t ht
    by_contra hn
    have h := hg1 t b hn
    rw [h1 t ht] at h
    norm_num at h

theorem exists_rectangular_weights (x0 x1 : X) (y0 y1 : Y) (f : C(X×Y,E))
    {δ : ℝ} (hδ : 0<δ) :
    ∃ S : Finset X,∃ T : Finset Y,∃ ρ : S → C(X,ℝ),∃ σ : T → C(Y,ℝ),
      (∀ i x,0≤ρ i x) ∧ (∀ j y,0≤σ j y) ∧
      (∀ x,∑ i,ρ i x=1) ∧ (∀ y,∑ j,σ j y=1) ∧
      (∀ i,i.val≠x0 → ρ i x0=0) ∧ (∀ i,i.val≠x1 → ρ i x1=0) ∧
      (∀ j,j.val≠y0 → σ j y0=0) ∧ (∀ j,j.val≠y1 → σ j y1=0) ∧
      ∀ i j x y,ρ i x≠0 → σ j y≠0 → ‖f (x,y)-f (i.val,j.val)‖<δ := by
  obtain ⟨S,ρ,hρ,hs,hx0,hx1,hf⟩ := exists_weights x0 x1
    (fun _ : Unit => f.curry) (show 0<δ/2 by positivity)
  let fs : S → C(Y,E) := fun i => f.curry i.val
  obtain ⟨T,σ,hσ,ht,hy0,hy1,hg⟩ := exists_weights y0 y1 fs (show 0<δ/2 by positivity)
  refine ⟨S,T,ρ,σ,hρ,hσ,hs,ht,hx0,hx1,hy0,hy1,?_⟩
  intro i j x y hix hjy
  have hfirst : ‖f (x,y)-f (i.val,y)‖<δ/2 :=
    ((f.curry x-f.curry i.val).norm_coe_le_norm y).trans_lt (hf i x hix ())
  have hsecond : ‖f (i.val,y)-f (i.val,j.val)‖<δ/2 := hg j y hjy i
  calc
    _ ≤ ‖f (x,y)-f (i.val,y)‖+‖f (i.val,y)-f (i.val,j.val)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < δ := by linarith

end EndpointPartition

end
end

end OAI
