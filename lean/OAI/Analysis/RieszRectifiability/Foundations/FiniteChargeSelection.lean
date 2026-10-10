import Mathlib

namespace OAI

namespace RieszRectifiability

open scoped ENNReal

theorem exists_finite_pair_witnesses {ι τ : Type*} (F : Finset ι)
    (Rel : ι → ι → Prop) (Q : ι → ι → τ → Prop)
    (hex : ∀ i ∈ F, ∀ j ∈ F, Rel i j → ∃ t, Q i j t) :
    ∃ O : Finset τ, ∀ i ∈ F, ∀ j ∈ F, Rel i j → ∃ t ∈ O, Q i j t := by
  classical
  let P := (F.product F).filter (fun ij => Rel ij.1 ij.2)
  have hchoose (p : {ij // ij ∈ P}) : ∃ t, Q p.val.1 p.val.2 t := by
    have hm := Finset.mem_filter.mp p.property
    have hp := Finset.mem_product.mp hm.1
    exact hex p.val.1 hp.1 p.val.2 hp.2 hm.2
  let O := P.attach.image (fun p => (hchoose p).choose)
  refine ⟨O, ?_⟩
  intro i hi j hj hRel
  have hp : (i, j) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hRel⟩
  let p : {ij // ij ∈ P} := ⟨(i, j), hp⟩
  exact ⟨(hchoose p).choose, Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩,
    (hchoose p).choose_spec⟩

theorem finite_subtype_sum_le_tsum {ι : Type*} (P : ι → Prop) (f : ι → ℝ≥0∞)
    (s : Finset ι) (hs : ∀ i ∈ s, P i) :
    ∑ i ∈ s, f i ≤ ∑' i : {i // P i}, f i.val := by
  classical
  let emb : {i // i ∈ s} ↪ {i // P i} :=
    ⟨fun i => ⟨i.val, hs i.val i.property⟩,
      fun i j hij => Subtype.ext (congrArg (fun t : {i // P i} => t.val) hij)⟩
  let t := s.attach.map emb
  have heq : ∑ i ∈ t, f i.val = ∑ i ∈ s, f i := by
    rw [Finset.sum_map]
    change (∑ i ∈ s.attach, f i.val) = ∑ i ∈ s, f i
    exact Finset.sum_attach s f
  exact heq.symm.le.trans (ENNReal.sum_le_tsum t)

end RieszRectifiability

end OAI
