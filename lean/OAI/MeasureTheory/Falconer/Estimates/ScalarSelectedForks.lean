import OAI.MeasureTheory.Falconer.Estimates.ScalarBinaryEmbedding
import OAI.MeasureTheory.Falconer.Geometry.ScalarForkGeometry

namespace OAI

/-! Embedding selected regularized forks into the scalar binary cube.
 Gaps between selected levels are filled by actual descendant fibers. -/
namespace Falconer.Regularization

 theorem prefixFiber_child_subset {L : Finset (CellPath 1)} {a b : ℕ}
    (hab : a ≤ b) {p c : CellPath 1} (hc : c ∈ prefixChildren L a b p) :
    prefixFiber L b c ⊆ prefixFiber L a p := by
  classical
  rw [← prefixFiber_parent_filter hab hc]
  exact Finset.filter_subset _ _

 theorem prefixFiber_nested {L : Finset (CellPath 1)} {a b : ℕ}
    (hab : a ≤ b) {p q : CellPath 1} (hq : q ∈ prefixFiber L a p) :
    prefixFiber L b (q.take b) ⊆ prefixFiber L a p := by
  classical
  intro u hu
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,
    (take_eq_of_take_eq hab (Finset.mem_filter.mp hu).2).trans (Finset.mem_filter.mp hq).2⟩

 theorem scalar_selected_binary_forks {N : ℕ} (Q : Finset (CellPath 1))
    (hQ : Q ⊆ cubePaths 1 N) (hne : Q.Nonempty) (t : ℕ)
    (a b k n : ℕ → ℕ)
    (hab : ∀ i < t, a i ≤ b i) (hnext : ∀ i < t, b i ≤ a (i+1))
    (hb : ∀ i < t, b i ≤ N)
    (hlevel : ∀ i < t, ScalarBranchingLevel Q (a i) (b i) (k i) (n i))
    (hk : ∀ i < t, k i ≠ 0) :
    ∃ f : (Fin t → Bool) → ℝ, (∀ w, f w ∈ Q.image scalarPathCenter) ∧
      ∀ i : Fin t, ∀ w, ScalarBinaryTail i w →
        6*(1/2:ℝ)^(n i) ≤ |f (Function.update w i true)-f w| ∧
        |f (Function.update w i true)-f w| ≤ 18*(1/2:ℝ)^(n i) := by
  classical
  let P : ℕ → Finset ℝ → Prop := fun i E =>
    ∃ p ∈ Q.image (List.take (a i)), E = (prefixFiber Q (a i) p).image scalarPathCenter
  have hPn : ∀ i ≤ t, ∀ E, P i E → E.Nonempty := by
    intro i _ E hE
    obtain ⟨p,hp,rfl⟩ := hE
    exact (prefixFiber_nonempty hp).image scalarPathCenter
  have hstep : ∀ i < t, ∀ E, P i E → ∃ E0 E1 : Finset ℝ,
      E0 ⊆ E ∧ E1 ⊆ E ∧ P (i+1) E0 ∧ P (i+1) E1 ∧
      ∀ x ∈ E0, ∀ y ∈ E1,
        6*(1/2:ℝ)^(n i) ≤ |x-y| ∧ |x-y| ≤ 18*(1/2:ℝ)^(n i) := by
    intro i hi E hE
    obtain ⟨p,hp,rfl⟩ := hE
    obtain ⟨c,hc,d,hd,_,hfork⟩ := scalar_fork_leaf_bounds hQ (hb i hi) (hlevel i hi) (hk i hi) hp
    obtain ⟨u,hu⟩ := prefixFiber_nonempty (prefixChildren_mem_image hc)
    obtain ⟨v,hv⟩ := prefixFiber_nonempty (prefixChildren_mem_image hd)
    let E0 := (prefixFiber Q (a (i+1)) (u.take (a (i+1)))).image scalarPathCenter
    let E1 := (prefixFiber Q (a (i+1)) (v.take (a (i+1)))).image scalarPathCenter
    have h0 := prefixFiber_nested (hnext i hi) hu
    have h1 := prefixFiber_nested (hnext i hi) hv
    have h0P := prefixFiber_child_subset (hab i hi) hc
    have h1P := prefixFiber_child_subset (hab i hi) hd
    refine ⟨E0,E1,Finset.image_subset_image (h0.trans h0P),
      Finset.image_subset_image (h1.trans h1P),?_,?_,?_⟩
    · exact ⟨u.take (a (i+1)),Finset.mem_image_of_mem _ (Finset.mem_filter.mp hu).1,rfl⟩
    · exact ⟨v.take (a (i+1)),Finset.mem_image_of_mem _ (Finset.mem_filter.mp hv).1,rfl⟩
    · intro x hx y hy
      obtain ⟨u',hu',rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v',hv',rfl⟩ := Finset.mem_image.mp hy
      exact hfork u' (h0 hu') v' (h1 hv')
  obtain ⟨q,hq⟩ := hne
  let S := (prefixFiber Q (a 0) (q.take (a 0))).image scalarPathCenter
  have hS : P 0 S := ⟨q.take (a 0),Finset.mem_image_of_mem _ hq,rfl⟩
  obtain ⟨f,hf,hbits⟩ := scalar_binary_embedding t P (fun i => 6*(1/2:ℝ)^(n i))
    (fun i => 18*(1/2:ℝ)^(n i)) S hS hPn hstep
  refine ⟨f,?_,hbits⟩
  intro w
  exact Finset.image_subset_image (Finset.filter_subset _ _) (hf w)

end Falconer.Regularization

end OAI
