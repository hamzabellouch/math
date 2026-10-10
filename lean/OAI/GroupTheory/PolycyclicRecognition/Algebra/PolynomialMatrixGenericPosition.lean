import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixStabilizer
import Mathlib.Topology.Irreducible

namespace OAI

/-! # Simultaneous generic position in an irreducible polynomial matrix group

A finite collection of proper linear subspaces can be avoided both by a
matrix and its inverse whenever each vector has a spanning orbit.
-/

noncomputable section
namespace PolycyclicRecognition

private theorem finite_open_intersection_nonempty
    {X I : Type*} [TopologicalSpace X] [PreirreducibleSpace X] [Nonempty X] [Finite I]
    (U : I → Set X) (ho : ∀ i, IsOpen (U i)) (hn : ∀ i, (U i).Nonempty) :
    ∃ x, ∀ i, x ∈ U i := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have h (s : Finset I) : (⋂ i ∈ s, U i).Nonempty := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨x⟩ := ‹Nonempty X›
      exact ⟨x, by simp⟩
    | @insert i s hi ih =>
      have he : (⋂ j ∈ insert i s, U j) = U i ∩ ⋂ j ∈ s, U j := by ext; simp
      rw [he]
      exact nonempty_preirreducible_inter (ho i) (isOpen_biInter_finset fun j _ => ho j) (hn i) ih
  obtain ⟨x, hx⟩ := h Finset.univ
  exact ⟨x, fun i => Set.mem_iInter.mp (Set.mem_iInter.mp hx i) (Finset.mem_univ i)⟩

namespace PolynomialMatrixGroup

variable {K G I : Type*} [Field K] [Group G] [TopologicalSpace G]
    [PreirreducibleSpace G] [ContinuousInv G] [Finite I] {n : ℕ}

theorem exists_simultaneous_forward_inverse_avoidance
    (ι : G →* PolynomialMatrixGroup K n) (hι : Continuous ι)
    (v : I → Fin n → K) (W : I → Submodule K (Fin n → K))
    (hspan : ∀ i, Submodule.span K (Set.range (fun g => linearAction (ι g) (v i))) = ⊤)
    (hproper : ∀ i, W i ≠ ⊤) :
    ∃ g : G, ∀ i, linearAction (ι g) (v i) ∉ W i ∧
      linearAction (ι g⁻¹) (v i) ∉ W i := by
  have hex (i : I) : ∃ g : G, linearAction (ι g) (v i) ∉ W i := by
    by_contra! h
    have hs : Submodule.span K (Set.range (fun g => linearAction (ι g) (v i))) ≤ W i := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      exact h g
    exact hproper i (top_unique ((hspan i) ▸ hs))
  let U (p : I × Bool) : Set G :=
    {g | linearAction (ι (if p.2 then g⁻¹ else g)) (v p.1) ∉ W p.1}
  have ho (p : I × Bool) : IsOpen (U p) := by
    have hc := isClosed_linearAction_mem (W p.1) (v p.1)
    cases p with
    | mk i b =>
      cases b
      · exact (hc.preimage hι).isOpen_compl
      · exact (hc.preimage (hι.comp continuous_inv)).isOpen_compl
  have hn (p : I × Bool) : (U p).Nonempty := by
    obtain ⟨g, hg⟩ := hex p.1
    cases p with
    | mk i b =>
      cases b
      · exact ⟨g, hg⟩
      · refine ⟨g⁻¹, ?_⟩
        change linearAction (ι ((g⁻¹)⁻¹)) (v i) ∉ W i
        simpa only [inv_inv] using hg
  obtain ⟨g, hg⟩ := finite_open_intersection_nonempty U ho hn
  exact ⟨g, fun i => ⟨hg (i, false), hg (i, true)⟩⟩

end PolynomialMatrixGroup
end PolycyclicRecognition

end

end OAI
