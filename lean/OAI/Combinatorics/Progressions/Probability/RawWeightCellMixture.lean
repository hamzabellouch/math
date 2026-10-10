import OAI.Combinatorics.Progressions.Estimates.NormalizedTwistCellSelection

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem embedded_cell_mixture {X R : Type*} [Fintype X] [DecidableEq X] [DecidableEq R]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (F : X → R) (S : Finset R) (Y : S → Type*) [∀ r, Fintype (Y r)]
    (e : ∀ r, Y r ↪ X)
    (hcell : ∀ r, finiteEmbeddingRange (e r) = Finset.univ.filter (fun x => F x = r.val))
    (hchild : ∀ r, 0 < ∑ y, w (e r y)) (f : X → ℂ) :
    (∑ r : S,
      ((ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x = r.val)) : ℂ) *
        (ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r)).complexMean
          (fun y => f (e r y))) =
      (ofPositiveWeights w hw htotal).complexMean (fun x => if F x ∈ S then f x else 0) := by
  calc
    _ = ∑ r : S, (ofPositiveWeights w hw htotal).fiberComplexMean F r.val f := by
      apply Finset.sum_congr rfl
      intro r _
      exact ofPositiveWeights_embedded_fiber_complexMean w hw htotal F r.val
        (e r) (hcell r) (hchild r) f
    _ = ∑ r ∈ S, (ofPositiveWeights w hw htotal).fiberComplexMean F r f :=
      Finset.sum_coe_sort S (fun r => (ofPositiveWeights w hw htotal).fiberComplexMean F r f)
    _ = _ := (ofPositiveWeights w hw htotal).sum_fiberComplexMean_on F S f

theorem embedded_cell_mixture_error {X R : Type*} [Fintype X] [DecidableEq X] [DecidableEq R]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (F : X → R) (S : Finset R) (Y : S → Type*) [∀ r, Fintype (Y r)]
    (e : ∀ r, Y r ↪ X)
    (hcell : ∀ r, finiteEmbeddingRange (e r) = Finset.univ.filter (fun x => F x = r.val))
    (hchild : ∀ r, 0 < ∑ y, w (e r y)) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(ofPositiveWeights w hw htotal).complexMean f - ∑ r : S,
      ((ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x = r.val)) : ℂ) *
        (ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r)).complexMean
          (fun y => f (e r y))‖ ≤
      (ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x ∉ S)) := by
  rw [embedded_cell_mixture w hw htotal F S Y e hcell hchild f]
  have h := (ofPositiveWeights w hw htotal).norm_complexMean_remove_set_le_mass
    (Finset.univ.filter (fun x => F x ∉ S)) f hf
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, ite_not] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem ofPositiveWeights_lowWeightFibers_mass {X R : Type*}
    [Fintype X] [Nonempty X] [Fintype R]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (hm : 0 < (uniform X).mean w) (F : X → R) {η : ℝ} (hη : 0 ≤ η) :
    (ofPositiveWeights w hw htotal).mass
      (Finset.univ.filter (fun x => F x ∈ (uniform X).lowWeightFibers F w η)) ≤
        η / (uniform X).mean w := by
  rw [← uniform_reweightPositive_eq w hw hm htotal]
  exact (uniform X).reweightPositive_lowWeightFibers_mass F w hw hm hη

theorem embedded_lowWeight_cell_mixture_error {X R : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X] [Fintype R] [DecidableEq R]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (htotal : 0 < ∑ x, w x)
    (hm : 0 < (uniform X).mean w) (F : X → R) {η : ℝ} (hη : 0 ≤ η)
    (S : Finset R) (hS : S = Finset.univ \ (uniform X).lowWeightFibers F w η)
    (Y : S → Type*) [∀ r, Fintype (Y r)] (e : ∀ r, Y r ↪ X)
    (hcell : ∀ r, finiteEmbeddingRange (e r) = Finset.univ.filter (fun x => F x = r.val))
    (hchild : ∀ r, 0 < ∑ y, w (e r y)) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(ofPositiveWeights w hw htotal).complexMean f - ∑ r : S,
      ((ofPositiveWeights w hw htotal).mass (Finset.univ.filter (fun x => F x = r.val)) : ℂ) *
        (ofPositiveWeights (fun y => w (e r y)) (fun y => hw (e r y)) (hchild r)).complexMean
          (fun y => f (e r y))‖ ≤ η / (uniform X).mean w := by
  apply (embedded_cell_mixture_error w hw htotal F S Y e hcell hchild f hf).trans
  have h := ofPositiveWeights_lowWeightFibers_mass w hw htotal hm F hη
  apply le_trans (le_of_eq ?_) h
  apply congrArg (ofPositiveWeights w hw htotal).mass
  ext x
  simp only [hS, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

end Erdos3.FiniteProbabilityWeights

end

end OAI
