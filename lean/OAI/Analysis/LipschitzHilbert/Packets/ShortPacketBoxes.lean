import OAI.Analysis.LipschitzHilbert.Packets.PacketBoxes
import OAI.Analysis.LipschitzHilbert.Packets.HilbertPacketSums

namespace OAI

/-! Exact finite decomposition of the short-scale synthesis into its actual
center boxes. Empty fibers are retained and contribute zero. -/

noncomputable section
open scoped BigOperators

namespace LipschitzHilbert

attribute [local instance] Classical.propDecidable

def centerBoxIndex {σ : Type*} {ι : σ → Type*} (X Z : ∀ j, ι j → ℝ)
    (u y r W : ℝ) (j : σ) (i : ι j) : ℤ × ℤ :=
  packetBoxIndex u y r W (X j i) (Z j i)

def allPacketBoxes {σ : Type*} {ι : σ → Type*} [Fintype σ] [∀ j, Fintype (ι j)]
    (index : ∀ j, ι j → ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.univ.image (fun p : Sigma ι => index p.1 p.2)

theorem mem_allPacketBoxes {σ : Type*} {ι : σ → Type*} [Fintype σ] [∀ j, Fintype (ι j)]
    (index : ∀ j, ι j → ℤ × ℤ) (j : σ) (i : ι j) : index j i ∈ allPacketBoxes index :=
  Finset.mem_image.mpr ⟨⟨j,i⟩, Finset.mem_univ _, rfl⟩

abbrev ShortBoxFiber {σ : Type*} {ι : σ → Type*}
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ) (b : ℤ × ℤ) (j : σ) :=
  {i : ι j // len j ≤ r ∧ index j i = b}

def shortBoxSynthesis {σ : Type*} {ι : σ → Type*} [∀ j, Fintype (ι j)]
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ)
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ) (b : ℤ × ℤ) (j : σ) :
    SchwartzMap ℝ ℂ :=
  packetSynthesis (fun i : ShortBoxFiber len index r b j => c j i)
    (fun i => f j i)

theorem shortBoxSynthesis_eq {σ : Type*} {ι : σ → Type*} [∀ j, Fintype (ι j)]
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ)
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ) (b : ℤ × ℤ) (j : σ) :
    shortBoxSynthesis len index r c f b j =
      if len j ≤ r then packetBoxSynthesis (index j) (c j) (f j) b else 0 := by
  have h := Finset.sum_subtype (Finset.univ.filter (fun i : ι j => len j ≤ r ∧ index j i = b))
    (p := fun i : ι j => len j ≤ r ∧ index j i = b) (F := inferInstance)
    (by simp) (fun i => c j i • f j i)
  rw [Finset.sum_filter] at h
  change (∑ i : ShortBoxFiber len index r b j, c j i • f j i) = _
  rw [← h]
  by_cases hj : len j ≤ r
  · simp only [hj, true_and, ite_true, packetBoxSynthesis]
  · simp [hj]

theorem shortSynthesis_eq_sum_boxes {σ : Type*} {ι : σ → Type*}
    [Fintype σ] [∀ j, Fintype (ι j)]
    (len : σ → ℝ) (index : ∀ j, ι j → ℤ × ℤ) (r : ℝ)
    (c : ∀ j, ι j → ℂ) (f : ∀ j, ι j → SchwartzMap ℝ ℂ) (j : σ) :
    (if len j ≤ r then packetSynthesis (c j) (f j) else 0) =
      ∑ b ∈ allPacketBoxes index, shortBoxSynthesis len index r c f b j := by
  simp_rw [shortBoxSynthesis_eq]
  by_cases hj : len j ≤ r
  · simp only [hj, ite_true]
    exact packetSynthesis_eq_sum_boxes_of_mem (index j) (c j) (f j) _
      (fun i => mem_allPacketBoxes index j i)
  · simp [hj]

theorem component_coefficient_energy {κ ι : Type*} [Fintype κ] [Fintype ι]
    (c : ι → EuclideanSpace ℂ κ) :
    (∑ k, ∑ i, ‖c i k‖ ^ 2) = ∑ i, ‖c i‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (EuclideanSpace.norm_sq_eq (c i)).symm

end LipschitzHilbert

end

end OAI
