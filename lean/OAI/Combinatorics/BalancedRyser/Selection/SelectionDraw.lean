import OAI.Combinatorics.BalancedRyser.Selection.Selection
import OAI.Combinatorics.BalancedRyser.Selection.SelectionThinning

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection

noncomputable section

variable {I V : Type*} [Fintype I] [Fintype V]

def vertexDrawMass (G : Input I V) (v : V) : ℝ :=
  (Fintype.card I : ℝ)⁻¹ * ((slotVertices G (G.slot v)).card : ℝ)⁻¹

lemma vertexDrawMass_nonneg (G : Input I V) (v : V) : 0 ≤ vertexDrawMass G v := by
  unfold vertexDrawMass
  positivity

lemma vertexDrawMass_in_slot (G : Input I V) (i : I) (v : V) (hv : v ∈ slotVertices G i) :
    vertexDrawMass G v = (Fintype.card I : ℝ)⁻¹ * ((slotVertices G i).card : ℝ)⁻¹ := by
  have hs : G.slot v = i := (Finset.mem_filter.mp hv).2
  simp [vertexDrawMass, hs]

lemma vertexDrawMass_fiber (G : Input I V) (i : I) (hi : (slotVertices G i).Nonempty) :
    (∑ v ∈ slotVertices G i, vertexDrawMass G v) = (Fintype.card I : ℝ)⁻¹ := by
  have hc : ((slotVertices G i).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hi).ne'
  calc
    _ = ∑ _v ∈ slotVertices G i,
      (Fintype.card I : ℝ)⁻¹ * ((slotVertices G i).card : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      exact fun v hv => vertexDrawMass_in_slot G i v hv
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

lemma sum_vertexDrawMass [Nonempty I] (G : Input I V)
    (hslots : ∀ i, (slotVertices G i).Nonempty) :
    (∑ v, vertexDrawMass G v) = 1 := by
  have hf := Finset.sum_fiberwise Finset.univ G.slot (vertexDrawMass G)
  change (∑ i, ∑ v ∈ slotVertices G i, vertexDrawMass G v) = _ at hf
  rw [← hf]
  simp only [vertexDrawMass_fiber G _ (hslots _), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact mul_inv_cancel₀ hc

lemma vertexDrawMass_slot (G : Input I V) (hslots : ∀ i, (slotVertices G i).Nonempty)
    (i : I) :
    SelectionThinning.eventMass (vertexDrawMass G) (fun v => G.slot v = i) =
      (Fintype.card I : ℝ)⁻¹ := by
  unfold SelectionThinning.eventMass
  rw [← Finset.sum_filter]
  exact vertexDrawMass_fiber G i (hslots i)

def conflictHazard (G : Input I V) (u : V) : ℝ :=
  SelectionThinning.eventMass (vertexDrawMass G) (G.graph.Adj u)

lemma conflictHazard_nonneg (G : Input I V) (u : V) : 0 ≤ conflictHazard G u := by
  apply Finset.sum_nonneg
  intro v _
  split
  · exact vertexDrawMass_nonneg G v
  · exact le_rfl

lemma conflictHazard_eq (G : Input I V) (u : V) :
    conflictHazard G u = (Fintype.card I : ℝ)⁻¹ *
      ∑ i, (((neighbors G u ∩ slotVertices G i).card : ℝ) /
        ((slotVertices G i).card : ℝ)) := by
  unfold conflictHazard SelectionThinning.eventMass
  rw [← Finset.sum_filter]
  change (∑ v ∈ neighbors G u, vertexDrawMass G v) = _
  have hf := Finset.sum_fiberwise (neighbors G u) G.slot (vertexDrawMass G)
  rw [← hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : (neighbors G u).filter (fun v => G.slot v = i) =
      neighbors G u ∩ slotVertices G i := by
    ext v
    simp [slotVertices]
  rw [he]
  calc
    _ = ∑ _v ∈ neighbors G u ∩ slotVertices G i,
        (Fintype.card I : ℝ)⁻¹ * ((slotVertices G i).card : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro v hv
      exact vertexDrawMass_in_slot G i v (Finset.mem_inter.mp hv).2
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]; ring

def nextStepMass (G : Input I V) (α : ℝ) (w : V) (b : V → Bool) : ℝ :=
  SelectionThinning.jointMass (vertexDrawMass G)
    (fun u => SelectionThinning.thinningRate α (conflictHazard G u)) w b

lemma nextStepMass_nonneg (G : Input I V) (α : ℝ) (ha : α < 1)
    (hcheck : ∀ u, conflictHazard G u ≤ α) (w : V) (b : V → Bool) :
    0 ≤ nextStepMass G α w b := by
  apply SelectionThinning.jointMass_nonneg _ (vertexDrawMass_nonneg G)
  intro u
  have hb := SelectionThinning.thinningRate_bounds (conflictHazard_nonneg G u) (hcheck u) ha
  exact ⟨hb.1, hb.2.trans ha.le⟩

lemma sum_nextStepMass [Nonempty I] (G : Input I V)
    (hslots : ∀ i, (slotVertices G i).Nonempty) (α : ℝ) :
    (∑ w, ∑ b, nextStepMass G α w b) = 1 :=
  SelectionThinning.sum_jointMass _ (sum_vertexDrawMass G hslots) _

def stepLaw [Nonempty I] (G : Input I V)
    (hslots : ∀ i, (slotVertices G i).Nonempty) (α : ℝ) (ha : α < 1)
    (hcheck : ∀ u, conflictHazard G u ≤ α) : PMF (V × (V → Bool)) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (nextStepMass G α z.1 z.2)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun z _ => nextStepMass_nonneg G α ha hcheck z.1 z.2)]
    rw [Fintype.sum_prod_type, sum_nextStepMass G hslots]
    simp)

@[simp] lemma stepLaw_apply [Nonempty I] (G : Input I V)
    (hslots : ∀ i, (slotVertices G i).Nonempty) (α : ℝ) (ha : α < 1)
    (hcheck : ∀ u, conflictHazard G u ≤ α) (z : V × (V → Bool)) :
    stepLaw G hslots α ha hcheck z = ENNReal.ofReal (nextStepMass G α z.1 z.2) := rfl

lemma nextStep_pre_survival [Nonempty I] (G : Input I V)
    (hslots : ∀ i, (slotVertices G i).Nonempty) (α : ℝ) (ha : α < 1)
    (hcheck : ∀ u, conflictHazard G u ≤ α) (u : V) :
    (∑ w, ∑ b : V → Bool,
      if ¬ G.graph.Adj u w ∧ b u = false then nextStepMass G α w b else 0) = 1 - α := by
  have h := SelectionThinning.pre_removal_survival (vertexDrawMass G)
    (sum_vertexDrawMass G hslots) (fun w v => G.graph.Adj v w) α
    (fun v => lt_of_le_of_lt (hcheck v) ha) u
  convert h using 1
  apply Finset.sum_congr (by ext; simp)
  intro w _
  apply Finset.sum_congr (by ext; simp)
  intro b _
  by_cases he : ¬ G.graph.Adj u w ∧ b u = false <;>
    simp [he, nextStepMass, conflictHazard]

lemma nextStep_post_survival_le [Nonempty I] (G : Input I V)
    (hslots : ∀ i, (slotVertices G i).Nonempty)
    (hwithin : ∀ u w, G.slot u = G.slot w → ¬ G.graph.Adj u w)
    (α : ℝ) (ha : α < 1) (hcheck : ∀ u, conflictHazard G u ≤ α) (u : V) :
    (∑ w, ∑ b : V → Bool,
      if (¬ G.graph.Adj u w ∧ G.slot w ≠ G.slot u) ∧ b u = false then
        nextStepMass G α w b else 0) ≤
        (1 - α) * (1 - (Fintype.card I : ℝ)⁻¹) := by
  have h := SelectionThinning.post_removal_survival_le (vertexDrawMass G)
    (sum_vertexDrawMass G hslots) (fun w v => G.graph.Adj v w)
    (fun w v => G.slot w = G.slot v) (fun w v he => hwithin v w he.symm)
    α (Fintype.card I : ℝ)⁻¹ (by positivity) ha (conflictHazard_nonneg G)
    hcheck (fun v => vertexDrawMass_slot G hslots (G.slot v)) u
  convert h using 1
  apply Finset.sum_congr (by ext; simp)
  intro w _
  apply Finset.sum_congr (by ext; simp)
  intro b _
  by_cases he : (¬ G.graph.Adj u w ∧ G.slot w ≠ G.slot u) ∧ b u = false <;>
    simp [he, nextStepMass, conflictHazard]

end
end Balanced.Selection

end OAI
