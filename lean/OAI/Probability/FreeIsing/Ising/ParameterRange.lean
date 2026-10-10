import OAI.Probability.FreeIsing.Estimates.CylinderBasics
import OAI.Probability.FreeIsing.Trees.EdgeCylinders

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.parameter_mem_Icc_of_adj {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    {u v : TreeVertex d} (huv : treeAdj u v) : theta ∈ Set.Icc (-1 : ℝ) 1 := by
  have hbound (a b : IsingSpin) :
      (1 + (if a = b then theta else -theta)) / 4 ≤ (1 / 2 : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp
    rw [← hmu.edge_cylinder huv a b, ← hmu.marginal u a]
    exact measure_mono (fun _ hx => hx.1)
  have hp := hbound IsingSpin.pos IsingSpin.pos
  have hn := hbound IsingSpin.pos IsingSpin.neg
  simp only [ite_true] at hp
  simp only [reduceCtorEq, ite_false] at hn
  constructor <;> linarith

theorem HasFreeIsingLaw.parameter_mem_Icc {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (hd : 0 < d) : theta ∈ Set.Icc (-1 : ℝ) 1 := by
  let a : Fin d := ⟨0, hd⟩
  let u : TreeVertex d := ⟨[], List.isChain_nil⟩
  let v : TreeVertex d := ⟨[a], List.isChain_singleton a⟩
  exact hmu.parameter_mem_Icc_of_adj (u := u) (v := v) (Or.inl ⟨a, rfl⟩)

theorem IsFactorOfIID.parameter_mem_Icc {d : ℕ} {theta : ℝ}
    (h : IsFactorOfIID d theta) (hd : 0 < d) : theta ∈ Set.Icc (-1 : ℝ) 1 := by
  obtain ⟨_, _, hLaw, _⟩ := h
  exact hLaw.parameter_mem_Icc hd

end Problem367

end

end OAI
