import OAI.Probability.FreeIsing.Cavity.LogOdds
import OAI.Probability.FreeIsing.Gibbs.Leaf

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

def eliminationConstant (beta z : ℝ) : ℝ :=
  2 * Real.exp ((Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2)

theorem eliminationConstant_pos (beta z : ℝ) : 0 < eliminationConstant beta z := by
  unfold eliminationConstant
  positivity

theorem cosh_eq_eliminationConstant_mul_message (beta z : ℝ) (s : IsingSpin) :
    2 * Real.cosh (z + beta * spinSign s) =
      eliminationConstant beta z * Real.exp
        (cavityMessage (Real.tanh beta) z * spinSign s) := by
  unfold eliminationConstant
  rw [mul_assoc, ← Real.exp_add, cavityMessage_eq_log_cosh_sub]
  cases s
  · simp only [spinSign_neg, mul_neg_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        -((Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2) =
        Real.log (Real.cosh (z - beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]
    congr 2
  · simp only [spinSign_pos, mul_one]
    rw [show (Real.log (Real.cosh (z + beta)) + Real.log (Real.cosh (z - beta))) / 2 +
        (Real.log (Real.cosh (z + beta)) - Real.log (Real.cosh (z - beta))) / 2 =
        Real.log (Real.cosh (z + beta)) by ring]
    rw [Real.exp_log (Real.cosh_pos _)]

theorem energy_update_field {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) {p : TreeVertex d} (hp : p ∈ D)
    (z : ℝ) (eta : TreeVertex d → IsingSpin) :
    energy beta (Function.update h p (h p + z)) D eta =
      energy beta h D eta + z * spinSign (eta p) := by
  classical
  have hsum : (∑ x ∈ D.erase p, Function.update h p (h p + z) x * spinSign (eta x)) =
      ∑ x ∈ D.erase p, h x * spinSign (eta x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  unfold energy
  rw [← Finset.sum_erase_add D
    (fun x => Function.update h p (h p + z) x * spinSign (eta x)) hp,
    ← Finset.sum_erase_add D (fun x => h x * spinSign (eta x)) hp, hsum]
  simp only [Function.update_self]
  ring

theorem sum_weight_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      eliminationConstant beta (h v) *
        weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
          (D.erase v) eta := by
  rw [sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges,
    cosh_eq_eliminationConstant_mul_message]
  simp only [weight, energy_update_field beta h (D.erase v) hp, Real.exp_add]
  ring

theorem partition_eq_cavity_partition
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      eliminationConstant beta (h v) *
        ∑ eta : D.erase v → IsingSpin,
          weight beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
            (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  rw [sum_weight_eq_erase_sum beta h hv (Finset.mem_erase.mp hp).1 hedges, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  rw [← sum_weight_update_of_edges beta h hv (Finset.mem_erase.mp hp).1 hedges]
  exact sum_weight_update_eq_cavity beta h hv hp hedges _

def partition {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) : ℝ :=
  ∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)

def mass {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ℝ :=
  weight beta h D eta / partition beta h D

theorem partition_pos {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) : 0 < partition beta h D := by
  classical
  let : Nonempty (D → IsingSpin) := ⟨fun _ => .neg⟩
  exact Finset.sum_pos (fun eta _ => Real.exp_pos _) Finset.univ_nonempty

theorem sum_mass_update_eq_cavity
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hp : p ∈ D.erase v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, mass beta h D (Function.update eta v s)) =
      mass beta (Function.update h p (h p + cavityMessage (Real.tanh beta) (h v)))
        (D.erase v) eta := by
  classical
  simp only [mass, ← Finset.sum_div]
  rw [sum_weight_update_eq_cavity beta h hv hp hedges]
  unfold partition
  rw [partition_eq_cavity_partition beta h hv hp hedges]
  exact mul_div_mul_left _ _ (ne_of_gt (eliminationConstant_pos beta (h v)))

end Problem367.GibbsLeaf

end

end OAI
