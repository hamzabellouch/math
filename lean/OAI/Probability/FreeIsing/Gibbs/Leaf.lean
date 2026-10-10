import OAI.Probability.FreeIsing.Gibbs.Weights

namespace OAI

noncomputable section

namespace Problem367.GibbsLeaf

def energy {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ℝ :=
  (∑ x ∈ D, h x * spinSign (eta x)) +
    beta * ∑ e ∈ inducedEdges D, spinSign (eta e.1) * spinSign (eta e.2)

def weight {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) : ℝ :=
  Real.exp (energy beta h D eta)

theorem energy_congr_on {d : ℕ} (beta : ℝ) (h : TreeVertex d → ℝ)
    (D : Finset (TreeVertex d)) {eta xi : TreeVertex d → IsingSpin}
    (heq : ∀ x ∈ D, eta x = xi x) : energy beta h D eta = energy beta h D xi := by
  classical
  unfold energy
  congr 1
  · exact Finset.sum_congr rfl (fun x hx => by rw [heq x hx])
  · congr 1
    apply Finset.sum_congr rfl
    intro e he
    have hm := (Finset.mem_filter.mp he).1
    rw [Finset.product_eq_sprod] at hm
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hm
    rw [heq e.1 hu, heq e.2 hv]

theorem energy_update_eq_erase_add
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) (s : IsingSpin) :
    energy beta h D (Function.update eta v s) = energy beta h (D.erase v) eta +
      (h v + beta * spinSign (eta p)) * spinSign s := by
  classical
  have hnot : (p, v) ∉ inducedEdges (D.erase v) := by
    simp [inducedEdges, Finset.product_eq_sprod]
  have hfield : (∑ x ∈ D, h x * spinSign (Function.update eta v s x)) =
      (∑ x ∈ D.erase v, h x * spinSign (eta x)) + h v * spinSign s := by
    rw [← Finset.sum_erase_add D _ hv]
    simp only [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.mem_erase.mp hx).1]
  have hedge : (∑ e ∈ inducedEdges (D.erase v),
      spinSign (Function.update eta v s e.1) * spinSign (Function.update eta v s e.2)) =
      ∑ e ∈ inducedEdges (D.erase v), spinSign (eta e.1) * spinSign (eta e.2) := by
    apply Finset.sum_congr rfl
    intro e he
    have hm := (Finset.mem_filter.mp he).1
    rw [Finset.product_eq_sprod] at hm
    obtain ⟨hu, hw⟩ := Finset.mem_product.mp hm
    rw [Function.update_of_ne (Finset.mem_erase.mp hu).1,
      Function.update_of_ne (Finset.mem_erase.mp hw).1]
  unfold energy
  rw [hfield, hedges, Finset.sum_insert hnot, hedge]
  simp only [Function.update_of_ne hpne, Function.update_self]
  ring

theorem sum_weight_update_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      2 * Real.cosh (h v + beta * spinSign (eta p)) * weight beta h (D.erase v) eta := by
  simp only [weight, energy_update_eq_erase_add beta h hv hpne hedges, Real.exp_add]
  rw [← Finset.mul_sum, sum_isingSpin]
  simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one]
  rw [Real.cosh_eq]
  ring

theorem sum_weight_update_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ)
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length)
    (eta : TreeVertex d → IsingSpin) :
    (∑ s : IsingSpin, weight beta h D (Function.update eta v s)) =
      2 * Real.cosh (h v + beta * spinSign (eta p)) * weight beta h (D.erase v) eta := by
  apply sum_weight_update_of_edges beta h hv
  · intro heq
    subst p
    exact lt_irrefl _ hplen
  · exact inducedEdges_eq_insert_erase_of_max_length hv hp hpv hplen hmax

theorem sum_weight_eq_erase_sum
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d}
    (beta : ℝ) (h : TreeVertex d → ℝ) (hv : v ∈ D) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v))) :
    (∑ eta : D → IsingSpin, weight beta h D (extendFiniteSpin D eta)) =
      ∑ eta : D.erase v → IsingSpin,
        2 * Real.cosh (h v + beta * spinSign (extendFiniteSpin (D.erase v) eta p)) *
          weight beta h (D.erase v) (extendFiniteSpin (D.erase v) eta) := by
  classical
  calc
    _ = ∑ z : (D.erase v → IsingSpin) × IsingSpin,
        weight beta h D (extendFiniteSpin D ((finiteSpinEraseEquiv hv).symm z)) :=
      ((finiteSpinEraseEquiv hv).symm.sum_comp
        (fun eta => weight beta h D (extendFiniteSpin D eta))).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro eta _
      simp only [extendFiniteSpin_eraseEquiv_symm]
      exact sum_weight_update_of_edges beta h hv hpne hedges _

end Problem367.GibbsLeaf

end

end OAI
