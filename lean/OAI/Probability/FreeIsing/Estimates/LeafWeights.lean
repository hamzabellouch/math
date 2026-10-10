import OAI.Probability.FreeIsing.Estimates.LeafDeletion
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

namespace Problem367

private theorem leafWeight_congr_on {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) {eta eta' : TreeVertex d → IsingSpin}
    (h : ∀ v ∈ D, eta v = eta' v) :
    freeCylinderWeight theta D eta = freeCylinderWeight theta D eta' := by
  classical
  apply congrArg ENNReal.ofReal
  apply congrArg ((1 / 2 : ℝ) * ·)
  apply Finset.prod_congr rfl
  intro e he
  have hm := (Finset.mem_filter.mp he).1
  rw [Finset.product_eq_sprod] at hm
  have hmem := Finset.mem_product.mp hm
  rw [h e.1 hmem.1, h e.2 hmem.2]

theorem freeCylinderWeight_eq_mul_erase_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      freeCylinderWeight theta (D.erase v) eta *
        ENNReal.ofReal (transitionKernel theta (eta p) (eta v)) := by
  classical
  have hnot : (p, v) ∉ inducedEdges (D.erase v) := by
    simp [inducedEdges, Finset.product_eq_sprod]
  rw [freeCylinderWeight_eq_transitionKernel,
    hedges,
    Finset.prod_insert hnot, freeCylinderWeight_eq_transitionKernel]
  rw [show (1 / 2 : ℝ) * (transitionKernel theta (eta p) (eta v) *
      ∏ e ∈ inducedEdges (D.erase v), transitionKernel theta (eta e.1) (eta e.2)) =
      ((1 / 2 : ℝ) * ∏ e ∈ inducedEdges (D.erase v),
        transitionKernel theta (eta e.1) (eta e.2)) *
      transitionKernel theta (eta p) (eta v) by ring]
  exact ENNReal.ofReal_mul (by
    apply mul_nonneg (by norm_num)
    apply Finset.prod_nonneg
    intro e he
    exact transitionKernel_nonneg hlo hhi _ _)

theorem freeCylinderWeight_eq_mul_erase_of_max_length
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length)
    (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      freeCylinderWeight theta (D.erase v) eta *
        ENNReal.ofReal (transitionKernel theta (eta p) (eta v)) :=
  freeCylinderWeight_eq_mul_erase_of_edges hlo hhi
    (inducedEdges_eq_insert_erase_of_max_length hv hp hpv hplen hmax) eta

theorem freeCylinderWeight_update_erase {d : ℕ} (theta : ℝ)
    (D : Finset (TreeVertex d)) (v : TreeVertex d)
    (eta : TreeVertex d → IsingSpin) (s : IsingSpin) :
    freeCylinderWeight theta (D.erase v) (Function.update eta v s) =
      freeCylinderWeight theta (D.erase v) eta := by
  apply leafWeight_congr_on
  intro x hx
  exact Function.update_of_ne (Finset.mem_erase.mp hx).1 _ _

theorem sum_ofReal_transitionKernel {theta : ℝ} (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (a : IsingSpin) :
    ∑ s : IsingSpin, ENNReal.ofReal (transitionKernel theta a s) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => transitionKernel_nonneg hlo hhi a s)]
  simp

theorem freeCylinderWeight_sum_update_of_edges
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1) (hpne : p ≠ v)
    (hedges : inducedEdges D = insert (p, v) (inducedEdges (D.erase v)))
    (eta : TreeVertex d → IsingSpin) :
    ∑ s : IsingSpin, freeCylinderWeight theta D (Function.update eta v s) =
      freeCylinderWeight theta (D.erase v) eta := by
  simp_rw [freeCylinderWeight_eq_mul_erase_of_edges hlo hhi hedges,
    freeCylinderWeight_update_erase, Function.update_of_ne hpne, Function.update_self]
  rw [← Finset.mul_sum, sum_ofReal_transitionKernel hlo hhi, mul_one]

theorem freeCylinderWeight_sum_update_leaf
    {d : ℕ} {D : Finset (TreeVertex d)} {v p : TreeVertex d} {theta : ℝ}
    (hlo : -1 ≤ theta) (hhi : theta ≤ 1)
    (hv : v ∈ D) (hp : p ∈ D) (hpv : treeAdj p v)
    (hplen : p.1.length < v.1.length)
    (hmax : ∀ x ∈ D, x.1.length ≤ v.1.length)
    (eta : TreeVertex d → IsingSpin) :
    ∑ s : IsingSpin, freeCylinderWeight theta D (Function.update eta v s) =
      freeCylinderWeight theta (D.erase v) eta := by
  have hpne : p ≠ v := by
    intro h
    subst p
    exact (lt_irrefl _ hplen)
  exact freeCylinderWeight_sum_update_of_edges hlo hhi hpne
    (inducedEdges_eq_insert_erase_of_max_length hv hp hpv hplen hmax) eta

end Problem367

end

end OAI
