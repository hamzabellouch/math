import OAI.Combinatorics.MatchingPSD.ColorPolynomials

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
attribute [local instance] Classical.propDecidable
section TableCoordinates
variable {V : Type u_1} {C : Type u_2} [Fintype V]

lemma tableCoordinate_symm (z : V → C) (a b : C) :
    tableCoordinate z (a,b) = tableCoordinate z (b,a) := by
  funext M
  unfold tableCoordinate
  rw [← Equiv.sum_comp M.1 (fun v => if z v = b ∧ z (M.1 v) = a then (1:ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro v _
  simp [M.partner_partner, and_comm]

lemma tableCoordinate_row_sum [Fintype C] (z : V → C) (a : C) :
    ∑ b, tableCoordinate z (a,b) = (histogram z a : ℝ) • 1 := by
  classical
  funext M
  simp only [Finset.sum_apply, tableCoordinate, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, mul_one]
  rw [Finset.sum_comm, histogram_cast_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases ha : z v = a
  · simp [ha]
  · simp [ha]

lemma tableCoordinate_diagonal [Fintype C] (z : V → C) (a : C) :
    tableCoordinate z (a,a) = (histogram z a : ℝ) • 1 -
      ∑ b ∈ Finset.univ.erase a, tableCoordinate z (a,b) := by
  classical
  rw [← tableCoordinate_row_sum]
  rw [eq_sub_iff_add_eq, add_comm]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ a)

end TableCoordinates

section ThreeCoordinates
variable {V : Type u_3} [Fintype V]

def crossPair : Fin 3 → Fin 3 × Fin 3 := ![(0,1), (0,2), (1,2)]
noncomputable def crossCoordinate (z : V → Fin 3) (i : Fin 3) : Pairing V → ℝ :=
  tableCoordinate z (crossPair i)

lemma tableCoordinate_offdiag_low (z : V → Fin 3) (a b : Fin 3) (hab : a ≠ b) :
    tableCoordinate z (a,b) ∈ lowDegree (crossCoordinate z) 1 := by
  have h01 : tableCoordinate z (0,1) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 0
  have h02 : tableCoordinate z (0,2) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 1
  have h12 : tableCoordinate z (1,2) ∈ lowDegree (crossCoordinate z) 1 :=
    coord_mem_lowDegree (crossCoordinate z) 2
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | exact h01 | exact h02 | exact h12 |
    rwa [tableCoordinate_symm]

lemma tableCoordinate_three_affine (z : V → Fin 3) (c : Fin 3 × Fin 3) :
    tableCoordinate z c ∈ lowDegree (crossCoordinate z) 1 := by
  classical
  obtain ⟨a,b⟩ := c
  by_cases hab : a = b
  · subst b
    rw [tableCoordinate_diagonal]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ (one_mem_lowDegree _ _)
    · apply Submodule.sum_mem
      intro b hb
      simp only [Finset.mem_erase] at hb
      exact tableCoordinate_offdiag_low z a b hb.1.symm
  · exact tableCoordinate_offdiag_low z a b hab

lemma colorAverage_cross_lowDegree (z : V → Fin 3) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    colorAverage z f ∈ lowDegree (crossCoordinate z) d :=
  lowDegree_substitute (crossCoordinate z) (tableCoordinate z)
    (tableCoordinate_three_affine z) d (colorAverage_lowDegree z d f hf)

lemma colorAverage_polynomial (z : V → Fin 3) (d : ℕ)
    (f : Pairing V → ℝ) (hf : f ∈ lowDegree Pairing.edgeCoord d) :
    ∃ P ∈ lowDegree (fun i (v : Fin 3 → ℝ) => v i) d,
      ∀ M, colorAverage z f M = P (fun i => crossCoordinate z i M) :=
  lowDegree_lift _ _ _ (colorAverage_cross_lowDegree z d f hf)

end ThreeCoordinates

section TableRelation
variable {H : Type u_4} [Fintype H]

lemma tableCoordinate_relabel (z : H × Bool → Fin 3) (c : Fin 3 × Fin 3)
    (p : Equiv.Perm (H × Bool)) (M : Pairing (H × Bool)) :
    tableCoordinate z c (Pairing.relabel p M) = tableCoordinate (z ∘ p) c M := by
  classical
  unfold tableCoordinate
  apply Fintype.sum_equiv p.symm
  intro v
  split_ifs <;> simp_all [Function.comp_apply, Pairing.relabel_apply]

lemma three_order_indicator (a b x y : Fin 3) :
    (if x=a ∧ y=b then (1:ℝ) else 0) + (if y=a ∧ x=b then (1:ℝ) else 0) =
      (if a=b then 2 else 1) *
      (if threeEdgeType (x,y) = threeEdgeType (a,b) then (1:ℝ) else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [threeEdgeType, Fin.ext_iff]

lemma standard_tableCoordinate (z : H × Bool → Fin 3) (a b : Fin 3) :
    tableCoordinate z (a,b) standardPairing =
      (if a=b then (2:ℝ) else 1) * (threeTable z (threeEdgeType (a,b)) : ℝ) := by
  classical
  simp only [tableCoordinate, Fintype.sum_prod_type, Fintype.sum_bool,
    standardPairing, Equiv.prodCongr_apply]
  change (∑ i, ((if z (i,true)=a ∧ z (i,false)=b then (1:ℝ) else 0) +
    (if z (i,false)=a ∧ z (i,true)=b then (1:ℝ) else 0))) = _
  calc
    _ = ∑ i, (if a=b then (2:ℝ) else 1) *
        (if threeEdgeType (z (i,false),z (i,true)) = threeEdgeType (a,b) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [add_comm] using three_order_indicator a b (z (i,false)) (z (i,true))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      exact (histogram_cast_sum (threeEdgeType ∘ pairColorEquiv z) _).symm

lemma tableCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (a b : Fin 3) :
    tableCoordinate z (a,b) M =
      (if a=b then (2:ℝ) else 1) * (M.table z (threeEdgeType (a,b)) : ℝ) := by
  classical
  obtain ⟨p, rfl⟩ := Pairing.exists_relabel (standardPairing (H := H)) M
  rw [tableCoordinate_relabel, Pairing.table_relabel, standardPairing_table,
    standard_tableCoordinate]

lemma crossCoordinate_eq_table [DecidableEq H] (z : H × Bool → Fin 3)
    (M : Pairing (H × Bool)) (i : Fin 3) :
    crossCoordinate z i M = (M.table z (threeEdgeType (crossPair i)) : ℝ) := by
  rw [crossCoordinate, tableCoordinate_eq_table]
  have hne : (crossPair i).1 ≠ (crossPair i).2 := by fin_cases i <;> decide
  rw [ite_eq_right hne, one_mul]

end TableRelation
end MatchingSmoothing

end OAI
