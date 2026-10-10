import OAI.Combinatorics.MatchingPSD.SpectralMultiplicity

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing

namespace Pairing
variable {V : Type u_1} [Fintype V] [DecidableEq V]

noncomputable instance : Fintype (Pairing V) := Fintype.ofFinite _

instance relabelMulAction : MulAction (Equiv.Perm V) (Pairing V) where
  smul := relabel
  one_smul := relabel_one
  mul_smul := relabel_mul

omit [Fintype V] [DecidableEq V] in
lemma smul_eq_relabel (p : Equiv.Perm V) (M : Pairing V) : p • M = relabel p M := rfl

noncomputable def table (M : Pairing V) (f : V → Fin 3) (t : Fin 6) : ℕ :=
  histogram (fun v => threeEdgeType (f v, f (M.1 v))) t / 2

omit [DecidableEq V] in
lemma table_relabel (p : Equiv.Perm V) (M : Pairing V) (f : V → Fin 3) :
    (relabel p M).table f = M.table (f ∘ p) := by
  funext t
  unfold table
  congr 1
  have he : (fun v => threeEdgeType (f v, f ((relabel p M).1 v))) ∘ p =
      (fun v => threeEdgeType ((f ∘ p) v, (f ∘ p) (M.1 v))) := by
    funext v
    simp only [Function.comp_apply, relabel_apply]
    rw [Equiv.Perm.inv_def, p.symm_apply_apply]
  rw [← he, histogram_comp_perm]

end Pairing

section StandardTable
variable {H : Type u_2} [Fintype H] [DecidableEq H]

def standardPairing : Pairing (H × Bool) :=
  ⟨Equiv.prodCongr (Equiv.refl H) Equiv.boolNot,
    by rintro ⟨i,b⟩; cases b <;> rfl,
    by rintro ⟨i,b⟩ h; have he := congrArg Prod.snd h; cases b <;> contradiction⟩

omit [DecidableEq H] in
lemma standardPairing_table (f : H × Bool → Fin 3) :
    (standardPairing (H := H)).table f = threeTable f := by
  funext t
  have he : histogram (fun v => threeEdgeType (f v, f ((standardPairing (H := H)).1 v))) t =
      2 * threeTable f t := by
    have hr : (histogram (fun v => threeEdgeType (f v,
        f ((standardPairing (H := H)).1 v))) t : ℝ) = 2 * threeTable f t := by
      simp only [histogram_cast_sum, Fintype.sum_prod_type, Fintype.sum_bool,
        standardPairing, Equiv.prodCongr_apply]
      change (∑ i, ((if threeEdgeType (f (i,true),f (i,false)) = t then (1 : ℝ) else 0) +
        (if threeEdgeType (f (i,false),f (i,true)) = t then 1 else 0))) = _
      simp_rw [threeEdgeType_symm (f (_,true)) (f (_,false))]
      rw [Finset.sum_add_distrib]
      change (∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then (1 : ℝ) else 0) +
        (∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then (1 : ℝ) else 0) = _
      rw [show (threeTable f t : ℝ) =
        ∑ i, if threeEdgeType (f (i,false),f (i,true)) = t then 1 else 0 from
          histogram_cast_sum (threeEdgeType ∘ pairColorEquiv f) t]
      ring
    exact_mod_cast hr
  change _ / 2 = _
  rw [he, Nat.mul_div_right _ (by decide : 0 < 2)]

end StandardTable

section MatchingIncidence
variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def tableRelation (f₀ : H × Bool → Fin 3) :
    Pairing (H × Bool) → Colorings (H × Bool) (Fin 3) (histogram f₀) → Prop :=
  fun M z => M.table z.1 = threeTable f₀

noncomputable def coloringPerm (s : Fin 3 → ℕ) (p : Equiv.Perm (H × Bool)) :
    Equiv.Perm (Colorings (H × Bool) (Fin 3) s) where
  toFun z := ⟨z.1 ∘ p, (histogram_comp_perm z.1 p).trans z.2⟩
  invFun z := ⟨z.1 ∘ p.symm, (histogram_comp_perm z.1 p.symm).trans z.2⟩
  left_inv z := by apply Subtype.ext; funext v; simp
  right_inv z := by apply Subtype.ext; funext v; simp

omit [DecidableEq H] in
lemma commonIncidence_table_relabel (f₀ : H × Bool → Fin 3)
    (p : Equiv.Perm (H × Bool)) (M N : Pairing (H × Bool)) :
    commonIncidence (tableRelation f₀) (Pairing.relabel p M) (Pairing.relabel p N) =
      commonIncidence (tableRelation f₀) M N := by
  classical
  unfold commonIncidence
  congr 1
  apply Fintype.card_congr
  apply (coloringPerm (histogram f₀) p).subtypeEquiv
  intro z
  change ((Pairing.relabel p M).table z.1 = _ ∧ (Pairing.relabel p N).table z.1 = _) ↔
    (M.table (z.1 ∘ p) = _ ∧ N.table (z.1 ∘ p) = _)
  simp only [Pairing.table_relabel]

lemma commonIncidence_standard (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (p : Equiv.Perm (H × Bool)) :
    commonIncidence (tableRelation f₀) standardPairing (Pairing.relabel p standardPairing) =
      (Fintype.card {f : H × Bool → Fin 3 //
        threeTable f = threeTable f₀ ∧ threeTable (f ∘ p) = threeTable f₀} : ℝ) := by
  classical
  unfold commonIncidence
  congr 1
  apply Fintype.card_congr
  refine { toFun := fun z => ⟨z.1.1, ?_⟩
           invFun := fun f => ⟨⟨f.1, threeTable_histogram_eq hH f.2.1⟩, ?_⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl }
  · simpa only [tableRelation, Pairing.table_relabel, standardPairing_table] using z.2
  · simpa only [tableRelation, Pairing.table_relabel, standardPairing_table] using f.2

lemma matching_table_trace_square (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
    Matrix.trace (incidenceOperator (tableRelation f₀) D *
      incidenceOperator (tableRelation f₀) D) ≤ (Fintype.card H + 1 : ℝ) ^ 33 := by
  classical
  dsimp only
  let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
  change Matrix.trace (incidenceOperator (tableRelation f₀) D *
    incidenceOperator (tableRelation f₀) D) ≤ _
  have he := trace_normalized_invariant_kernel_sq (G := Equiv.Perm (H × Bool))
    (standardPairing (H := H)) (fun M => Pairing.exists_relabel _ M)
    (incidenceKernel (tableRelation f₀) D)
    (incidenceKernel_symm (tableRelation f₀) D)
    (fun p M N => by
      change (Fintype.card _ : ℝ) / D ^ 2 * commonIncidence _ (Pairing.relabel p M)
        (Pairing.relabel p N) = (Fintype.card _ : ℝ) / D ^ 2 * commonIncidence _ M N
      rw [commonIncidence_table_relabel])
  change Matrix.trace (incidenceOperator (tableRelation f₀) D *
    incidenceOperator (tableRelation f₀) D) = _ at he
  rw [he]
  have hp : (0 : ℝ) < Fintype.card (Equiv.Perm (H × Bool)) := Nat.cast_pos.mpr Fintype.card_pos
  apply (div_le_iff₀ hp).mpr
  simp only [incidenceKernel, Pairing.smul_eq_relabel,
    commonIncidence_standard f₀ hH]
  exact (three_table_kernel_moment f₀ hH hf₀).trans_eq (mul_comm _ _)

end MatchingIncidence
end MatchingSmoothing

end OAI
