import OAI.Combinatorics.MatchingPSD.PolynomialSpaces

namespace OAI

universe u_1 u_2 u_3

namespace MatchingSmoothing
open Matrix
attribute [local instance] Classical.propDecidable
section FiberAverages
variable {X : Type u_1} {Z : Type u_2} [Fintype X] [Fintype Z]

noncomputable def fiberAverage (P : X → Z → Prop) (f : X → ℝ) (z : Z) : ℝ :=
  conditionalAverage P (Fintype.card {x // P x z}) f z

lemma cardinal_fibers_balance (P : X → Z → Prop) (D E : ℕ)
    (hD : ∀ x, Fintype.card {z // P x z} = D)
    (hE : ∀ z, Fintype.card {x // P x z} = E) :
    Fintype.card X * D = Fintype.card Z * E := by
  classical
  calc
    _ = ∑ x : X, Fintype.card {z // P x z} := by simp [hD]
    _ = ∑ z : Z, Fintype.card {x // P x z} := by
      simp only [Fintype.card_subtype, Finset.card_filter]
      exact Finset.sum_comm
    _ = _ := by simp [hE]

end FiberAverages

section TableFibers
variable {H : Type u_3} [Fintype H] [DecidableEq H]

lemma table_row_card (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (M : Pairing (H × Bool)) :
    Fintype.card {z // tableRelation f₀ M z} =
      Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} := by
  classical
  obtain ⟨p, rfl⟩ := Pairing.exists_relabel (standardPairing (H := H)) M
  apply Fintype.card_congr
  refine ((coloringPerm (histogram f₀) p).subtypeEquiv
    (q := tableRelation f₀ standardPairing) (fun z => ?_)).trans ?_
  · change ((Pairing.relabel p standardPairing).table z.1 = _) ↔
      (standardPairing.table (z.1 ∘ p) = _)
    rw [Pairing.table_relabel]
  · refine { toFun := fun z => ⟨z.1.1, ?_⟩
             invFun := fun f => ⟨⟨f.1, threeTable_histogram_eq hH f.2⟩, ?_⟩
             left_inv := fun _ => rfl
             right_inv := fun _ => rfl }
    · simpa only [tableRelation, standardPairing_table] using z.2
    · simpa only [tableRelation, standardPairing_table] using f.2

omit [DecidableEq H] in
lemma table_col_card (f₀ : H × Bool → Fin 3)
    (z w : Colorings (H × Bool) (Fin 3) (histogram f₀)) :
    Fintype.card {M // tableRelation f₀ M z} =
      Fintype.card {M // tableRelation f₀ M w} := by
  classical
  let p := permOfHistogram (z.2.trans w.2.symm)
  have hp : w.1 ∘ p = z.1 := funext (permOfHistogram_spec _)
  apply Fintype.card_congr
  apply (Pairing.relabelEquiv p).subtypeEquiv
  intro M
  change (M.table z.1 = _) ↔ ((Pairing.relabel p M).table w.1 = _)
  rw [Pairing.table_relabel, hp]

lemma table_fiber_size (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (z : Colorings (H × Bool) (Fin 3) (histogram f₀)) :
    (Fintype.card {M // tableRelation f₀ M z} : ℝ) =
      (Fintype.card (Pairing (H × Bool)) : ℝ) *
        Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} /
        Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) := by
  classical
  have : Nonempty (Colorings (H × Bool) (Fin 3) (histogram f₀)) := ⟨⟨f₀, rfl⟩⟩
  have he := cardinal_fibers_balance (tableRelation f₀) _ _
    (table_row_card f₀ hH) (fun w => table_col_card f₀ w z)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  have hr : (Fintype.card (Pairing (H × Bool)) : ℝ) *
      Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} =
      Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) *
        Fintype.card {M // tableRelation f₀ M z} := by exact_mod_cast he
  rw [mul_comm]
  exact hr.symm

end TableFibers

open scoped RealInnerProductSpace
lemma table_smoothing_bound {h : ℕ} (k : ℕ) (hk : 4*k < h)
    (f₀ : Vertices h → Fin 3) (hf₀ : ∀ i, 0 < histogram f₀ i)
    (a : ℝ) (ha : 0 ≤ a) (hHa : (h+1 : ℝ)^33 ≤ (h.choose k : ℝ) * a^2)
    (f : MatchingSpace h) (hf : f ∈ (polynomialSpace h ((4*k)*(4*k)))ᗮ) :
    (∑ z, fiberAverage (tableRelation f₀) (matchingEquiv h f) z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) ≤
    a * ((∑ M, (f M)^2) / Fintype.card (Pairing (Vertices h))) := by
  classical
  have hH : 0 < Fintype.card (Fin h) := by simpa using (show 0 < h by omega)
  have : Nonempty (Pairing (Vertices h)) := ⟨standardPairing⟩
  have : Nonempty (Colorings (Vertices h) (Fin 3) (histogram f₀)) := ⟨⟨f₀, rfl⟩⟩
  let D : ℝ := Fintype.card {f : Vertices h → Fin 3 // threeTable f = threeTable f₀}
  have hD : D ≠ 0 := by
    have : Nonempty {f : Vertices h → Fin 3 // threeTable f = threeTable f₀} := ⟨⟨f₀, rfl⟩⟩
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have he : (∑ z, fiberAverage (tableRelation f₀) (matchingEquiv h f) z ^ 2) /
      Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) =
      (∑ M, f M * (incidenceOperator (tableRelation f₀) D *ᵥ (matchingEquiv h f)) M) /
        Fintype.card (Pairing (Vertices h)) := by
    simp only [fiberAverage, table_fiber_size f₀ hH]
    exact conditionalAverage_energy _ D hD _
  rw [he]
  have hb := symmetric_matching_smoothing k hk (incidenceOperator (tableRelation f₀) D)
    (incidenceOperator_posSemidef _ _).isHermitian
    (fun p M N => by
      simp only [incidenceOperator, incidenceKernel, commonIncidence_table_relabel])
    ((h+1)^33) a ha (by simpa using matching_table_trace_square f₀ hH hf₀) hHa f hf
  rw [EuclideanSpace.real_norm_sq_eq] at hb
  have hinner : ⟪f, (incidenceOperator (tableRelation f₀) D).toEuclideanLin f⟫ =
      ∑ M, f M * (incidenceOperator (tableRelation f₀) D *ᵥ (matchingEquiv h f)) M := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    exact dotProduct_comm _ _
  rw [hinner] at hb
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hb
    (show (0 : ℝ) ≤ Fintype.card (Pairing (Vertices h)) by positivity)

end MatchingSmoothing

end OAI
