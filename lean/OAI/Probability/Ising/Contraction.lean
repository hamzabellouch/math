import OAI.Probability.Ising.Covariance

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- A finite pair interaction allowing self-loops and arbitrary vertex and edge labels. -/
structure PairInteraction (V E : Type*) where
  left : E → V
  right : E → V
  coupling : E → ℝ
  coupling_nonneg : ∀ e, 0 ≤ coupling e

noncomputable def interactionEnergy {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) : ℝ :=
  (∑ e, P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e))) +
    ∑ v, h v * spin (σ v)

noncomputable def interactionWeight {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) : ℝ :=
  Real.exp (interactionEnergy P h σ)

abbrev NonloopEdge {V E : Type*} (P : PairInteraction V E) :=
  {e : E // P.left e ≠ P.right e}

noncomputable def interactionLoopConstant {V E : Type*} [Fintype E]
    (P : PairInteraction V E) : ℝ := ∑ e, if P.left e = P.right e then P.coupling e else 0

/-- Relabeling a finite loop-deleted interaction by `Fin` does not introduce
any assumption on the fields or on connectivity. Parallel edges are kept. -/
noncomputable def interactionGraph {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) :
    FiniteGraph (Fintype.card V) (Fintype.card (NonloopEdge P)) where
  left e := Fintype.equivFin V (P.left ((Fintype.equivFin (NonloopEdge P)).symm e).val)
  right e := Fintype.equivFin V (P.right ((Fintype.equivFin (NonloopEdge P)).symm e).val)
  coupling e := P.coupling ((Fintype.equivFin (NonloopEdge P)).symm e).val
  coupling_nonneg e := P.coupling_nonneg _
  no_loops e := by
    intro H
    exact ((Fintype.equivFin (NonloopEdge P)).symm e).property
      ((Fintype.equivFin V).injective H)

lemma sum_nonloop {V E : Type*} [Fintype E] (P : PairInteraction V E) (f : E → ℝ) :
    (∑ e : NonloopEdge P, f e.val) = ∑ e : E, if P.left e ≠ P.right e then f e else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun e => by simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]) f).symm

lemma interactionEnergy_relabel {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) :
    energy (interactionGraph P) (fun v => h ((Fintype.equivFin V).symm v))
      (fun v => σ ((Fintype.equivFin V).symm v)) =
      interactionEnergy P h σ - interactionLoopConstant P := by
  classical
  unfold energy interactionGraph interactionEnergy interactionLoopConstant
  simp only [Equiv.symm_apply_apply]
  rw [(Fintype.equivFin (NonloopEdge P)).symm.sum_comp (fun e : NonloopEdge P =>
      P.coupling e.val * spin (σ (P.left e.val)) * spin (σ (P.right e.val))),
    (Fintype.equivFin V).symm.sum_comp (fun v => h v * spin (σ v))]
  rw [sum_nonloop P (fun e => P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e)))]
  have he : (∑ e : E, P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e))) =
      (∑ e : E, if P.left e ≠ P.right e then
        P.coupling e * spin (σ (P.left e)) * spin (σ (P.right e)) else 0) +
        ∑ e : E, if P.left e = P.right e then P.coupling e else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : P.left e = P.right e
    · simp only [he, ne_eq, not_true_eq_false, ite_false, ite_true, zero_add]
      rw [mul_assoc, spin_sq, mul_one]
    · simp [he]
  rw [he]
  ring

lemma interactionWeight_relabel {V E : Type*} [Fintype V] [Fintype E]
    (P : PairInteraction V E) (h : V → ℝ) (σ : V → Bool) :
    weight (interactionGraph P) (fun v => h ((Fintype.equivFin V).symm v))
      (fun v => σ ((Fintype.equivFin V).symm v)) =
      Real.exp (-interactionLoopConstant P) * interactionWeight P h σ := by
  unfold weight interactionWeight
  rw [interactionEnergy_relabel, ← Real.exp_add]
  congr 1
  ring

/-- Marginal tables commute with a bijective change of vertex labels. -/
lemma pairTable_relabel {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ≃ W) (f : (V → Bool) → ℝ)
    (u v : V) (s t : Bool) :
    pairTable (fun σ : W → Bool => f (fun x => σ (e x))) (e u) (e v) s t =
      pairTable f u v s t := by
  classical
  unfold pairTable
  let E : (V → Bool) ≃ (W → Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  rw [← E.sum_comp]
  simp only [E, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_apply,
    Equiv.symm_apply_apply]

lemma pairTable_scale {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ℝ) (c : ℝ) (u v : V) (s t : Bool) :
    pairTable (fun σ => c * f σ) u v s t = c * pairTable f u v s t := by
  classical
  unfold pairTable
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

lemma tableCoupling_scale (w : Bool → Bool → ℝ) (hw : ∀ s t, 0 < w s t)
    (c : ℝ) (hc : 0 < c) : tableCoupling (fun s t => c * w s t) = tableCoupling w := by
  simp only [tableCoupling, Real.log_mul hc.ne' (hw _ _).ne']
  ring

lemma pairTable_pos_of_weight_pos {V : Type*} [Fintype V] [DecidableEq V]
    (W : (V → Bool) → ℝ) (hW : ∀ σ, 0 < W σ) (u v : V) (huv : u ≠ v)
    (s t : Bool) : 0 < pairTable W u v s t := by
  classical
  unfold pairTable
  apply Finset.sum_pos'
  · intro σ _
    split_ifs
    · exact (hW σ).le
    · exact le_rfl
  · refine ⟨fun x => if x = u then s else t, Finset.mem_univ _, ?_⟩
    simp only [ite_eq_right (Ne.symm huv), and_self, ite_true]
    exact hW _

lemma pairTable_quotient {V : Type*} [Fintype V] [DecidableEq V]
    (S : Setoid V) (W : (V → Bool) → ℝ) (u v : V) (s t : Bool) :
    pairTable (fun σ => if Respects S σ then W σ else 0) u v s t =
      pairTable (fun c : Quotient S → Bool => W (fun x => c (Quotient.mk S x)))
        (Quotient.mk S u) (Quotient.mk S v) s t := by
  classical
  unfold pairTable
  calc
    _ = ∑ σ, if Respects S σ then
        (if σ u = s ∧ σ v = t then W σ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hR : Respects S σ <;> by_cases hT : σ u = s ∧ σ v = t <;> simp [hR, hT]
    _ = ∑ σ : Colorings S, if σ.val u = s ∧ σ.val v = t then W σ.val else 0 :=
      sum_if_respects S _
    _ = _ := by
      rw [Fintype.sum_equiv (componentColoringEquiv S)]
      · intro σ
        rfl

abbrev ContractedVertex {n m : ℕ} (G : FiniteGraph n m) (I J F : Finset (Fin n)) :=
  Quotient (comparisonSetoid G I J F ∅)

abbrev KeptEdge {n m : ℕ} (G : FiniteGraph n m) (F : Finset (Fin n)) :=
  {e : Fin m // e ∈ keptEdges G F}

noncomputable def edgeLeftKept {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (e : KeptEdge G F) : KeptVertex F :=
  ⟨G.left e.val, (Finset.mem_filter.mp e.property).2.1⟩

noncomputable def edgeRightKept {n m : ℕ} (G : FiniteGraph n m)
    (F : Finset (Fin n)) (e : KeptEdge G F) : KeptVertex F :=
  ⟨G.right e.val, (Finset.mem_filter.mp e.property).2.2⟩

noncomputable def contractedInteraction {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) : PairInteraction (ContractedVertex G I J F) (KeptEdge G F) where
  left e := Quotient.mk _ (edgeLeftKept G F e)
  right e := Quotient.mk _ (edgeRightKept G F e)
  coupling e := G.coupling e.val
  coupling_nonneg e := G.coupling_nonneg e.val

/-- The contracted finite field is the SUM of the fields in the identified
class. Common fixed spins have already been removed and contribute through
`pinField`; opposite common signs are never wired together. -/
noncomputable def quotientField {V : Type*} [Fintype V] (S : Setoid V)
    (h : V → ℝ) (q : Quotient S) : ℝ := ∑ v, if Quotient.mk S v = q then h v else 0

lemma quotientField_sum {V : Type*} [Fintype V] (S : Setoid V) (h : V → ℝ)
    (c : Quotient S → Bool) :
    (∑ q, quotientField S h q * spin (c q)) =
      ∑ v, h v * spin (c (Quotient.mk S v)) := by
  classical
  simp only [quotientField, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simp

lemma quotientField_zero {V : Type*} [Fintype V] (S : Setoid V) :
    quotientField S (fun _ => 0) = fun _ => 0 := by
  funext q
  simp [quotientField]

lemma contractedInteraction_energy {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (h : KeptVertex F → ℝ)
    (c : ContractedVertex G I J F → Bool) :
    interactionEnergy (contractedInteraction G I J F)
      (quotientField (comparisonSetoid G I J F ∅) h) c =
      deletedEnergy G F (fun v => c (Quotient.mk _ v)) +
        ∑ v, h v * spin (c (Quotient.mk _ v)) := by
  classical
  unfold interactionEnergy
  rw [quotientField_sum]
  congr 1
  unfold contractedInteraction deletedEnergy
  rw [Finset.sum_subtype (keptEdges G F) (fun e => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro e _
  simp only [extendKept, edgeLeftKept, edgeRightKept,
    dite_eq_left (Finset.mem_filter.mp e.property).2.1,
    dite_eq_left (Finset.mem_filter.mp e.property).2.2]

lemma contractedPinned_quotient_weight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n)
    (c : ContractedVertex G I J F → Bool) :
    weight G h (pinExtension F τ (fun v => c (Quotient.mk _ v))) =
      Real.exp (pinConstant G h F τ) *
        interactionWeight (contractedInteraction G I J F)
          (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)) c := by
  rw [weight_pinExtension]
  unfold interactionWeight
  rw [contractedInteraction_energy]

lemma contractedPinned_pairTable_quotient {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n)
    (i j : KeptVertex F) (s t : Bool) :
    pairTable (contractedPinnedWeight G h I J F τ) i j s t =
      Real.exp (pinConstant G h F τ) *
        pairTable (interactionWeight (contractedInteraction G I J F)
          (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)))
          (Quotient.mk _ i) (Quotient.mk _ j) s t := by
  unfold contractedPinnedWeight
  rw [pairTable_quotient]
  simp_rw [contractedPinned_quotient_weight]
  rw [pairTable_scale]

lemma contractedZero_pairTable_quotient {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i j : KeptVertex F) (s t : Bool) :
    pairTable (contractedZeroWeight G I J F) i j s t =
      pairTable (interactionWeight (contractedInteraction G I J F) (fun _ => 0))
        (Quotient.mk _ i) (Quotient.mk _ j) s t := by
  unfold contractedZeroWeight
  rw [pairTable_quotient]
  have H := contractedInteraction_energy G I J F (fun _ => 0)
  have He : ∀ c : ContractedVertex G I J F → Bool,
      interactionEnergy (contractedInteraction G I J F) (fun _ => 0) c =
        deletedEnergy G F (fun v => c (Quotient.mk _ v)) := by
    intro c
    simpa only [quotientField_zero, zero_mul, Finset.sum_const_zero, add_zero] using H c
  have hw : (fun c : ContractedVertex G I J F → Bool =>
      Real.exp (deletedEnergy G F (fun v => c (Quotient.mk _ v)))) =
      interactionWeight (contractedInteraction G I J F) (fun _ => 0) := by
    funext c
    rw [interactionWeight, He]
  rw [hw]

lemma interactionGraph_pairTable {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (P : PairInteraction V E) (h : V → ℝ) (u v : V) (s t : Bool) :
    pairTable (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v) s t =
      Real.exp (-interactionLoopConstant P) * pairTable (interactionWeight P h) u v s t := by
  classical
  have H := pairTable_relabel (Fintype.equivFin V).symm
    (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
    (Fintype.equivFin V u) (Fintype.equivFin V v) s t
  simp only [Equiv.symm_apply_apply] at H
  rw [← H]
  simp_rw [interactionWeight_relabel]
  exact pairTable_scale _ _ _ _ _ _

lemma interactionGraph_coupling {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (P : PairInteraction V E) (h : V → ℝ) (u v : V) (huv : u ≠ v) :
    tableCoupling (pairTable
      (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v)) =
      tableCoupling (pairTable (interactionWeight P h) u v) := by
  classical
  have H : pairTable
      (weight (interactionGraph P) (fun x => h ((Fintype.equivFin V).symm x)))
      (Fintype.equivFin V u) (Fintype.equivFin V v) =
      fun s t => Real.exp (-interactionLoopConstant P) *
        pairTable (interactionWeight P h) u v s t := by
    funext s t
    exact interactionGraph_pairTable P h u v s t
  rw [H]
  exact tableCoupling_scale _
    (pairTable_pos_of_weight_pos _ (fun σ => Real.exp_pos _) u v huv) _ (Real.exp_pos _)

lemma contractedTerminal_ne {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    Quotient.mk (comparisonSetoid G I J F ∅) i ≠ Quotient.mk _ j := by
  intro H
  exact Finset.disjoint_left.mp hIJ
    ((comparison_empty_preserves_I G I J F hIJ i j (Quotient.exact H)).mp hi) hj

noncomputable def actualComparisonGraph {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) := interactionGraph (contractedInteraction G I J F)

noncomputable def actualComparisonField {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n) :=
    fun x => quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)
      ((Fintype.equivFin (ContractedVertex G I J F)).symm x)

noncomputable def actualTerminal {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (i : KeptVertex F) :=
    Fintype.equivFin (ContractedVertex G I J F) (Quotient.mk _ i)

lemma actualTerminal_ne {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    actualTerminal G I J F i ≠ actualTerminal G I J F j := by
  intro H
  exact contractedTerminal_ne G I J F hIJ i j hi hj ((Fintype.equivFin _).injective H)

/-- The extreme log odds equals four times the effective coupling after deletion and separate terminal contraction, with fields induced by the common pins. -/
lemma extremeLogOdds_eq_actualCoupling {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ = 4 * tableCoupling (pairTable
      (weight (actualComparisonGraph G I J F) (actualComparisonField G h I J F τ))
      (actualTerminal G I J F i) (actualTerminal G I J F j)) := by
  classical
  rw [extremeLogOdds_eq_effective G h I J F hIF hJF i j hi hj τ]
  congr 1
  have H : pairTable (contractedPinnedWeight G h I J F τ) i j =
      fun s t => Real.exp (pinConstant G h F τ) * pairTable
        (interactionWeight (contractedInteraction G I J F)
          (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)))
        (Quotient.mk _ i) (Quotient.mk _ j) s t := by
    funext s t
    exact contractedPinned_pairTable_quotient G h I J F τ i j s t
  have hp : ∀ s t, 0 < pairTable
      (interactionWeight (contractedInteraction G I J F)
        (quotientField (comparisonSetoid G I J F ∅) (pinField G h F τ)))
      (Quotient.mk _ i) (Quotient.mk _ j) s t :=
    pairTable_pos_of_weight_pos _ (fun σ => Real.exp_pos _)
      _ _ (contractedTerminal_ne G I J F hIJ i j hi hj)
  rw [H, tableCoupling_scale _ hp (Real.exp (pinConstant G h F τ)) (Real.exp_pos _)]
  exact (interactionGraph_coupling _ _ _ _ (contractedTerminal_ne G I J F hIJ i j hi hj)).symm

/-- The inverse hyperbolic tangent of the FK connection probability equals the zero-field coupling on the deleted, separately contracted graph. -/
lemma artanh_qZero_eq_actualCoupling {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIJ : Disjoint I J)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) :
    Real.artanh (qZero G I J F i j) = tableCoupling (pairTable
      (weight (actualComparisonGraph G I J F) (fun _ => 0))
      (actualTerminal G I J F i) (actualTerminal G I J F j)) := by
  classical
  rw [artanh_qZero_eq_effective G I J F hIJ i j hi hj]
  have H : pairTable (contractedZeroWeight G I J F) i j =
      pairTable (interactionWeight (contractedInteraction G I J F) (fun _ => 0))
        (Quotient.mk _ i) (Quotient.mk _ j) := by
    funext s t
    exact contractedZero_pairTable_quotient G I J F i j s t
  rw [H]
  exact (interactionGraph_coupling _ (fun _ => 0) _ _
    (contractedTerminal_ne G I J F hIJ i j hi hj)).symm

end BufferedIsing

end OAI
