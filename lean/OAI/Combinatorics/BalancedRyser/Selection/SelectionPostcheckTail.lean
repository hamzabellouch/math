import OAI.Combinatorics.BalancedRyser.Selection.SelectionFlagTail

namespace OAI

open scoped BigOperators Classical

namespace Balanced.Selection.Process

noncomputable section

private theorem finite_union_weight_le {Ω J : Type*} [Fintype Ω] [Fintype J]
    (weight : Ω → ℝ) (hw : ∀ ω, 0 ≤ weight ω) (E : J → Ω → Prop) :
    (∑ ω, if ∃ j, E j ω then weight ω else 0) ≤
      ∑ j, ∑ ω, if E j ω then weight ω else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ j, E j ω
  · obtain ⟨j, hj⟩ := h
    rw [ite_eq_left ⟨j, hj⟩]
    calc
      weight ω = (if E j ω then weight ω else 0) := by rw [ite_eq_left hj]
      _ ≤ _ := Finset.single_le_sum (s := Finset.univ)
        (f := fun j => if E j ω then weight ω else 0)
        (fun j _ => by split <;> first | exact hw ω | exact le_rfl) (Finset.mem_univ j)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by split <;> first | exact hw ω | exact le_rfl)

variable {I V : Type*} [Fintype I] [Fintype V]

omit [Fintype I] in

theorem flag_mean_le_card_mul_alpha (p : Parameters) (q t : ℕ)
    (G : Input I V) (S : State I V) (hpre : Precheck p q t G S) (A : Finset V) :
    (∑ v ∈ A, thinningRate p q G S v) ≤ (A.card : ℝ) * p.alpha q := by
  calc
    _ ≤ ∑ _v ∈ A, p.alpha q := Finset.sum_le_sum
      (fun v _ => (thinningRate_bounds_of_precheck p q t G S hpre v).2)
    _ = _ := by simp

def postcheckMean (p : Parameters) : ℝ := p.Pstar * max 1 p.C

def postcheckTail (p : Parameters) (q : ℕ) : ℝ :=
  (Real.exp 1 * postcheckMean p / (BernoulliTail.thinningCutoff (1 / 8) q : ℝ)) ^
    BernoulliTail.thinningCutoff (1 / 8) q

theorem domain_flag_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (i : I) :
    (∑ v ∈ domain G S i, thinningRate p q G S v) ≤ postcheckMean p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 ≤ p.Pstar := by
    have h := hpre.2.1
    simpa using (le_div_iff₀ hqR).mp h
  have hdom : ((domain G S i).card : ℝ) ≤ q := by
    apply le_trans _ (show ((slotVertices G i).card : ℝ) ≤ q by exact_mod_cast (hG.2.2.1 i).2)
    exact_mod_cast Finset.card_le_card (show domain G S i ⊆ slotVertices G i from by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩)
  calc
    _ ≤ ((domain G S i).card : ℝ) * p.alpha q :=
      flag_mean_le_card_mul_alpha p q t G S hpre _
    _ ≤ (q : ℝ) * p.alpha q := mul_le_mul_of_nonneg_right hdom hpre.2.1
    _ = p.Pstar := by unfold Parameters.alpha; field_simp
    _ ≤ postcheckMean p := by
      unfold postcheckMean
      simpa using mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) p.C) hP

theorem neighbor_flag_mean_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) (v : V) :
    (∑ u ∈ neighbors G v, thinningRate p q G S u) ≤ postcheckMean p := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hP : 0 ≤ p.Pstar := by
    have h := hpre.2.1
    simpa using (le_div_iff₀ hqR).mp h
  calc
    _ ≤ ((neighbors G v).card : ℝ) * p.alpha q :=
      flag_mean_le_card_mul_alpha p q t G S hpre _
    _ ≤ (p.C * q) * p.alpha q :=
      mul_le_mul_of_nonneg_right (hG.2.2.2.1 v) hpre.2.1
    _ = p.Pstar * p.C := by unfold Parameters.alpha; field_simp
    _ ≤ postcheckMean p :=
      mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) p.C) hP

theorem postcheck_failure_mass_le (p : Parameters) (q t : ℕ) (hq : 0 < q)
    (G : Input I V) (hG : GraphBounds G q p.c p.C)
    (S : State I V) (hpre : Precheck p q t G S) :
    (∑ r : Noise I V, if ¬ Postcheck q G S r.2.1 r.2.2 then
      noiseWeight p q G S r else 0) ≤
      ((Fintype.card I : ℝ) + Fintype.card V) * postcheckTail p q := by
  let A : I ⊕ V → Finset V := Sum.elim (domain G S) (neighbors G)
  let E : (I ⊕ V) → Noise I V → Prop := fun j r =>
    (q : ℝ) ^ (1 / 8 : ℝ) < ((thinned G S r.2.1 r.2.2 ∩ A j).card : ℝ)
  have hsub (r : Noise I V) (hr : ¬ Postcheck q G S r.2.1 r.2.2) : ∃ j, E j r := by
    unfold Postcheck at hr
    rcases not_and_or.mp hr with h | h
    · push Not at h
      obtain ⟨i, _, hi⟩ := h
      exact ⟨Sum.inl i, hi⟩
    · push Not at h
      obtain ⟨v, _, hv⟩ := h
      exact ⟨Sum.inr v, hv⟩
  calc
    _ ≤ ∑ r : Noise I V, if ∃ j, E j r then noiseWeight p q G S r else 0 := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : ¬ Postcheck q G S r.2.1 r.2.2
      · simp only [hr, ite_true, hsub r hr]
        exact le_rfl
      · rw [ite_eq_right hr]
        split
        · exact noiseWeight_nonnegative_of_precheck p q t G S hpre r
        · exact le_rfl
    _ ≤ ∑ j : I ⊕ V, ∑ r : Noise I V, if E j r then noiseWeight p q G S r else 0 :=
      finite_union_weight_le _ (noiseWeight_nonnegative_of_precheck p q t G S hpre) E
    _ ≤ ∑ _j : I ⊕ V, postcheckTail p q := by
      apply Finset.sum_le_sum
      intro j _
      apply noise_thinned_tail_le p q t G S hpre (A j) (postcheckMean p)
      cases j with
      | inl i => exact domain_flag_mean_le p q t hq G hG S hpre i
      | inr v => exact neighbor_flag_mean_le p q t hq G hG S hpre v
    _ = _ := by simp [Nat.cast_add]

end
end Balanced.Selection.Process

end OAI
