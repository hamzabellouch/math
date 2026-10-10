import OAI.Probability.Ising.SpinCorrelation
import OAI.Probability.Ising.Marginals

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- The actual contracted marginal retains arbitrary fields and all effects
of the common pins. It is distinct from the zero-field comparison weight. -/
noncomputable def contractedPinnedWeight {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) : ℝ :=
  if Respects (comparisonSetoid G I J F ∅) σ then weight G h (pinExtension F τ σ) else 0

lemma respects_terminals_iff {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (σ : KeptVertex F → Bool) :
    Respects (comparisonSetoid G I J F ∅) σ ↔
      (∀ x y, x.val ∈ I → y.val ∈ I → σ x = σ y) ∧
        (∀ x y, x.val ∈ J → y.val ∈ J → σ x = σ y) := by
  constructor
  · intro H
    exact ⟨fun x y hx hy => H x y (Relation.EqvGen.rel _ _ (Or.inl ⟨hx, hy⟩)),
      fun x y hx hy => H x y (Relation.EqvGen.rel _ _ (Or.inr (Or.inl ⟨hx, hy⟩)))⟩
  · rintro ⟨hI, hJ⟩ x y hxy
    induction hxy with
    | rel x y h =>
      rcases h with h | h | ⟨e, he, _⟩
      · exact hI x y h.1 h.2
      · exact hJ x y h.1 h.2
      · exact (Finset.notMem_empty e he).elim
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

lemma contracted_prescription_iff {n m : ℕ} (G : FiniteGraph n m)
    (I J F : Finset (Fin n)) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (τ : Spins n) (σ : KeptVertex F → Bool) (s t : Bool) :
    (σ i = s ∧ σ j = t ∧ Respects (comparisonSetoid G I J F ∅) σ) ↔
      AgreesOn I (pinExtension F τ σ) (fun _ => s) ∧
        AgreesOn J (pinExtension F τ σ) (fun _ => t) := by
  constructor
  · rintro ⟨his, hjt, hresp⟩
    obtain ⟨hI, hJ⟩ := (respects_terminals_iff G I J F σ).mp hresp
    constructor
    · intro v hv
      have hvF : v ∉ F := fun hvF => Finset.disjoint_left.mp hIF hv hvF
      exact (pinExtension_apply F τ σ ⟨v, hvF⟩).trans ((hI _ i hv hi).trans his)
    · intro v hv
      have hvF : v ∉ F := fun hvF => Finset.disjoint_left.mp hJF hv hvF
      exact (pinExtension_apply F τ σ ⟨v, hvF⟩).trans ((hJ _ j hv hj).trans hjt)
  · rintro ⟨hI, hJ⟩
    have hI' : ∀ v : KeptVertex F, v.val ∈ I → σ v = s := by
      intro v hv
      simpa only [pinExtension_apply] using hI v.val hv
    have hJ' : ∀ v : KeptVertex F, v.val ∈ J → σ v = t := by
      intro v hv
      simpa only [pinExtension_apply] using hJ v.val hv
    refine ⟨hI' i hi, hJ' j hj, (respects_terminals_iff G I J F σ).mpr ?_⟩
    exact ⟨fun x y hx hy => (hI' x hx).trans (hI' y hy).symm,
      fun x y hx hy => (hJ' x hx).trans (hJ' y hy).symm⟩

/-- Identifying each terminal set separately is *exactly* restriction to its
constant configurations; no new model comparison enters this identity. -/
lemma pairTable_contractedPinned {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (τ : Spins n) (s t : Bool) :
    pairTable (contractedPinnedWeight G h I J F τ) i j s t =
      jointWeight G h I J F τ (fun _ => s) (fun _ => t) := by
  classical
  have hdel := constrainedSum_delete_variables G h F τ
    (fun ρ => AgreesOn I ρ (fun _ => s) ∧ AgreesOn J ρ (fun _ => t))
  have hswap : jointWeight G h I J F τ (fun _ => s) (fun _ => t) =
      constrainedSum G h (fun ρ => AgreesOn F ρ τ ∧
        (AgreesOn I ρ (fun _ => s) ∧ AgreesOn J ρ (fun _ => t))) := by
    unfold jointWeight constrainedSum
    apply Finset.sum_congr rfl
    intro ρ _
    congr 1
    exact propext and_rotate.symm
  rw [hswap, hdel]
  unfold pairTable
  apply Finset.sum_congr rfl
  intro σ _
  unfold contractedPinnedWeight
  have H := contracted_prescription_iff G I J F hIF hJF i j hi hj τ σ s t
  by_cases hc : σ i = s ∧ σ j = t
  · rw [ite_eq_left hc]
    by_cases hr : Respects (comparisonSetoid G I J F ∅) σ
    · rw [ite_eq_left hr, ite_eq_left (H.mp ⟨hc.1, hc.2, hr⟩)]
    · rw [ite_eq_right hr, ite_eq_right (fun hp => hr (H.mpr hp).2.2)]
  · rw [ite_eq_right hc, ite_eq_right (fun hp => hc ⟨(H.mpr hp).1, (H.mpr hp).2.1⟩)]

lemma extremeLogOdds_eq_effective {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J) (τ : Spins n) :
    extremeLogOdds G h I J F τ =
      4 * tableCoupling (pairTable (contractedPinnedWeight G h I J F τ) i j) := by
  simp only [tableCoupling, pairTable_contractedPinned G h I J F hIF hJF i j hi hj]
  unfold extremeLogOdds
  change _ = 4 * ((Real.log (jointWeight G h I J F τ ⊤ ⊤) +
    Real.log (jointWeight G h I J F τ ⊥ ⊥) - Real.log (jointWeight G h I J F τ ⊤ ⊥) -
    Real.log (jointWeight G h I J F τ ⊥ ⊤)) / 4)
  ring

lemma sum_pin_incidence {n m : ℕ} (l r : Fin m → Fin n) (F : Finset (Fin n)) (f : Fin m → ℝ) (σ : Fin n → ℝ) :
    (∑ v : Fin n, if v ∉ F then (∑ e, if l e = v ∧ r e ∈ F then f e else 0) * σ v else 0) =
      ∑ e, if l e ∉ F ∧ r e ∈ F then f e * σ (l e) else 0 := by
  classical
  calc
    _ = ∑ v : Fin n, ∑ e, if v ∉ F ∧ l e = v ∧ r e ∈ F then f e * σ v else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ F
      · simp [hv]
      · simp only [hv, not_false_eq_true, ite_true, true_and, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        split_ifs <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      have H : ∀ v : Fin n, (v ∉ F ∧ l e = v ∧ r e ∈ F) ↔
          (l e = v ∧ l e ∉ F ∧ r e ∈ F) := by
        intro v
        constructor
        · rintro ⟨hv, he, hr⟩
          exact ⟨he, he.symm ▸ hv, hr⟩
        · rintro ⟨he, hl, hr⟩
          exact ⟨he ▸ hl, he, hr⟩
      simp_rw [H]
      by_cases he : l e ∉ F ∧ r e ∈ F
      · simp [he]
      · simp [he]

/-- The finite-field contribution induced by the actual prescribed spins.
Neither these induced fields nor the original fields survive in `qZero`. -/
noncomputable def pinField {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (v : KeptVertex F) : ℝ :=
  h v + (∑ e, if G.left e = v.val ∧ G.right e ∈ F then
    G.coupling e * spin (τ (G.right e)) else 0) +
    ∑ e, if G.right e = v.val ∧ G.left e ∈ F then
      G.coupling e * spin (τ (G.left e)) else 0

/-- Field and bond terms depending only on fixed sites. They cancel from
all normalized laws, but recording them makes the elimination exact. -/
noncomputable def pinConstant {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) : ℝ :=
  (∑ e, if G.left e ∈ F ∧ G.right e ∈ F then
    G.coupling e * spin (τ (G.left e)) * spin (τ (G.right e)) else 0) +
    ∑ v ∈ F, h v * spin (τ v)

lemma energy_pin_expansion {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ ρ : Spins n) (hρ : AgreesOn F ρ τ) :
    energy G h ρ = pinConstant G h F τ +
      (∑ e, if G.left e ∉ F ∧ G.right e ∉ F then
        G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)) else 0) +
      ∑ v : Fin n, if v ∉ F then
        (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
          G.coupling e * spin (τ (G.right e)) else 0) +
          ∑ e, if G.right e = v ∧ G.left e ∈ F then
            G.coupling e * spin (τ (G.left e)) else 0) * spin (ρ v) else 0 := by
  classical
  have hsplit : (∑ v : Fin n, if v ∉ F then
        (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
          G.coupling e * spin (τ (G.right e)) else 0) +
          ∑ e, if G.right e = v ∧ G.left e ∈ F then
            G.coupling e * spin (τ (G.left e)) else 0) * spin (ρ v) else 0) =
      (∑ v : Fin n, if v ∉ F then h v * spin (ρ v) else 0) +
      (∑ e, if G.left e ∉ F ∧ G.right e ∈ F then
        (G.coupling e * spin (τ (G.right e))) * spin (ρ (G.left e)) else 0) +
      (∑ e, if G.right e ∉ F ∧ G.left e ∈ F then
        (G.coupling e * spin (τ (G.left e))) * spin (ρ (G.right e)) else 0) := by
    rw [← sum_pin_incidence G.left G.right F
      (fun e => G.coupling e * spin (τ (G.right e))) (fun v => spin (ρ v)),
      ← sum_pin_incidence G.right G.left F
        (fun e => G.coupling e * spin (τ (G.left e))) (fun v => spin (ρ v))]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ F <;> simp [hv, add_mul]
  rw [hsplit]
  unfold energy pinConstant
  have he : (∑ e, G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e))) =
      (∑ e, if G.left e ∈ F ∧ G.right e ∈ F then
        G.coupling e * spin (τ (G.left e)) * spin (τ (G.right e)) else 0) +
      (∑ e, if G.left e ∉ F ∧ G.right e ∉ F then
        G.coupling e * spin (ρ (G.left e)) * spin (ρ (G.right e)) else 0) +
      (∑ e, if G.left e ∉ F ∧ G.right e ∈ F then
        (G.coupling e * spin (τ (G.right e))) * spin (ρ (G.left e)) else 0) +
      (∑ e, if G.right e ∉ F ∧ G.left e ∈ F then
        (G.coupling e * spin (τ (G.left e))) * spin (ρ (G.right e)) else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hl : G.left e ∈ F <;> by_cases hr : G.right e ∈ F
    · simp [hl, hr, hρ _ hl, hρ _ hr]
    · simp [hl, hr, hρ _ hl]
    · simp [hl, hr, hρ _ hr, mul_comm, mul_left_comm]
    · simp [hl, hr]
  have hv : (∑ v, h v * spin (ρ v)) =
      (∑ v ∈ F, h v * spin (τ v)) +
      (∑ v : Fin n, if v ∉ F then h v * spin (ρ v) else 0) := by
    rw [← Fintype.sum_extend_by_zero F (fun v => h v * spin (τ v)),
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ F <;> simp [hv, hρ v]
  rw [he, hv]
  ring

lemma sum_kept {n : ℕ} (F : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ v : KeptVertex F, f v.val) = ∑ v : Fin n, if v ∉ F then f v else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (fun v => by simp only [Finset.mem_filter,
    Finset.mem_univ, true_and]) f).symm

/-- Exact deletion of fixed sites: their incident bonds become finite real
fields, while only bonds with two free endpoints remain as interactions. -/
lemma energy_pinExtension {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (σ : KeptVertex F → Bool) :
    energy G h (pinExtension F τ σ) = pinConstant G h F τ +
      deletedEnergy G F σ + ∑ v : KeptVertex F, pinField G h F τ v * spin (σ v) := by
  classical
  rw [energy_pin_expansion G h F τ _ (pinExtension_agrees F τ σ)]
  congr 1
  · congr 1
    unfold deletedEnergy keptEdges
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs with he
    · simp only [pinExtension, extendKept, dite_eq_right he.1, dite_eq_right he.2, dite_eq_left he.1, dite_eq_left he.2]
    · rfl
  · have hs : (∑ v : KeptVertex F, pinField G h F τ v * spin (σ v)) =
        ∑ v : Fin n, if v ∉ F then
          (h v + (∑ e, if G.left e = v ∧ G.right e ∈ F then
            G.coupling e * spin (τ (G.right e)) else 0) +
            ∑ e, if G.right e = v ∧ G.left e ∈ F then
              G.coupling e * spin (τ (G.left e)) else 0) *
              spin (pinExtension F τ σ v) else 0 := by
      rw [← sum_kept]
      simp only [pinField, pinExtension_apply]
    exact hs.symm

lemma weight_pinExtension {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (F : Finset (Fin n)) (τ : Spins n) (σ : KeptVertex F → Bool) :
    weight G h (pinExtension F τ σ) = Real.exp (pinConstant G h F τ) *
      Real.exp (deletedEnergy G F σ + ∑ v : KeptVertex F, pinField G h F τ v * spin (σ v)) := by
  unfold weight
  rw [energy_pinExtension]
  rw [← Real.exp_add]
  congr 1
  ring

end BufferedIsing

end OAI
