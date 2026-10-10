import OAI.Probability.MatroidProphet.Residual.Encoding

namespace OAI

namespace MatroidProphet

open Set Finset Pivots

variable {α : Type*} [Fintype α] [LinearOrder α] {n : ℕ}

lemma nominal_residual_mem_family (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (hκ : 0 < κ) (D C : ℕ → Set α) (h : ℕ)
    (U Z : Finset α) (hDU : D h ⊆ (U : Set α)) (hZU : Z ⊆ U)
    (hZcard : Z.card ≤ U.card / κ) (ε : Fin 2)
    (K : ParityWindow (activation h) ε → Set α)
    (hK : ∀ b, K b ⊆ guardedPath M hE κ D C h b.val.val)
    (β : Z → ParityWindow (activation h) ε)
    (hz : ∀ w, w.val ∈ nominalPath M hE κ D C h (β w).val.val)
    (test : Fin n → α) (hnonloop : ∀ f, test f ∉ M.closure ∅) :
    integerResidual M (nominalPath M hE κ D C h) test (activation h) ε K
        (fun w : Z => w.val) β ∈
      integerResidualFamily M U (U.card / κ) (guardedPath M hE κ D C h)
        (activation h) ε K test := by
  classical
  obtain ⟨G, hGD, hGcard, τ, hτ, hgen⟩ := nominalPath_all_time_generators M hE κ hκ D C h
  let J : Finset α := G.toFinset
  let ν : J → ℤ := fun i => activation h + (τ i.val : ℤ)
  have hJ : J ⊆ U := by
    intro e he
    exact hDU (hGD (Set.mem_toFinset.mp he))
  have hJcard : J.card ≤ U.card / κ := by
    apply (Nat.le_div_iff_mul_le hκ).2
    have hDUcard : (D h).ncard ≤ U.card := by simpa using Set.ncard_mono hDU
    have hcard : κ * J.card ≤ U.card := by
      simpa only [J, ← Set.ncard_eq_toFinset_card'] using hGcard.trans hDUcard
    simpa only [Nat.mul_comm] using hcard
  have hν : ∀ i, activation h ≤ ν i ∧ ν i ≤ 0 := by
    intro i
    have hτi := hτ i.val (Set.mem_toFinset.mp i.property)
    have hhor := activation_add_horizon h
    dsimp [ν]
    constructor <;> omega
  have hX : nominalPath M hE κ D C h = generatedPath M (guardedPath M hE κ D C h)
      (fun i : J => i.val) ν := by
    funext k
    rw [hgen k]
    unfold generatedPath
    congr 1
    congr 1
    ext e
    constructor
    · rintro ⟨he, ht⟩
      exact ⟨⟨e, Set.mem_toFinset.mpr he⟩, ht, rfl⟩
    · rintro ⟨i, ht, rfl⟩
      exact ⟨Set.mem_toFinset.mp i.property, ht⟩
  rw [hX] at hz ⊢
  apply integerResidual_mem_family M hE U J Z (U.card / κ)
    (guardedPath M hE κ D C h) (guardedPath_mono M hE κ D C h)
    (activation h) (by unfold activation; omega) _
    (fun k hk => guardedPath_nonnegative M hE κ D C h hk) ε K hK ν hν β hz test hnonloop hJ hJcard hZU hZcard
  intro k hk
  apply guardedPath_early M hE κ D C h
  unfold activation at hk
  omega

lemma integerResidualFamily_card_le_exp (M : Matroid α) (hE : M.E = Set.univ) (d : α)
    (U : Finset α) (κ : ℕ) (hκ : 2 ≤ κ) (F : ℤ → Set α) (a : ℤ) (ε : Fin 2)
    (K : ParityWindow a ε → Set α) (test : Fin n → α) (hn : U.card = n) :
    ((integerResidualFamily M U (U.card / κ) F a ε K test).card : ℝ) ≤
      Real.exp (1000 * Real.log (κ : ℝ) / (κ : ℝ) * n) := by
  apply card_residualFamily_le_exp M d U (U.card / κ) _ _ _ _ test
    (by simp [hE]) (by simp [hE]) (by simp [hE]) hn (κ : ℝ) (by exact_mod_cast hκ)
  have hkpos : (0 : ℝ) < κ := by exact_mod_cast (show 0 < κ by omega)
  apply (le_div_iff₀ hkpos).2
  rw [← hn]
  exact_mod_cast Nat.div_mul_le_self U.card κ

end MatroidProphet

end OAI
