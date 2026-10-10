import OAI.Probability.SignedSweeps.WordTwirl

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct ComplexOrder Classical
open Module

lemma word_polytabloid_collision {p : ℕ} {C : Type*} [Fintype C]
    (μ : Partition p)
    (f : Representation.IntertwiningMap (spechtRepresentation μ) (wordRepresentation p C))
    (w : Fin p → C) {i j : Fin p} (hij : i ≠ j)
    (hc : μ.colOf i = μ.colOf j) (hw : w i = w j) :
    f (spechtGenerator μ) w = 0 := by
  let g : colSubgroup μ := ⟨Equiv.swap i j, swap_mem_fiberSubgroup _ hc⟩
  have hg : complexSign p g.1 = -1 := by
    simp [g, complexSign, Equiv.Perm.sign_swap hij]
  have hs : w ∘ g.1 = w := by
    ext a
    change w (Equiv.swap i j a) = w a
    by_cases hai : a = i
    · subst a; simpa using hw.symm
    by_cases haj : a = j
    · subst a; simpa using hw
    · rw [Equiv.swap_apply_of_ne_of_ne hai haj]
  have he := congrArg (fun v : WordSpace p C => v w) (Representation.IntertwiningMap.isIntertwining _ _ f g.1 (spechtGenerator μ))
  rw [spechtGenerator_column_action, hg, map_smul] at he
  simp only [neg_one_smul, PiLp.neg_apply, wordRepresentation_apply] at he
  rw [hs] at he
  linear_combination -he / 2

lemma fin_injective_antitone_prod {a q : ℕ} (ha : a ≤ q)
    (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (f : Fin a → Fin q) (hf : Function.Injective f) :
    (∏ i, x (f i)) ≤ ∏ i : Fin a, x (Fin.castLE ha i) := by
  let s : Finset (Fin q) := Finset.univ.image f
  have hs : s.card = a := by rw [Finset.card_image_of_injective _ hf]; simp
  have he : ∏ i : Fin a, x (s.orderEmbOfFin hs i) = ∏ i, x (f i) := by
    have h₁ := Finset.prod_image (s := Finset.univ) (f := x) (s.orderEmbOfFin hs).injective.injOn
    have h₂ := Finset.prod_image (s := Finset.univ) (f := x) hf.injOn
    simp only [Finset.image_orderEmbOfFin_univ] at h₁
    exact h₁.symm.trans h₂
  rw [← he]
  apply Finset.prod_le_prod₀ (fun i _ => hx0 _)
  intro i _
  apply hx
  change i.val ≤ (s.orderEmbOfFin hs i).val
  exact fin_strictMono_val_le _ (Fin.val_strictMono.comp (s.orderEmbOfFin hs).strictMono) i

lemma word_column_monomial_le {p q : ℕ} (μ : Partition p) (hμ : μ.1.colLen 0 ≤ q)
    (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i)
    (w : Fin p → Fin q)
    (hw : ∀ i j, μ.colOf i = μ.colOf j → w i = w j → i = j) :
    (∏ i, x (w i)) ≤ ∏ i, x (Fin.castLE hμ (μ.rowIndex i)) := by
  let e := μ.colEquiv
  have hcol (j : Fin (μ.1.rowLen 0)) : μ.1.colLen j.val ≤ q :=
    (μ.1.colLen_anti 0 _ (Nat.zero_le _)).trans hμ
  have hprod (f : Fin p → ℝ) : ∏ i, f i = ∏ j : Fin (μ.1.rowLen 0),
      ∏ k : Fin (μ.1.colLen j.val), f (e ⟨j, k⟩) := by
    exact (e.prod_comp f).symm.trans (Fintype.prod_sigma (fun z => f (e z)))
  rw [hprod, hprod]
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.prod_nonneg (fun i _ => hx0 _)
  · intro j _
    have hinj : Function.Injective (fun k : Fin (μ.1.colLen j.val) => w (e ⟨j, k⟩)) := by
      intro k t hkt
      have heq : e ⟨j, k⟩ = e ⟨j, t⟩ := by
        apply hw _ _ _ hkt
        simp [e]
      exact eq_of_heq (Sigma.mk.inj_iff.mp (e.injective heq)).2
    have hb := fin_injective_antitone_prod (hcol j) x hx hx0 _ hinj
    refine hb.trans_eq ?_
    apply Finset.prod_congr rfl
    intro k _
    congr 1
    apply Fin.ext
    simp [e, Partition.colEquiv, Partition.rowIndex, Partition.rowOf]

lemma specht_intertwiner_range_mem {p : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] (μ : Partition p)
    (ρ : Representation ℂ (SymmetricGroup p) E)
    (f : Representation.IntertwiningMap (spechtRepresentation μ) ρ)
    (S : Subrepresentation ρ) (h : f (spechtGenerator μ) ∈ S.toSubmodule)
    (v : Specht μ) : f v ∈ S.toSubmodule := by
  have haux : ∀ v (hv : v ∈ (spechtSubrepresentation μ).toSubmodule),
      f ⟨v, hv⟩ ∈ S.toSubmodule := by
    intro v hv
    change v ∈ Submodule.span ℂ _ at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g, rfl⟩ := hv
      change f (spechtRepresentation μ g (spechtGenerator μ)) ∈ S.toSubmodule
      rw [f.isIntertwining]
      exact S.apply_mem_toSubmodule _ h
    | zero => exact (map_zero f).symm ▸ S.toSubmodule.zero_mem
    | add v w hv hw ihv ihw =>
      change v ∈ (spechtSubrepresentation μ).toSubmodule at hv
      change w ∈ (spechtSubrepresentation μ).toSubmodule at hw
      change f ((⟨v, hv⟩ : Specht μ) + (⟨w, hw⟩ : Specht μ)) ∈ S.toSubmodule
      exact (map_add f (show Specht μ from ⟨v, hv⟩) (show Specht μ from ⟨w, hw⟩)).symm ▸
        S.toSubmodule.add_mem ihv ihw
    | smul a v hv ih =>
      change v ∈ (spechtSubrepresentation μ).toSubmodule at hv
      change f (a • (⟨v, hv⟩ : Specht μ)) ∈ S.toSubmodule
      exact (map_smul f a (show Specht μ from ⟨v, hv⟩)).symm ▸ S.toSubmodule.smul_mem a ih
  exact haux _ v.2

def wordWeightSubrepresentation {p : ℕ} {C : Type*} [Fintype C]
    (x : C → ℝ) (b : ℝ) : Subrepresentation (wordRepresentation p C) where
  toSubmodule := {
    carrier := {v | ∀ w, b < ∏ i, x (w i) → v w = 0}
    zero_mem' := by intro w hw; rfl
    add_mem' := by intro v w hv hw z hz; change v z + w z = 0; rw [hv _ hz, hw _ hz]; simp
    smul_mem' := by intro c v hv z hz; change c * v z = 0; rw [hv _ hz, mul_zero] }
  apply_mem_toSubmodule g v hv := by
    intro w hw
    change v (w ∘ g) = 0
    apply hv
    change b < ∏ i, (x ∘ w) (g i)
    rw [Equiv.prod_comp g]
    exact hw

theorem word_isotypic_weight_support {p q : ℕ} (μ : Partition p) (hμ : μ.1.colLen 0 ≤ q)
    (x : Fin q → ℝ) (hx : Antitone x) (hx0 : ∀ i, 0 ≤ x i) :
    (isotypicSubrepresentation (spechtRepresentation μ) (wordRepresentation p (Fin q))).toSubmodule ≤
      (wordWeightSubrepresentation x (∏ i, x (Fin.castLE hμ (μ.rowIndex i)))).toSubmodule := by
  apply iSup_le
  intro f v hv
  obtain ⟨v, rfl⟩ := hv
  apply specht_intertwiner_range_mem μ (wordRepresentation p (Fin q)) f _ _ v
  intro w hw
  by_contra hn
  have hinj : ∀ i j, μ.colOf i = μ.colOf j → w i = w j → i = j := by
    intro i j hc hij
    by_contra hne
    exact hn (word_polytabloid_collision μ f w hne hc hij)
  exact (not_lt_of_ge (word_column_monomial_le μ hμ x hx hx0 w hinj)) hw

end SignedSweeps
end

end OAI
