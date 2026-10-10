import OAI.Combinatorics.MatchingPSD.Pairings

namespace OAI

universe u_1

namespace MatchingSmoothing
section StandardPairs

abbrev Vertices (h : ℕ) := Fin h × Bool

variable {h : ℕ}

def firstVertices (h t : ℕ) : Finset (Vertices h) :=
  (Finset.univ.filter fun i : Fin h => i.val < t) ×ˢ Finset.univ

@[simp] lemma mem_firstVertices (t : ℕ) (v : Vertices h) :
    v ∈ firstVertices h t ↔ v.1.val < t := by simp [firstVertices]

lemma card_firstVertices {t : ℕ} (ht : t ≤ h) :
    (firstVertices h t).card = 2 * t := by
  simp [firstVertices, Fin.card_filter_val_lt, min_eq_right ht, Nat.mul_comm]

def pairSwap (i : Fin h) : Equiv.Perm (Vertices h) :=
  Equiv.swap (i, false) (i, true)

lemma pairSwap_commute (i j : Fin h) : Commute (pairSwap i) (pairSwap j) := by
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · change Equiv.swap (i,false) (i,true) * Equiv.swap (j,false) (j,true) =
      Equiv.swap (j,false) (j,true) * Equiv.swap (i,false) (i,true)
    rw [Equiv.mul_swap_eq_swap_mul]
    simp [Equiv.swap_apply_def, Ne.symm hij]

lemma act_pairSwap_commute (i j : Fin h) :
    Commute (Pairing.act (pairSwap i)).toLinearMap (Pairing.act (pairSwap j)).toLinearMap := by
  apply LinearMap.ext
  intro f
  change Pairing.act (pairSwap i) (Pairing.act (pairSwap j) f) = _
  rw [← Pairing.act_mul, (pairSwap_commute i j).eq, Pairing.act_mul]
  rfl

lemma pairSwap_fixed_outside {i : Fin h} {a b : Vertices h}
    (ha : a.1 ≠ i) (hb : b.1 ≠ i) :
    Equiv.swap a b (i,false) = (i,false) ∧ Equiv.swap a b (i,true) = (i,true) := by
  simp [Equiv.swap_apply_def, Prod.ext_iff, Ne.symm ha, Ne.symm hb]

lemma eigen_weighted_projection {V : Type u_1} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) (hinv : ∀ v, A (A v) = v)
    (c : ℝ) (hc : c = 1 ∨ c = -1) (v : V) :
    A (v + c • A v) = c • (v + c • A v) := by
  rcases hc with rfl | rfl
  · simp [hinv, add_comm]
  · simp [hinv, add_comm]

lemma next_prescribed_sign (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    {t : ℕ} (ht : t < h) (χ : Fin h → ℝ) (c : ℝ) (hc : c = 1 ∨ c = -1)
    (f : Pairing (Vertices h) → ℝ) (hf : f ∈ W)
    (heig : ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) f = χ i • f)
    (hex : ∃ a, a ∉ firstVertices h t ∧ ∃ b, b ∉ firstVertices h t ∧ a ≠ b ∧
      f + c • Pairing.act (Equiv.swap a b) f ≠ 0) :
    ∃ g ∈ W, g ≠ 0 ∧ Pairing.act (pairSwap ⟨t, ht⟩) g = c • g ∧
      ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) g = χ i • g := by
  obtain ⟨a, ha, b, hb, hab, h0⟩ := hex
  let i : Fin h := ⟨t, ht⟩
  obtain ⟨p, hp, hpa, hpb⟩ := Pairing.exists_perm_fixing_pair (firstVertices h t)
    ha hb (c := (i,false)) (d := (i,true)) (by simp [i]) (by simp [i]) hab (by simp)
  let v := f + c • Pairing.act (Equiv.swap a b) f
  have hv : v ∈ W := W.add_mem hf (W.smul_mem c (hW _ _ hf))
  refine ⟨Pairing.act p v, hW _ _ hv, ?_, ?_, ?_⟩
  · intro hz
    apply h0
    change v = 0
    exact (Pairing.act p).injective (hz.trans (map_zero _).symm)
  · change Pairing.act (Equiv.swap (i,false) (i,true)) (Pairing.act p v) = _
    rw [← hpa, ← hpb, Pairing.act_swap_conj]
    have hvsign := eigen_weighted_projection (Pairing.act (Equiv.swap a b)).toLinearMap
      (Pairing.act_swap_involution a b) c hc f
    change Pairing.act (Equiv.swap a b) v = c • v at hvsign
    rw [hvsign, map_smul]
  · intro j hj
    have hpj (b : Bool) : p (j,b) = (j,b) := hp _ (by simpa using hj)
    change Pairing.act (Equiv.swap (j,false) (j,true)) (Pairing.act p v) = _
    rw [Pairing.act_commute_of_swap_fixed p _ _ (hpj false) (hpj true)]
    have haj : a.1 ≠ j := by
      intro he
      apply ha
      simpa only [mem_firstVertices, he] using hj
    have hbj : b.1 ≠ j := by
      intro he
      apply hb
      simpa only [mem_firstVertices, he] using hj
    obtain ⟨hfix₁, hfix₂⟩ := pairSwap_fixed_outside haj hbj
    have hpast : Pairing.act (pairSwap j) v = χ j • v := by
      change Pairing.act (Equiv.swap (j,false) (j,true))
        (f + c • Pairing.act (Equiv.swap a b) f) = _
      rw [map_add, map_smul, Pairing.act_commute_of_swap_fixed _ _ _ hfix₁ hfix₂]
      change Pairing.act (pairSwap j) f +
        c • Pairing.act (Equiv.swap a b) (Pairing.act (pairSwap j) f) = _
      rw [heig j hj, map_smul]
      change χ j • f + c • (χ j • Pairing.act (Equiv.swap a b) f) =
        χ j • (f + c • Pairing.act (Equiv.swap a b) f)
      rw [smul_add, smul_comm c (χ j)]
    change Pairing.act p (Pairing.act (pairSwap j) v) = _
    rw [hpast, map_smul]

lemma exists_negative_projection {α : Type u_1} [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : f ∉ lowDegree Pairing.edgeCoord (U.card * U.card)) :
    ∃ a, a ∉ U ∧ ∃ b, b ∉ U ∧ a ≠ b ∧ f + (-1 : ℝ) • Pairing.act (Equiv.swap a b) f ≠ 0 := by
  by_contra! hall
  apply hf
  apply Pairing.mem_lowDegree_of_swap_invariant U f
  intro a ha b hb hab
  have he := hall a ha b hb hab
  have hz : f - Pairing.act (Equiv.swap a b) f = 0 := by
    simpa only [neg_smul, one_smul, sub_eq_add_neg] using he
  exact (sub_eq_zero.mp hz).symm

lemma exists_positive_projection {α : Type u_1} [Fintype α] [DecidableEq α]
    (U : Finset α) (hU : 2 * U.card < Fintype.card α)
    (f : Pairing α → ℝ) (hf : f ≠ 0) :
    ∃ a, a ∉ U ∧ ∃ b, b ∉ U ∧ a ≠ b ∧ f + (1 : ℝ) • Pairing.act (Equiv.swap a b) f ≠ 0 := by
  by_contra! hall
  apply hf
  apply Pairing.no_sign_on_complement U hU f
  intro a ha b hb hab
  have he := hall a ha b hb hab
  exact eq_neg_of_add_eq_zero_left (by simpa only [one_smul, add_comm] using he)

lemma prescribed_sign_vector (k : ℕ) (hk : 4 * k < h)
    (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    (hdis : Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k))))
    (hne : ∃ f ∈ W, f ≠ 0) :
    ∃ f ∈ W, f ≠ 0 ∧ ∀ i : Fin h, i.val < 2 * k →
      Pairing.act (pairSwap i) f = (if i.val < k then (-1 : ℝ) else 1) • f := by
  let χ (i : Fin h) : ℝ := if i.val < k then -1 else 1
  have hind : ∀ t : ℕ, t ≤ 2 * k → ∃ f ∈ W, f ≠ 0 ∧
      ∀ i : Fin h, i.val < t → Pairing.act (pairSwap i) f = χ i • f := by
    intro t
    induction t with
    | zero =>
      intro _
      obtain ⟨f, hf, hf0⟩ := hne
      exact ⟨f, hf, hf0, by simp⟩
    | succ t ih =>
      intro ht
      obtain ⟨f, hf, hf0, he⟩ := ih (by omega)
      have hth : t < h := by omega
      let c : ℝ := if t < k then -1 else 1
      have hc : c = 1 ∨ c = -1 := by dsimp [c]; split_ifs <;> simp
      have hex : ∃ a, a ∉ firstVertices h t ∧ ∃ b, b ∉ firstVertices h t ∧ a ≠ b ∧
          f + c • Pairing.act (Equiv.swap a b) f ≠ 0 := by
        by_cases htk : t < k
        · dsimp [c]; rw [ite_eq_left htk]
          apply exists_negative_projection
          intro hlow
          have hd : (firstVertices h t).card * (firstVertices h t).card ≤ (4*k) * (4*k) := by
            rw [card_firstVertices hth.le]
            apply Nat.mul_self_le_mul_self
            omega
          exact hf0 ((Submodule.disjoint_def.mp hdis) f hf (lowDegree_mono _ hd hlow))
        · dsimp [c]; rw [ite_eq_right htk]
          apply exists_positive_projection _ _ f hf0
          rw [card_firstVertices hth.le]
          simp only [Vertices, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
          omega
      obtain ⟨g, hg, hg0, hnew, hold⟩ := next_prescribed_sign W hW hth χ c hc f hf he hex
      refine ⟨g, hg, hg0, ?_⟩
      intro i hi
      by_cases hit : i.val < t
      · exact hold i hit
      · have hie : i = ⟨t, hth⟩ := Fin.ext (by change i.val = t; omega)
        subst i
        exact hnew
  exact hind (2*k) le_rfl

lemma choose_le_choose_of_le_of_le_compl {n k w : ℕ}
    (hkw : k ≤ w) (hw : w ≤ n - k) : n.choose k ≤ n.choose w := by
  have hmon : ∀ a b : ℕ, a ≤ b → b ≤ n / 2 → n.choose a ≤ n.choose b := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => intro _; rfl
    | succ b hab ih =>
      intro hb
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases hhalf : w ≤ n / 2
  · exact hmon k w hkw hhalf
  · have hwn : w ≤ n := hw.trans (Nat.sub_le _ _)
    rw [← Nat.choose_symm hwn]
    apply hmon k (n-w) <;> omega

lemma invariant_high_degree_dimension (k : ℕ) (hk : 4 * k < h)
    (W : Submodule ℝ (Pairing (Vertices h) → ℝ))
    (hW : ∀ p f, f ∈ W → Pairing.act p f ∈ W)
    (hdis : Disjoint W (lowDegree Pairing.edgeCoord ((4 * k) * (4 * k))))
    (hne : ∃ f ∈ W, f ≠ 0) : h.choose k ≤ Module.finrank ℝ W := by
  classical
  obtain ⟨v, hv, hv0, he⟩ := prescribed_sign_vector k hk W hW hdis hne
  let A (i : Fin h) := (Pairing.act (pairSwap i)).toLinearMap
  let s₀ := Finset.univ.filter fun i : Fin h => i.val < 2*k
  obtain ⟨ψ, w, hw, hw0, hew, hp⟩ := simultaneous_sign_eigenvector_preserving A
    act_pairSwap_commute (fun i => Pairing.act_swap_involution (i,false) (i,true))
    W (fun i => hW (pairSwap i)) s₀ (fun i => if i.val < k then -1 else 1)
    v hv hv0 (by simpa [A, s₀] using he)
  have hpres (i : Fin h) (hi : i.val < 2*k) : ψ i = if i.val < k then -1 else 1 :=
    hp i (by simpa only [s₀, Finset.mem_filter, Finset.mem_univ, true_and] using hi)
  let s := Finset.univ.filter fun i => ψ i = -1
  have hlow : k ≤ s.card := by
    let e (i : Fin k) : s := ⟨⟨i.val, by omega⟩, by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpres _ (by dsimp; omega)]
      exact ite_eq_left i.isLt⟩
    have hinj : Function.Injective e := by
      intro i j hij
      exact Fin.ext (congrArg (fun x : s => x.1.val) hij)
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective e hinj
  have hhigh : k ≤ sᶜ.card := by
    let e (i : Fin k) : ↥(sᶜ) := ⟨⟨k+i.val, by omega⟩, by
      simp only [Finset.mem_compl, s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hpres _ (by dsimp; omega), ite_eq_right (by dsimp; omega)]
      norm_num⟩
    have hinj : Function.Injective e := by
      intro i j hij
      have heq := congrArg (fun x : ↥(sᶜ) => x.1.val) hij
      apply Fin.ext
      dsimp [e] at heq
      omega
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective e hinj
  have hsc : s.card ≤ h := Finset.card_le_univ s |>.trans_eq (Fintype.card_fin h)
  rw [Finset.card_compl, Fintype.card_fin] at hhigh
  have hchoose := choose_le_choose_of_le_of_le_compl hlow (by omega : s.card ≤ h-k)
  apply hchoose.trans
  let P (p : Equiv.Perm (Fin h)) := Pairing.act (Equiv.prodCongr p (Equiv.refl Bool))
  have hconj (p : Equiv.Perm (Fin h)) (i : Fin h) (f : Pairing (Vertices h) → ℝ) :
      A (p i) (P p f) = P p (A i f) :=
    Pairing.act_swap_conj (Equiv.prodCongr p (Equiv.refl Bool)) (i,false) (i,true) f
  have hsigne (i : Fin h) : A i w = (if i ∈ s then (-1 : ℝ) else 1) • w := by
    have hi := hew i
    rw [hi.2]
    congr 1
    by_cases his : ψ i = -1
    · simp [s, his]
    · have hie : ψ i = 1 := hi.1.resolve_right his
      simp [s, hie]
  simpa only [Fintype.card_fin] using
    binomial_le_finrank_of_eigenvector_mem A act_pairSwap_commute P hconj W
      (fun p => hW _) s w hw hw0 hsigne

end StandardPairs
end MatchingSmoothing

end OAI
