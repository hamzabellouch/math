import OAI.Combinatorics.HalvingLines.Basic

namespace OAI

namespace PlanarHalving

namespace Sweep

noncomputable def projection (s : ℝ) (p : Point) : ℝ := p.2 - s * p.1

def Separates {n : ℕ} (P : Fin n → Point) (s : ℝ) (M : Finset (Fin n)) : Prop :=
  ∀ i ∈ M, ∀ j ∉ M, projection s (P i) < projection s (P j)

lemma comparison_persists (p q : Point) {s₀ s t : ℝ} (h₀ : s₀ ≤ s) (ht : s ≤ t)
    (hbefore : projection s₀ q < projection s₀ p)
    (hafter : projection s p < projection s q) :
    p.1 > q.1 ∧ projection t p < projection t q := by
  unfold projection at *
  have hm : 0 < (s - s₀) * (p.1 - q.1) := by nlinarith only [hbefore, hafter]
  have hx : 0 < p.1 - q.1 := by
    rcases mul_pos_iff.mp hm with hh | hh
    · exact hh.2
    · exact False.elim ((not_lt_of_ge (sub_nonneg.mpr h₀)) hh.1)
  have hprod := mul_nonneg (sub_nonneg.mpr ht) hx.le
  constructor
  · exact sub_pos.mp hx
  · nlinarith only [hafter, hprod]

lemma exchange_rightward {n : ℕ} {P : Fin n → Point} {s t : ℝ}
    {M M' : Finset (Fin n)} (hst : s ≤ t)
    (hM : Separates P s M) (hM' : Separates P t M')
    {i j : Fin n} (hi : i ∈ M \ M') (hj : j ∈ M' \ M) : (P i).1 < (P j).1 := by
  exact (comparison_persists (P j) (P i) hst le_rfl
    (hM i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
    (hM' j (Finset.mem_sdiff.mp hj).1 i (Finset.mem_sdiff.mp hi).2)).1

theorem distance_of_outside_visitors {n k c : ℕ} (P : Fin n → Point)
    (s₀ t : ℝ) (E E' U : Finset (Fin n))
    (hE : E.card = k + c) (hE' : E'.card = k + c)
    (hsep : Separates P s₀ E) (hsep' : Separates P t E')
    (hU : c ≤ U.card)
    (hvisit : ∀ u ∈ U, u ∉ E ∧ ∃ (s : ℝ) (M : Finset (Fin n)),
      s₀ ≤ s ∧ s ≤ t ∧ M.card = k ∧ Separates P s M ∧ u ∈ M) :
    c ≤ (E \ E').card := by
  classical
  by_cases hh : ∃ u ∈ U, u ∉ E'
  · obtain ⟨u, hu, hu'⟩ := hh
    obtain ⟨huE, s, M, h₀, ht, hcard, hM, huM⟩ := hvisit u hu
    have hsub : E \ M ⊆ E \ E' := by
      intro v hv
      obtain ⟨hvE, hvM⟩ := Finset.mem_sdiff.mp hv
      refine Finset.mem_sdiff.mpr ⟨hvE, ?_⟩
      intro hv'
      have hvt := (comparison_persists (P u) (P v) h₀ ht
        (hsep v hvE u huE) (hM u huM v hvM)).2
      exact (not_lt_of_gt hvt) (hsep' v hv' u hu')
    have hcount := Finset.card_sdiff_add_card_inter E M
    have hinter : (E ∩ M).card ≤ M.card := Finset.card_le_card Finset.inter_subset_right
    have hc : c ≤ (E \ M).card := by omega
    exact hc.trans (Finset.card_le_card hsub)
  · have hsub : U ⊆ E' \ E := by
      intro u hu
      refine Finset.mem_sdiff.mpr ⟨?_, (hvisit u hu).1⟩
      by_contra hnot
      exact hh ⟨u, hu, hnot⟩
    have hc := hU.trans (Finset.card_le_card hsub)
    have hc₁ := Finset.card_sdiff_add_card_inter E E'
    have hc₂ := Finset.card_sdiff_add_card_inter E' E
    rw [Finset.inter_comm E' E] at hc₂
    omega

private structure ProjectionIndex (n : ℕ) where
  down : Fin n

private def projectionIndexEquiv (n : ℕ) : ProjectionIndex n ≃ Fin n where
  toFun := ProjectionIndex.down
  invFun := ProjectionIndex.mk
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_state {n k : ℕ} (P : Fin n → Point) (s : ℝ) (hk : k ≤ n)
    (hinj : Function.Injective (fun i => projection s (P i))) :
    ∃ M : Finset (Fin n), M.card = k ∧ Separates P s M := by
  classical
  let ind := projectionIndexEquiv n
  let : Fintype (ProjectionIndex n) := Fintype.ofEquiv (Fin n) ind.symm
  let : LinearOrder (ProjectionIndex n) :=
    LinearOrder.lift' (fun i => projection s (P (ind i))) (hinj.comp ind.injective)
  let e := Fintype.orderIsoFinOfCardEq (ProjectionIndex n)
    ((Fintype.card_congr ind).trans (Fintype.card_fin n))
  let f : Fin k ↪ Fin n := (Fin.castLEEmb hk).trans
    (e.toEmbedding.trans ind.toEmbedding)
  let M := Finset.univ.map f
  have hmem (z : Fin n) : z ∈ M ↔ (e.symm (ind.symm z)).val < k := by
    constructor
    · intro hz
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hz
      change (e.symm (ind.symm (ind (e (Fin.castLE hk a))))).val < k
      rw [ind.symm_apply_apply, e.symm_apply_apply]
      exact a.isLt
    · intro hz
      let a : Fin k := ⟨(e.symm (ind.symm z)).val, hz⟩
      apply Finset.mem_map.mpr
      refine ⟨a, Finset.mem_univ _, ?_⟩
      change ind (e (Fin.castLE hk a)) = z
      apply ind.symm.injective
      rw [ind.symm_apply_apply]
      apply e.symm.injective
      rw [e.symm_apply_apply]
      apply Fin.ext
      rfl
  refine ⟨M, by simp only [M, Finset.card_map, Finset.card_univ, Fintype.card_fin], ?_⟩
  intro i hi j hj
  have hi' := (hmem i).mp hi
  have hj' : k ≤ (e.symm (ind.symm j)).val := Nat.le_of_not_gt (fun h => hj ((hmem j).mpr h))
  have hlt : e.symm (ind.symm i) < e.symm (ind.symm j) := by
    change (e.symm (ind.symm i)).val < (e.symm (ind.symm j)).val
    exact lt_of_lt_of_le hi' hj'
  have he := e.strictMono hlt
  rw [e.apply_symm_apply, e.apply_symm_apply] at he
  change projection s (P (ind (ind.symm i))) < projection s (P (ind (ind.symm j))) at he
  simpa only [ind.apply_symm_apply] using he

lemma states_nested {n : ℕ} {P : Fin n → Point} {s : ℝ} {M E : Finset (Fin n)}
    (hM : Separates P s M) (hE : Separates P s E) (hcard : M.card ≤ E.card) : M ⊆ E := by
  classical
  intro i hi
  by_contra hiE
  have hsub : E ⊆ M := by
    intro j hj
    by_contra hjM
    exact (not_lt_of_gt (hM i hi j hjM)) (hE j hj i hiE)
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  exact hiE (heq.symm ▸ hi)

theorem outside_class_distance {n k c : ℕ} (P : Fin n → Point)
    (s₀ t : ℝ) (M₀ E E' V : Finset (Fin n))
    (hM₀ : M₀.card = k) (hE : E.card = k + c) (hE' : E'.card = k + c)
    (hsep₀ : Separates P s₀ M₀) (hsep : Separates P s₀ E)
    (hsep' : Separates P t E') (hV : 2 * c ≤ V.card)
    (hvisit : ∀ u ∈ V, u ∉ M₀ ∧ ∃ (s : ℝ) (M : Finset (Fin n)),
      s₀ ≤ s ∧ s ≤ t ∧ M.card = k ∧ Separates P s M ∧ u ∈ M) :
    c ≤ (E \ E').card := by
  classical
  have hsubset : M₀ ⊆ E := states_nested hsep₀ hsep (by omega)
  have hdiff : (E \ M₀).card = c := by
    have hh := Finset.card_sdiff_add_card_inter E M₀
    rw [Finset.inter_eq_right.mpr hsubset, hM₀, hE] at hh
    omega
  have hinter : V ∩ E ⊆ E \ M₀ := by
    intro u hu
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hu).2,
      (hvisit u (Finset.mem_inter.mp hu).1).1⟩
  have hU : c ≤ (V \ E).card := by
    have hh := Finset.card_sdiff_add_card_inter V E
    have hle := Finset.card_le_card hinter
    omega
  apply distance_of_outside_visitors P s₀ t E E' (V \ E) hE hE' hsep hsep' hU
  intro u hu
  exact ⟨(Finset.mem_sdiff.mp hu).2, (hvisit u (Finset.mem_sdiff.mp hu).1).2⟩

end Sweep

namespace Sweep

lemma separates_neg_compl {n : ℕ} {P : Fin n → Point} {s : ℝ}
    {M : Finset (Fin n)} (hM : Separates P s M) :
    Separates (fun i => -P i) s Mᶜ := by
  classical
  intro i hi j hj
  have hi' : i ∉ M := Finset.mem_compl.mp hi
  have hj' : j ∈ M := by simpa using hj
  have h := hM j hj' i hi'
  simp only [projection, Prod.fst_neg, Prod.snd_neg] at *
  linarith

noncomputable def activity {n : ℕ} {ι : Type*} [Fintype ι]
    (M : ι → Finset (Fin n)) (i₀ : ι) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ i, (u ∈ M i ∧ u ∉ M i₀) ∨
    (u ∉ M i ∧ u ∈ M i₀)

lemma mem_activity {n : ℕ} {ι : Type*} [Fintype ι]
    {M : ι → Finset (Fin n)} {i₀ : ι} {u : Fin n} :
    u ∈ activity M i₀ ↔ ∃ i, (u ∈ M i ∧ u ∉ M i₀) ∨
      (u ∉ M i ∧ u ∈ M i₀) := by
  classical
  simp [activity]

theorem activity_distance {n k c : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin n → Point) (s : ι → ℝ) (M : ι → Finset (Fin n)) (i₀ i₁ : ι)
    (hsize : ∀ i, (M i).card = k) (hsep : ∀ i, Separates P (s i) (M i))
    (hlo : ∀ i, s i₀ ≤ s i) (hhi : ∀ i, s i ≤ s i₁)
    (hinj₀ : Function.Injective (fun u => projection (s i₀) (P u)))
    (hinj₁ : Function.Injective (fun u => projection (s i₁) (P u)))
    (hc : 4 * c ≤ (activity M i₀).card) :
    (k + c ≤ n ∧ ∃ E E' : Finset (Fin n),
      E.card = k + c ∧ E'.card = k + c ∧
      Separates P (s i₀) E ∧ Separates P (s i₁) E' ∧ c ≤ (E \ E').card) ∨
    (c ≤ k ∧ ∃ E E' : Finset (Fin n),
      E.card = k - c ∧ E'.card = k - c ∧
      Separates P (s i₀) E ∧ Separates P (s i₁) E' ∧ c ≤ (E \ E').card) := by
  classical
  let A := activity M i₀
  let V := A \ M i₀
  let W := A ∩ M i₀
  have hpart : V.card + W.card = A.card := Finset.card_sdiff_add_card_inter A (M i₀)
  have hk : k ≤ n := by
    simpa only [hsize i₀, Fintype.card_fin] using (M i₀).card_le_univ
  by_cases hV : 2 * c ≤ V.card
  · have hVsub : V ⊆ (M i₀)ᶜ := by
      intro u hu
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hu).2
    have hfeas : k + c ≤ n := by
      have hle := Finset.card_le_card hVsub
      simp only [Finset.card_compl, Fintype.card_fin, hsize] at hle
      omega
    obtain ⟨E, hE, hsepE⟩ := exists_state P (s i₀) hfeas hinj₀
    obtain ⟨E', hE', hsepE'⟩ := exists_state P (s i₁) hfeas hinj₁
    refine Or.inl ⟨hfeas, E, E', hE, hE', hsepE, hsepE', ?_⟩
    apply outside_class_distance P (s i₀) (s i₁) (M i₀) E E' V
      (hsize i₀) hE hE' (hsep i₀) hsepE hsepE' hV
    intro u hu
    obtain ⟨huA, huM⟩ := Finset.mem_sdiff.mp hu
    obtain ⟨i, hi | hi⟩ := mem_activity.mp huA
    · exact ⟨huM, s i, M i, hlo i, hhi i, hsize i, hsep i, hi.1⟩
    · exact False.elim (huM hi.2)
  · have hW : 2 * c ≤ W.card := by change 4 * c ≤ A.card at hc; omega
    have hfeas : c ≤ k := by
      have hle : W.card ≤ (M i₀).card := Finset.card_le_card Finset.inter_subset_right
      rw [hsize] at hle
      omega
    obtain ⟨E, hE, hsepE⟩ := exists_state P (s i₀) (show k-c ≤ n by omega) hinj₀
    obtain ⟨E', hE', hsepE'⟩ := exists_state P (s i₁) (show k-c ≤ n by omega) hinj₁
    refine Or.inr ⟨hfeas, E, E', hE, hE', hsepE, hsepE', ?_⟩
    have hbound : c ≤ (Eᶜ \ E'ᶜ).card := by
      apply outside_class_distance (fun u => -P u) (s i₀) (s i₁) (M i₀)ᶜ Eᶜ E'ᶜ W
        (k := n-k) (c := c)
      · simp only [Finset.card_compl, Fintype.card_fin, hsize]
      · simp only [Finset.card_compl, Fintype.card_fin, hE]
        omega
      · simp only [Finset.card_compl, Fintype.card_fin, hE']
        omega
      · exact separates_neg_compl (hsep i₀)
      · exact separates_neg_compl hsepE
      · exact separates_neg_compl hsepE'
      · exact hW
      · intro u hu
        obtain ⟨huA, huM⟩ := Finset.mem_inter.mp hu
        obtain ⟨i, hi | hi⟩ := mem_activity.mp huA
        · exact False.elim (hi.2 huM)
        · refine ⟨by simpa using huM, s i, (M i)ᶜ, hlo i, hhi i, ?_,
            separates_neg_compl (hsep i), Finset.mem_compl.mpr hi.1⟩
          simp only [Finset.card_compl, Fintype.card_fin, hsize]
    have heq : Eᶜ \ E'ᶜ = E' \ E := by ext u; simp; tauto
    rw [heq] at hbound
    have he := Finset.card_sdiff_add_card_inter E E'
    have he' := Finset.card_sdiff_add_card_inter E' E
    rw [Finset.inter_comm E' E] at he'
    omega

lemma projection_lt_between (p q : Point) {s₀ s₁ t : ℝ}
    (h₀ : s₀ ≤ t) (h₁ : t ≤ s₁)
    (hp₀ : projection s₀ p < projection s₀ q)
    (hp₁ : projection s₁ p < projection s₁ q) : projection t p < projection t q := by
  unfold projection at *
  by_cases hx : p.1 ≤ q.1
  · have hprod := mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr hx)
    nlinarith only [hp₁, hprod]
  · have hprod := mul_nonneg (sub_nonneg.mpr h₀) (sub_nonneg.mpr (le_of_not_ge hx))
    nlinarith only [hp₀, hprod]

lemma separates_between {n : ℕ} {P : Fin n → Point} {s₀ s₁ t : ℝ}
    {M : Finset (Fin n)} (h₀ : s₀ ≤ t) (h₁ : t ≤ s₁)
    (hM₀ : Separates P s₀ M) (hM₁ : Separates P s₁ M) : Separates P t M := by
  intro u hu v hv
  exact projection_lt_between (P u) (P v) h₀ h₁ (hM₀ u hu v hv) (hM₁ u hu v hv)

lemma states_unique {n : ℕ} {P : Fin n → Point} {s : ℝ} {M E : Finset (Fin n)}
    (hM : Separates P s M) (hE : Separates P s E) (hcard : M.card = E.card) : M = E :=
  Finset.eq_of_subset_of_card_le (states_nested hM hE hcard.le) hcard.ge

theorem activity_pos_distance {n k : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin n → Point) (s : ι → ℝ) (M : ι → Finset (Fin n)) (i₀ i₁ : ι)
    (hsize : ∀ i, (M i).card = k) (hsep : ∀ i, Separates P (s i) (M i))
    (hlo : ∀ i, s i₀ ≤ s i) (hhi : ∀ i, s i ≤ s i₁)
    (hactivity : 0 < (activity M i₀).card) : 1 ≤ (M i₀ \ M i₁).card := by
  classical
  by_contra hn
  have hempty : M i₀ \ M i₁ = ∅ := Finset.card_eq_zero.mp (by omega)
  have hsub : M i₀ ⊆ M i₁ := Finset.sdiff_eq_empty_iff_subset.mp hempty
  have heq : M i₀ = M i₁ := Finset.eq_of_subset_of_card_le hsub (by rw [hsize, hsize])
  have hconstant (i : ι) : M i = M i₀ := by
    apply states_unique (hsep i)
      (separates_between (hlo i) (hhi i) (hsep i₀) (by rw [heq]; exact hsep i₁))
    rw [hsize, hsize]
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hactivity
  obtain ⟨i, hi | hi⟩ := mem_activity.mp hu
  · rw [hconstant i] at hi
    exact hi.2 hi.1
  · rw [hconstant i] at hi
    exact hi.1 hi.2

lemma exchange_slope_between {n : ℕ} {P : Fin n → Point} {s t : ℝ}
    {M M' : Finset (Fin n)} (hst : s ≤ t)
    (hM : Separates P s M) (hM' : Separates P t M')
    {i j : Fin n} (hi : i ∈ M \ M') (hj : j ∈ M' \ M) :
    s < slope (P i) (P j) ∧ slope (P i) (P j) < t := by
  have hx := exchange_rightward hst hM hM' hi hj
  have h₀ := hM i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2
  have h₁ := hM' j (Finset.mem_sdiff.mp hj).1 i (Finset.mem_sdiff.mp hi).2
  have hdx : 0 < (P j).1 - (P i).1 := sub_pos.mpr hx
  unfold slope
  constructor
  · apply (lt_div_iff₀ hdx).mpr
    unfold projection at h₀
    nlinarith only [h₀]
  · apply (div_lt_iff₀ hdx).mpr
    unfold projection at h₁
    nlinarith only [h₁]

end Sweep

end PlanarHalving

end OAI
