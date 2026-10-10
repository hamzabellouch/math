import Mathlib

namespace OAI

/-! Entropy and counting bounds for selected coordinates in finite probability laws. -/

section
open scoped BigOperators
open Finset
open scoped Classical

namespace SharpLogRamsey.Selection

structure Law (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

variable {α β : Type*} [Fintype α] [Fintype β]

noncomputable def entropy (p : Law α) : ℝ := - ∑ a, p.mass a * Real.log (p.mass a)

theorem entropy_ge_neg_log (p : Law α) {c : ℝ} (_hc : 0 < c)
    (hcap : ∀ a, p.mass a ≤ c) : -Real.log c ≤ entropy p := by
  have h : ∑ a, p.mass a * Real.log (p.mass a) ≤ Real.log c := by
    calc
      _ ≤ ∑ a, p.mass a * Real.log c := by
        apply Finset.sum_le_sum
        intro a _
        rcases (p.nonneg a).eq_or_lt with hz | hp
        · simp [← hz]
        · exact mul_le_mul_of_nonneg_left (Real.log_le_log hp (hcap a)) (p.nonneg a)
      _ = Real.log c := by rw [← Finset.sum_mul, p.total, one_mul]
  exact neg_le_neg h

noncomputable def Law.map (p : Law α) (f : α → β) : Law β := by
  classical
  refine ⟨fun b => ∑ a with f a = b, p.mass a, ?_, ?_⟩
  · intro b; exact Finset.sum_nonneg fun a _ => p.nonneg a
  · exact (Finset.sum_fiberwise Finset.univ f p.mass).trans p.total

theorem card_fixed_coordinates {N ℓ : ℕ} (e : Fin ℓ ↪ Fin N)
    (f : Fin ℓ → α) :
    Fintype.card {g : Fin N → α // ∀ i, g (e i) = f i} ≤
      Fintype.card α ^ (N - ℓ) := by
  classical
  let S : Finset (Fin N) := Finset.univ.map e
  have hS : S.card = ℓ := by simp [S]
  have he (i : Fin ℓ) : e i ∈ S := Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let restrict : {g : Fin N → α // ∀ i, g (e i) = f i} → ({x // x ∉ S} → α) :=
    fun g x => g.val x.val
  have hi : Function.Injective restrict := by
    intro g h hgh
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ S
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      exact (g.property i).trans (h.property i).symm
    · exact congr_fun hgh ⟨x, hx⟩
  have hc : Fintype.card {x // x ∉ S} = N - ℓ := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, hS]
  simpa only [Fintype.card_fun, hc] using Fintype.card_le_of_injective restrict hi

abbrev Positions (N ℓ : ℕ) := {S : Finset (Fin N) // S.card = ℓ}

noncomputable def positionMap {N ℓ : ℕ} (S : Positions N ℓ) : Fin ℓ ↪ Fin N :=
  (S.val.orderEmbOfFin S.property).toEmbedding

def Occurs {N ℓ : ℕ} (f : Fin ℓ → α) (g : Fin N → α) : Prop :=
  ∃ S : Positions N ℓ, ∀ i, g (positionMap S i) = f i

theorem card_occurs {N ℓ : ℕ} (f : Fin ℓ → α) :
    Fintype.card {g : Fin N → α // Occurs f g} ≤
      N.choose ℓ * Fintype.card α ^ (N - ℓ) := by
  classical
  let cyl (S : Positions N ℓ) : Finset (Fin N → α) :=
    {g | ∀ i, g (positionMap S i) = f i}
  have h : ({g | Occurs f g} : Finset (Fin N → α)) = Finset.univ.biUnion cyl := by
    ext g; simp [cyl, Occurs]
  rw [Fintype.card_subtype, h]
  calc
    _ ≤ ∑ S : Positions N ℓ, (cyl S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S : Positions N ℓ, Fintype.card α ^ (N - ℓ) := by
      apply Finset.sum_le_sum
      intro S _
      simpa only [cyl, ← Fintype.card_subtype] using card_fixed_coordinates (positionMap S) f
    _ = N.choose ℓ * Fintype.card α ^ (N - ℓ) := by simp [Fintype.card_finset_len]

theorem card_occurs_two {N ℓ : ℕ} (f f' : Fin ℓ → α) :
    Fintype.card {g : Fin N → α // Occurs f g ∨ Occurs f' g} ≤
      2 * N.choose ℓ * Fintype.card α ^ (N - ℓ) := by
  classical
  have h : ({g | Occurs f g ∨ Occurs f' g} : Finset (Fin N → α)) =
      ({g | Occurs f g} : Finset _) ∪ ({g | Occurs f' g} : Finset _) := by ext; simp
  rw [Fintype.card_subtype, h]
  have h1 := card_occurs f (N := N)
  have h2 := card_occurs f' (N := N)
  rw [Fintype.card_subtype] at h1 h2
  exact (Finset.card_union_le _ _).trans (by nlinarith)

noncomputable def Law.fst (p : Law (α × β)) : Law α where
  mass a := ∑ b, p.mass (a,b)
  nonneg a := Finset.sum_nonneg fun b _ => p.nonneg (a,b)
  total := by simpa only [← Fintype.sum_prod_type] using p.total

noncomputable def Law.snd (p : Law (α × β)) : Law β where
  mass b := ∑ a, p.mass (a,b)
  nonneg b := Finset.sum_nonneg fun a _ => p.nonneg (a,b)
  total := by rw [Finset.sum_comm]; simpa only [← Fintype.sum_prod_type] using p.total

theorem selected_atom_bound [Nonempty α] {N ℓ : ℕ} (hℓ : ℓ ≤ N)
    (p : Law ((Fin N → α) × (Fin ℓ → α)))
    (reverse : (Fin ℓ → α) → (Fin ℓ → α)) {C : ℝ} (hC : 0 < C)
    (hdom : ∀ g, p.fst.mass g ≤ C / (Fintype.card α : ℝ)^N)
    (hselect : ∀ g f, p.mass (g,f) ≠ 0 → Occurs f g ∨ Occurs (reverse f) g)
    (f : Fin ℓ → α) :
    p.snd.mass f ≤ 2 * C * N.choose ℓ / (Fintype.card α : ℝ)^ℓ := by
  let a : ℝ := Fintype.card α
  have ha : 0 < a := by
    dsimp [a]; exact_mod_cast (Fintype.card_pos (α := α))
  let E : Finset (Fin N → α) := {g | Occurs f g ∨ Occurs (reverse f) g}
  have hcard : (E.card : ℝ) ≤ 2 * N.choose ℓ * a^(N-ℓ) := by
    have hc := card_occurs_two f (reverse f) (N := N)
    rw [Fintype.card_subtype] at hc
    dsimp [E, a]
    exact_mod_cast hc
  have hsum : p.snd.mass f ≤ (E.card : ℝ) * (C / a^N) := by
    calc
      _ = ∑ g, p.mass (g,f) := rfl
      _ ≤ ∑ g, if g ∈ E then C / a^N else 0 := by
        apply Finset.sum_le_sum
        intro g _
        by_cases hg : g ∈ E
        · rw [ite_eq_left hg]
          exact (Finset.single_le_sum (fun b _ => p.nonneg (g,b))
            (Finset.mem_univ f)).trans (hdom g)
        · rw [ite_eq_right hg]
          have hz : p.mass (g,f) = 0 := by
            by_contra h
            exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hselect g f h⟩)
          rw [hz]
      _ = _ := by simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  calc
    _ ≤ (2 * (N.choose ℓ : ℝ) * a^(N-ℓ)) * (C / a^N) :=
      hsum.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = 2 * C * N.choose ℓ / a^ℓ := by
      have hp : a^N = a^(N-ℓ) * a^ℓ := by rw [← pow_add, Nat.sub_add_cancel hℓ]
      rw [hp]
      field_simp

theorem selected_entropy_bound [Nonempty α] {N ℓ : ℕ} (hℓ : ℓ ≤ N)
    (p : Law ((Fin N → α) × (Fin ℓ → α)))
    (reverse : (Fin ℓ → α) → (Fin ℓ → α)) {C : ℝ} (hC : 0 < C)
    (hdom : ∀ g, p.fst.mass g ≤ C / (Fintype.card α : ℝ)^N)
    (hselect : ∀ g f, p.mass (g,f) ≠ 0 → Occurs f g ∨ Occurs (reverse f) g) :
    (ℓ : ℝ) * Real.log (Fintype.card α) - Real.log (2 * C * N.choose ℓ)
      ≤ entropy p.snd := by
  have ha : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hchoose : (0 : ℝ) < N.choose ℓ := by exact_mod_cast Nat.choose_pos hℓ
  have h := entropy_ge_neg_log p.snd
    (c := 2 * C * N.choose ℓ / (Fintype.card α : ℝ)^ℓ) (by positivity)
    (selected_atom_bound hℓ p reverse hC hdom hselect)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at h
  linarith

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

def Law.AbsolutelyContinuous (p q : Law α) : Prop := ∀ a, q.mass a = 0 → p.mass a = 0

noncomputable def divergence (p q : Law α) : ℝ :=
  ∑ a, p.mass a * Real.log (p.mass a / q.mass a)

theorem Law.mass_le_one (p : Law α) (a : α) : p.mass a ≤ 1 := by
  rw [← p.total]
  exact single_le_sum (fun b hb => p.nonneg b) (mem_univ a)

theorem entropy_nonneg (p : Law α) : 0 ≤ entropy p := by
  apply neg_nonneg.mpr
  exact sum_nonpos fun a ha => mul_nonpos_of_nonneg_of_nonpos (p.nonneg a)
    (Real.log_nonpos (p.nonneg a) (p.mass_le_one a))

theorem mul_log_div_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hab : y = 0 → x = 0) : x-y ≤ x*Real.log (x/y) := by
  rcases hx.eq_or_lt with hx0 | hx0
  · rw [← hx0]; simp [hy]
  have hy0 : 0 < y := lt_of_le_of_ne hy (fun h => hx0.ne' (hab h.symm))
  have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
  rw [Real.log_div hy0.ne' hx0.ne'] at h
  rw [Real.log_div hx0.ne' hy0.ne']
  have hh := mul_le_mul_of_nonneg_left h hx0.le
  have he : x*(y/x-1) = y-x := by field_simp
  rw [he] at hh
  nlinarith

theorem divergence_nonneg (p q : Law α) (hab : p.AbsolutelyContinuous q) :
    0 ≤ divergence p q := by
  calc
    0 = ∑ a, (p.mass a-q.mass a) := by rw [sum_sub_distrib,p.total,q.total]; ring
    _ ≤ _ := sum_le_sum fun a ha => mul_log_div_ge (p.nonneg a) (q.nonneg a) (hab a)

noncomputable def Law.event (p : Law α) (E : Finset α) : ℝ := ∑ a ∈ E, p.mass a

theorem Law.event_nonneg (p : Law α) (E : Finset α) : 0 ≤ p.event E :=
  sum_nonneg fun a _ha => p.nonneg a

theorem Law.event_le_one (p : Law α) (E : Finset α) : p.event E ≤ 1 := by
  rw [← p.total]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ E) (fun a ha hE => p.nonneg a)

theorem event_transfer (p q : Law α) (hab : p.AbsolutelyContinuous q) (E : Finset α) :
    q.event E ≤ 2*(divergence p q+p.event E) := by
  have hlog2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have pointwise (a : α) : p.mass a-q.mass a + (if a ∈ E then q.mass a/2 else 0) ≤
      p.mass a*Real.log (p.mass a/q.mass a)+(if a ∈ E then p.mass a*Real.log 2 else 0) := by
    by_cases ha : a ∈ E
    · simp only [ite_eq_left ha]
      have h := mul_log_div_ge (p.nonneg a) (div_nonneg (q.nonneg a) (by norm_num : (0:ℝ) ≤ 2))
        (fun h => hab a (by linarith))
      by_cases hp : p.mass a = 0
      · simp only [hp,zero_mul,zero_sub] at h ⊢; linarith
      have hp0 := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
      have hq : q.mass a ≠ 0 := fun h => hp (hab a h)
      have he : Real.log (p.mass a/(q.mass a/2)) =
          Real.log (p.mass a/q.mass a)+Real.log 2 := by
        rw [div_div_eq_mul_div, mul_div_right_comm,
          Real.log_mul (div_ne_zero hp hq) (by norm_num)]
      rw [he] at h
      nlinarith
    · simpa only [ite_eq_right ha,add_zero] using mul_log_div_ge (p.nonneg a) (q.nonneg a) (hab a)
  have h := sum_le_sum (fun a (_ : a ∈ univ) => pointwise a)
  simp only [sum_add_distrib, sum_sub_distrib, p.total, q.total, sub_self, zero_add,
    ← sum_filter, filter_mem_eq_inter, univ_inter] at h
  rw [← sum_div, ← sum_mul] at h
  change q.event E/2 ≤ divergence p q+p.event E*Real.log 2 at h
  have hh := mul_le_mul_of_nonneg_left hlog2 (p.event_nonneg E)
  nlinarith

noncomputable def Law.prod (p : Law α) (q : Law β) : Law (α × β) where
  mass z := p.mass z.1*q.mass z.2
  nonneg z := mul_nonneg (p.nonneg z.1) (q.nonneg z.2)
  total := by rw [Fintype.sum_prod_type, ← sum_mul_sum, p.total,q.total]; ring

theorem Law.le_fst (p : Law (α × β)) (a : α) (b : β) : p.mass (a,b) ≤ p.fst.mass a :=
  single_le_sum (fun c _hc => p.nonneg (a,c)) (mem_univ b)

theorem Law.le_snd (p : Law (α × β)) (a : α) (b : β) : p.mass (a,b) ≤ p.snd.mass b :=
  single_le_sum (fun c _hc => p.nonneg (c,b)) (mem_univ a)

theorem Law.absContinuous_prod (p : Law (α × β)) : p.AbsolutelyContinuous (p.fst.prod p.snd) := by
  rintro ⟨a,b⟩ h
  rcases mul_eq_zero.mp h with h | h
  · exact le_antisymm (by simpa [h] using p.le_fst a b) (p.nonneg _)
  · exact le_antisymm (by simpa [h] using p.le_snd a b) (p.nonneg _)

noncomputable def mutualInfo (p : Law (α × β)) : ℝ :=
  entropy p.fst+entropy p.snd-entropy p

theorem mutualInfo_eq_divergence (p : Law (α × β)) :
    mutualInfo p = divergence p (p.fst.prod p.snd) := by
  have he (a : α) (b : β) : p.mass (a,b)*Real.log (p.mass (a,b)/(p.fst.mass a*p.snd.mass b)) =
      p.mass (a,b)*Real.log (p.mass (a,b))-
      p.mass (a,b)*Real.log (p.fst.mass a)-p.mass (a,b)*Real.log (p.snd.mass b) := by
    by_cases h : p.mass (a,b) = 0
    · simp [h]
    have hp := lt_of_le_of_ne (p.nonneg (a,b)) (Ne.symm h)
    have hf : 0 < p.fst.mass a := hp.trans_le (p.le_fst a b)
    have hs : 0 < p.snd.mass b := hp.trans_le (p.le_snd a b)
    rw [Real.log_div h (mul_ne_zero hf.ne' hs.ne'),Real.log_mul hf.ne' hs.ne']
    ring
  have hf : ∑ a, ∑ b, p.mass (a,b)*Real.log (p.fst.mass a) =
      ∑ a, p.fst.mass a*Real.log (p.fst.mass a) := by
    apply sum_congr rfl; intro a ha
    rw [← sum_mul]; rfl
  have hs : ∑ a, ∑ b, p.mass (a,b)*Real.log (p.snd.mass b) =
      ∑ b, p.snd.mass b*Real.log (p.snd.mass b) := by
    rw [sum_comm]
    apply sum_congr rfl; intro b hb
    rw [← sum_mul]; rfl
  unfold divergence mutualInfo entropy Law.prod
  simp only [Fintype.sum_prod_type, he, sum_sub_distrib]
  rw [hf,hs]
  ring

theorem mutualInfo_nonneg (p : Law (α × β)) : 0 ≤ mutualInfo p := by
  rw [mutualInfo_eq_divergence]
  exact divergence_nonneg _ _ p.absContinuous_prod

theorem entropy_subadditive (p : Law (α × β)) : entropy p ≤ entropy p.fst+entropy p.snd := by
  have h := mutualInfo_nonneg p
  unfold mutualInfo at h
  linarith

theorem mutualInfo_event_transfer (p : Law (α × β)) (E : Finset (α × β)) :
    (p.fst.prod p.snd).event E ≤ 2*(mutualInfo p+p.event E) := by
  rw [mutualInfo_eq_divergence]
  exact event_transfer p _ p.absContinuous_prod E

end SharpLogRamsey.Selection

namespace SharpLogRamsey.Selection
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem Law.sum_map (p : Law α) (f : α → β) (g : β → ℝ) :
    ∑ b, (p.map f).mass b*g b = ∑ a, p.mass a*g (f a) := by
  change ∑ b, (∑ a with f a = b, p.mass a)*g b = _
  simp_rw [sum_mul]
  calc
    _ = ∑ b, ∑ a with f a = b, p.mass a*g (f a) := by
      apply sum_congr rfl; intro b hb
      apply sum_congr rfl; intro a ha
      rw [(mem_filter.mp ha).2]
    _ = _ := sum_fiberwise univ f (fun a => p.mass a*g (f a))

theorem entropy_map (p : Law α) (f : α → β) :
    entropy (p.map f) = -∑ a, p.mass a*Real.log ((p.map f).mass (f a)) := by
  exact congrArg Neg.neg (p.sum_map f (fun b => Real.log ((p.map f).mass b)))

theorem Law.le_map (p : Law α) (f : α → β) (a : α) :
    p.mass a ≤ (p.map f).mass (f a) := by
  apply single_le_sum (fun b hb => p.nonneg b)
  simp

theorem entropy_map_le (p : Law α) (f : α → β) : entropy (p.map f) ≤ entropy p := by
  rw [entropy_map,entropy]
  apply neg_le_neg
  apply sum_le_sum
  intro a ha
  by_cases hz : p.mass a = 0
  · simp [hz]
  apply mul_le_mul_of_nonneg_left _ (p.nonneg a)
  exact Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm hz)) (p.le_map f a)

noncomputable def Law.condFst (p : Law (α × β)) (b : β) : Law α := by
  by_cases h : p.snd.mass b = 0
  · exact p.fst
  · refine ⟨fun a => p.mass (a,b)/p.snd.mass b, ?_, ?_⟩
    · intro a; exact div_nonneg (p.nonneg _) (p.snd.nonneg b)
    · rw [← sum_div]
      change p.snd.mass b/p.snd.mass b = 1
      exact div_self h

theorem Law.condFst_mass (p : Law (α × β)) (b : β) (h : p.snd.mass b ≠ 0) (a : α) :
    (p.condFst b).mass a = p.mass (a,b)/p.snd.mass b := by
  simp [Law.condFst,h]

theorem Law.snd_mul_condFst (p : Law (α × β)) (a : α) (b : β) :
    p.snd.mass b*(p.condFst b).mass a = p.mass (a,b) := by
  by_cases h : p.snd.mass b = 0
  · rw [h,zero_mul]
    exact (le_antisymm (by simpa [h] using p.le_snd a b) (p.nonneg _)).symm
  · rw [p.condFst_mass b h a]
    field_simp

theorem entropy_chain (p : Law (α × β)) :
    entropy p = entropy p.snd+∑ b, p.snd.mass b*entropy (p.condFst b) := by
  have pointwise (a : α) (b : β) :
      p.mass (a,b)*Real.log (p.mass (a,b)) =
      p.mass (a,b)*Real.log (p.snd.mass b)+
      p.snd.mass b*((p.condFst b).mass a*Real.log ((p.condFst b).mass a)) := by
    by_cases hp : p.mass (a,b) = 0
    · have hh := p.snd_mul_condFst a b
      rw [hp] at hh
      simp only [hp,zero_mul,zero_add]
      rw [← mul_assoc,hh,zero_mul]
    have hs : 0 < p.snd.mass b := (lt_of_le_of_ne (p.nonneg (a,b)) (Ne.symm hp)).trans_le (p.le_snd a b)
    rw [p.condFst_mass b hs.ne', Real.log_div hp hs.ne']
    field_simp
    ring
  unfold entropy
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [pointwise, sum_add_distrib, ← mul_sum, ← sum_mul]
  change -((∑ b, p.snd.mass b*Real.log (p.snd.mass b))+
    ∑ b, p.snd.mass b*∑ a, (p.condFst b).mass a*Real.log ((p.condFst b).mass a)) = _
  simp only [mul_neg, sum_neg_distrib]
  ring

theorem conditional_entropy_le (p : Law (α × β)) :
    ∑ b, p.snd.mass b*entropy (p.condFst b) ≤ entropy p.fst := by
  have h := entropy_subadditive p
  rw [entropy_chain] at h
  linarith

theorem log_sum {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i)
    (hab : ∀ i ∈ s, y i = 0 → x i = 0) :
    (∑ i ∈ s, x i)*Real.log ((∑ i ∈ s, x i)/(∑ i ∈ s, y i)) ≤
      ∑ i ∈ s, x i*Real.log (x i/y i) := by
  let X := ∑ i ∈ s, x i
  let Y := ∑ i ∈ s, y i
  have hX : 0 ≤ X := sum_nonneg hx
  have hY : 0 ≤ Y := sum_nonneg hy
  by_cases hz : X = 0
  · have hh : ∀ i ∈ s, x i = 0 := (sum_eq_zero_iff_of_nonneg hx).mp hz
    change X*Real.log (X/Y) ≤ _
    rw [hz,zero_mul]
    rw [sum_eq_zero (fun i hi => by rw [hh i hi,zero_mul])]
  have hXp : 0 < X := lt_of_le_of_ne hX (Ne.symm hz)
  have hYp : 0 < Y := by
    by_contra hn
    have hyz : Y = 0 := le_antisymm (le_of_not_gt hn) hY
    have hh := (sum_eq_zero_iff_of_nonneg hy).mp hyz
    apply hz
    apply sum_eq_zero
    intro i hi
    exact hab i hi (hh i hi)
  have hscale : 0 < X/Y := div_pos hXp hYp
  have hterm (i : ι) (hi : i ∈ s) :
      x i-y i*(X/Y) ≤ x i*Real.log (x i/y i)-x i*Real.log (X/Y) := by
    by_cases hxi : x i = 0
    · simp only [hxi,zero_mul,zero_sub,sub_zero]
      exact neg_nonpos.mpr (mul_nonneg (hy i hi) hscale.le)
    have hyi : y i ≠ 0 := fun h => hxi (hab i hi h)
    have h := mul_log_div_ge (hx i hi) (mul_nonneg (hy i hi) hscale.le)
      (fun h => hab i hi ((mul_eq_zero.mp h).resolve_right hscale.ne'))
    have he : Real.log (x i/(y i*(X/Y))) = Real.log (x i/y i)-Real.log (X/Y) := by
      rw [← div_div,Real.log_div (div_ne_zero hxi hyi) hscale.ne']
    rw [he,mul_sub] at h
    exact h
  have hsum := sum_le_sum hterm
  simp only [sum_sub_distrib, ← sum_mul] at hsum
  change X-Y*(X/Y) ≤ (∑ i ∈ s, x i*Real.log (x i/y i))-X*Real.log (X/Y) at hsum
  have he : Y*(X/Y) = X := by field_simp
  rw [he,sub_self] at hsum
  linarith

end SharpLogRamsey.Selection
end

end OAI
