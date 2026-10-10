import OAI.Combinatorics.MatchingPSD.EdgeProducts

namespace OAI

universe u_1 u_2

namespace MatchingSmoothing
abbrev Pairing (α : Type u_1) :=
  {M : Equiv.Perm α // Function.Involutive M ∧ ∀ a, M a ≠ a}

namespace Pairing
variable {α : Type u_2}

@[ext] lemma ext {M N : Pairing α} (h : ∀ a, M.1 a = N.1 a) : M = N :=
  Subtype.ext (Equiv.ext h)

@[simp] lemma partner_partner (M : Pairing α) (a : α) : M.1 (M.1 a) = a := M.2.1 a

lemma partner_ne (M : Pairing α) (a : α) : M.1 a ≠ a := M.2.2 a

@[simp] lemma partner_eq_iff (M : Pairing α) (a b : α) : M.1 a = b ↔ M.1 b = a := by
  constructor <;> intro h <;> rw [← h, partner_partner]

def relabel (p : Equiv.Perm α) (M : Pairing α) : Pairing α :=
  ⟨p * M.1 * p⁻¹, by
    constructor
    · intro a
      simp [Equiv.Perm.mul_apply]
    · intro a h
      apply M.partner_ne (p⁻¹ a)
      simpa using
        congrArg (fun b => p⁻¹ b) h⟩

@[simp] lemma relabel_apply (p : Equiv.Perm α) (M : Pairing α) (a : α) :
    (relabel p M).1 a = p (M.1 (p⁻¹ a)) := rfl

@[simp] lemma relabel_one (M : Pairing α) : relabel 1 M = M := by ext a; simp

@[simp] lemma relabel_mul (p q : Equiv.Perm α) (M : Pairing α) :
    relabel (p * q) M = relabel p (relabel q M) := by
  ext a
  simp [Equiv.Perm.mul_apply]

def relabelEquiv (p : Equiv.Perm α) : Equiv.Perm (Pairing α) where
  toFun := relabel p
  invFun := relabel p⁻¹
  left_inv M := by rw [← relabel_mul, inv_mul_cancel, relabel_one]
  right_inv M := by rw [← relabel_mul, mul_inv_cancel, relabel_one]

def act (p : Equiv.Perm α) : (Pairing α → ℝ) ≃ₗ[ℝ] (Pairing α → ℝ) where
  toFun f M := f (relabel p⁻¹ M)
  invFun f M := f (relabel p M)
  left_inv f := by ext M; simp [← relabel_mul]
  right_inv f := by ext M; simp [← relabel_mul]
  map_add' f g := rfl
  map_smul' c f := rfl

@[simp] lemma act_apply (p : Equiv.Perm α) (f : Pairing α → ℝ) (M : Pairing α) :
    act p f M = f (relabel p⁻¹ M) := rfl

@[simp] lemma act_mul (p q : Equiv.Perm α) (f : Pairing α → ℝ) :
    act (p * q) f = act p (act q f) := by
  ext M
  simp [← relabel_mul]

@[simp] lemma act_one (f : Pairing α → ℝ) : act 1 f = f := by ext M; simp

@[simp] lemma partner_sq (M : Pairing α) : M.1 ^ 2 = 1 := by
  ext a
  simp [pow_two, Equiv.Perm.mul_apply]

lemma cycleType_eq [Fintype α] [DecidableEq α] (M N : Pairing α) :
    M.1.cycleType = N.1.cycleType := by
  have hm := Equiv.Perm.cycleType_of_pow_prime_eq_one M.partner_sq
  have hn := Equiv.Perm.cycleType_of_pow_prime_eq_one N.partner_sq
  have hsum (P : Pairing α) : P.1.cycleType.sum = Fintype.card α := by
    rw [Equiv.Perm.sum_cycleType]
    have hs : P.1.support = Finset.univ := by
      ext a
      simp [Equiv.Perm.mem_support, P.partner_ne]
    rw [hs, Finset.card_univ]
  have hc : M.1.cycleType.card = N.1.cycleType.card := by
    have he := (hsum M).trans (hsum N).symm
    rw [hm, hn] at he
    simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at he
    omega
  rw [hm, hn, hc]

lemma exists_relabel [Fintype α] [DecidableEq α] (M N : Pairing α) :
    ∃ p : Equiv.Perm α, relabel p M = N := by
  have h := Equiv.Perm.isConj_iff_cycleType_eq.mpr (cycleType_eq M N)
  rcases isConj_iff.mp h with ⟨p, hp⟩
  refine ⟨p, Subtype.ext ?_⟩
  exact hp

@[simp] lemma relabel_swap_partner [DecidableEq α] (M : Pairing α) (a : α) :
    relabel (Equiv.swap a (M.1 a)) M = M := by
  apply Subtype.ext
  change Equiv.swap a (M.1 a) * M.1 * (Equiv.swap a (M.1 a))⁻¹ = M.1
  have hc : M.1 * Equiv.swap a (M.1 a) = Equiv.swap a (M.1 a) * M.1 := by
    rw [Equiv.mul_swap_eq_swap_mul, partner_partner, Equiv.swap_comm]
  rw [← hc, mul_inv_cancel_right]

lemma exists_internal_edge_compl [Fintype α] [DecidableEq α]
    (M : Pairing α) (U : Finset α) (hU : 2 * U.card < Fintype.card α) :
    ∃ a, a ∉ U ∧ M.1 a ∉ U := by
  by_contra! h
  have hinj : Set.InjOn M.1 (↑Uᶜ : Set α) := M.1.injective.injOn
  have hmaps : ∀ a ∈ Uᶜ, M.1 a ∈ U := by simpa using h
  have hc := Finset.card_le_card_of_injOn M.1 hmaps hinj
  rw [Finset.card_compl] at hc
  have hu := Finset.card_le_univ U
  omega

lemma no_sign_on_complement [Fintype α] [DecidableEq α]
    (U : Finset α) (hU : 2 * U.card < Fintype.card α)
    (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = -f) : f = 0 := by
  ext M
  obtain ⟨a, ha, hma⟩ := exists_internal_edge_compl M U hU
  have he := congrFun (hf a ha (M.1 a) hma (M.partner_ne a).symm) M
  simp only [act_apply, Equiv.swap_inv, relabel_swap_partner, Pi.neg_apply] at he
  dsimp
  linarith

def SameInternal (U : Finset α) (M N : Pairing α) : Prop :=
  ∀ a ∈ U, ∀ b ∈ U, M.1 a = b ↔ N.1 a = b

lemma align_partners [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α) (hMN : SameInternal U M N) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧
      ∀ a ∈ U, (relabel p M).1 a = N.1 a := by
  classical
  let S := {a : α // a ∈ U ∧ M.1 a ∉ U}
  have hnout (a : S) : N.1 a.1 ∉ U := by
    intro hn
    have he := (hMN a.1 a.2.1 (N.1 a.1) hn).mpr rfl
    exact a.2.2 (he.symm ▸ hn)
  let f : U ⊕ S → α := Sum.elim (fun a => a.1) (fun a => M.1 a.1)
  let g : U ⊕ S → α := Sum.elim (fun a => a.1) (fun a => N.1 a.1)
  have hf : Function.Injective f := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.1 = M.1 b.1 at h
        exact False.elim (b.2.2 (h ▸ a.2))
    | inr a =>
      cases y with
      | inl b =>
        change M.1 a.1 = b.1 at h
        exact False.elim (a.2.2 (h.symm ▸ b.2))
      | inr b => exact congrArg Sum.inr (Subtype.ext (M.1.injective h))
  have hg : Function.Injective g := by
    intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.1 = N.1 b.1 at h
        exact False.elim (hnout b (h ▸ a.2))
    | inr a =>
      cases y with
      | inl b =>
        change N.1 a.1 = b.1 at h
        exact False.elim (hnout a (h.symm ▸ b.2))
      | inr b => exact congrArg Sum.inr (Subtype.ext (N.1.injective h))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hfix (a : α) (ha : a ∈ U) : p a = a := hp (Sum.inl ⟨a, ha⟩)
  have hpart (a : α) (ha : a ∈ U) : p (M.1 a) = N.1 a := by
    by_cases hm : M.1 a ∈ U
    · rw [hfix _ hm]
      exact ((hMN a ha (M.1 a) hm).mp rfl).symm
    · exact hp (Sum.inr ⟨a, ha, hm⟩)
  refine ⟨p, hfix, ?_⟩
  intro a ha
  have hi : p⁻¹ a = a := by
    calc
      p⁻¹ a = p⁻¹ (p a) := congrArg (fun b => p⁻¹ b) (hfix a ha).symm
      _ = a := by simp
  simp only [relabel_apply, hi, hpart a ha]

def restrict (M : Pairing α) (S : Finset α)
    (hS : ∀ a, M.1 a ∈ S ↔ a ∈ S) : Pairing S :=
  ⟨M.1.subtypePerm hS, by
    constructor
    · intro a; apply Subtype.ext; exact M.partner_partner a.1
    · intro a h; exact M.partner_ne a.1 (congrArg Subtype.val h)⟩

@[simp] lemma restrict_apply (M : Pairing α) (S : Finset α)
    (hS : ∀ a, M.1 a ∈ S ↔ a ∈ S) (a : S) :
    ((restrict M S hS).1 a).1 = M.1 a.1 := rfl

def closure [DecidableEq α] (M : Pairing α) (U : Finset α) : Finset α :=
  U ∪ U.image M.1

lemma mem_closure [DecidableEq α] (M : Pairing α) (U : Finset α) (a : α) :
    a ∈ closure M U ↔ a ∈ U ∨ M.1 a ∈ U := by
  simp only [closure, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa using hb)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨M.1 a, h, M.partner_partner a⟩

lemma stable_closure [DecidableEq α] (M : Pairing α) (U : Finset α) (a : α) :
    M.1 a ∈ closure M U ↔ a ∈ closure M U := by
  simp only [mem_closure, partner_partner, or_comm]

lemma agree_on_closure [DecidableEq α] (U : Finset α) (M N : Pairing α)
    (h : ∀ a ∈ U, M.1 a = N.1 a) :
    ∀ a ∈ closure N U, M.1 a = N.1 a := by
  intro a ha
  rcases (mem_closure N U a).mp ha with ha | ha
  · exact h a ha
  · apply (M.partner_eq_iff a (N.1 a)).mpr
    rw [h _ ha, partner_partner]

lemma align_remaining [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α)
    (hMN : ∀ a ∈ U, M.1 a = N.1 a) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧ relabel p M = N := by
  classical
  let S := (closure N U)ᶜ
  have hagree := agree_on_closure U M N hMN
  have hcM : ∀ a ∈ closure N U, M.1 a ∈ closure N U := by
    intro a ha
    rw [hagree a ha]
    exact (stable_closure N U a).mpr ha
  have hcMi (a : α) : M.1 a ∈ closure N U ↔ a ∈ closure N U := by
    constructor
    · intro ha
      simpa using hcM (M.1 a) ha
    · exact hcM a
  have hM (a : α) : M.1 a ∈ S ↔ a ∈ S := by
    simp only [S, Finset.mem_compl, hcMi]
  have hN (a : α) : N.1 a ∈ S ↔ a ∈ S := by
    simp only [S, Finset.mem_compl, stable_closure]
  obtain ⟨q, hq⟩ := exists_relabel (restrict M S hM) (restrict N S hN)
  let p := q.extendDomain (Equiv.refl S)
  have hpin (a : α) (ha : a ∈ S) : p a = (q ⟨a, ha⟩).1 := by
    simpa [p] using Equiv.Perm.extendDomain_apply_subtype q (Equiv.refl S) ha
  have hpout (a : α) (ha : a ∉ S) : p a = a := by
    exact Equiv.Perm.extendDomain_apply_not_subtype q (Equiv.refl S) ha
  have hinter (a : α) : p (M.1 a) = N.1 (p a) := by
    by_cases ha : a ∈ S
    · have hh := congrArg (fun P : Pairing S => (P.1 (q ⟨a, ha⟩)).1) hq
      rw [hpin _ ((hM a).mpr ha), hpin a ha]
      simpa [restrict] using hh
    · have hma : M.1 a ∉ S := by simpa only [hM] using ha
      rw [hpout _ hma, hpout _ ha]
      exact hagree a (by simpa only [S, Finset.mem_compl, not_not] using ha)
  refine ⟨p, ?_, ?_⟩
  · intro a ha
    apply hpout
    simp only [S, Finset.mem_compl, not_not]
    exact (mem_closure N U a).mpr (Or.inl ha)
  · ext a
    obtain ⟨b, rfl⟩ := p.surjective a
    simpa using hinter b

lemma exists_relabel_fixing [Fintype α] [DecidableEq α]
    (U : Finset α) (M N : Pairing α) (hMN : SameInternal U M N) :
    ∃ p : Equiv.Perm α, (∀ a ∈ U, p a = a) ∧ relabel p M = N := by
  obtain ⟨p, hp, hpM⟩ := align_partners U M N hMN
  obtain ⟨q, hq, hqM⟩ := align_remaining U (relabel p M) N hpM
  refine ⟨q * p, ?_, ?_⟩
  · intro a ha
    simp only [Equiv.Perm.mul_apply, hp a ha, hq a ha]
  · rw [relabel_mul, hqM]

lemma extend_swap [DecidableEq α] (S : Finset α) (x y : S) :
    (Equiv.swap x y).extendDomain (Equiv.refl S) = Equiv.swap x.1 y.1 := by
  ext a
  by_cases ha : a ∈ S
  · rw [Equiv.Perm.extendDomain_apply_subtype _ _ ha]
    by_cases hx : a = x.1 <;> by_cases hy : a = y.1 <;>
      simp [Equiv.swap_apply_def, Subtype.ext_iff, hx, hy]
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ ha]
    have hx : a ≠ x.1 := by rintro rfl; exact ha x.2
    have hy : a ≠ y.1 := by rintro rfl; exact ha y.2
    simp [Equiv.swap_apply_def, hx, hy]

lemma invariant_of_swap_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f)
    (p : Equiv.Perm α) (hp : ∀ a ∈ U, p a = a) : act p f = f := by
  classical
  let S := Uᶜ
  have hU (a : α) : p a ∈ U ↔ a ∈ U := by
    constructor
    · intro h
      have he : p a = a := p.injective (hp (p a) h)
      simpa [he] using h
    · intro h; simpa [hp a h] using h
  have hS (a : α) : p a ∈ S ↔ a ∈ S := by simp only [S, Finset.mem_compl, hU]
  have hind (q : Equiv.Perm S) : act (q.extendDomain (Equiv.refl S)) f = f := by
    induction q using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul q x y hxy ih =>
      rw [← Equiv.Perm.extendDomain_mul, act_mul, ih, extend_swap]
      apply hf x.1 (by simpa only [S, Finset.mem_compl] using x.2)
        y.1 (by simpa only [S, Finset.mem_compl] using y.2)
      exact fun h => hxy (Subtype.ext h)
  have he : (p.subtypePerm hS).extendDomain (Equiv.refl S) = p := by
    ext a
    by_cases ha : a ∈ S
    · rw [Equiv.Perm.extendDomain_apply_subtype _ _ ha]
      rfl
    · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ ha]
      exact (hp a (by simpa only [S, Finset.mem_compl, not_not] using ha)).symm
  rw [← he]
  exact hind _

lemma sameInternal_value_of_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f)
    (M N : Pairing α) (hMN : SameInternal U M N) : f M = f N := by
  obtain ⟨p, hp, hpM⟩ := exists_relabel_fixing U M N hMN
  have he := congrFun (invariant_of_swap_invariant U f hf p hp) N
  rw [act_apply, ← hpM, ← relabel_mul, inv_mul_cancel, relabel_one] at he
  simpa only [hpM] using he

noncomputable def edgeCoord (e : α × α) (M : Pairing α) : ℝ := by
  classical
  exact if M.1 e.1 = e.2 then 1 else 0

noncomputable def internalPattern [DecidableEq α] (U : Finset α)
    (M : Pairing α) : Finset (α × α) :=
  (U ×ˢ U).filter fun e => M.1 e.1 = e.2

lemma internalPattern_eq_iff [DecidableEq α] (U : Finset α) (M N : Pairing α) :
    internalPattern U M = internalPattern U N ↔ SameInternal U M N := by
  constructor
  · intro h a ha b hb
    have he := Finset.ext_iff.mp h (a,b)
    simpa [internalPattern, ha, hb] using he
  · intro h
    ext ⟨a,b⟩
    simp only [internalPattern, Finset.mem_filter, Finset.mem_product]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp_all [SameInternal]

lemma internal_indicator_mem_lowDegree [Fintype α] [DecidableEq α]
    (U : Finset α) (M : Pairing α) :
    (fun N => if internalPattern U N = internalPattern U M then (1 : ℝ) else 0)
      ∈ lowDegree edgeCoord (U.card * U.card) := by
  classical
  have h := boolean_pattern_mem_lowDegree edgeCoord (U ×ˢ U) (internalPattern U M)
  rw [Finset.card_product] at h
  convert h using 1
  ext N
  rw [Finset.prod_apply]
  have hf (e : α × α) (he : e ∈ U ×ˢ U) :
      (if e ∈ internalPattern U M then edgeCoord e else 1 - edgeCoord e) N =
        (if (N.1 e.1 = e.2 ↔ M.1 e.1 = e.2) then (1 : ℝ) else 0) := by
    by_cases hm : M.1 e.1 = e.2 <;> by_cases hn : N.1 e.1 = e.2 <;>
      simp [internalPattern, he, hm, hn, edgeCoord]
  rw [Finset.prod_congr rfl hf, Finset.prod_boole]
  congr 1
  rw [internalPattern_eq_iff]
  simp only [SameInternal, Finset.mem_product, Prod.forall]
  aesop

lemma mem_lowDegree_of_swap_invariant [Fintype α] [DecidableEq α]
    (U : Finset α) (f : Pairing α → ℝ)
    (hf : ∀ a ∉ U, ∀ b ∉ U, a ≠ b → act (Equiv.swap a b) f = f) :
    f ∈ lowDegree edgeCoord (U.card * U.card) := by
  apply mem_of_fiber_indicators (internalPattern U) f
  · intro M N hMN
    exact sameInternal_value_of_invariant U f hf M N
      ((internalPattern_eq_iff U M N).mp hMN)
  · exact internal_indicator_mem_lowDegree U

lemma exists_perm_fixing_pair [Fintype α] [DecidableEq α]
    (U : Finset α) {a b c d : α} (ha : a ∉ U) (hb : b ∉ U)
    (hc : c ∉ U) (hd : d ∉ U) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ p : Equiv.Perm α, (∀ u ∈ U, p u = u) ∧ p a = c ∧ p b = d := by
  let f : U ⊕ Bool → α := Sum.elim Subtype.val (fun i => cond i b a)
  let g : U ⊕ Bool → α := Sum.elim Subtype.val (fun i => cond i d c)
  have hi {x y : α} (hx : x ∉ U) (hy : y ∉ U) (hxy : x ≠ y) :
      Function.Injective (Sum.elim (Subtype.val : U → α) (fun i : Bool => cond i y x)) := by
    rw [Sum.elim_injective]
    refine ⟨Subtype.val_injective, ?_, ?_⟩
    · intro i j h
      cases i <;> cases j <;> simp_all
    · intro u i
      cases i <;> simp only [Bool.cond_false, Bool.cond_true]
      · intro h; exact hx (h ▸ u.2)
      · intro h; exact hy (h ▸ u.2)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair f g (hi ha hb hab) (hi hc hd hcd)
  exact ⟨p, fun u hu => hp (Sum.inl ⟨u, hu⟩), hp (Sum.inr false), hp (Sum.inr true)⟩

lemma act_swap_involution [DecidableEq α] (a b : α) (f : Pairing α → ℝ) :
    act (Equiv.swap a b) (act (Equiv.swap a b) f) = f := by
  rw [← act_mul, Equiv.swap_mul_self, act_one]

lemma act_swap_conj [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (f : Pairing α → ℝ) :
    act (Equiv.swap (p a) (p b)) (act p f) = act p (act (Equiv.swap a b) f) := by
  rw [← act_mul, ← act_mul, Equiv.mul_swap_eq_swap_mul]

lemma act_commute_of_swap_fixed [DecidableEq α] (p : Equiv.Perm α) (a b : α)
    (ha : p a = a) (hb : p b = b) (f : Pairing α → ℝ) :
    act (Equiv.swap a b) (act p f) = act p (act (Equiv.swap a b) f) := by
  simpa only [ha, hb] using act_swap_conj p a b f

end Pairing
end MatchingSmoothing

end OAI
