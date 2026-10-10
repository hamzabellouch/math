import Mathlib

namespace OAI

section
namespace ElementaryPositivity.ShufflePolynomiality

open MvPolynomial

variable {α : Type*} [DecidableEq α]

noncomputable def diagonal (i j : α) : MvPolynomial α ℚ := X j - X i

def merge (i j x : α) : α := if x = j then i else x

noncomputable def identify (i j : α) : MvPolynomial α ℚ →ₐ[ℚ] MvPolynomial α ℚ :=
  rename (merge i j)

@[simp] lemma merge_left (i j : α) : merge i j i = i := by
  simp [merge]

@[simp] lemma merge_right (i j : α) : merge i j j = i := by
  simp [merge]

@[simp] lemma identify_diagonal (i j : α) : identify i j (diagonal i j) = 0 := by
  simp [identify, diagonal]

lemma diagonal_dvd_sub_identify (i j : α) (f : MvPolynomial α ℚ) :
    diagonal i j ∣ f - identify i j f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [identify]
  | add p q hp hq =>
    convert dvd_add hp hq using 1
    simp only [map_add]
    ring
  | mul_X p k hp =>
    have hx : diagonal i j ∣ X k - identify i j (X k) := by
      by_cases hk : k = j
      · subst k
        simp [identify, diagonal]
      · simp [identify, merge, hk]
    convert dvd_add (dvd_mul_of_dvd_left hp (X k))
      (dvd_mul_of_dvd_right hx (identify i j p)) using 1
    simp only [map_mul]
    ring

lemma diagonal_dvd_iff_identify_eq_zero (i j : α) (f : MvPolynomial α ℚ) :
    diagonal i j ∣ f ↔ identify i j f = 0 := by
  constructor
  · intro h
    simpa using map_dvd (identify i j) h
  · intro h
    simpa [h] using diagonal_dvd_sub_identify i j f

lemma ker_identify (i j : α) :
    RingHom.ker (identify i j) = Ideal.span {diagonal i j} := by
  ext f
  simp [RingHom.mem_ker, Ideal.mem_span_singleton, diagonal_dvd_iff_identify_eq_zero]

omit [DecidableEq α] in
lemma diagonal_ne_zero {i j : α} (hij : i ≠ j) : diagonal i j ≠ 0 := by
  simpa [diagonal, sub_eq_zero, MvPolynomial.X_inj] using hij.symm

lemma diagonal_prime {i j : α} (hij : i ≠ j) : Prime (diagonal i j) := by
  apply (Ideal.span_singleton_prime (diagonal_ne_zero hij)).mp
  rw [← ker_identify]
  exact RingHom.ker_isPrime _

section Ordered
variable [LinearOrder α]

lemma merge_equal_for_ordered_pair {i j a b : α} (hij : i < j) (hab : a < b)
    (h : merge i j a = merge i j b) : a = i ∧ b = j := by
  by_cases ha : a = j
  · subst a
    by_cases hb : b = j
    · subst b
      exact (lt_irrefl _ hab).elim
    · simp only [merge, ite_eq_right hb] at h
      subst b
      exact (lt_asymm hij hab).elim
  · by_cases hb : b = j
    · subst b
      simpa [merge, ha] using h
    · simp only [merge, ite_eq_right ha, ite_eq_right hb] at h
      exact (hab.ne h).elim

lemma diagonals_not_dvd {i j a b : α} (hij : i < j) (hab : a < b)
    (hne : (i,j) ≠ (a,b)) : ¬ diagonal i j ∣ diagonal a b := by
  intro h
  have hz := (diagonal_dvd_iff_identify_eq_zero i j _).mp h
  have hm : merge i j a = merge i j b := by
    have hrev : merge i j b = merge i j a := by
      simpa [identify, diagonal, sub_eq_zero, MvPolynomial.X_inj] using hz
    exact hrev.symm
  obtain ⟨ha, hb⟩ := merge_equal_for_ordered_pair hij hab hm
  exact hne (by simp [ha, hb])

lemma diagonals_isRelPrime {i j a b : α} (hij : i < j) (hab : a < b)
    (hne : (i,j) ≠ (a,b)) : IsRelPrime (diagonal i j) (diagonal a b) := by
  exact (diagonal_prime hij.ne).irreducible.isRelPrime_iff_not_dvd.mpr
    (diagonals_not_dvd hij hab hne)

theorem diagonal_powers_product_dvd (s : Finset (α × α))
    (hs : ∀ ij ∈ s, ij.1 < ij.2) (e : α × α → ℕ) (f : MvPolynomial α ℚ)
    (hf : ∀ ij ∈ s, diagonal ij.1 ij.2 ^ e ij ∣ f) :
    (∏ ij ∈ s, diagonal ij.1 ij.2 ^ e ij) ∣ f := by
  apply Finset.prod_dvd_of_isRelPrime _ hf
  intro ij hij kl hkl hne
  exact (diagonals_isRelPrime (hs ij hij) (hs kl hkl) hne).pow

end Ordered

lemma merge_swap (i j : α) : merge i j ∘ Equiv.swap i j = merge i j := by
  funext x
  by_cases hi : x = i
  · subst x
    simp
  · by_cases hj : x = j
    · subst x
      simp
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj, Function.comp_apply]

theorem diagonal_dvd_of_antisymmetric (i j : α) (f : MvPolynomial α ℚ)
    (hf : rename (Equiv.swap i j) f = -f) : diagonal i j ∣ f := by
  apply (diagonal_dvd_iff_identify_eq_zero i j f).mpr
  have h := congrArg (identify i j) hf
  simp only [identify, MvPolynomial.rename_rename, merge_swap, map_neg] at h
  have hh : (2 : ℚ) • (rename (merge i j) f) = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h
  exact (smul_eq_zero.mp hh).resolve_left (by norm_num)

theorem vandermonde_dvd [LinearOrder α] (s : Finset α) (f : MvPolynomial α ℚ)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i < j → rename (Equiv.swap i j) f = -f) :
    (∏ ij ∈ (s ×ˢ s).filter (fun ij => ij.1 < ij.2), diagonal ij.1 ij.2) ∣ f := by
  let t := (s ×ˢ s).filter (fun ij => ij.1 < ij.2)
  have ht : ∀ ij ∈ t, ij.1 < ij.2 := by
    intro ij hij
    exact (Finset.mem_filter.mp hij).2
  simpa using diagonal_powers_product_dvd t ht (fun _ => 1) f (by
    intro ij hij
    obtain ⟨hij, hlt⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
    simpa using diagonal_dvd_of_antisymmetric ij.1 ij.2 f (hf ij.1 hi ij.2 hj hlt))

section Alternation
variable {G : Type*} [Group G] [Fintype G]

noncomputable def alternate (ρ : G →* Equiv.Perm α) (χ : G →* ℤˣ)
    (f : MvPolynomial α ℚ) : MvPolynomial α ℚ :=
  ∑ g : G, (χ g : ℤ) • rename (ρ g) f

omit [DecidableEq α] in
lemma rename_alternate_of_sign_neg (ρ : G →* Equiv.Perm α) (χ : G →* ℤˣ)
    (f : MvPolynomial α ℚ) (t : G) (ht : χ t = -1) :
    rename (ρ t) (alternate ρ χ f) = -alternate ρ χ f := by
  rw [alternate, map_sum]
  calc
    (∑ g : G, rename (ρ t) ((χ g : ℤ) • rename (ρ g) f)) =
      -(∑ g : G, (χ (t*g) : ℤ) • rename (ρ (t*g)) f) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro g _
        simp only [map_zsmul, MvPolynomial.rename_rename, map_mul,
          Equiv.Perm.coe_mul, ht, neg_one_mul, Units.val_neg, neg_smul, neg_neg]
    _ = -alternate ρ χ f := by
      simpa [alternate] using congrArg Neg.neg
        (Equiv.sum_comp (Equiv.mulLeft t) (fun g => (χ g : ℤ) • rename (ρ g) f))

lemma diagonal_dvd_alternate (ρ : G →* Equiv.Perm α) (χ : G →* ℤˣ)
    (f : MvPolynomial α ℚ) (i j : α) (t : G)
    (hρ : ρ t = Equiv.swap i j) (hχ : χ t = -1) :
    diagonal i j ∣ alternate ρ χ f := by
  apply diagonal_dvd_of_antisymmetric
  rw [← hρ]
  exact rename_alternate_of_sign_neg ρ χ f t hχ

theorem same_pack_alternation_polynomial [Fintype α] [LinearOrder α]
    (f : MvPolynomial α ℚ) :
    ∃ q : MvPolynomial α ℚ,
      alternate (MonoidHom.id (Equiv.Perm α)) Equiv.Perm.sign f =
        (∏ ij ∈ (Finset.univ ×ˢ Finset.univ).filter
          (fun ij : α × α => ij.1 < ij.2), diagonal ij.1 ij.2) * q := by
  apply vandermonde_dvd Finset.univ
  intro i _ j _ hij
  apply rename_alternate_of_sign_neg (MonoidHom.id (Equiv.Perm α)) Equiv.Perm.sign
    f (Equiv.swap i j)
  exact Equiv.Perm.sign_swap hij.ne

end Alternation

section UnorderedPairs

lemma merge_equal_pair {i j a b : α} (hab : a ≠ b)
    (h : merge i j a = merge i j b) :
    (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  by_cases ha : a = j
  · subst a
    by_cases hb : b = j
    · exact (hab hb.symm).elim
    · simp only [merge, ite_eq_right hb] at h
      exact Or.inr ⟨rfl, h.symm⟩
  · by_cases hb : b = j
    · subst b
      simp only [merge, ite_eq_right ha] at h
      exact Or.inl ⟨h, rfl⟩
    · simp only [merge, ite_eq_right ha, ite_eq_right hb] at h
      exact (hab h).elim

lemma independent_diagonals {i j a b : α} (hij : i ≠ j) (hab : a ≠ b)
    (h₁ : (i,j) ≠ (a,b)) (h₂ : (i,j) ≠ (b,a)) :
    IsRelPrime (diagonal i j) (diagonal a b) := by
  apply (diagonal_prime hij).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  have hz := (diagonal_dvd_iff_identify_eq_zero i j _).mp hd
  have he : merge i j b = merge i j a := by
    simpa [identify, diagonal, sub_eq_zero, MvPolynomial.X_inj] using hz
  obtain (⟨ha,hb⟩ | ⟨ha,hb⟩) := merge_equal_pair hab he.symm
  · exact h₁ (by simp [ha, hb])
  · exact h₂ (by simp [ha, hb])

theorem pair_powers_product_dvd (s : Finset (α × α))
    (hs : ∀ ij ∈ s, ij.1 ≠ ij.2)
    (hrev : ∀ ij ∈ s, (ij.2,ij.1) ∉ s)
    (e : α × α → ℕ) (f : MvPolynomial α ℚ)
    (hf : ∀ ij ∈ s, diagonal ij.1 ij.2 ^ e ij ∣ f) :
    (∏ ij ∈ s, diagonal ij.1 ij.2 ^ e ij) ∣ f := by
  apply Finset.prod_dvd_of_isRelPrime _ hf
  intro ij hij kl hkl hne
  apply (independent_diagonals (hs ij hij) (hs kl hkl) hne _).pow
  intro hr
  apply hrev ij hij
  have heq : (ij.2,ij.1) = kl := by
    simpa only [Prod.swap, Prod.eta] using congrArg Prod.swap hr
  rwa [heq]

end UnorderedPairs

section Packs

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (V : I → Type*) [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]

def packAction : (∀ i, Equiv.Perm (V i)) →* Equiv.Perm (Σ i, V i) where
  toFun g := Equiv.sigmaCongrRight g
  map_one' := by apply Equiv.ext; rintro ⟨i,a⟩; rfl
  map_mul' g h := by apply Equiv.ext; rintro ⟨i,a⟩; rfl

def packSign (E : I → Prop) [DecidablePred E] :
    (∀ i, Equiv.Perm (V i)) →* ℤˣ where
  toFun g := ∏ i, if E i then Equiv.Perm.sign (g i) else 1
  map_one' := by simp
  map_mul' g h := by
    simp only [Pi.mul_apply, map_mul]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp

omit [Fintype I] [∀ i, Fintype (V i)] in
lemma packAction_transposition (i : I) (a b : V i) :
    packAction V (Function.update 1 i (Equiv.swap a b)) =
      Equiv.swap (⟨i,a⟩ : Σ i,V i) ⟨i,b⟩ := by
  apply Equiv.ext
  rintro ⟨j,c⟩
  by_cases hj : j = i
  · subst j
    change (⟨i, (Function.update (1 : ∀ i, Equiv.Perm (V i)) i (Equiv.swap a b)) i c⟩ : Σ i,V i) = _
    rw [Function.update_self]
    simp only [Equiv.swap_apply_def, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    split_ifs <;> rfl
  · change (⟨j, (Function.update (1 : ∀ i, Equiv.Perm (V i)) i (Equiv.swap a b)) j c⟩ : Σ i,V i) = _
    rw [Function.update_of_ne hj]
    exact (Equiv.swap_apply_of_ne_of_ne
      (fun h => hj (congrArg Sigma.fst h))
      (fun h => hj (congrArg Sigma.fst h))).symm

lemma packSign_transposition (E : I → Prop) [DecidablePred E]
    (i : I) (a b : V i) (hi : E i) (hab : a ≠ b) :
    packSign V E (Function.update 1 i (Equiv.swap a b)) = -1 := by
  change (∏ j, if E j then
    Equiv.Perm.sign ((Function.update (1 : ∀ i, Equiv.Perm (V i)) i
      (Equiv.swap a b)) j) else 1) = -1
  rw [Fintype.prod_eq_single i]
  · simp [hi, Equiv.Perm.sign_swap hab]
  · intro j hji
    simp [Function.update_of_ne hji]

lemma pack_alternate_diagonal (E : I → Prop) [DecidablePred E]
    (f : MvPolynomial (Σ i,V i) ℚ) (i : I) (a b : V i)
    (hi : E i) (hab : a ≠ b) :
    diagonal ⟨i,a⟩ ⟨i,b⟩ ∣ alternate (packAction V) (packSign V E) f := by
  apply diagonal_dvd_alternate (packAction V) (packSign V E) f
    ⟨i,a⟩ ⟨i,b⟩ (Function.update 1 i (Equiv.swap a b))
  · exact packAction_transposition V i a b
  · exact packSign_transposition V E i a b hi hab

noncomputable def packPairs (E : I → Prop) [DecidablePred E] :
    Finset ((Σ i,V i) × (Σ i,V i)) := by
  classical
  exact (Finset.univ ×ˢ Finset.univ).filter (fun ij =>
    ij.1.1 = ij.2.1 ∧ E ij.1.1 ∧
      Fintype.equivFin (Σ i,V i) ij.1 < Fintype.equivFin (Σ i,V i) ij.2)

noncomputable def packVandermonde (E : I → Prop) [DecidablePred E] :
    MvPolynomial (Σ i,V i) ℚ :=
  ∏ ij ∈ packPairs V E, diagonal ij.1 ij.2

theorem pack_alternation_polynomial (E : I → Prop) [DecidablePred E]
    (f : MvPolynomial (Σ i,V i) ℚ) :
    ∃ q : MvPolynomial (Σ i,V i) ℚ,
      alternate (packAction V) (packSign V E) f = packVandermonde V E * q := by
  classical
  change packVandermonde V E ∣ alternate (packAction V) (packSign V E) f
  unfold packVandermonde
  have hi (ij) (hij : ij ∈ packPairs V E) :
      ij.1.1 = ij.2.1 ∧ E ij.1.1 ∧
      Fintype.equivFin (Σ i,V i) ij.1 < Fintype.equivFin (Σ i,V i) ij.2 :=
    (Finset.mem_filter.mp hij).2
  have hn (ij) (hij : ij ∈ packPairs V E) : ij.1 ≠ ij.2 := by
    intro h
    exact (hi ij hij).2.2.ne (congrArg (Fintype.equivFin (Σ i,V i)) h)
  have hr (ij) (hij : ij ∈ packPairs V E) : (ij.2,ij.1) ∉ packPairs V E := by
    intro hrev
    exact lt_asymm (hi ij hij).2.2 (hi _ hrev).2.2
  simpa using pair_powers_product_dvd (packPairs V E) hn hr (fun _ => 1)
    (alternate (packAction V) (packSign V E) f) (by
      rintro ⟨⟨i,a⟩,⟨j,b⟩⟩ hij
      have he : i = j := (hi _ hij).1
      subst j
      have hab : a ≠ b := by
        intro h
        exact hn _ hij (by cases h; rfl)
      simpa using pack_alternate_diagonal V E f i a b (hi _ hij).2.1 hab)

end Packs

section FinPacks
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (n : I → ℕ) (E : I → Prop) [DecidablePred E]

noncomputable def naturalVandermonde : MvPolynomial (Σ i, Fin (n i)) ℚ :=
  ∏ i, if E i then (Matrix.vandermonde (fun a : Fin (n i) =>
    (X ⟨i,a⟩ : MvPolynomial (Σ i, Fin (n i)) ℚ))).det else 1

def finPackPair (a : Σ i, Fin (n i) × Fin (n i)) :
    (Σ i, Fin (n i)) × (Σ i, Fin (n i)) :=
  (⟨a.1,a.2.1⟩, ⟨a.1,a.2.2⟩)

omit [Fintype I] [DecidableEq I] in
lemma finPackPair_injective : Function.Injective (finPackPair n) := by
  rintro ⟨i,a,b⟩ ⟨j,c,d⟩ h
  have hij : i = j := congrArg (fun p => p.1.1) h
  subst j
  simp only [finPackPair, Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  obtain ⟨rfl,rfl⟩ := h
  rfl

noncomputable def naturalPairs : Finset (Σ i, Fin (n i) × Fin (n i)) :=
  Finset.univ.sigma (fun i => (Finset.univ ×ˢ Finset.univ).filter
    (fun ab : Fin (n i) × Fin (n i) => E i ∧ ab.1 < ab.2))

omit [DecidableEq I] in
lemma naturalVandermonde_product : naturalVandermonde n E =
    ∏ a ∈ naturalPairs n E, diagonal (finPackPair n a).1 (finPackPair n a).2 := by
  rw [naturalVandermonde, naturalPairs, Finset.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : E i
  · simp only [hi, ite_true, Matrix.det_vandermonde, true_and]
    rw [Finset.prod_filter, Finset.prod_product]
    apply Finset.prod_congr rfl
    intro a _
    simp only [← Finset.filter_lt_eq_Ioi, Finset.prod_filter, diagonal, finPackPair]
  · simp [hi]

omit [DecidableEq I] in
lemma rename_naturalVandermonde (g : ∀ i, Equiv.Perm (Fin (n i))) :
    rename (packAction (fun i => Fin (n i)) g) (naturalVandermonde n E) =
      (packSign (fun i => Fin (n i)) E g : ℤ) • naturalVandermonde n E := by
  rw [naturalVandermonde, map_prod]
  simp only [packSign, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod,
    zsmul_eq_mul, Int.cast_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : E i
  · simp only [hi, ite_true]
    change ((rename (packAction (fun i => Fin (n i)) g)).toRingHom)
      (Matrix.vandermonde (fun a : Fin (n i) => X ⟨i,a⟩)).det = _
    rw [RingHom.map_det]
    have hm : (rename (packAction (fun i => Fin (n i)) g)).toRingHom.mapMatrix
        (Matrix.vandermonde (fun a : Fin (n i) =>
          (X ⟨i,a⟩ : MvPolynomial (Σ i, Fin (n i)) ℚ))) =
        (Matrix.vandermonde (fun a : Fin (n i) =>
          (X ⟨i,a⟩ : MvPolynomial (Σ i, Fin (n i)) ℚ))).submatrix (g i) id := by
      ext a b
      simp [Matrix.vandermonde, Matrix.submatrix_apply, packAction]
    rw [hm, Matrix.det_permute]
  · simp [hi]

lemma naturalVandermonde_dvd_alternate (f : MvPolynomial (Σ i, Fin (n i)) ℚ) :
    naturalVandermonde n E ∣
      alternate (packAction (fun i => Fin (n i))) (packSign (fun i => Fin (n i)) E) f := by
  rw [naturalVandermonde_product]
  apply Finset.prod_dvd_of_isRelPrime
  · rintro ⟨i,a,b⟩ hi ⟨j,c,d⟩ hj hne
    change (⟨i,(a,b)⟩ : Σ i, Fin (n i) × Fin (n i)) ∈ naturalPairs n E at hi
    change (⟨j,(c,d)⟩ : Σ i, Fin (n i) × Fin (n i)) ∈ naturalPairs n E at hj
    simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
      Finset.mem_product, true_and] at hi hj
    have hab : (⟨i,a⟩ : Σ i,Fin (n i)) ≠ ⟨i,b⟩ := by simpa using hi.2.ne
    have hcd : (⟨j,c⟩ : Σ i,Fin (n i)) ≠ ⟨j,d⟩ := by simpa using hj.2.ne
    apply independent_diagonals hab hcd
    · exact fun h => hne (finPackPair_injective n h)
    · intro hr
      have hij : i = j := congrArg (fun p => p.1.1) hr
      subst j
      simp only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hr
      obtain ⟨rfl,rfl⟩ := hr
      exact lt_asymm hi.2 hj.2
  · rintro ⟨i,a,b⟩ ha
    simp only [naturalPairs, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
      Finset.mem_product, true_and] at ha
    exact pack_alternate_diagonal (fun i => Fin (n i)) E f i a b ha.1 ha.2.ne

end FinPacks

section FractionRename
variable {α : Type*} [DecidableEq α]

end FractionRename
end ElementaryPositivity.ShufflePolynomiality
end

end OAI
