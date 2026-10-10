import OAI.MathematicalPhysics.Heisenberg.StableSections

namespace OAI

section
noncomputable section
open scoped Classical Topology
open Set Filter Metric
open scoped ComplexConjugate

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def pairAssignment (i j : σ) (z w : ℂ) (k : σ) : ℂ :=
  if k = i then z else if k = j then w else 1

omit [Fintype σ] in
lemma prod_pairAssignment (A : Finset σ) (i j : σ) (hij : i ≠ j) (z w : ℂ) :
    (∏ k ∈ A, pairAssignment i j z w k) =
      (if i ∈ A then z else 1) * (if j ∈ A then w else 1) := by
  have he (k : σ) : pairAssignment i j z w k =
      (if k = i then z else 1) * (if k = j then w else 1) := by
    by_cases hi : k = i
    · subst k; simp [pairAssignment, hij]
    · by_cases hj : k = j <;> simp [pairAssignment, hi, hj, Ne.symm hij]
  simp_rw [he, Finset.prod_mul_distrib]
  simp

lemma ofReal_presence (μ : Finset σ → ℝ) (B : Finset σ) :
    (presence μ B : ℂ) = ∑ A : Finset σ, if B ⊆ A then (μ A : ℂ) else 0 := by
  simp [presence, apply_ite]

lemma eval_presencePolynomial_pair (μ : Finset σ → ℝ) (B : Finset σ)
    (i j : σ) (hij : i ≠ j) (hi : i ∉ B) (hj : j ∉ B) (z w : ℂ) :
    MvPolynomial.eval (pairAssignment i j z w) (presencePolynomial μ B) =
      (presence μ B : ℂ) + (presence μ (insert i B) : ℂ) * (z - 1) +
      (presence μ (insert j B) : ℂ) * (w - 1) +
      (presence μ (insert i (insert j B)) : ℂ) * (z - 1) * (w - 1) := by
  simp only [presencePolynomial, map_sum, apply_ite, map_mul, MvPolynomial.eval_C,
    map_zero, subsetMonomial, MvPolynomial.eval_prod, MvPolynomial.eval_X]
  simp_rw [prod_pairAssignment _ i j hij z w]
  simp_rw [ofReal_presence, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hB : B ⊆ A
  · by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;>
      simp [Finset.insert_subset_iff, Finset.mem_sdiff, hi, hj, hB, hiA, hjA] <;> ring
  · have hBi : ¬ insert i B ⊆ A := fun h => hB (Finset.Subset.trans (Finset.subset_insert _ _) h)
    have hBj : ¬ insert j B ⊆ A := fun h => hB (Finset.Subset.trans (Finset.subset_insert _ _) h)
    have hBij : ¬ insert i (insert j B) ⊆ A := fun h => hBj (Finset.Subset.trans (Finset.subset_insert _ _) h)
    simp [hB, hBi, hBj, hBij]

lemma presence_mono {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    {B C : Finset σ} (hBC : B ⊆ C) : presence μ C ≤ presence μ B := by
  unfold presence
  apply Finset.sum_le_sum
  intro A _
  by_cases hC : C ⊆ A
  · simp [hC, Finset.Subset.trans hBC hC]
  · simp only [ite_eq_right hC]
    split_ifs
    · exact hμ A
    · exact le_rfl

theorem presence_pair_inequality {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    (hs : Stable (presencePolynomial μ ∅)) (B : Finset σ) (i j : σ)
    (hij : i ≠ j) (hi : i ∉ B) (hj : j ∉ B) :
    presence μ (insert i (insert j B)) * presence μ B ≤
      presence μ (insert i B) * presence μ (insert j B) := by
  by_cases hB : presence μ B = 0
  · rw [hB, mul_zero]
    exact mul_nonneg (presence_nonneg hμ _) (presence_nonneg hμ _)
  have hBpos : 0 < presence μ B := lt_of_le_of_ne (presence_nonneg hμ B) (Ne.symm hB)
  have hsB : Stable (presencePolynomial μ B) :=
    (stable_presencePolynomial hs B).resolve_left (presence_polynomial_ne_zero hBpos)
  let f : σ → Option Bool := fun k => if k = i then some false else if k = j then some true else none
  let q := boundarySection (presencePolynomial μ B) f (fun _ => (1 : ℂ))
  have evalq (z w : ℂ) :
      MvPolynomial.eval (fun b : Bool => if b then w else z) q =
       MvPolynomial.eval (pairAssignment i j z w) (presencePolynomial μ B) := by
    rw [eval_boundarySection]
    apply congrArg (fun z => MvPolynomial.eval z (presencePolynomial μ B))
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [f, pairAssignment, hki, hkj, Ne.symm hij]
  have hq : q ≠ 0 := by
    intro h
    have he := evalq 1 1
    simp only [h, map_zero] at he
    have hone : pairAssignment i j 1 1 = fun _ => 1 := by funext k; simp [pairAssignment]
    rw [hone, eval_presencePolynomial_one] at he
    exact hB (by exact_mod_cast he.symm)
  have hsq : Stable q := stable_boundarySection hsB f (fun _ => 1) hq
  have hsection : StableSection
      ((presence μ B - presence μ (insert i B) - presence μ (insert j B) +
        presence μ (insert i (insert j B)) : ℝ) : ℂ)
      ((presence μ (insert i B) - presence μ (insert i (insert j B)) : ℝ) : ℂ)
      ((presence μ (insert j B) - presence μ (insert i (insert j B)) : ℝ) : ℂ)
      (presence μ (insert i (insert j B)) : ℂ) := by
    intro z w hz hw
    have hn := hsq (fun b : Bool => if b then w else z) (by intro b; cases b <;> assumption)
    rw [evalq, eval_presencePolynomial_pair μ B i j hij hi hj] at hn
    convert hn using 1
    push_cast
    unfold biaffine
    ring
  have hiq := stable_section_real_rayleigh hsection
  nlinarith

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem presence_insert_le {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    (h₁ : presence μ ∅ = 1) (hs : Stable (presencePolynomial μ ∅))
    (B : Finset σ) (i : σ) (hi : i ∉ B) :
    presence μ (insert i B) ≤ presence μ {i} * presence μ B := by
  induction B using Finset.induction_on with
  | empty => simp [h₁]
  | @insert j B hj ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hiB : i ∉ B := fun h => hi (Finset.mem_insert_of_mem h)
    by_cases hB : presence μ B = 0
    · have hBi : presence μ (insert i (insert j B)) = 0 := by
        apply le_antisymm
        · calc
            _ ≤ presence μ B := presence_mono hμ (B := B)
                (C := insert i (insert j B)) (by intro k hk; simp [hk])
            _ = 0 := hB
        · exact presence_nonneg hμ _
      rw [hBi]
      exact mul_nonneg (presence_nonneg hμ _) (presence_nonneg hμ _)
    have hp : 0 < presence μ B := lt_of_le_of_ne (presence_nonneg hμ B) (Ne.symm hB)
    have hpair := presence_pair_inequality hμ hs B i j hij hiB hj
    have hstep := mul_le_mul_of_nonneg_right (ih hiB) (presence_nonneg hμ (insert j B))
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      presence μ (insert i (insert j B)) * presence μ B
          ≤ presence μ (insert i B) * presence μ (insert j B) := hpair
      _ ≤ (presence μ {i} * presence μ B) * presence μ (insert j B) := hstep
      _ = (presence μ {i} * presence μ (insert j B)) * presence μ B := by ring

theorem presence_product {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A)
    (h₁ : presence μ ∅ = 1) (hs : Stable (presencePolynomial μ ∅))
    (J : Finset σ) : presence μ J ≤ ∏ j ∈ J, presence μ {j} := by
  induction J using Finset.induction_on with
  | empty => simp [h₁]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi]
    exact (presence_insert_le hμ h₁ hs J i hi).trans
      (mul_le_mul_of_nonneg_left ih (presence_nonneg hμ _))

end Heisenberg.Pin

namespace Heisenberg.Pin

lemma product_le_mean_pow {σ : Type*} (J : Finset σ) (hJ : J.Nonempty)
    (v : σ → ℝ) (hv : ∀ j ∈ J, 0 ≤ v j) :
    (∏ j ∈ J, v j) ≤ ((∑ j ∈ J, v j) / J.card) ^ J.card := by
  have hn : 0 < (J.card : ℝ) := by exact_mod_cast hJ.card_pos
  have hmean := Real.geom_mean_le_arith_mean J (fun _ => 1) v (by intros; norm_num)
    (by simpa using hn) hv
  simp only [Real.rpow_one, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at hmean
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Finset.prod_nonneg hv) _) hmean J.card
  rw [Real.rpow_inv_natCast_pow (Finset.prod_nonneg hv) (ne_of_gt hJ.card_pos)] at hpow
  exact hpow

theorem presence_mean_bound {σ : Type*} [Fintype σ] [DecidableEq σ]
    {μ : Finset σ → ℝ} (hμ : ∀ A, 0 ≤ μ A) (h₁ : presence μ ∅ = 1)
    (hs : Stable (presencePolynomial μ ∅)) (J : Finset σ) (hJ : J.Nonempty) :
    presence μ J ≤ ((∑ j ∈ J, presence μ {j}) / J.card) ^ J.card :=
  (presence_product hμ h₁ hs J).trans
    (product_le_mean_pow J hJ (fun j => presence μ {j}) (fun _ _ => presence_nonneg hμ _))

end Heisenberg.Pin

namespace Heisenberg.Pin

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def MultiAffine (p : MvPolynomial σ ℂ) : Prop := ∀ i, p.degreeOf i ≤ 1

lemma prod_pow_update (z : σ → ℂ) (i : σ) (u : ℂ) (a : σ →₀ ℕ) :
    (∏ k, (Function.update z i u k) ^ a k) =
      u ^ a i * ∏ k ∈ Finset.univ.erase i, z k ^ a k := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

lemma eval_update_affine (p : MvPolynomial σ ℂ) (i : σ) (hi : p.degreeOf i ≤ 1)
    (z : σ → ℂ) (u : ℂ) :
    MvPolynomial.eval (Function.update z i u) p =
      MvPolynomial.eval (Function.update z i 0) p +
      (MvPolynomial.eval (Function.update z i 1) p -
        MvPolynomial.eval (Function.update z i 0) p) * u := by
  simp only [MvPolynomial.eval_eq', prod_pow_update]
  rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hdeg : a i ≤ 1 := (MvPolynomial.degreeOf_le_iff.mp hi) a ha
  interval_cases a i
  · simp
  · simp only [pow_one, zero_mul, mul_zero, sub_zero, zero_add]; ring

lemma exists_biaffine_section (p : MvPolynomial σ ℂ) (hp : MultiAffine p)
    (i j : σ) (hij : i ≠ j) (z : σ → ℂ) :
    ∃ a b c e : ℂ, ∀ u v,
      MvPolynomial.eval (Function.update (Function.update z i u) j v) p =
        biaffine a b c e u v := by
  let f (u v : ℂ) := MvPolynomial.eval (Function.update (Function.update z i u) j v) p
  have hf (u v : ℂ) : f u v = f 0 v + (f 1 v - f 0 v) * u := by
    unfold f
    rw [Function.update_comm hij]
    rw [eval_update_affine p i (hp i)]
    simp only [Function.update_comm hij]
  have hg (u v : ℂ) : f u v = f u 0 + (f u 1 - f u 0) * v :=
    eval_update_affine p j (hp j) _ _
  refine ⟨f 0 0, f 1 0 - f 0 0, f 0 1 - f 0 0,
    f 1 1 - f 1 0 - f 0 1 + f 0 0, ?_⟩
  intro u v
  change f u v = _
  rw [hf u v, hg 0 v, hg 1 v]
  unfold biaffine
  ring

def symmetrize (p : MvPolynomial σ ℂ) (i j : σ) (u : ℝ) : MvPolynomial σ ℂ :=
  MvPolynomial.C (1 - (u : ℂ)) * p +
    MvPolynomial.C (u : ℂ) * MvPolynomial.rename (Equiv.swap i j) p

omit [Fintype σ] [DecidableEq σ] in
lemma MultiAffine.add {p q : MvPolynomial σ ℂ} (hp : MultiAffine p)
    (hq : MultiAffine q) : MultiAffine (p + q) :=
  fun i => (MvPolynomial.degreeOf_add_le i p q).trans (max_le (hp i) (hq i))

omit [Fintype σ] [DecidableEq σ] in
lemma MultiAffine.const_mul {p : MvPolynomial σ ℂ} (hp : MultiAffine p) (c : ℂ) :
    MultiAffine (MvPolynomial.C c * p) := by
  intro i
  exact (MvPolynomial.degreeOf_mul_le i _ _).trans (by simpa using hp i)

omit [Fintype σ] [DecidableEq σ] in
lemma MultiAffine.rename {p : MvPolynomial σ ℂ} (hp : MultiAffine p)
    (e : Equiv.Perm σ) : MultiAffine (MvPolynomial.rename e p) := by
  intro i
  have he := MvPolynomial.degreeOf_rename_of_injective (p := p) e.injective (e.symm i)
  calc
    MvPolynomial.degreeOf i (MvPolynomial.rename e p) =
      MvPolynomial.degreeOf (e.symm i) p := by simpa using he
    _ ≤ 1 := hp (e.symm i)

omit [Fintype σ] in
lemma MultiAffine.symmetrize {p : MvPolynomial σ ℂ} (hp : MultiAffine p)
    (i j : σ) (u : ℝ) : MultiAffine (symmetrize p i j u) :=
  (hp.const_mul _).add ((hp.rename (Equiv.swap i j)).const_mul _)

theorem stable_symmetrize {p : MvPolynomial σ ℂ} (hp : Stable p)
    (hm : MultiAffine p) (i j : σ) {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Stable (symmetrize p i j u) := by
  by_cases hij : i = j
  · subst j
    have he : symmetrize p i i u = p := by
      simp only [symmetrize, Equiv.swap_self, Equiv.coe_refl, MvPolynomial.rename_id, AlgHom.id_apply]
      rw [← add_mul, ← map_add]
      simp
    rw [he]
    exact hp
  intro z hz
  obtain ⟨a, b, c, e, hsec⟩ := exists_biaffine_section p hm i j hij z
  have hs : StableSection a b c e := by
    intro v w hv hw
    rw [← hsec v w]
    apply hp
    intro k
    by_cases hj : k = j
    · subst k; simpa using hw
    by_cases hi : k = i
    · subst k; simpa [Function.update_of_ne hij] using hv
    simpa [Function.update_of_ne hj, Function.update_of_ne hi] using hz k
  have hs' := partial_symmetrization hs h0 h1 (z i) (z j) (hz i) (hz j)
  have hzself : Function.update (Function.update z i (z i)) j (z j) = z := by simp
  have hzswap : Function.update (Function.update z i (z j)) j (z i) = z ∘ Equiv.swap i j := by
    funext k
    by_cases hi : k = i
    · subst k; simp [hij]
    by_cases hj : k = j
    · subst k; simp
    simp [Function.update_of_ne hi, Function.update_of_ne hj,
      Equiv.swap_apply_of_ne_of_ne hi hj]
  have heval : MvPolynomial.eval z (symmetrize p i j u) =
      biaffine a ((1 - (u : ℂ)) * b + (u : ℂ) * c)
        ((1 - (u : ℂ)) * c + (u : ℂ) * b) e (z i) (z j) := by
    simp only [symmetrize, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_rename]
    rw [← hzself, hsec]
    rw [hzself, ← hzswap, hsec]
    unfold biaffine
    ring
  rwa [heval]

end Heisenberg.Pin
end
end

end OAI
