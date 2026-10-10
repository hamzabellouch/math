import OAI.NumberTheory.CubicMoment.Estimates.SieveCoefficients

namespace OAI

/-!
# The Möbius coefficient below the sieve truncation

The union convolution of the squarefree Möbius weights is the same
Möbius weight. This proves the exact low-divisor coefficient identity,
which is stronger than a divisor bound and is needed in the residue.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma insert_union_eq_iff {ι : Type*} [DecidableEq ι]
    {p : ι} {s t U : Finset ι} (hp : p ∉ U) (hs : s ⊆ U) (ht : t ⊆ U) :
    insert p (s ∪ t) = insert p U ↔ s ∪ t = U := by
  constructor
  · intro h
    have h' := congrArg (fun v : Finset ι => v.erase p) h
    have hpst : p ∉ s ∪ t := by simp only [Finset.mem_union,not_or]; exact ⟨fun h => hp (hs h),fun h => hp (ht h)⟩
    simpa [hpst,hp] using h'
  · exact congrArg (insert p)

private lemma union_step {ι : Type*} [DecidableEq ι]
    {p : ι} {s t U : Finset ι} (hp : p ∉ U) (hs : s ⊆ U) (ht : t ⊆ U) :
    (if s ∪ t = insert p U then (-1:ℝ)^s.card*(-1)^t.card else 0) +
    (if s ∪ insert p t = insert p U then (-1:ℝ)^s.card*(-1)^(insert p t).card else 0) +
    (if insert p s ∪ t = insert p U then (-1:ℝ)^(insert p s).card*(-1)^t.card else 0) +
    (if insert p s ∪ insert p t = insert p U then
      (-1:ℝ)^(insert p s).card*(-1)^(insert p t).card else 0) =
    -(if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0) := by
  have hps : p ∉ s := fun h => hp (hs h)
  have hpt : p ∉ t := fun h => hp (ht h)
  have hne : s ∪ t ≠ insert p U := by
    intro h
    have hm : p ∈ s ∪ t := h ▸ Finset.mem_insert_self p U
    rcases Finset.mem_union.mp hm with hm | hm
    · exact hps hm
    · exact hpt hm
  have hi := insert_union_eq_iff hp hs ht
  simp only [hne,ite_false,Finset.union_insert,Finset.insert_union,Finset.insert_idem,
    hi,Finset.card_insert_of_notMem hps,Finset.card_insert_of_notMem hpt,pow_succ]
  split_ifs <;> ring

/-- The exact union convolution of the signed subset weights. -/
theorem squarefree_mobius_union {ι : Type*} [DecidableEq ι] (U : Finset ι) :
    (∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
      if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0) = (-1)^U.card := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert p U hp ih =>
    rw [Finset.sum_powerset_insert hp]
    simp_rw [Finset.sum_powerset_insert hp]
    calc
      _ = ∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
          ((if s ∪ t = insert p U then (-1:ℝ)^s.card*(-1)^t.card else 0) +
          (if s ∪ insert p t = insert p U then (-1:ℝ)^s.card*(-1)^(insert p t).card else 0) +
          (if insert p s ∪ t = insert p U then (-1:ℝ)^(insert p s).card*(-1)^t.card else 0) +
          (if insert p s ∪ insert p t = insert p U then
            (-1:ℝ)^(insert p s).card*(-1)^(insert p t).card else 0)) := by
        simp only [Finset.sum_add_distrib]
        ring
      _ = ∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
          -(if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0) := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro t ht
        exact union_step hp (Finset.mem_powerset.mp hs) (Finset.mem_powerset.mp ht)
      _ = -((-1:ℝ)^U.card) := by simp only [Finset.sum_neg_distrib,ih]
      _ = _ := by rw [Finset.card_insert_of_notMem hp,pow_succ]; ring

lemma primaryPrimeFactors_finset_prod (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) :
    primaryPrimeFactors (∏ p ∈ U, p) = U := by
  have hprod := primary_finset_prod U (fun p : Eisenstein => p) (fun p hp => (hU p hp).1)
  ext p
  rw [primaryPrime_mem_factors_iff hprod]
  constructor
  · rintro ⟨hp,hd⟩
    obtain ⟨q,hq,hpq⟩ := (hp.2.dvd_finsetProd_iff (fun p : Eisenstein => p)).mp hd
    have he : p = q := primary_associated_eq hp.1 (hU q hq).1
      (hp.2.associated_of_dvd (hU q hq).2 hpq)
    exact he ▸ hq
  · intro hp
    exact ⟨hU p hp,Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp⟩

lemma primaryPrimeFactors_prod_injective {U : Finset Eisenstein}
    (hU : ∀ p ∈ U, primaryPrime p) :
    Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p) (↑U.powerset : Set (Finset Eisenstein)) := by
  intro s hs t ht he
  have hs' := Finset.mem_powerset.mp hs
  have ht' := Finset.mem_powerset.mp ht
  have hh := congrArg primaryPrimeFactors he
  simpa only [primaryPrimeFactors_finset_prod s (fun p hp => hU p (hs' hp)),
    primaryPrimeFactors_finset_prod t (fun p hp => hU p (ht' hp))] using hh

lemma primaryPrime_product_squarefree (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) : Squarefree (∏ p ∈ U, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact isRelPrime_iff_isCoprime.mpr (primaryPrimes_isCoprime (hU p hp) (hU q hq) hpq)
  · intro p hp
    exact (hU p hp).2.squarefree

lemma collectedSieveCoefficient_restrict_divisors (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) (e : Eisenstein) :
    collectedSquarefreeSieveCoefficient C e =
      collectedSquarefreeSieveCoefficient (C.filter (· ∣ e)) e := by
  have hset : (C.product C).filter (fun t => primarySquarefreeJoin t.1 t.2 = e) =
      ((C.filter (· ∣ e)).product (C.filter (· ∣ e))).filter
        (fun t => primarySquarefreeJoin t.1 t.2 = e) := by
    ext t
    simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨ha,hb⟩,he⟩
      refine ⟨⟨⟨ha,?_⟩,⟨hb,?_⟩⟩,he⟩
      · exact he ▸ dvd_primarySquarefreeJoin_left (hC t.1 ha).1 (hC t.1 ha).2
      · exact he ▸ dvd_primarySquarefreeJoin_right (hC t.2 hb).1 (hC t.2 hb).2
    · rintro ⟨⟨⟨ha,_⟩,⟨hb,_⟩⟩,he⟩
      exact ⟨⟨ha,hb⟩,he⟩
  unfold collectedSquarefreeSieveCoefficient
  rw [hset]

lemma primary_divisors_eq_subset_products (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {e : Eisenstein}
    (he : primary e) (hcomplete : ∀ c, primary c → Squarefree c → c ∣ e → c ∈ C) :
    C.filter (· ∣ e) = (primaryPrimeFactors e).powerset.image (fun s => ∏ p ∈ s, p) := by
  ext c
  constructor
  · intro hc
    obtain ⟨hc,hce⟩ := Finset.mem_filter.mp hc
    refine Finset.mem_image.mpr ⟨primaryPrimeFactors c,
      Finset.mem_powerset.mpr (primaryPrimeFactors_subset_of_dvd (hC c hc).1 he hce),
      primaryPrimeFactors_prod (hC c hc).1 (hC c hc).2⟩
  · intro hc
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hc
    have hsub := Finset.mem_powerset.mp hs
    have hsp : ∀ p ∈ s, primaryPrime p := fun p hp => (primaryPrimeFactor_spec he (hsub hp)).1
    have hp := primary_finset_prod s (fun p : Eisenstein => p) (fun p hp => (hsp p hp).1)
    have hd : (∏ p ∈ s, p) ∣ e :=
      (primary_subsets_prod_dvd he hsub e).mpr (fun p hp => (primaryPrimeFactor_spec he (hsub hp)).2)
    exact Finset.mem_filter.mpr ⟨hcomplete _ hp (primaryPrime_product_squarefree s hsp) hd,hd⟩

/-- If the truncation contains every divisor of `e`, the collected
coefficient is exactly the ideal Möbius function. -/
theorem collectedSieveCoefficient_eq_moebius (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c) {e : Eisenstein}
    (he : primary e) (hse : Squarefree e)
    (hcomplete : ∀ c, primary c → Squarefree c → c ∣ e → c ∈ C) :
    collectedSquarefreeSieveCoefficient C e = (idealMoebius e : ℝ) := by
  let U := primaryPrimeFactors e
  have hU : ∀ p ∈ U, primaryPrime p := fun p hp => (primaryPrimeFactor_spec he hp).1
  have hinj := primaryPrimeFactors_prod_injective hU
  have hprod : (∏ p ∈ U, p) = e := primaryPrimeFactors_prod he hse
  rw [collectedSieveCoefficient_restrict_divisors C hC e,
    primary_divisors_eq_subset_products C hC he hcomplete]
  unfold collectedSquarefreeSieveCoefficient
  rw [Finset.sum_filter]
  simp only [Finset.product_eq_sprod,Finset.sum_product]
  change (∑ a ∈ U.powerset.image (fun s => ∏ p ∈ s, p),
    ∑ b ∈ U.powerset.image (fun s => ∏ p ∈ s, p),
      if primarySquarefreeJoin a b = e then (idealMoebius a : ℝ)*(idealMoebius b : ℝ) else 0) = _
  rw [Finset.sum_image hinj]
  have hex : (∑ s ∈ U.powerset, ∑ t ∈ U.powerset.image (fun v => ∏ p ∈ v, p),
      if primarySquarefreeJoin (∏ p ∈ s, p) t = e then
        (idealMoebius (∏ p ∈ s, p) : ℝ)*(idealMoebius t : ℝ) else 0) =
      ∑ s ∈ U.powerset, ∑ t ∈ U.powerset,
        if s ∪ t = U then (-1:ℝ)^s.card*(-1)^t.card else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro t ht
    have hsU := Finset.mem_powerset.mp hs
    have htU := Finset.mem_powerset.mp ht
    have hsP : ∀ p ∈ s, primaryPrime p := fun p hp => hU p (hsU hp)
    have htP : ∀ p ∈ t, primaryPrime p := fun p hp => hU p (htU hp)
    have hstP : ∀ p ∈ s ∪ t, primaryPrime p := by
      intro p hp
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hsP p hp
      · exact htP p hp
    have hj : primarySquarefreeJoin (∏ p ∈ s, p) (∏ p ∈ t, p) = e ↔ s ∪ t = U := by
      unfold primarySquarefreeJoin
      rw [primaryPrimeFactors_finset_prod s hsP,primaryPrimeFactors_finset_prod t htP]
      constructor
      · intro h
        have hh := congrArg primaryPrimeFactors h
        simpa only [primaryPrimeFactors_finset_prod (s ∪ t) hstP] using hh
      · intro h
        rw [h,hprod]
    simp only [hj,idealMoebius_prod_primaryPrimes s hsP,idealMoebius_prod_primaryPrimes t htP,
      Int.cast_pow,Int.cast_neg,Int.cast_one]
  rw [hex,squarefree_mobius_union]
  rw [← hprod,idealMoebius_prod_primaryPrimes U hU]
  push_cast
  rfl

/-- Terms at nonsquarefree divisors have zero Möbius weight, so this
finite truncation gives exactly the original truncated divisor sum. -/
def squarefreeDivisorTruncation (D : ℝ) : Finset Eisenstein :=
  (squareDivisorTruncation D).filter Squarefree

lemma mem_squarefreeDivisorTruncation {D : ℝ} {c : Eisenstein} :
    c ∈ squarefreeDivisorTruncation D ↔ primary c ∧ Squarefree c ∧ norm c ≤ D := by
  simp only [squarefreeDivisorTruncation,squareDivisorTruncation,Finset.mem_filter,
    mem_nonzeroNormBall]
  constructor
  · rintro ⟨⟨⟨hn,_⟩,hp⟩,hs⟩
    exact ⟨hp,hs,hn⟩
  · rintro ⟨hp,hs,hn⟩
    exact ⟨⟨⟨hn,primary_ne_zero hp⟩,hp⟩,hs⟩

lemma truncatedSquareDivisorSum_squarefree (D : ℝ) (a : Eisenstein) :
    truncatedSquareDivisorSum (squarefreeDivisorTruncation D) a =
      truncatedSquareDivisorSum (squareDivisorTruncation D) a := by
  unfold truncatedSquareDivisorSum squarefreeDivisorTruncation
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hs : Squarefree c
  · simp only [hs,ite_true]
  · have hmu : idealMoebius c = 0 := by
      simp [idealMoebius,UniqueFactorizationMonoid.moebius,hs]
    simp [hs,hmu]

/-- The exact low-divisor identity for the concrete norm truncation. -/
theorem squarefreeSieveCoefficient_small {D : ℝ} {e : Eisenstein}
    (he : primary e) (hse : Squarefree e) (hD : norm e ≤ D) :
    collectedSquarefreeSieveCoefficient (squarefreeDivisorTruncation D) e =
      (idealMoebius e : ℝ) := by
  apply collectedSieveCoefficient_eq_moebius _
    (fun c hc => ⟨(mem_squarefreeDivisorTruncation.mp hc).1,
      (mem_squarefreeDivisorTruncation.mp hc).2.1⟩) he hse
  intro c hc hsc hce
  exact mem_squarefreeDivisorTruncation.mpr ⟨hc,hsc,
    (norm_le_of_dvd_nonzero (primary_ne_zero he) hce).trans hD⟩

end CubicFirstMoment

end

end OAI
