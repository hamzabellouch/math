import OAI.Geometry.UnitDistances.Sequence

namespace OAI

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset
noncomputable section

section Rational

def badPrimes (q : ℚ) : Finset ℕ := q.num.natAbs.primeFactors ∪ q.den.primeFactors

lemma padic_nat_eq (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (padicNorm p (n : ℚ) : ℝ) = ((p : ℝ)^n.factorization p)⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat,
    ← Nat.factorization_def n hp]
  norm_cast
  simp

lemma prod_padic_nat {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {n : ℕ}
    (hn : n ≠ 0) (hsn : n.primeFactors ⊆ s) :
    (∏ p ∈ s, (padicNorm p (n : ℚ) : ℝ)) = (n : ℝ)⁻¹ := by
  have heq : (∏ p ∈ s, p^n.factorization p) = n := by
    have hh := Finsupp.prod_of_support_subset n.factorization
      (s := s) (by simpa only [Nat.support_factorization] using hsn)
      (fun p e => p^e) (by simp)
    rw [Nat.prod_factorization_pow_eq_self hn] at hh
    exact hh.symm
  have heqR : (∏ p ∈ s, (p : ℝ)^n.factorization p) = (n : ℝ) := by
    exact_mod_cast heq
  calc
    (∏ p ∈ s, (padicNorm p (n : ℚ) : ℝ)) =
        ∏ p ∈ s, ((p : ℝ)^n.factorization p)⁻¹ :=
      prod_congr rfl (fun p hp => padic_nat_eq p n (hs p hp) hn)
    _ = (∏ p ∈ s, (p : ℝ)^n.factorization p)⁻¹ := by rw [prod_inv_distrib]
    _ = (n : ℝ)⁻¹ := by rw [heqR]

lemma padic_int_natAbs (p : ℕ) (z : ℤ) :
    padicNorm p (z : ℚ) = padicNorm p (z.natAbs : ℚ) := by
  cases z with
  | ofNat n => simp
  | negSucc n => simpa only [Int.cast_negSucc, Int.natAbs_negSucc, Nat.cast_add,
      Nat.cast_one, Nat.cast_succ] using padicNorm.neg (p := p) ((n:ℚ)+1)

lemma padic_rat_outside {q : ℚ} (hq : q ≠ 0) {p : ℕ} (hp : p.Prime)
    (hps : p ∉ badPrimes q) : padicNorm p q = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : q.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hq)
  have hnd : ¬ p ∣ q.num.natAbs := by
    intro h
    exact hps (mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp,h,hn⟩))
  have hdd : ¬ p ∣ q.den := by
    intro h
    exact hps (mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp,h,q.den_ne_zero⟩))
  conv_lhs => rw [← q.num_div_den]
  rw [padicNorm.div, padic_int_natAbs, (padicNorm.nat_eq_one_iff _).mpr hnd,
    (padicNorm.nat_eq_one_iff _).mpr hdd, div_one]

theorem rational_product_formula {q : ℚ} (hq : q ≠ 0) :
    |(q : ℝ)| * ∏ p ∈ badPrimes q, (padicNorm p q : ℝ) = 1 := by
  have hn : q.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hq)
  have hp : ∀ p ∈ badPrimes q, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hprod : (∏ p ∈ badPrimes q, (padicNorm p q : ℝ)) =
      (q.num.natAbs : ℝ)⁻¹/(q.den : ℝ)⁻¹ := by
    calc
      (∏ p ∈ badPrimes q, (padicNorm p q : ℝ)) =
          ∏ p ∈ badPrimes q, (padicNorm p (q.num.natAbs:ℚ) : ℝ) /
            (padicNorm p (q.den:ℚ) : ℝ) := by
        apply prod_congr rfl
        intro p hps
        let : Fact p.Prime := ⟨hp p hps⟩
        conv_lhs => rw [← q.num_div_den]
        rw [padicNorm.div, padic_int_natAbs, Rat.cast_div]
      _ = _ := by
        rw [prod_div_distrib, prod_padic_nat hp hn (subset_union_left),
          prod_padic_nat hp q.den_ne_zero (subset_union_right)]
  have hval : |(q : ℝ)| = (q.num.natAbs:ℝ)/(q.den:ℝ) := by
    have hdabs : |(q.den:ℝ)| = (q.den:ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [Rat.cast_def, abs_div, hdabs, Nat.cast_natAbs, Int.cast_abs]
  rw [hprod,hval]
  have hnR : (q.num.natAbs:ℝ) ≠ 0 := by exact_mod_cast hn
  have hdR : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  field_simp

end Rational

section Entries
variable (K : Type*) [Field K] [NumberField K]

def primeEmbedding (p : ℕ) [Fact p.Prime] : K →ₐ[ℚ] PadicAlgCl p :=
  IsAlgClosed.lift

def primeAbsoluteValue (p : ℕ) [Fact p.Prime] : AbsoluteValue K ℝ :=
  (NormedField.toAbsoluteValue (PadicAlgCl p)).comp (primeEmbedding K p).injective

@[simp] lemma primeAbsoluteValue_apply (p : ℕ) [Fact p.Prime] (u : K) :
    primeAbsoluteValue K p u = ‖primeEmbedding K p u‖ := rfl

@[simp] theorem primeAbsoluteValue_rat (p : ℕ) [Fact p.Prime] (q : ℚ) :
    primeAbsoluteValue K p (algebraMap ℚ K q) = (padicNorm p q : ℝ) := by
  rw [primeAbsoluteValue_apply, AlgHom.commutes]
  change ‖(q : PadicAlgCl p)‖ = _
  have hh : (q : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (q:ℚ_[p]) := by simp
  rw [hh, PadicAlgCl.norm_extends, Padic.eq_padicNorm]

theorem primeAbsoluteValue_nonarch (p : ℕ) [Fact p.Prime] :
    IsNonarchimedean (primeAbsoluteValue K p) := by
  intro x y
  change ‖primeEmbedding K p (x+y)‖ ≤ _
  rw [map_add]
  exact PadicAlgCl.isNonarchimedean p _ _

def finiteEntry (p : Nat.Primes) (σ : Gal(K/ℚ)) : AbsoluteValue K ℝ := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  exact (primeAbsoluteValue K p.val).comp (f := σ.toRingHom) σ.injective

def infiniteEntry (σ : K →ₐ[ℚ] ℂ) : AbsoluteValue K ℝ :=
  (NormedField.toAbsoluteValue ℂ).comp σ.injective

@[simp] theorem infiniteEntry_apply (σ : K →ₐ[ℚ] ℂ) (u : K) :
    infiniteEntry K σ u = ‖σ u‖ := rfl

lemma infiniteEntry_count : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
  AlgHom.card ℚ K ℂ

lemma finiteEntry_nonarch (p : Nat.Primes) (σ : Gal(K/ℚ)) :
    IsNonarchimedean (finiteEntry K p σ) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  intro x y
  change primeAbsoluteValue K p.val (σ (x+y)) ≤ _
  rw [map_add]
  exact primeAbsoluteValue_nonarch K p.val _ _

@[simp] lemma finiteEntry_rat (p : Nat.Primes) (σ : Gal(K/ℚ)) (q : ℚ) :
    finiteEntry K p σ (algebraMap ℚ K q) = (padicNorm p.val q : ℝ) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  change primeAbsoluteValue K p.val (σ (algebraMap ℚ K q)) = _
  rw [AlgEquiv.commutes, primeAbsoluteValue_rat]

def rootDenominators (x : K) : Finset ℕ :=
  (range (minpoly ℚ x).natDegree).biUnion fun i => ((minpoly ℚ x).coeff i).den.primeFactors

end Entries

lemma nonarch_root_one {L : Type*} [Field L] (v : AbsoluteValue L ℝ)
    (hv : IsNonarchimedean v) {m : ℕ} (hm : 0 < m)
    (a : Fin m → L) (x : L) (hcoeff : ∀ i, v (a i) ≤ 1)
    (hrel : x^m = ∑ i, a i * x^(i:ℕ)) : v x ≤ 1 := by
  by_contra h
  have hx : 1 < v x := lt_of_not_ge h
  have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hs : (v x)^m ≤ (v x)^(m-1) := by
    calc
      (v x)^m = v (∑ i, a i * x^(i:ℕ)) := by rw [← hrel,map_pow]
      _ ≤ ⨆ i, v (a i * x^(i:ℕ)) := hv.apply_sum_univ_le
      _ ≤ (v x)^(m-1) := by
        apply ciSup_le
        intro i
        rw [map_mul,map_pow]
        have hi : (v x)^(i:ℕ) ≤ (v x)^(m-1) := pow_le_pow_right₀ hx.le (by omega)
        exact (mul_le_mul (hcoeff i) hi (pow_nonneg (v.nonneg x) _) zero_le_one).trans_eq (one_mul _)
  have heq : (v x)^m = v x * (v x)^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpos : 0 < (v x)^(m-1) := pow_pos (lt_trans zero_lt_one hx) _
  rw [heq] at hs
  have hh : v x ≤ 1 := (mul_le_mul_iff_left₀ hpos).mp (by simpa using hs)
  exact h hh

section Support
variable (K : Type*) [Field K] [NumberField K]

lemma finiteEntry_le_one_off_denominators (x : K) (p : Nat.Primes) (σ : Gal(K/ℚ))
    (hp : p.val ∉ rootDenominators K x) : finiteEntry K p σ x ≤ 1 := by
  classical
  let : Fact p.val.Prime := ⟨p.property⟩
  let f := minpoly ℚ x
  have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hroot : Polynomial.aeval x f = 0 := minpoly.aeval ℚ x
  have hm : 0 < f.natDegree :=
    Polynomial.natDegree_pos_of_aeval_root hf.ne_zero hroot (fun a ha => by simpa using ha)
  apply nonarch_root_one (finiteEntry K p σ) (finiteEntry_nonarch K p σ) hm
    (fun i => -algebraMap ℚ K (f.coeff (i:ℕ))) x
  · intro i
    rw [AbsoluteValue.map_neg, finiteEntry_rat]
    have hden : ¬ p.val ∣ (f.coeff (i:ℕ)).den := by
      intro hd
      apply hp
      apply mem_biUnion.mpr
      refine ⟨(i:ℕ), mem_range.mpr i.isLt, ?_⟩
      exact Nat.mem_primeFactors.mpr ⟨p.property, hd, (f.coeff (i:ℕ)).den_ne_zero⟩
    simpa only [Padic.eq_padicNorm] using (Padic.norm_rat_le_one (p := p.val) hden)
  · have hh := congrArg (Polynomial.aeval x) hf.as_sum
    rw [hroot] at hh
    simp only [map_add,map_sum,map_mul,map_pow,Polynomial.aeval_X,Polynomial.aeval_C] at hh
    rw [← Fin.sum_univ_eq_sum_range] at hh
    simp only [neg_mul, sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hh.symm

lemma finiteEntry_eq_one_off_support {x : K} (hx : x ≠ 0)
    (p : Nat.Primes) (σ : Gal(K/ℚ))
    (hp : p.val ∉ rootDenominators K x ∪ rootDenominators K x⁻¹) :
    finiteEntry K p σ x = 1 := by
  have hu := finiteEntry_le_one_off_denominators K x p σ (fun h => hp (mem_union_left _ h))
  have hi := finiteEntry_le_one_off_denominators K x⁻¹ p σ (fun h => hp (mem_union_right _ h))
  have hpos : 0 < finiteEntry K p σ x := (finiteEntry K p σ).pos hx
  have hh := mul_le_mul_of_nonneg_left hi hpos.le
  rw [map_inv₀, mul_inv_cancel₀ (ne_of_gt hpos), mul_one] at hh
  exact le_antisymm hu hh

theorem finiteEntry_hasFiniteMulSupport {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport (fun v : Nat.Primes × Gal(K/ℚ) => finiteEntry K v.1 v.2 x) := by
  classical
  let S := (rootDenominators K x ∪ rootDenominators K x⁻¹).subtype Nat.Prime
  apply (S ×ˢ (univ : Finset Gal(K/ℚ))).finite_toSet.subset
  intro v hv
  apply mem_product.mpr
  refine ⟨?_,mem_univ _⟩
  apply Finset.mem_subtype.mpr
  by_contra hn
  exact hv (finiteEntry_eq_one_off_support K hx v.1 v.2 hn)

end Support

section Product
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma finiteEntry_block (p : Nat.Primes) (x : K) :
    (∏ σ : Gal(K/ℚ), finiteEntry K p σ x) =
      (padicNorm p.val (Algebra.norm ℚ x) : ℝ) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  change (∏ σ : Gal(K/ℚ), primeAbsoluteValue K p.val (σ x)) = _
  rw [← map_prod, ← Algebra.norm_eq_prod_automorphisms ℚ, primeAbsoluteValue_rat]

lemma infiniteEntry_block (x : K) :
    (∏ σ : K →ₐ[ℚ] ℂ, infiniteEntry K σ x) = |(Algebra.norm ℚ x : ℝ)| := by
  simp only [infiniteEntry_apply]
  rw [← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ]
  simp only [eq_ratCast, Complex.norm_ratCast]

lemma rational_product_formula_on {q : ℚ} (hq : q ≠ 0) (s : Finset Nat.Primes)
    (hs : ∀ p ∈ badPrimes q, ∃ hp : p.Prime, (⟨p,hp⟩ : Nat.Primes) ∈ s) :
    |(q : ℝ)| * (∏ p ∈ s, (padicNorm p.val q : ℝ)) = 1 := by
  classical
  have heq : (∏ p ∈ s, (padicNorm p.val q : ℝ)) =
      ∏ p ∈ badPrimes q, (padicNorm p q : ℝ) := by
    let t := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hsub : badPrimes q ⊆ t := by
      intro p hp
      obtain ⟨hpr,hps⟩ := hs p hp
      exact mem_map.mpr ⟨⟨p,hpr⟩,hps,rfl⟩
    have he : (∏ p ∈ t, (padicNorm p q : ℝ)) =
        ∏ p ∈ badPrimes q, (padicNorm p q : ℝ) := by
      exact (prod_subset hsub (by
        intro p hpt hp
        obtain ⟨r,hr,he⟩ := mem_map.mp hpt
        subst p
        change (padicNorm r.val q : ℝ) = 1
        exact_mod_cast (padic_rat_outside hq r.property hp))).symm
    change (∏ p ∈ s.map (⟨Subtype.val, Subtype.val_injective⟩ : Nat.Primes ↪ ℕ),
      (padicNorm p q : ℝ)) = _ at he
    rw [Finset.prod_map] at he
    exact he
  rw [heq]
  exact rational_product_formula hq

theorem product_formula {x : K} (hx : x ≠ 0) :
    (∏ σ : K →ₐ[ℚ] ℂ, infiniteEntry K σ x) *
      (∏ᶠ v : Nat.Primes × Gal(K/ℚ), finiteEntry K v.1 v.2 x) = 1 := by
  classical
  let q := Algebra.norm ℚ x
  have hq : q ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  let S := rootDenominators K x ∪ rootDenominators K x⁻¹ ∪ badPrimes q
  let s : Finset Nat.Primes := S.subtype Nat.Prime
  have hsup : Function.mulSupport (fun v : Nat.Primes × Gal(K/ℚ) =>
      finiteEntry K v.1 v.2 x) ⊆ (↑(s ×ˢ (univ : Finset Gal(K/ℚ))) : Set (Nat.Primes × Gal(K/ℚ))) := by
    intro v hv
    apply mem_product.mpr
    refine ⟨?_,mem_univ _⟩
    apply Finset.mem_subtype.mpr
    by_contra hn
    apply hv
    apply finiteEntry_eq_one_off_support K hx
    intro h
    exact hn (mem_union_left _ h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsup, Finset.prod_product]
  simp_rw [finiteEntry_block K]
  rw [infiniteEntry_block K]
  apply rational_product_formula_on hq
  intro p hp
  have hpr : p.Prime := by
    rcases mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  refine ⟨hpr,?_⟩
  apply Finset.mem_subtype.mpr
  exact mem_union_right _ hp

theorem weighted_log_product_formula {x : K} (hx : x ≠ 0) :
    ((∑ σ : K →ₐ[ℚ] ℂ, Real.log (infiniteEntry K σ x)) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), Real.log (finiteEntry K v.1 v.2 x))) /
        (Module.finrank ℚ K : ℝ) = 0 := by
  have hp : ∀ σ : K →ₐ[ℚ] ℂ, 0 < infiniteEntry K σ x :=
    fun σ => (infiniteEntry K σ).pos hx
  have hfin : ∀ v : Nat.Primes × Gal(K/ℚ), 0 < finiteEntry K v.1 v.2 x :=
    fun v => (finiteEntry K v.1 v.2).pos hx
  have h1 : (∏ σ : K →ₐ[ℚ] ℂ, infiniteEntry K σ x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun σ _ => (hp σ).ne')
  have h2 : (∏ᶠ v : Nat.Primes × Gal(K/ℚ), finiteEntry K v.1 v.2 x) ≠ 0 := by
    rw [finprod_eq_prod _ (finiteEntry_hasFiniteMulSupport K hx)]
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (hfin v).ne')
  have hh := congrArg Real.log (product_formula K hx)
  rw [Real.log_mul h1 h2, Real.log_prod (fun σ _ => (hp σ).ne'),
    Real.log_finprod hfin, Real.log_one] at hh
  rw [hh, zero_div]

end Product
end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
lemma finiteEntry_composed_support (g : ℝ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0)
    (x : K) : Function.HasFiniteSupport
      (fun v : Nat.Primes × Gal(K/ℚ) => g (finiteEntry K v.1 v.2 x)) := by
  by_cases hx : x = 0
  · subst x
    simpa only [map_zero,h0] using (Function.hasFiniteSupport_zero :
      Function.HasFiniteSupport (0 : Nat.Primes × Gal(K/ℚ) → ℝ))
  · apply (finiteEntry_hasFiniteMulSupport K hx).subset
    intro v hv he
    change finiteEntry K v.1 v.2 x = 1 at he
    apply hv
    change g (finiteEntry K v.1 v.2 x) = 0
    rw [he,h1]

omit [IsGalois ℚ K] in
lemma finite_posLog_support (x : K) : Function.HasFiniteSupport
    (fun v : Nat.Primes × Gal(K/ℚ) => log⁺ (finiteEntry K v.1 v.2 x)) :=
  finiteEntry_composed_support K _ posLog_zero posLog_one x

omit [IsGalois ℚ K] in
lemma finite_log_support (x : K) : Function.HasFiniteSupport
    (fun v : Nat.Primes × Gal(K/ℚ) => log (finiteEntry K v.1 v.2 x)) :=
  finiteEntry_composed_support K _ log_zero log_one x

def exactHeight (x : K) : ℝ :=
  ((∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
    (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x))) /
      (Module.finrank ℚ K : ℝ)

omit [IsGalois ℚ K] in
lemma finrank_pos : 0 < (Module.finrank ℚ K : ℝ) := by
  exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)

omit [IsGalois ℚ K] in
lemma exactHeight_nonneg (x : K) : 0 ≤ exactHeight K x := by
  apply div_nonneg _ (finrank_pos K).le
  exact add_nonneg (sum_nonneg (fun _ _ => posLog_nonneg))
    (finsum_nonneg (fun _ => posLog_nonneg))

omit [IsGalois ℚ K] in
@[simp] lemma exactHeight_zero : exactHeight K (0 : K) = 0 := by
  simp [exactHeight]

omit [IsGalois ℚ K] in
@[simp] lemma exactHeight_one : exactHeight K (1 : K) = 0 := by
  simp [exactHeight]

omit [IsGalois ℚ K] in
@[simp] lemma exactHeight_neg (x : K) : exactHeight K (-x) = exactHeight K x := by
  simp only [exactHeight,AbsoluteValue.map_neg]

@[simp] lemma exactHeight_inv (x : K) : exactHeight K x⁻¹ = exactHeight K x := by
  by_cases hx : x = 0
  · simp [hx]
  have he : exactHeight K x - exactHeight K x⁻¹ = 0 := by
    unfold exactHeight
    rw [← sub_div]
    have hs :
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) -
          (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x⁻¹)) =
        ∑ σ : K →ₐ[ℚ] ℂ, log (infiniteEntry K σ x) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro σ hσ
      rw [map_inv₀,posLog_sub_posLog_inv]
    have hf :
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) -
          (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x⁻¹)) =
        ∑ᶠ v : Nat.Primes × Gal(K/ℚ), log (finiteEntry K v.1 v.2 x) := by
      rw [← finsum_sub_distrib (finite_posLog_support K x) (finite_posLog_support K x⁻¹)]
      apply finsum_congr
      intro v
      rw [map_inv₀,posLog_sub_posLog_inv]
    rw [show ∀ a b c d : ℝ, (a+b)-(c+d)=(a-c)+(b-d) by intros; ring, hs,hf]
    exact weighted_log_product_formula K hx
  exact (sub_eq_zero.mp he).symm

omit [IsGalois ℚ K] in
lemma exactHeight_mul_le (x y : K) :
    exactHeight K (x*y) ≤ exactHeight K x + exactHeight K y := by
  unfold exactHeight
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (finrank_pos K).le
  have harch :
      (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ (x*y))) ≤
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ y)) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro σ _
    rw [map_mul]
    exact posLog_mul
  have hfin :
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 (x*y))) ≤
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) +
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 y)) := by
    rw [← finsum_add_distrib (finite_posLog_support K x) (finite_posLog_support K y)]
    apply finsum_le_finsum (finite_posLog_support K (x*y))
      ((finite_posLog_support K x).add (finite_posLog_support K y))
    intro v
    dsimp only
    rw [map_mul]
    exact posLog_mul
  linarith

lemma exactHeight_add_le (x y : K) :
    exactHeight K (x+y) ≤ log 2 + exactHeight K x + exactHeight K y := by
  have harch :
      (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ (x+y))) ≤
        (Module.finrank ℚ K : ℝ) * log 2 +
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ y)) := by
    calc
      _ ≤ ∑ σ : K →ₐ[ℚ] ℂ,
          (log 2 + log⁺ (infiniteEntry K σ x) + log⁺ (infiniteEntry K σ y)) := by
        apply sum_le_sum
        intro σ _
        exact (posLog_le_posLog (neg_one_lt_zero.le.trans ((infiniteEntry K σ).nonneg _))
          ((infiniteEntry K σ).add_le x y)).trans posLog_add
      _ = _ := by simp [sum_add_distrib]
  have hfin :
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 (x+y))) ≤
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) +
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 y)) := by
    rw [← finsum_add_distrib (finite_posLog_support K x) (finite_posLog_support K y)]
    apply finsum_le_finsum (finite_posLog_support K (x+y))
      ((finite_posLog_support K x).add (finite_posLog_support K y))
    intro v
    dsimp only
    apply (posLog_le_posLog (neg_one_lt_zero.le.trans ((finiteEntry K v.1 v.2).nonneg _))
      (finiteEntry_nonarch K v.1 v.2 x y)).trans
    rcases le_total (finiteEntry K v.1 v.2 x) (finiteEntry K v.1 v.2 y) with h|h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left posLog_nonneg
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right posLog_nonneg
  unfold exactHeight
  have hh := div_le_div_of_nonneg_right (add_le_add harch hfin) (finrank_pos K).le
  simp only [add_div, mul_div_cancel_left₀ _ (finrank_pos K).ne'] at hh ⊢
  linarith

lemma abs_log_eq_posLog_add (r : ℝ) : |log r| = log⁺ r + log⁺ r⁻¹ := by
  have h := (half_mul_log_add_log_abs (x := r))
  have h' := (posLog_sub_posLog_inv (x := r))
  linarith

lemma weighted_abs_log_eq_twice {x : K} (_hx : x ≠ 0) :
    ((∑ σ : K →ₐ[ℚ] ℂ, |log (infiniteEntry K σ x)|) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |log (finiteEntry K v.1 v.2 x)|)) /
        (Module.finrank ℚ K : ℝ) = 2 * exactHeight K x := by
  have harch : (∑ σ : K →ₐ[ℚ] ℂ, |log (infiniteEntry K σ x)|) =
    (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
      (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x⁻¹)) := by
    simp only [abs_log_eq_posLog_add, map_inv₀,sum_add_distrib]
  have hfin : (∑ᶠ v : Nat.Primes × Gal(K/ℚ), |log (finiteEntry K v.1 v.2 x)|) =
    (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x⁻¹)) := by
    simp only [abs_log_eq_posLog_add]
    simpa only [map_inv₀] using
      finsum_add_distrib (finite_posLog_support K x) (finite_posLog_support K x⁻¹)
  rw [harch,hfin]
  have := exactHeight_inv K x
  unfold exactHeight at this ⊢
  simp only [add_div] at this ⊢
  linarith

end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.ExactHeightLocal

open scoped BigOperators

section Local
variable {K : Type*} [Field K]

theorem abv_root_le (v : AbsoluteValue K ℝ) {m : ℕ} (hm : 0 < m)
    (a : Fin m → K) (u : K) (hu : u ^ m = ∑ i, a i * u ^ (i : ℕ)) :
    max (v u) 1 ≤ (m : ℝ) * ∏ i, max (v (a i)) 1 := by
  let A := ∏ i, max (v (a i)) 1
  have hA : 1 ≤ A := Finset.one_le_prod₀ fun i _ => le_max_right _ _
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : 1 ≤ (m : ℝ) * A := by nlinarith
  apply max_le _ hbase
  by_cases hv : v u ≤ 1
  · exact hv.trans hbase
  have hv1 : 1 < v u := lt_of_not_ge hv
  have hcoeff (i : Fin m) : v (a i) ≤ A := by
    exact Finset.le_prod_max_one (Finset.mem_univ i) (fun j => v (a j))
  have hp (i : Fin m) : (v u) ^ (i : ℕ) ≤ (v u) ^ (m - 1) :=
    pow_le_pow_right₀ hv1.le (by omega)
  have hsum : (v u) ^ m ≤ (m : ℝ) * (A * (v u) ^ (m - 1)) := by
    calc
      (v u) ^ m = v (∑ i, a i * u ^ (i : ℕ)) := by rw [← hu, map_pow]
      _ ≤ ∑ i, v (a i * u ^ (i : ℕ)) := v.sum_le _ _
      _ ≤ ∑ _i : Fin m, A * (v u) ^ (m - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [map_mul, map_pow]
        exact mul_le_mul (hcoeff i) (hp i) (pow_nonneg (v.nonneg u) _) (by positivity)
      _ = (m : ℝ) * (A * (v u) ^ (m - 1)) := by simp
  have hpow : 0 < (v u) ^ (m - 1) := pow_pos (lt_trans zero_lt_one hv1) _
  have hrewrite : (v u) ^ m = (v u) * (v u) ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hrewrite, ← mul_assoc] at hsum
  exact (mul_le_mul_iff_left₀ hpow).mp hsum

theorem nonarch_root_le (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {m : ℕ} (hm : 0 < m) (a : Fin m → K) (u : K)
    (hu : u ^ m = ∑ i, a i * u ^ (i : ℕ)) :
    max (v u) 1 ≤ ∏ i, max (v (a i)) 1 := by
  let A := ∏ i, max (v (a i)) 1
  have hA : 1 ≤ A := Finset.one_le_prod₀ fun i _ => le_max_right _ _
  apply max_le _ hA
  by_cases hu1 : v u ≤ 1
  · exact hu1.trans hA
  have hv1 : 1 < v u := lt_of_not_ge hu1
  have hcoeff (i : Fin m) : v (a i) ≤ A :=
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => v (a j))
  have hp (i : Fin m) : (v u) ^ (i : ℕ) ≤ (v u) ^ (m - 1) :=
    pow_le_pow_right₀ hv1.le (by omega)
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hsum : (v u) ^ m ≤ A * (v u) ^ (m - 1) := by
    calc
      (v u) ^ m = v (∑ i, a i * u ^ (i : ℕ)) := by rw [← hu, map_pow]
      _ ≤ ⨆ i, v (a i * u ^ (i : ℕ)) := hv.apply_sum_univ_le
      _ ≤ A * (v u) ^ (m - 1) := by
        apply ciSup_le
        intro i
        rw [map_mul, map_pow]
        exact mul_le_mul (hcoeff i) (hp i) (pow_nonneg (v.nonneg u) _) (by positivity)
  have hpow : 0 < (v u) ^ (m - 1) := pow_pos (lt_trans zero_lt_one hv1) _
  have hrewrite : (v u) ^ m = (v u) * (v u) ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hrewrite] at hsum
  exact (mul_le_mul_iff_left₀ hpow).mp hsum

end Local

end PlanarUnitDistances.ExactHeightLocal

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real ExactHeightLocal
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma posLog_max_one (r : ℝ) (hr : 0 ≤ r) : log⁺ (max r 1) = log⁺ r := by
  rw [posLog_eq_log_max_one (by positivity),posLog_eq_log_max_one hr]
  congr 1
  simp [max_comm]

omit [NumberField K] [IsGalois ℚ K] in
lemma local_posLog_root (v : AbsoluteValue K ℝ) {m : ℕ} (hm : 0 < m)
    (a : Fin m → K) (x : K) (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    log⁺ (v x) ≤ log m + ∑ i, log⁺ (v (a i)) := by
  have h := abv_root_le v hm a x hx
  have h' := (posLog_le_posLog (neg_one_lt_zero.le.trans (v.nonneg x)) ((le_max_left _ _).trans h)).trans
    (posLog_mul (x := (m:ℝ)) (y := ∏ i, max (v (a i)) 1))
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmEq : log⁺ (m:ℝ) = log m := by rw [posLog_eq_log_max_one (by positivity),max_eq_right hmR]
  rw [hmEq] at h'
  have hprod := posLog_prod univ (fun i => max (v (a i)) 1)
  simp only [posLog_max_one _ (v.nonneg _)] at hprod
  linarith

omit [NumberField K] [IsGalois ℚ K] in
lemma local_nonarch_posLog_root (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {m : ℕ} (hm : 0 < m) (a : Fin m → K) (x : K)
    (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    log⁺ (v x) ≤ ∑ i, log⁺ (v (a i)) := by
  have h := nonarch_root_le v hv hm a x hx
  have h' := (posLog_le_posLog (neg_one_lt_zero.le.trans (v.nonneg x)) ((le_max_left _ _).trans h)).trans
    (posLog_prod univ (fun i => max (v (a i)) 1))
  simpa only [posLog_max_one _ (v.nonneg _)] using h'

omit [IsGalois ℚ K] in
lemma exactHeight_root_le {m : ℕ} (hm : 0 < m) (a : Fin m → K) (x : K)
    (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    exactHeight K x ≤ log m + ∑ i, exactHeight K (a i) := by
  have harch : (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) ≤
      (Module.finrank ℚ K : ℝ)*log m +
      ∑ i, ∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ (a i)) := by
    calc
      _ ≤ ∑ σ : K →ₐ[ℚ] ℂ, (log m + ∑ i, log⁺ (infiniteEntry K σ (a i))) :=
        sum_le_sum fun σ _ => local_posLog_root K (infiniteEntry K σ) hm a x hx
      _ = _ := by
        rw [sum_add_distrib,sum_comm]
        simp only [sum_const,card_univ,nsmul_eq_mul,infiniteEntry_count]
  have hfin : (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) ≤
      ∑ i, ∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 (a i)) := by
    rw [← finsum_sum_comm univ (fun (v : Nat.Primes × Gal(K/ℚ)) (i : Fin m) => log⁺ (finiteEntry K v.1 v.2 (a i)))
      (fun i _ => finite_posLog_support K (a i))]
    apply finsum_le_finsum (finite_posLog_support K x)
      (Function.HasFiniteSupport.sum (fun i => finite_posLog_support K (a i)) univ)
    intro v
    exact local_nonarch_posLog_root K (finiteEntry K v.1 v.2)
      (finiteEntry_nonarch K v.1 v.2) hm a x hx
  have hh := div_le_div_of_nonneg_right (add_le_add harch hfin) (finrank_pos K).le
  unfold exactHeight
  simp only [add_div,mul_div_cancel_left₀ _ (finrank_pos K).ne',sum_div,sum_add_distrib] at hh ⊢
  linarith

end
end PlanarUnitDistances.WeightedAbsoluteValues

end OAI
