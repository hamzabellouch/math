import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

open scoped Pointwise
namespace WeightedTorusJets

section

theorem finrank_sup_quadratic {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) (hK : Module.finrank F K = 2)
    (hL : Module.finrank F L = 2) (hne : K ≠ L) :
    Module.finrank F ↥(K ⊔ L) = 4 := by
  have : FiniteDimensional F K := Module.finite_of_finrank_eq_succ hK
  have : FiniteDimensional F L := Module.finite_of_finrank_eq_succ hL
  have hle : Module.finrank F ↥(K ⊔ L) ≤ 4 := by
    simpa [hK, hL] using K.finrank_sup_le L
  have hdiv : 2 ∣ Module.finrank F ↥(K ⊔ L) := by
    simpa [hK] using IntermediateField.finrank_dvd_of_le_right
      (show K ≤ K ⊔ L from le_sup_left)
  have hlt : 2 < Module.finrank F ↥(K ⊔ L) := by
    by_contra hc
    have hKeq : K = K ⊔ L := IntermediateField.eq_of_le_of_finrank_le le_sup_left
      (by omega)
    have hLK : L ≤ K := hKeq.symm ▸ le_sup_right
    have hLK_eq : L = K := IntermediateField.eq_of_le_of_finrank_le hLK (by omega)
    exact hne hLK_eq.symm
  omega

theorem biquadratic_monomials_integral {E : Type*} [CommRing E] [Algebra ℤ E]
    (a b : E) (d e : ℤ) (ha : a ^ 2 = d) (hb : b ^ 2 = e) :
    IsIntegral ℤ (1 : E) ∧ IsIntegral ℤ a ∧ IsIntegral ℤ b ∧ IsIntegral ℤ (a * b) := by
  have hai : IsIntegral ℤ a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_intCast d)
  have hbi : IsIntegral ℤ b := IsIntegral.of_pow (by decide : 0 < 2)
    (hb ▸ isIntegral_intCast e)
  exact ⟨isIntegral_one, hai, hbi, hai.mul hbi⟩

theorem span_pair_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (d : F) (ha : a ^ 2 = algebraMap F E d) :
    Submodule.span F ({1, a} : Set E) = (Algebra.adjoin F {a}).toSubmodule := by
  have heval : Polynomial.aeval a (Polynomial.X ^ 2 - Polynomial.C d) = 0 := by
    simpa using sub_eq_zero.mpr ha
  have h := Submodule.span_range_natDegree_eq_adjoin
    (Polynomial.monic_X_pow_sub_C d (by decide : 2 ≠ 0)) heval
  simpa [Finset.range_add_one, Set.pair_comm] using h

theorem span_biquadratic_monomials {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) :
    Submodule.span F (Set.range ![1, a, b, a * b]) =
      (Algebra.adjoin F ({a, b} : Set E)).toSubmodule := by
  have hsets : ({1, a} : Set E) * ({1, b} : Set E) = Set.range ![1, a, b, a * b] := by
    ext x
    simp only [Set.mem_mul, Matrix.range_cons, Matrix.range_empty, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]
    aesop
  rw [← hsets, ← Submodule.span_mul_span, span_pair_sqrt a d ha,
    span_pair_sqrt b e hb, ← Algebra.adjoin_union_coe_submodule]
  simp [Set.pair_comm]

noncomputable def biquadraticBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e)
    (hgen : Algebra.adjoin F ({a, b} : Set E) = ⊤)
    (hdim : Module.finrank F E = 4) : Module.Basis (Fin 4) F E :=
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ hdim
  basisOfTopLeSpanOfCardEqFinrank ![1, a, b, a * b]
    (by rw [span_biquadratic_monomials a b d e ha hb, hgen]; rfl)
    (by simpa using hdim.symm)

@[simp]
theorem biquadraticBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e)
    (hgen : Algebra.adjoin F ({a, b} : Set E) = ⊤)
    (hdim : Module.finrank F E = 4) (i : Fin 4) :
    biquadraticBasis a b d e ha hb hgen hdim i = ![1, a, b, a * b] i := by
  simp [biquadraticBasis]

theorem finrank_adjoin_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a : E) (d : F) (ha : a ^ 2 = algebraMap F E d) (hd : ¬ IsSquare d) :
    Module.finrank F (IntermediateField.adjoin F {a}) = 2 := by
  have hai : IsIntegral F a := IsIntegral.of_pow (by decide : 0 < 2)
    (ha ▸ isIntegral_algebraMap)
  have : FiniteDimensional F (IntermediateField.adjoin F {a}) :=
    IntermediateField.adjoin.finiteDimensional hai
  have hpos := Module.finrank_pos (R := F) (M := IntermediateField.adjoin F {a})
  have hne : Module.finrank F (IntermediateField.adjoin F {a}) ≠ 1 := by
    intro hone
    have hamem := IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hone
    obtain ⟨r, hr⟩ := (IntermediateField.mem_bot).mp hamem
    apply hd
    refine ⟨r, ?_⟩
    apply (algebraMap F E).injective
    simpa [map_mul, hr, sq] using ha.symm
  have hle : Module.finrank F (IntermediateField.adjoin F {a}) ≤ 2 := by
    rw [← IntermediateField.finrank_eq_finrank_subalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hai.isAlgebraic]
    change Module.finrank F (Algebra.adjoin F {a}).toSubmodule ≤ 2
    rw [← span_pair_sqrt a d ha]
    have h := finrank_range_le_card (R := F) ![(1 : E), a]
    change Module.finrank F (Submodule.span F (Set.range ![(1 : E), a])) ≤ 2 at h
    rwa [Matrix.range_cons_cons_empty] at h
  omega

theorem adjoin_pair_generators {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) :
    let K := IntermediateField.adjoin F ({a, b} : Set E)
    let a' : K := ⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩
    let b' : K := ⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩
    Algebra.adjoin F ({a', b'} : Set K) = ⊤ := by
  dsimp only
  let K := IntermediateField.adjoin F ({a, b} : Set E)
  let a' : K := ⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩
  let b' : K := ⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩
  have hai : IsIntegral F a' := IsIntegral.of_pow (by decide : 0 < 2)
    (by have h : a' ^ 2 = algebraMap F K d := Subtype.ext ha
        rw [h]; exact isIntegral_algebraMap)
  have hbi : IsIntegral F b' := IsIntegral.of_pow (by decide : 0 < 2)
    (by have h : b' ^ 2 = algebraMap F K e := Subtype.ext hb
        rw [h]; exact isIntegral_algebraMap)
  apply Algebra.adjoin_eq_top_of_intermediateField
    (by intro x hx; rcases hx with rfl | rfl
        · exact hai.isAlgebraic
        · exact hbi.isAlgebraic)
  apply IntermediateField.map_injective K.val
  simp only [IntermediateField.adjoin_map, Set.image_pair, IntermediateField.val_mk]
  ext x
  simp [IntermediateField.mem_map, K]

theorem finrank_adjoin_pair_sqrt {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) :
    Module.finrank F (IntermediateField.adjoin F ({a, b} : Set E)) = 4 := by
  rw [← Set.singleton_union, IntermediateField.adjoin_union]
  exact finrank_sup_quadratic _ _ (finrank_adjoin_sqrt a d ha hd)
    (finrank_adjoin_sqrt b e hb he) hne

noncomputable def sqrtPairBasis {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) :
    Module.Basis (Fin 4) F (IntermediateField.adjoin F ({a, b} : Set E)) :=
  let a' := (⟨a, IntermediateField.subset_adjoin F _ (by simp)⟩ :
    IntermediateField.adjoin F ({a, b} : Set E))
  let b' := (⟨b, IntermediateField.subset_adjoin F _ (by simp)⟩ :
    IntermediateField.adjoin F ({a, b} : Set E))
  biquadraticBasis a' b' d e (Subtype.ext ha) (Subtype.ext hb)
    (adjoin_pair_generators a b d e ha hb)
    (finrank_adjoin_pair_sqrt a b d e ha hb hd he hne)

@[simp]
theorem coe_sqrtPairBasis_apply {F E : Type*} [Field F] [Field E] [Algebra F E]
    (a b : E) (d e : F) (ha : a ^ 2 = algebraMap F E d)
    (hb : b ^ 2 = algebraMap F E e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin F {a} ≠ IntermediateField.adjoin F {b}) (i : Fin 4) :
    (sqrtPairBasis a b d e ha hb hd he hne i : E) = ![1, a, b, a * b] i := by
  fin_cases i <;> simp [sqrtPairBasis]

open Module

variable {K : Type*} [Field K] [Algebra ℚ K]

noncomputable def biquadraticLinearMap (v : Basis (Fin 4) ℚ K) (a' b' : K) : K →ₗ[ℚ] K :=
  v.constr ℚ ![1, a', b', a' * b']

lemma biquadraticLinearMap_basis (v : Basis (Fin 4) ℚ K) (a' b' : K) (i : Fin 4) :
    biquadraticLinearMap v a' b' (v i) = ![1, a', b', a' * b'] i :=
  v.constr_basis ℚ _ i

lemma biquadraticLinearMap_mul (v : Basis (Fin 4) ℚ K) (a b a' b' : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (ha' : a' * a' = algebraMap ℚ K d) (hb' : b' * b' = algebraMap ℚ K e) :
    ∀ x y, biquadraticLinearMap v a' b' (x * y) =
      biquadraticLinearMap v a' b' x * biquadraticLinearMap v a' b' y := by
  let f := biquadraticLinearMap v a' b'
  have hf (i : Fin 4) : f (![1, a, b, a * b] i) = ![1, a', b', a' * b'] i := by
    rw [← hv i]
    exact biquadraticLinearMap_basis v a' b' i
  have hf1 : f 1 = 1 := hf 0
  have hfa : f a = a' := hf 1
  have hfb : f b = b' := hf 2
  have hfab : f (a * b) = a' * b' := hf 3
  have hfc (c : ℚ) (x : K) : f ((algebraMap ℚ K c) * x) = (algebraMap ℚ K c) * f x := by
    simpa only [Algebra.smul_def] using f.map_smul c x
  have hfq (c : ℚ) : f (algebraMap ℚ K c) = algebraMap ℚ K c := by simpa [hf1] using hfc c 1
  have h1 : a * (a * b) = (algebraMap ℚ K d) * b := by rw [← mul_assoc, ha]
  have h2 : b * (a * b) = (algebraMap ℚ K e) * a := by rw [mul_left_comm, hb, mul_comm]
  have h3 : (a * b) * (a * b) = (algebraMap ℚ K (d * e)) := by
    rw [mul_mul_mul_comm, ha, hb, map_mul]
  have h1' : a' * (a' * b') = (algebraMap ℚ K d) * b' := by rw [← mul_assoc, ha']
  have h2' : b' * (a' * b') = (algebraMap ℚ K e) * a' := by rw [mul_left_comm, hb', mul_comm]
  have h3' : (a' * b') * (a' * b') = (algebraMap ℚ K (d * e)) := by
    rw [mul_mul_mul_comm, ha', hb', map_mul]
  apply (LinearMap.map_mul_iff f).mpr
  apply v.ext
  intro i
  apply v.ext
  intro j
  change f (v i * v j) = f (v i) * f (v j)
  rw [hv i, hv j]
  fin_cases i <;> fin_cases j <;> simp_all
  all_goals simp_all [mul_comm]

noncomputable def biquadraticSignEquiv (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t : Bool) : K ≃ₐ[ℚ] K := by
  let a' := if s then -a else a
  let b' := if t then -b else b
  let f := biquadraticLinearMap v a' b'
  have hf (i : Fin 4) : f (![1, a, b, a * b] i) = ![1, a', b', a' * b'] i := by
    rw [← hv i]
    exact biquadraticLinearMap_basis v a' b' i
  have hf1 : f 1 = 1 := hf 0
  have hfa : f a = a' := hf 1
  have hfb : f b = b' := hf 2
  have hfab : f (a * b) = a' * b' := hf 3
  have hcomp : f.comp f = LinearMap.id := by
    apply v.ext
    intro i
    change f (f (v i)) = v i
    rw [hv i]
    cases s <;> cases t <;> fin_cases i <;> simp_all [a', b']
  have hinv : Function.Involutive f := fun x => LinearMap.congr_fun hcomp x
  refine AlgEquiv.ofLinearEquiv (LinearEquiv.ofInvolutive f hinv) hf1 ?_
  apply biquadraticLinearMap_mul v a b a' b' d e hv ha hb
  · cases s <;> simpa [a'] using ha
  · cases t <;> simpa [b'] using hb

lemma biquadraticSignEquiv_basis (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t : Bool) (i : Fin 4) :
    biquadraticSignEquiv v a b d e hv ha hb s t (v i) =
      ![1, if s then -a else a, if t then -b else b,
        (if s then -a else a) * (if t then -b else b)] i :=
  biquadraticLinearMap_basis v _ _ i

lemma biquadratic_algEquiv_ext (v : Basis (Fin 4) ℚ K) (a b : K)
    (hv : ∀ i, v i = ![1, a, b, a * b] i) (f g : K ≃ₐ[ℚ] K)
    (ha : f a = g a) (hb : f b = g b) : f = g := by
  apply AlgEquiv.toLinearMap_injective
  apply v.ext
  intro i
  change f (v i) = g (v i)
  rw [hv i]
  fin_cases i <;> simp_all

lemma quadratic_algEquiv_dichotomy (a : K) (d : ℚ)
    (ha : a * a = algebraMap ℚ K d) (f : K ≃ₐ[ℚ] K) :
    f a = a ∨ f a = -a := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  simpa only [pow_two, ← map_mul, ha] using f.commutes d

lemma biquadratic_automorphism_eq_sign (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f : K ≃ₐ[ℚ] K) :
    ∃ s t : Bool, f = biquadraticSignEquiv v a b d e hv ha hb s t := by
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  rcases quadratic_algEquiv_dichotomy a d ha f with hfa | hfa <;>
    rcases quadratic_algEquiv_dichotomy b e hb f with hfb | hfb
  · refine ⟨false, false, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs false false 1).symm
    · exact hfb.trans (hs false false 2).symm
  · refine ⟨false, true, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs false true 1).symm
    · exact hfb.trans (hs false true 2).symm
  · refine ⟨true, false, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs true false 1).symm
    · exact hfb.trans (hs true false 2).symm
  · refine ⟨true, true, biquadratic_algEquiv_ext v a b hv f _ ?_ ?_⟩
    · exact hfa.trans (hs true true 1).symm
    · exact hfb.trans (hs true true 2).symm

lemma biquadraticSignEquiv_injective (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    Function.Injective (fun st : Bool × Bool =>
      biquadraticSignEquiv v a b d e hv ha hb st.1 st.2) := by
  let : CharZero K := algebraRat.charZero K
  have ha0 : a ≠ 0 := by simpa [hv] using v.ne_zero 1
  have hb0 : b ≠ 0 := by simpa [hv] using v.ne_zero 2
  have hana : a ≠ -a := fun h => ha0 (CharZero.eq_neg_self_iff.mp h)
  have hbna : b ≠ -b := fun h => hb0 (CharZero.eq_neg_self_iff.mp h)
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  intro st st' h
  have hA := congrArg (fun f : K ≃ₐ[ℚ] K => f a) h
  have hB := congrArg (fun f : K ≃ₐ[ℚ] K => f b) h
  have hsA (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t a =
      if s then -a else a := hs s t 1
  have hsB (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t b =
      if t then -b else b := hs s t 2
  simp only [hsA] at hA
  simp only [hsB] at hB
  clear hs hsA hsB h
  rcases st with ⟨s, t⟩
  rcases st' with ⟨s', t'⟩
  cases s <;> cases s' <;> cases t <;> cases t' <;> simp_all

lemma biquadratic_card_automorphisms (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    Nat.card (K ≃ₐ[ℚ] K) = 4 := by
  let f := fun st : Bool × Bool => biquadraticSignEquiv v a b d e hv ha hb st.1 st.2
  have hf : Function.Bijective f := by
    refine ⟨biquadraticSignEquiv_injective v a b d e hv ha hb, ?_⟩
    intro g
    obtain ⟨s, t, h⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb g
    exact ⟨⟨s, t⟩, h.symm⟩
  simpa using (Nat.card_congr (Equiv.ofBijective f hf)).symm

lemma biquadratic_isGalois (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    IsGalois ℚ K := by
  let : FiniteDimensional ℚ K := Module.Finite.of_basis v
  apply IsGalois.of_card_aut_eq_finrank
  rw [biquadratic_card_automorphisms v a b d e hv ha hb, Module.finrank_eq_card_basis v]
  rfl

lemma biquadraticSignEquiv_mul (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (s t s' t' : Bool) :
    biquadraticSignEquiv v a b d e hv ha hb s t *
        biquadraticSignEquiv v a b d e hv ha hb s' t' =
      biquadraticSignEquiv v a b d e hv ha hb (s.xor s') (t.xor t') := by
  have hs (s t : Bool) (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb s t i
  simp_rw [hv] at hs
  have hsA (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t a =
      if s then -a else a := hs s t 1
  have hsB (s t : Bool) : biquadraticSignEquiv v a b d e hv ha hb s t b =
      if t then -b else b := hs s t 2
  apply biquadratic_algEquiv_ext v a b hv
  · cases s <;> cases s' <;> simp [AlgEquiv.mul_apply, hsA]
  · cases t <;> cases t' <;> simp [AlgEquiv.mul_apply, hsB]

lemma biquadratic_automorphisms_commute (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f g : K ≃ₐ[ℚ] K) : Commute f g := by
  obtain ⟨s, t, rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb f
  obtain ⟨s', t', rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb g
  change _ = _
  simp only [biquadraticSignEquiv_mul, Bool.xor_comm]

lemma biquadraticSignEquiv_identity (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e) :
    biquadraticSignEquiv v a b d e hv ha hb false false = 1 := by
  have hs (i : Fin 4) := biquadraticSignEquiv_basis v a b d e hv ha hb false false i
  simp_rw [hv] at hs
  apply biquadratic_algEquiv_ext v a b hv
  · exact hs 1
  · exact hs 2

lemma biquadratic_four_automorphisms (v : Basis (Fin 4) ℚ K) (a b : K) (d e : ℚ)
    (hv : ∀ i, v i = ![1, a, b, a * b] i)
    (ha : a * a = algebraMap ℚ K d) (hb : b * b = algebraMap ℚ K e)
    (f : K ≃ₐ[ℚ] K) :
    let σ := biquadraticSignEquiv v a b d e hv ha hb true false
    let τ := biquadraticSignEquiv v a b d e hv ha hb false true
    f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ := by
  dsimp
  obtain ⟨s, t, rfl⟩ := biquadratic_automorphism_eq_sign v a b d e hv ha hb f
  cases s <;> cases t <;>
    simp [biquadraticSignEquiv_mul, biquadraticSignEquiv_identity]

end

lemma sqrtPair_isGalois {L : Type*} [Field L] [CharZero L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    IsGalois ℚ (IntermediateField.adjoin ℚ ({a, b} : Set L)) := by
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b d e ha hb hd he hne
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b d e ha hb hd he hne i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' * a' = algebraMap ℚ B d := by
    apply Subtype.ext
    simpa [a', pow_two] using ha
  have hb' : b' * b' = algebraMap ℚ B e := by
    apply Subtype.ext
    simpa [b', pow_two] using hb
  exact biquadratic_isGalois v a' b' d e hv ha' hb'

lemma sqrtPair_four_automorphisms {L : Type*} [Field L] [CharZero L]
    (a b : L) (d e : ℚ) (ha : a ^ 2 = algebraMap ℚ L d)
    (hb : b ^ 2 = algebraMap ℚ L e) (hd : ¬ IsSquare d) (he : ¬ IsSquare e)
    (hne : IntermediateField.adjoin ℚ {a} ≠ IntermediateField.adjoin ℚ {b}) :
    let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
    let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
    ∃ σ τ : B ≃ₐ[ℚ] B,
      σ a' = -a' ∧ σ b' = b' ∧ τ a' = a' ∧ τ b' = -b' ∧
      Nat.card (B ≃ₐ[ℚ] B) = 4 ∧
      (∀ f : B ≃ₐ[ℚ] B, f = 1 ∨ f = σ ∨ f = τ ∨ f = σ * τ) ∧
      (∀ f g : B ≃ₐ[ℚ] B, Commute f g) := by
  dsimp
  let B := IntermediateField.adjoin ℚ ({a, b} : Set L)
  let a' : B := ⟨a, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let b' : B := ⟨b, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let v := sqrtPairBasis a b d e ha hb hd he hne
  have hv (i : Fin 4) : v i = ![1, a', b', a' * b'] i := by
    apply Subtype.ext
    change (sqrtPairBasis a b d e ha hb hd he hne i : L) = _
    rw [coe_sqrtPairBasis_apply]
    fin_cases i <;> rfl
  have ha' : a' * a' = algebraMap ℚ B d := by
    apply Subtype.ext
    simpa [a', pow_two] using ha
  have hb' : b' * b' = algebraMap ℚ B e := by
    apply Subtype.ext
    simpa [b', pow_two] using hb
  let σ := biquadraticSignEquiv v a' b' d e hv ha' hb' true false
  let τ := biquadraticSignEquiv v a' b' d e hv ha' hb' false true
  have hs (s t : Bool) (i : Fin 4) :=
    biquadraticSignEquiv_basis v a' b' d e hv ha' hb' s t i
  simp_rw [hv] at hs
  refine ⟨σ, τ, hs true false 1, hs true false 2, hs false true 1,
    hs false true 2, biquadratic_card_automorphisms v a' b' d e hv ha' hb', ?_, ?_⟩
  · exact biquadratic_four_automorphisms v a' b' d e hv ha' hb'
  · exact biquadratic_automorphisms_commute v a' b' d e hv ha' hb'

end WeightedTorusJets

open scoped NumberField

namespace WeightedTorusJets

theorem ringOfIntegers_map_dvd_iff
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (f : K →ₐ[ℚ] L) (a b : 𝓞 K) :
    NumberField.RingOfIntegers.mapRingHom f.toRingHom a ∣
      NumberField.RingOfIntegers.mapRingHom f.toRingHom b ↔ a ∣ b := by
  let F := NumberField.RingOfIntegers.mapRingHom f.toRingHom
  have hF : Function.Injective F := by
    intro x y h
    apply NumberField.RingOfIntegers.ext
    apply f.injective
    exact congrArg (fun z : 𝓞 L ↦ (z : L)) h
  refine ⟨fun h ↦ ?_, fun h ↦ map_dvd F h⟩
  change F a ∣ F b at h
  by_cases ha : a = 0
  · subst a
    rw [map_zero, zero_dvd_iff] at h
    have hb : b = 0 := hF (h.trans (map_zero F).symm)
    simp [hb]
  · have haK : (a : K) ≠ 0 := fun h ↦ ha (NumberField.RingOfIntegers.ext h)
    have haL : f (a : K) ≠ 0 := fun h ↦ haK (f.injective (h.trans (map_zero f).symm))
    obtain ⟨c, hc⟩ := h
    have hquot : f ((b : K) / (a : K)) = (c : L) := by
      rw [map_div₀, div_eq_iff haL]
      simpa [F, map_mul, mul_comm] using congrArg (fun z : 𝓞 L ↦ (z : L)) hc
    have hint : IsIntegral ℤ ((b : K) / (a : K)) := by
      apply (isIntegral_algHom_iff (f.restrictScalars ℤ) f.injective).mp
      change IsIntegral ℤ (f ((b : K) / (a : K)))
      rw [hquot]
      exact c.2
    refine ⟨⟨(b : K) / (a : K), hint⟩, ?_⟩
    apply NumberField.RingOfIntegers.ext
    change (b : K) = (a : K) * ((b : K) / (a : K))
    rw [mul_comm, div_mul_cancel₀ _ haK]

theorem frobenius_congruence_descends
    {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    (f : K →ₐ[ℚ] L) (σ : K ≃ₐ[ℚ] K) (τ : L ≃ₐ[ℚ] L)
    (hcomm : ∀ x : K, f (σ x) = τ (f x)) (p : ℕ)
    (hfrob : ∀ y : 𝓞 L, (p : 𝓞 L) ∣ y ^ p - τ • y) (x : 𝓞 K) :
    (p : 𝓞 K) ∣ x ^ p - σ • x := by
  let F := NumberField.RingOfIntegers.mapRingHom f.toRingHom
  have hmap : F (σ • x) = τ • F x := by
    apply NumberField.RingOfIntegers.ext
    exact hcomm (x : K)
  apply (ringOfIntegers_map_dvd_iff f (p : 𝓞 K) (x ^ p - σ • x)).mp
  change F (p : 𝓞 K) ∣ F (x ^ p - σ • x)
  simpa only [map_natCast, map_sub, map_pow, hmap] using hfrob (F x)

end WeightedTorusJets

end SiegelZeros

end OAI
