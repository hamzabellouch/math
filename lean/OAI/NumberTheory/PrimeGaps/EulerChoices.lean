import OAI.NumberTheory.PrimeGaps.FourierNormalization

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

theorem eulerChoices_norm_tsum_le {κ : Type*} [DecidableEq κ] {A : κ → Type*} [∀ p, Fintype (A p)]
    (w : (p : κ) → A p → ℂ) (hw : Summable (eulerChoiceNorm w)) :
    (∑' c : EulerChoices A, ‖eulerChoiceTerm w c‖) ≤ Real.exp (∑' p, eulerChoiceNorm w p) := by
  classical
  have hc := eulerChoice_summable_norm w hw
  rw [hc.tsum_sigma]
  simp_rw [tsum_fintype, eulerChoice_sum_norm]
  have hs := summable_finsetProd_of_summable_nonneg (eulerChoiceNorm_nonneg w) hw
  apply hs.tsum_le_of_sum_le
  intro T
  calc
    _ ≤ ∑ s∈(T.biUnion id).powerset, ∏ p∈s, eulerChoiceNorm w p :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun s hs => Finset.mem_powerset.mpr
        (Finset.subset_biUnion_of_mem id hs))
        (fun s _ _ => Finset.prod_nonneg fun _ _ => eulerChoiceNorm_nonneg w _)
    _ = ∏ p∈T.biUnion id, (1+eulerChoiceNorm w p) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p∈T.biUnion id, eulerChoiceNorm w p) :=
      Real.prod_one_add_le_exp_sum _ (eulerChoiceNorm_nonneg w)
    _ ≤ _ := Real.exp_le_exp.mpr (hw.sum_le_tsum _ fun p _ => eulerChoiceNorm_nonneg w p)

theorem primeMonomial_norm_le_rpow {ι : Type*} {p : ℕ} (hp : 1≤p)
    (z : ι → ℂ) (S : Finset ι) (hS : S.Nonempty) {ε : ℝ} (hε : 0≤ε)
    (hz : ∀ i∈S, ε≤(z i).re) :
    ‖primeMonomial p z S‖ ≤ (p:ℝ)^(-ε) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast (by omega : 0<p)
  have hl : 0≤Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  obtain ⟨i,hi⟩ := hS
  have hs : ε≤∑ j∈S, (z j).re := (hz i hi).trans
    (Finset.single_le_sum (fun j hj => hε.trans (hz j hj)) hi)
  rw [primeMonomial, Complex.norm_exp, Real.rpow_def_of_pos hpR]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, sub_zero, Complex.re_sum]
  nlinarith

noncomputable def primeChoiceWeight {ι : Type*} (δ : ℕ) (z : ι → ℂ)
    (p : Nat.Primes) (S : Finset ι) : ℂ :=
  ((p:ℂ)-δ)⁻¹*((-1:ℂ)^S.card*primeMonomial p z S)

theorem primeChoiceWeight_norm_bound {ι : Type*} {δ : ℕ} (hδ : δ≤1)
    (z : ι → ℂ) (p : Nat.Primes) (S : Finset ι) (hS : S.Nonempty)
    {ε : ℝ} (hε : 0≤ε) (hz : ∀ i∈S, ε≤(z i).re) :
    ‖primeChoiceWeight δ z p S‖ ≤ 2/(p:ℝ)^(1+ε) := by
  have hd := delta_bounds p.property.two_le hδ
  have he' : ‖(p:ℂ)-δ‖ = (p:ℝ)-δ := by
    have h := Complex.norm_of_nonneg hd.1.le
    simpa using h
  have hp0 : (0:ℝ)<p := by exact_mod_cast p.property.pos
  calc
    _ = ((p:ℝ)-δ)⁻¹*‖primeMonomial p z S‖ := by
      simp only [primeChoiceWeight, norm_mul, norm_inv, he', norm_pow, norm_neg,
        norm_one, one_pow, one_mul]
    _ ≤ (2*(p:ℝ)⁻¹)*(p:ℝ)^(-ε) :=
      mul_le_mul hd.2.1 (primeMonomial_norm_le_rpow p.property.one_le z S hS hε hz)
        (norm_nonneg _) (by positivity)
    _ = _ := by rw [Real.rpow_neg hp0.le, Real.rpow_add hp0, Real.rpow_one]; field_simp

theorem prime_power_tsum_le_log_zeta {s : ℝ} (hs : 1<s) :
    (∑' p : Nat.Primes, 1/(p:ℝ)^s) ≤ Real.log (riemannZeta (s:ℂ)).re := by
  have hsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / ((n:ℝ)^s*Real.log n)) :=
    (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
      (mangoldt_log_term_nonneg s) (mangoldt_log_term_le s)
  have hprime := (Real.summable_one_div_nat_rpow.mpr hs).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have he (p : Nat.Primes) :
      ArithmeticFunction.vonMangoldt (p:ℕ)/((p:ℝ)^s*Real.log (p:ℝ)) = 1/(p:ℝ)^s := by
    have hl : Real.log (p:ℝ)≠0 := (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.property]
    field_simp
  rw [log_riemannZeta_eq hs]
  apply hprime.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p:ℕ)) (fun _ _ => Subtype.ext)
    (fun n _ => mangoldt_log_term_nonneg s n) (fun p => (he p).symm.le) hsum

noncomputable def primeAllowedWeight {ι : Type*} (δ : ℕ) (A : ℕ → Finset (Finset ι))
    (z : ι → ℂ) (p : Nat.Primes) (S : {S // S∈A p}) : ℂ := primeChoiceWeight δ z p S

theorem primeAllowedWeight_norm_le {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0≤ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) (p : Nat.Primes) :
    eulerChoiceNorm (primeAllowedWeight δ A z) p ≤ (2*R)/(p:ℝ)^(1+ε) := by
  classical
  have hb : ∀ S : {S // S∈A p}, ‖primeAllowedWeight δ A z p S‖ ≤ 2/(p:ℝ)^(1+ε) :=
    fun S => primeChoiceWeight_norm_bound hδ z p S (hA p S S.property) hε (fun _ _ => hz _)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun S _ => hb S)
  have hs : ((A p).card:ℝ) ≤ R := by exact_mod_cast hR p
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe] at hh
  exact hh.trans (by calc
    _ ≤ (R:ℝ)*(2/(p:ℝ)^(1+ε)) := mul_le_mul_of_nonneg_right hs (by positivity)
    _ = _ := by ring)

theorem primeAllowedWeight_summable_norm {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    Summable (eulerChoiceNorm (primeAllowedWeight δ A z)) := by
  have hs := (Real.summable_one_div_nat_rpow.mpr (by linarith : 1<1+ε)).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have hs' : Summable (fun p : Nat.Primes => (2*R)/(p:ℝ)^(1+ε)) := by
    simpa only [Function.comp_def, mul_one_div] using hs.mul_left (2*R:ℝ)
  exact hs'.of_nonneg_of_le (eulerChoiceNorm_nonneg _) (primeAllowedWeight_norm_le hδ A z
    hε.le hA hR hz)

theorem primeEulerChoices_hasProd {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    HasProd (fun p : Nat.Primes => eulerP p δ (A p) z)
      (∑' c : EulerChoices (fun p : Nat.Primes => {S // S∈A p}),
        eulerChoiceTerm (primeAllowedWeight δ A z) c) := by
  apply (eulerChoices_hasProd _ (primeAllowedWeight_summable_norm hδ A z hε hA hR hz)).congr_fun
  intro p
  simp only [eulerP, primeAllowedWeight, primeChoiceWeight, ← Finset.mul_sum,
    ]
  congr 2
  exact (Finset.sum_coe_sort (A p) (fun S => (-1:ℂ)^S.card*primeMonomial p z S)).symm

theorem primeEulerChoices_norm_tsum_le {ι : Type*} {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    (∑' c : EulerChoices (fun p : Nat.Primes => {S // S∈A p}),
        ‖eulerChoiceTerm (primeAllowedWeight δ A z) c‖) ≤
      Real.exp ((2*R)*Real.log (riemannZeta ((1+ε:ℝ):ℂ)).re) := by
  have hsum := primeAllowedWeight_summable_norm hδ A z hε hA hR hz
  refine (eulerChoices_norm_tsum_le _ hsum).trans (Real.exp_le_exp.mpr ?_)
  have hs := (Real.summable_one_div_nat_rpow.mpr (by linarith : 1<1+ε)).comp_injective
    (fun p q : Nat.Primes => Subtype.ext)
  have hs' : Summable (fun p : Nat.Primes => (2*R)/(p:ℝ)^(1+ε)) := by
    simpa only [Function.comp_def, mul_one_div] using hs.mul_left (2*R:ℝ)
  calc
    _ ≤ ∑' p : Nat.Primes, (2*R)/(p:ℝ)^(1+ε) :=
      hsum.tsum_le_tsum (primeAllowedWeight_norm_le hδ A z hε.le hA hR hz) hs'
    _ = (2*R:ℝ)*(∑' p : Nat.Primes, 1/(p:ℝ)^(1+ε)) := by
      simp only [← tsum_mul_left, mul_one_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_power_tsum_le_log_zeta (by linarith)) (by positivity)

noncomputable def choiceSubset {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) : Finset ι := by
  classical
  exact if hp : p∈c.1 then (c.2 ⟨p,hp⟩).val else ∅

@[simp] theorem choiceSubset_of_mem {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∈c.1) :
    choiceSubset c p = (c.2 ⟨p,hp⟩).val := by simp [choiceSubset, hp]

@[simp] theorem choiceSubset_of_not_mem {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) {p : Nat.Primes} (hp : p∉c.1) :
    choiceSubset c p = ∅ := by simp [choiceSubset, hp]

noncomputable def choiceDivisors {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) : ℕ := by
  classical
  exact ∏ p∈c.1.filter (fun p => i∈choiceSubset c p), (p:ℕ)

theorem choiceDivisors_squarefree {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    Squarefree (choiceDivisors c i) := by
  classical
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p _ q _ hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes p.property q.property).mpr
      (fun he => hpq (Subtype.ext he)))
  · intro p _
    exact p.property.prime.squarefree

theorem prime_dvd_choiceDivisors {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) (i : ι) :
    (p:ℕ) ∣ choiceDivisors c i ↔ i∈choiceSubset c p := by
  classical
  rw [choiceDivisors, p.property.prime.dvd_finsetProd_iff]
  constructor
  · rintro ⟨q,hq,hpq⟩
    have he : p=q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp hpq)
    simpa [he] using (Finset.mem_filter.mp hq).2
  · intro hi
    have hp : p∈c.1 := by
      by_contra hn
      simp [choiceSubset_of_not_mem c hn] at hi
    exact ⟨p,Finset.mem_filter.mpr ⟨hp,hi⟩,dvd_refl _⟩

noncomputable def tuplePrimeSupport {ι : Type*} [Fintype ι] (d : ι → ℕ) : Finset Nat.Primes := by
  classical
  exact (Finset.univ.biUnion fun i => (d i).primeFactors).subtype Nat.Prime

theorem mem_tuplePrimeSupport {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i≠0) (p : Nat.Primes) : p∈tuplePrimeSupport d ↔ ∃ i, (p:ℕ)∣d i := by
  classical
  refine (Finset.mem_subtype (a := (⟨p.val,p.property⟩ : {n : ℕ // Nat.Prime n}))).trans ?_
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Nat.mem_primeFactors,
    p.property, true_and]
  constructor
  · rintro ⟨i,hi,_⟩
    exact ⟨i,hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,hi,hd i⟩

noncomputable def tuplePrimeSubset {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => (p:ℕ)∣d i

@[simp] theorem mem_tuplePrimeSubset {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (p : Nat.Primes) (i : ι) : i∈tuplePrimeSubset d p ↔ (p:ℕ)∣d i := by
  classical
  simp [tuplePrimeSubset]

theorem tuplePrimeSubset_nonempty_iff {ι : Type*} [Fintype ι] (d : ι → ℕ)
    (hd : ∀ i, d i≠0) (p : Nat.Primes) :
    (tuplePrimeSubset d p).Nonempty ↔ p∈tuplePrimeSupport d := by
  rw [mem_tuplePrimeSupport hd]
  simp [Finset.Nonempty]

theorem choiceSubset_mem_of_nonempty {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes)
    (h : (choiceSubset c p).Nonempty) : choiceSubset c p∈A p := by
  classical
  by_cases hp : p∈c.1
  · rw [choiceSubset_of_mem c hp]
    exact (c.2 ⟨p,hp⟩).property
  · simp [choiceSubset_of_not_mem c hp] at h

theorem choice_primeSubset {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (p : Nat.Primes) :
    tuplePrimeSubset (choiceDivisors c) p = choiceSubset c p := by
  ext i
  simp [prime_dvd_choiceDivisors]

theorem choice_primeSupport {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) :
    tuplePrimeSupport (choiceDivisors c) = c.1 := by
  classical
  ext p
  rw [← tuplePrimeSubset_nonempty_iff _ (fun i => (choiceDivisors_squarefree c i).ne_zero),
    choice_primeSubset]
  by_cases hp : p∈c.1
  · simp only [hp, iff_true, choiceSubset_of_mem c hp]
    exact hA p _ (c.2 ⟨p,hp⟩).property
  · simp [hp]

theorem eulerChoices_ext {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    {c e : EulerChoices (fun p : Nat.Primes => {S // S∈A p})}
    (h : ∀ p, choiceSubset c p = choiceSubset e p) : c=e := by
  classical
  have hc (p : Nat.Primes) : p∈c.1 ↔ (choiceSubset c p).Nonempty := by
    by_cases hp : p∈c.1
    · simp only [hp, true_iff, choiceSubset_of_mem c hp]
      exact hA p _ (c.2 ⟨p,hp⟩).property
    · simp [hp]
  have he (p : Nat.Primes) : p∈e.1 ↔ (choiceSubset e p).Nonempty := by
    by_cases hp : p∈e.1
    · simp only [hp, true_iff, choiceSubset_of_mem e hp]
      exact hA p _ (e.2 ⟨p,hp⟩).property
    · simp [hp]
  have hce : c.1=e.1 := Finset.ext fun p => by rw [hc,he,h]
  rcases c with ⟨P,c⟩
  rcases e with ⟨Q,e⟩
  dsimp only at hce
  subst Q
  congr 1
  funext p
  apply Subtype.ext
  simpa only [choiceSubset_of_mem ⟨P,c⟩ p.property,
    choiceSubset_of_mem ⟨P,e⟩ p.property] using h p

theorem choiceDivisors_injective {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) :
    Function.Injective (choiceDivisors (A := A)) := by
  intro c e h
  apply eulerChoices_ext hA
  intro p
  ext i
  rw [← prime_dvd_choiceDivisors, ← prime_dvd_choiceDivisors, h]

def AllowedDivisorTuple {ι : Type*} [Fintype ι] (A : ℕ → Finset (Finset ι)) :=
  {d : ι → ℕ // (∀ i, Squarefree (d i)) ∧
    ∀ p : Nat.Primes, (tuplePrimeSubset d p).Nonempty → tuplePrimeSubset d p∈A p}

noncomputable def tupleChoices {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : AllowedDivisorTuple A) : EulerChoices (fun p : Nat.Primes => {S // S∈A p}) :=
  ⟨tuplePrimeSupport d.val, fun p => ⟨tuplePrimeSubset d.val p,
    d.property.2 p ((tuplePrimeSubset_nonempty_iff d.val
      (fun i => (d.property.1 i).ne_zero) p).mpr p.property)⟩⟩

theorem tupleChoices_subset {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : AllowedDivisorTuple A) (p : Nat.Primes) :
    choiceSubset (tupleChoices d) p = tuplePrimeSubset d.val p := by
  classical
  by_cases hp : p∈tuplePrimeSupport d.val
  · exact choiceSubset_of_mem (tupleChoices d) hp
  · rw [choiceSubset_of_not_mem (tupleChoices d) hp]
    apply Eq.symm
    exact Finset.not_nonempty_iff_eq_empty.mp (fun h => hp
      ((tuplePrimeSubset_nonempty_iff d.val (fun i => (d.property.1 i).ne_zero) p).mp h))

theorem choiceDivisors_tupleChoices {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (d : AllowedDivisorTuple A) : choiceDivisors (tupleChoices d) = d.val := by
  funext i
  apply (Nat.Squarefree.ext_iff (choiceDivisors_squarefree _ i) (d.property.1 i)).mpr
  intro p hp
  let p' : Nat.Primes := ⟨p,hp⟩
  exact (prime_dvd_choiceDivisors (tupleChoices d) p' i).trans
    ((Iff.of_eq (congrArg (fun S : Finset ι => i∈S) (tupleChoices_subset d p'))).trans
      (mem_tuplePrimeSubset d.val p' i))

noncomputable def choiceTuple {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) : AllowedDivisorTuple A :=
  ⟨choiceDivisors c, choiceDivisors_squarefree c, fun p h => by
    rw [choice_primeSubset] at h ⊢
    exact choiceSubset_mem_of_nonempty c p h⟩

noncomputable def primeChoicesEquivTuple {ι : Type*} [Fintype ι]
    (A : ℕ → Finset (Finset ι)) (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty) :
    EulerChoices (fun p : Nat.Primes => {S // S∈A p}) ≃ AllowedDivisorTuple A where
  toFun := choiceTuple
  invFun := tupleChoices
  left_inv c := by
    apply eulerChoices_ext hA
    intro p
    rw [tupleChoices_subset]
    exact choice_primeSubset c p
  right_inv d := Subtype.ext (choiceDivisors_tupleChoices d)

theorem choice_double_prod {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    {M : Type*} [CommMonoid M]
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (f : Nat.Primes → ι → M) :
    (∏ i, ∏ p∈c.1.filter (fun p => i∈choiceSubset c p), f p i) =
      ∏ p∈c.1, ∏ i∈choiceSubset c p, f p i := by
  classical
  simp_rw [Finset.prod_filter]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro p _
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

theorem moebius_choiceDivisors {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    ArithmeticFunction.moebius (choiceDivisors c i) =
      ∏ _p∈c.1.filter (fun p => i∈choiceSubset c p), (-1:ℤ) := by
  classical
  unfold choiceDivisors
  rw [ArithmeticFunction.IsMultiplicative.map_prod (fun p : Nat.Primes => (p:ℕ))
    ArithmeticFunction.isMultiplicative_moebius _ (fun p _ q _ hpq =>
      (Nat.coprime_primes p.property q.property).mpr (fun h => hpq (Subtype.ext h)))]
  apply Finset.prod_congr rfl
  intro p _
  exact ArithmeticFunction.moebius_apply_prime p.property

theorem moebius_choiceDivisors_prod {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) :
    (∏ i, ArithmeticFunction.moebius (choiceDivisors c i)) =
      ∏ p∈c.1, (-1:ℤ)^(choiceSubset c p).card := by
  classical
  simp_rw [moebius_choiceDivisors]
  rw [choice_double_prod c (fun _ _ => (-1:ℤ))]
  simp only [Finset.prod_const]

theorem choiceDivisors_log {ι : Type*} {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (i : ι) :
    Real.log (choiceDivisors c i) =
      ∑ p∈c.1.filter (fun p => i∈choiceSubset c p), Real.log (p:ℕ) := by
  classical
  rw [choiceDivisors, Nat.cast_prod]
  exact Real.log_prod (fun p _ => by exact_mod_cast p.property.ne_zero)

theorem primeMonomial_as_product {ι : Type*} (p : ℕ) (z : ι → ℂ) (S : Finset ι) :
    primeMonomial p z S = ∏ i∈S, Complex.exp (-(Real.log p : ℂ)*z i) := by
  rw [primeMonomial, Finset.mul_sum, Complex.exp_sum]

theorem choiceMonomial_prod {ι : Type*} [Fintype ι] {A : ℕ → Finset (Finset ι)}
    (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (z : ι → ℂ) :
    (∏ p∈c.1, primeMonomial p z (choiceSubset c p)) =
      Complex.exp (-∑ i, (Real.log (choiceDivisors c i) : ℂ)*z i) := by
  classical
  simp_rw [primeMonomial_as_product]
  rw [← choice_double_prod c (fun p i => Complex.exp (-(Real.log (p:ℕ) : ℂ)*z i)),
    ← Finset.sum_neg_distrib, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.exp_sum, choiceDivisors_log, Complex.ofReal_sum]
  congr 1
  simp only [Finset.sum_mul, ← Finset.sum_neg_distrib, neg_mul]

noncomputable def tuplePrimeDensity {ι : Type*} [Fintype ι] (δ : ℕ) (d : ι → ℕ) : ℂ :=
  ∏ p∈tuplePrimeSupport d, ((p:ℂ)-δ)⁻¹

noncomputable def tupleFourierCoefficient {ι : Type*} [Fintype ι] (δ : ℕ)
    (d : ι → ℕ) (z : ι → ℂ) : ℂ :=
  tuplePrimeDensity δ d * (∏ i, (ArithmeticFunction.moebius (d i):ℂ)) *
    Complex.exp (-∑ i, (Real.log (d i):ℂ)*z i)

theorem choiceTerm_eq_tupleFourierCoefficient {ι : Type*} [Fintype ι]
    {A : ℕ → Finset (Finset ι)} (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (δ : ℕ) (c : EulerChoices (fun p : Nat.Primes => {S // S∈A p})) (z : ι → ℂ) :
    eulerChoiceTerm (primeAllowedWeight δ A z) c =
      tupleFourierCoefficient δ (choiceDivisors c) z := by
  classical
  have hcast : (∏ i, (ArithmeticFunction.moebius (choiceDivisors c i):ℂ)) =
      ∏ p∈c.1, (-1:ℂ)^(choiceSubset c p).card := by
    exact_mod_cast moebius_choiceDivisors_prod c
  rw [tupleFourierCoefficient, tuplePrimeDensity, choice_primeSupport hA c, hcast,
    ← choiceMonomial_prod c z, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  unfold eulerChoiceTerm primeAllowedWeight primeChoiceWeight
  rw [← Finset.prod_coe_sort c.1]
  apply Finset.prod_congr rfl
  intro p _
  rw [← choiceSubset_of_mem c p.property]
  ring

theorem tupleFourier_summable_norm {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    Summable (fun d : AllowedDivisorTuple A => ‖tupleFourierCoefficient δ d.val z‖) := by
  apply (primeChoicesEquivTuple A hA).summable_iff.mp
  change Summable (fun c => ‖tupleFourierCoefficient δ (choiceDivisors c) z‖)
  simp_rw [← choiceTerm_eq_tupleFourierCoefficient hA δ]
  exact eulerChoice_summable_norm _ (primeAllowedWeight_summable_norm hδ A z hε hA hR hz)

theorem tupleFourier_hasProd {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    HasProd (fun p : Nat.Primes => eulerP p δ (A p) z)
      (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val z) := by
  rw [← (primeChoicesEquivTuple A hA).tsum_eq
    (fun d => tupleFourierCoefficient δ d.val z)]
  change HasProd _ (∑' c, tupleFourierCoefficient δ (choiceDivisors c) z)
  simp_rw [← choiceTerm_eq_tupleFourierCoefficient hA δ]
  exact primeEulerChoices_hasProd hδ A z hε hA hR hz

theorem tupleFourier_norm_tsum_le {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re) :
    (∑' d : AllowedDivisorTuple A, ‖tupleFourierCoefficient δ d.val z‖) ≤
      Real.exp ((2*R)*Real.log (riemannZeta ((1+ε:ℝ):ℂ)).re) := by
  rw [← (primeChoicesEquivTuple A hA).tsum_eq
    (fun d => ‖tupleFourierCoefficient δ d.val z‖)]
  change (∑' c, ‖tupleFourierCoefficient δ (choiceDivisors c) z‖) ≤ _
  simp_rw [← choiceTerm_eq_tupleFourierCoefficient hA δ]
  exact primeEulerChoices_norm_tsum_le hδ A z hε hA hR hz

theorem tupleFourier_eq_H_zeta {ι : Type*} [Fintype ι] {δ R : ℕ} (hδ : δ≤1)
    (A : ℕ → Finset (Finset ι)) (B : Finset (Finset ι)) (z : ι → ℂ) {ε : ℝ} (hε : 0<ε)
    (hA : ∀ p : Nat.Primes, ∀ S∈A p, S.Nonempty)
    (hR : ∀ p : Nat.Primes, (A p).card≤R) (hz : ∀ i, ε≤(z i).re)
    (hB : ∀ S∈B, S.Nonempty) {H : ℂ}
    (hH : HasProd (fun p : Nat.Primes => eulerH p δ (A p) B z) H) :
    (∑' d : AllowedDivisorTuple A, tupleFourierCoefficient δ d.val z) =
      H*eulerZetaProduct B z := by
  exact (tupleFourier_hasProd hδ A z hε hA hR hz).unique
    (eulerP_hasProd δ A B z hB (fun i => hε.trans_le (hz i)) hH)

theorem prime_dvd_finset_lcm {ι : Type*} (s : Finset ι) (d : ι → ℕ)
    {p : ℕ} (hp : Nat.Prime p) : p∣s.lcm d ↔ ∃ i∈s, p∣d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp.not_dvd_one]
  | @insert i s hi ih =>
    rw [Finset.lcm_insert]
    change p∣Nat.lcm (d i) (s.lcm d) ↔ _
    simp only [hp.dvd_lcm, ih, Finset.mem_insert, exists_eq_or_imp]

theorem tuplePrimeSupport_eq_modulus {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, d i≠0) :
    tuplePrimeSupport d = (tupleModulus d).primeFactors.subtype Nat.Prime := by
  ext p
  change p∈tuplePrimeSupport d ↔
    (⟨p.val,p.property⟩ : {n : ℕ // Nat.Prime n})∈(tupleModulus d).primeFactors.subtype Nat.Prime
  rw [mem_tuplePrimeSupport hd p, Finset.mem_subtype, Nat.mem_primeFactors]
  have hq0 : Finset.univ.lcm d ≠ 0 :=
    (tupleModulus_pos (fun i => Nat.pos_of_ne_zero (hd i))).ne'
  simp only [p.property, true_and, tupleModulus, prime_dvd_finset_lcm _ _ p.property,
    Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h,hq0⟩, fun h => h.1⟩

theorem tupleModulus_eq_primeSupport_prod {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : tupleModulus d = ∏ p∈tuplePrimeSupport d, (p:ℕ) := by
  rw [tuplePrimeSupport_eq_modulus (fun i => (hd i).ne_zero)]
  change tupleModulus d = Finset.prod ((tupleModulus d).primeFactors.subtype Nat.Prime)
    (fun p : {n : ℕ // Nat.Prime n} => p.val)
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => p)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  exact (Nat.prod_primeFactors_of_squarefree (tupleModulus_squarefree hd)).symm

theorem tupleTotient_eq_primeSupport_prod {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) :
    (tupleModulus d).totient = ∏ p∈tuplePrimeSupport d, ((p:ℕ)-1) := by
  rw [tuplePrimeSupport_eq_modulus (fun i => (hd i).ne_zero)]
  change (tupleModulus d).totient = Finset.prod ((tupleModulus d).primeFactors.subtype Nat.Prime)
    (fun p : {n : ℕ // Nat.Prime n} => p.val-1)
  rw [Finset.prod_subtype_of_mem (fun p : ℕ => p-1)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)]
  rw [Nat.totient_eq_div_primeFactors_mul,
    Nat.prod_primeFactors_of_squarefree (tupleModulus_squarefree hd),
    Nat.div_self (tupleModulus_pos (fun i => Nat.pos_of_ne_zero (hd i).ne_zero)), one_mul]

theorem tuplePrimeDensity_zero {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : tuplePrimeDensity 0 d = (tupleModulus d : ℂ)⁻¹ := by
  simp only [tuplePrimeDensity, Nat.cast_zero, sub_zero, Finset.prod_inv_distrib]
  rw [tupleModulus_eq_primeSupport_prod hd, Nat.cast_prod]

theorem tuplePrimeDensity_one {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : tuplePrimeDensity 1 d = ((tupleModulus d).totient : ℂ)⁻¹ := by
  simp only [tuplePrimeDensity, Nat.cast_one, Finset.prod_inv_distrib]
  rw [tupleTotient_eq_primeSupport_prod hd, Nat.cast_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  simp only [Nat.cast_sub p.property.one_le, Nat.cast_one]

open scoped ContDiff

end LargePrimeGaps

end OAI
