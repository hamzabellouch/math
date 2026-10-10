import Mathlib
import OAI.NumberTheory.PrimePackets.SieveConvolution

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
namespace PrimeDegreePackets.Sieve
open Finset Nat Filter Topology

lemma powerfulMoment_one_le (k : ℕ) : 1 ≤ powerfulMoment k := by
  simpa [powerfulCorrection_one] using powerfulCorrection_moment_sum_le k {1}

 

theorem corrected_relative_interval (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ R : ℕ, ∀ (g : ℕ → ℝ), (∀p, 0 ≤ g p ∧ g p ≤ 1) →
      ∀ a b : ℕ, R ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
      (∑ m ∈ Finset.Ioc a b, (powerfulFunction k * (primePenalty g)^(k+1)) m) ≤
        ((8 * intervalConstant k + 1) * powerfulMoment k) *
          (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by
  obtain ⟨B,hB⟩ := corrected_interval_finite k η hη
  obtain ⟨R,hR⟩ := eventual_tail_threshold k η hη
  let N := max 2 (max B ⌈2/η⌉₊)
  refine ⟨max R (N^2), ?_⟩
  intro g hg a b hb hab hrel
  have hRb : R ≤ b := (le_max_left _ _).trans hb
  have hNb : N^2 ≤ b := (le_max_right _ _).trans hb
  let T := Nat.sqrt b
  have hNT : N ≤ T := Nat.le_sqrt'.mpr hNb
  have hT : 2 ≤ T := (le_max_left _ _).trans hNT
  have hBT : B ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hNT)
  have hηT : 2 ≤ η * (T:ℝ) := by
    have hceil : ⌈2/η⌉₊ ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hNT)
    have hdiv : (2:ℝ)/η ≤ T := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have H := (div_le_iff₀ hη).mp hdiv
    simpa [mul_comm] using H
  have hTb : T^2 ≤ b := Nat.sqrt_le' b
  have hb4 : 4 ≤ b := by nlinarith
  have hbT : b ≤ T^4 := sqrt_fourth_bound hb4
  have hbp : 0 < b := by omega
  have htp : 0 < T := by omega
  have hlog := (hR b hRb).1
  have hM : 0 ≤ powerfulMoment k := powerfulMoment_nonneg k
  have hy : 0 ≤ ((b:ℝ)-a)/Real.log b := div_nonneg (sub_nonneg.mpr (by exact_mod_cast hab)) (by linarith)
  have hE := primeExponential_one_le g (fun p => (hg p).1) k b
  have htail := mul_le_mul_of_nonneg_right
    (tail_absorbed k a b T η hbp htp hbT hlog (hR b hRb).2 hrel) hM
  have herr : ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) * powerfulMoment k ≤
      powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by
    calc
      _ ≤ (((b:ℝ)-a)/Real.log b) * powerfulMoment k := htail
      _ ≤ powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by
        have H := mul_le_mul_of_nonneg_left hE (mul_nonneg hM hy)
        simpa [mul_comm] using H
  calc
    _ ≤ 8 * intervalConstant k * powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b +
        ((b:ℝ)*(1+Real.log b)^k) * (T:ℝ)^(-(1:ℝ)/4) * powerfulMoment k :=
      hB g hg a b T hab hT hBT hTb hbT hηT hrel
    _ ≤ 8 * intervalConstant k * powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b +
        powerfulMoment k * (((b:ℝ)-a)/Real.log b) * primeExponential g k b := by gcongr
    _ = _ := by ring

 

theorem divisor_bounded_relative_interval (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∃ R : ℕ,
      ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative →
        (∀m, 0 ≤ f m ∧ f m ≤ nFoldDivisor (k+1) m) →
        ∀ a b : ℕ, R ≤ b → a ≤ b → η*b ≤ (b:ℝ)-a →
          (∑ m ∈ Finset.Ioc a b, f m) ≤
            C * (((b:ℝ)-a)/Real.log b) *
              Real.exp (∑ p ∈ smallPrimes b, f p / p) := by
  refine ⟨(8 * intervalConstant k + 1) * powerfulMoment k, ?_, ?_⟩
  · exact mul_pos (by have := intervalConstant_nonneg k; linarith)
      (lt_of_lt_of_le zero_lt_one (powerfulMoment_one_le k))
  intro η hη
  obtain ⟨R,hR⟩ := corrected_relative_interval k η hη
  refine ⟨R, ?_⟩
  intro f hmult hf a b hb hab hrel
  have H := hR (coefficientPenalty k f) (coefficientPenalty_bounds k f hf) a b hb hab hrel
  have hE : primeExponential (coefficientPenalty k f) k b =
      Real.exp (∑ p ∈ smallPrimes b, f p / p) := by
    unfold primeExponential
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hprime : p.Prime := (Finset.mem_filter.mp hp).2
    rw [show ((k+1:ℕ):ℝ) = (k+1:ℝ) by push_cast; rfl, coefficientPenalty_prime k f hprime]
  rw [hE] at H
  exact (Finset.sum_le_sum (fun m _ => divisor_bounded_majorant k f hmult hf m)).trans H

end PrimeDegreePackets.Sieve

open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
namespace PrimeDegreePackets

variable (K : Type*) [Field K] [NumberField K]

 

def idealCoefficient : ArithmeticFunction ℕ where
  toFun m := if m = 0 then 0 else Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m}
  map_zero' := by simp

lemma idealCoefficient_pos (m : ℕ) (hm : m ≠ 0) :
    idealCoefficient K m = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := by
  simp [idealCoefficient,hm]

lemma idealCoefficient_one : idealCoefficient K 1 = 1 := by
  simp [idealCoefficient, Ideal.absNorm_eq_one_iff]

lemma ideal_eq_of_dvd_of_norm_eq {I J : Ideal (𝓞 K)} (hIJ : I ∣ J)
    (hI : Ideal.absNorm I ≠ 0) (hn : Ideal.absNorm I = Ideal.absNorm J) : I = J := by
  obtain ⟨A,rfl⟩ := hIJ
  have hA : Ideal.absNorm A = 1 := by
    rw [map_mul] at hn
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI) (by simpa using hn.symm)
  rw [Ideal.absNorm_eq_one_iff.mp hA]
  simp

lemma ideals_relprime_of_norm_coprime {I J : Ideal (𝓞 K)}
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) : IsRelPrime I J := by
  intro D hDI hDJ
  have hnorm : Ideal.absNorm D = 1 :=
    Nat.eq_one_of_dvd_coprimes h (map_dvd Ideal.absNorm hDI) (map_dvd Ideal.absNorm hDJ)
  rw [Ideal.absNorm_eq_one_iff.mp hnorm]
  simpa only [Ideal.one_eq_top] using (isUnit_one : IsUnit (1 : Ideal (𝓞 K)))

lemma ideal_multiplication_injective {m n : ℕ} (hm : m ≠ 0)
    (hmn : m.Coprime n) :
    Function.Injective (fun IJ : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} ×
      {J : Ideal (𝓞 K) // Ideal.absNorm J = n} => (IJ.1.1 * IJ.2.1 : Ideal (𝓞 K))) := by
  intro IJ PQ heq
  dsimp only at heq
  have hIP : IJ.1.1 ∣ PQ.1.1 := by
    apply (ideals_relprime_of_norm_coprime K (I := IJ.1.1) (J := PQ.2.1) (by simpa [IJ.1.2,PQ.2.2] using hmn)).dvd_of_dvd_mul_right
    rw [← heq]
    exact dvd_mul_right _ _
  have hI : IJ.1.1 = PQ.1.1 := ideal_eq_of_dvd_of_norm_eq K hIP
    (by simpa [IJ.1.2] using hm) (by rw [IJ.1.2,PQ.1.2])
  have hJ : IJ.2.1 = PQ.2.1 := by
    have hi0 : IJ.1.1 ≠ 0 := by
      intro h
      have H := IJ.1.2
      rw [h,_root_.map_zero] at H
      exact hm H.symm
    rw [← hI] at heq
    exact mul_left_cancel₀ hi0 heq
  exact Prod.ext (Subtype.ext hI) (Subtype.ext hJ)

lemma prime_pow_dvd_coprime_product {p e m n : ℕ} (hp : p.Prime)
    (hmn : m.Coprime n) (hdiv : p^e ∣ m*n) : p^e ∣ m ∨ p^e ∣ n := by
  by_cases hpm : p ∣ m
  · exact Or.inl ((hmn.of_dvd_left hpm).pow_left e |>.dvd_of_dvd_mul_right hdiv)
  · exact Or.inr ((hp.coprime_iff_not_dvd.mpr hpm).pow_left e |>.dvd_of_dvd_mul_left hdiv)

 
lemma ideal_split_norm (I : Ideal (𝓞 K)) :
    ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n → Ideal.absNorm I = m*n →
      ∃ J L : Ideal (𝓞 K), Ideal.absNorm J = m ∧ Ideal.absNorm L = n ∧ I = J*L := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    intro m n hm hn hmn heq
    have H : m*n = 0 := by simpa using heq.symm
    exact (mul_ne_zero hm hn H).elim
  | h₂ I hI =>
    intro m n hm hn hmn heq
    have htop : I = ⊤ := by simpa using hI
    have H : m*n = 1 := by simpa [htop] using heq.symm
    have hm1 : m = 1 := Nat.dvd_one.mp (H ▸ dvd_mul_right m n)
    have hn1 : n = 1 := Nat.dvd_one.mp (H ▸ dvd_mul_left n m)
    subst m; subst n
    refine ⟨⊤,⊤,by simp,by simp,?_⟩
    simpa using htop
  | h₃ I P hI hP IH =>
    have hPmax : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
    let := hPmax
    obtain ⟨p,e,he,hpP,hp,hPnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have hP0 : Ideal.absNorm P ≠ 0 := by rw [hPnorm]; exact pow_ne_zero _ hp.ne_zero
    have hleft : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → m.Coprime n →
        Ideal.absNorm (P*I) = m*n → Ideal.absNorm P ∣ m →
        ∃ J L : Ideal (𝓞 K), Ideal.absNorm J = m ∧ Ideal.absNorm L = n ∧ P*I = J*L := by
      intro m n hm hn hmn heq hdiv
      obtain ⟨u,rfl⟩ := hdiv
      have hu : u ≠ 0 := by intro h; apply hm; simp [h]
      have hcop : u.Coprime n := hmn.of_dvd_left (dvd_mul_left _ _)
      have hnorm : Ideal.absNorm I = u*n := by
        rw [map_mul, mul_assoc] at heq
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hP0) heq
      obtain ⟨J,L,hJ,hL,hJL⟩ := IH u n hu hn hcop hnorm
      refine ⟨P*J,L,by simp [map_mul,hJ],hL,?_⟩
      rw [hJL,mul_assoc]
    intro m n hm hn hmn heq
    have hdiv : p^e ∣ m*n := by
      rw [← heq,map_mul,← hPnorm]
      exact dvd_mul_right _ _
    rcases prime_pow_dvd_coprime_product hp hmn hdiv with hpm | hpn
    · exact hleft m n hm hn hmn heq (by simpa [hPnorm] using hpm)
    · obtain ⟨L,J,hL,hJ,hJL⟩ := hleft n m hn hm hmn.symm
        (by simpa [mul_comm] using heq) (by simpa [hPnorm] using hpn)
      exact ⟨J,L,hJ,hL,by simpa [mul_comm] using hJL⟩

 
def idealNormProductEquiv (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    ({I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n}) ≃
      {I : Ideal (𝓞 K) // Ideal.absNorm I = m*n} := by
  let f : ({I : Ideal (𝓞 K) // Ideal.absNorm I = m} × {J : Ideal (𝓞 K) // Ideal.absNorm J = n}) →
      {I : Ideal (𝓞 K) // Ideal.absNorm I = m*n} := fun IJ =>
    ⟨IJ.1.1 * IJ.2.1, by simp [map_mul,IJ.1.2,IJ.2.2]⟩
  apply Equiv.ofBijective f
  constructor
  · intro IJ PQ heq
    exact ideal_multiplication_injective K hm hmn (congrArg Subtype.val heq)
  · intro I
    obtain ⟨J,L,hJ,hL,hI⟩ := ideal_split_norm K I m n hm hn hmn I.2
    exact ⟨(⟨J,hJ⟩,⟨L,hL⟩),Subtype.ext hI.symm⟩

lemma idealCoefficient_multiplicative : (idealCoefficient K).IsMultiplicative := by
  refine ⟨idealCoefficient_one K, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [idealCoefficient_pos K _ (mul_ne_zero hm hn), idealCoefficient_pos K _ hm,
    idealCoefficient_pos K _ hn, ← Nat.card_prod]
  exact Nat.card_congr (idealNormProductEquiv K m n hm hn hmn).symm

 
lemma ideal_factor_prime_power {I P : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) (hP : P ∈ normalizedFactors I) :
    (p : 𝓞 K) ∈ P ∧ p ≤ Ideal.absNorm P := by
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hmax : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  let := hmax
  obtain ⟨q,e,he,hqP,hq,hNorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  have hdvd : P ∣ I := dvd_of_mem_normalizedFactors hP
  have h_qp : q ∣ p^r := by
    rw [← hI]
    exact dvd_trans (hNorm ▸ (dvd_pow_self q he.ne')) (map_dvd Ideal.absNorm hdvd)
  have heq : q = p := Nat.prime_eq_prime_of_dvd_pow hq hp h_qp
  subst q
  exact ⟨hqP, by rw [hNorm]; exact Nat.le_self_pow he.ne' p⟩

lemma ideal_factor_count_le {I : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) : (normalizedFactors I).card ≤ r := by
  have hI0 : I ≠ ⊥ := by
    intro h; have H : (0:ℕ) = p^r := by simpa [h] using hI
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have H : p ^ (normalizedFactors I).card ≤ Ideal.absNorm I := by
    have H := Multiset.pow_card_le_prod (s := (normalizedFactors I).map Ideal.absNorm)
      (a := p) (by
        intro x hx
        obtain ⟨P,hP,rfl⟩ := Multiset.mem_map.mp hx
        exact (ideal_factor_prime_power K hp hI hP).2)
    simpa only [Multiset.card_map, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI0] using H
  rw [hI] at H
  exact (pow_le_pow_iff_right₀ hp.one_lt).mp H

 
def idealsOverPrime (p : ℕ) : Finset (Ideal (𝓞 K)) :=
  (normalizedFactors (Ideal.span {(p : 𝓞 K)})).toFinset

lemma ideal_factor_mem_over {I P : Ideal (𝓞 K)} {p r : ℕ}
    (hp : p.Prime) (hI : Ideal.absNorm I = p^r) (hP : P ∈ normalizedFactors I) :
    P ∈ idealsOverPrime K p := by
  have hprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hspan : Ideal.span {(p : 𝓞 K)} ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] using hp.ne_zero
  rw [idealsOverPrime, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hspan]
  refine ⟨Ideal.isPrime_of_prime hprime, ?_⟩
  rw [Ideal.span_singleton_le_iff_mem]
  exact (ideal_factor_prime_power K hp hI hP).1

lemma idealsOverPrime_card_le {p : ℕ} (hp : p.Prime) :
    (idealsOverPrime K p).card ≤ Module.finrank ℤ (𝓞 K) := by
  exact (Multiset.toFinset_card_le _).trans
    (ideal_factor_count_le K hp (Ideal.absNorm_span_natCast p))

 
lemma idealCoefficient_prime_le {p : ℕ} (hp : p.Prime) :
    idealCoefficient K p ≤ Module.finrank ℤ (𝓞 K) := by
  rw [idealCoefficient_pos K p hp.ne_zero]
  have hmem : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p}, I.1 ∈ idealsOverPrime K p := by
    intro I
    have hI0 : I.1 ≠ ⊥ := by
      intro h
      have H : p = 0 := by simpa [h] using I.2.symm
      exact hp.ne_zero H
    have hIprime : I.1.IsPrime := Ideal.isPrime_of_irreducible_absNorm
      (by rw [I.2]; exact Nat.irreducible_iff_prime.mpr hp.prime)
    have hfac : I.1 ∈ normalizedFactors I.1 :=
      (Ideal.mem_normalizedFactors_iff hI0).mpr ⟨hIprime, le_rfl⟩
    exact ideal_factor_mem_over K hp (r := 1) (by simpa using I.2) hfac
  let f : {I : Ideal (𝓞 K) // Ideal.absNorm I = p} → idealsOverPrime K p :=
    fun I => ⟨I.1,hmem I⟩
  have hf : Function.Injective f := by
    intro I J h
    exact Subtype.ext (show I.1 = J.1 from congrArg (fun x : idealsOverPrime K p => x.1) h)
  have H := Nat.card_le_card_of_injective f hf
  exact H.trans (by simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using idealsOverPrime_card_le K hp)

 

def padMultiset {α : Type*} (s : Finset α) (r : ℕ) (m : Multiset α)
    (hm : ∀x ∈ m, x ∈ s) (hr : m.card ≤ r) : Sym (Option s) r :=
  ⟨m.attach.map (fun x => some (⟨x.1,hm x.1 x.2⟩ : s)) +
      Multiset.replicate (r-m.card) none, by simp; omega⟩

lemma decode_padMultiset {α : Type*} (s : Finset α) (r : ℕ) (m : Multiset α)
    (hm : ∀x ∈ m, x ∈ s) (hr : m.card ≤ r) :
    (padMultiset s r m hm hr).val.filterMap (Option.map Subtype.val) = m := by
  simp only [padMultiset, Multiset.filterMap_add, Multiset.filterMap_map]
  have hnone : ∀k, (Multiset.replicate k (none : Option s)).filterMap
      (Option.map Subtype.val) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Multiset.replicate_succ, Multiset.filterMap_cons_none _ _ rfl, ih]
  rw [hnone, add_zero]
  change m.attach.filterMap (some ∘ Subtype.val) = m
  rw [Multiset.filterMap_eq_map, Multiset.attach_map_val]

lemma card_le_of_multiset_encoding {α β : Type*} (s : Finset β) (r : ℕ)
    (f : α → Multiset β) (hf : Function.Injective f)
    (hs : ∀a x, x ∈ f a → x ∈ s) (hr : ∀a, (f a).card ≤ r) :
    Nat.card α ≤ (s.card + 1).multichoose r := by
  let g : α → Sym (Option s) r := fun a => padMultiset s r (f a) (hs a) (hr a)
  have hg : Function.Injective g := by
    intro a b hab
    apply hf
    have H := congrArg (fun v : Sym (Option s) r =>
      v.val.filterMap (Option.map Subtype.val)) hab
    simpa only [g, decode_padMultiset] using H
  have H := Nat.card_le_card_of_injective g hg
  rw [Sym.natCard_sym_eq_multichoose] at H
  simpa only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe] using H

 

lemma idealCoefficient_prime_pow_le {p : ℕ} (hp : p.Prime) (r : ℕ) :
    idealCoefficient K (p^r) ≤ (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
  rw [idealCoefficient_pos K _ (pow_ne_zero _ hp.ne_zero)]
  let f : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r} → Multiset (Ideal (𝓞 K)) :=
    fun I => normalizedFactors I.1
  have hzero : ∀I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^r}, I.1 ≠ ⊥ := by
    intro I h
    have H : (0:ℕ) = p^r := by simpa [h] using I.2
    exact (pow_ne_zero _ hp.ne_zero) H.symm
  have hf : Function.Injective f := by
    intro I J h
    apply Subtype.ext
    have H := congrArg Multiset.prod h
    simpa only [f, Ideal.prod_normalizedFactors_eq_self (hzero I),
      Ideal.prod_normalizedFactors_eq_self (hzero J)] using H
  have H := card_le_of_multiset_encoding (idealsOverPrime K p) r f hf
    (fun I _ hP => ideal_factor_mem_over K hp I.2 hP)
    (fun I => ideal_factor_count_le K hp I.2)
  apply H.trans
  rw [Nat.multichoose_eq]
  calc
    _ ≤ (Module.finrank ℤ (𝓞 K) + r).choose r :=
      Nat.choose_le_choose r (by have := idealsOverPrime_card_le K hp; omega)
    _ = (r + Module.finrank ℤ (𝓞 K)).choose (Module.finrank ℤ (𝓞 K)) := by
      rw [Nat.add_comm (Module.finrank ℤ (𝓞 K)) r, Nat.choose_symm_add]

 
theorem idealCoefficient_le_divisor (m : ℕ) :
    idealCoefficient K m ≤ nFoldDivisor (Module.finrank ℤ (𝓞 K) + 1) m := by
  by_cases hm : m = 0
  · simp [hm,nFoldDivisor]
  unfold nFoldDivisor
  rw [(idealCoefficient_multiplicative K).multiplicative_factorization _ hm,
    ArithmeticFunction.isMultiplicative_zeta.pow.multiplicative_factorization _ hm]
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
  intro p hp
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  exact (idealCoefficient_prime_pow_le K hprime _).trans_eq
    (nFoldDivisor_prime_pow _ _ _ hprime).symm

open Filter Topology Asymptotics
 
def idealCoefficientReal : ArithmeticFunction ℝ where
  toFun m := idealCoefficient K m
  map_zero' := by simp

lemma idealCoefficientReal_multiplicative : (idealCoefficientReal K).IsMultiplicative := by
  refine ⟨by simp [idealCoefficientReal,idealCoefficient_one], ?_⟩
  intro m n hmn
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk]
  rw [(idealCoefficient_multiplicative K).map_mul_of_coprime hmn, Nat.cast_mul]

lemma idealCoefficientReal_nonneg (m : ℕ) : 0 ≤ idealCoefficientReal K m := Nat.cast_nonneg _

 
lemma idealCoefficient_summatory_limit :
    Tendsto (fun n : ℕ => (∑k ∈ Icc 1 n, idealCoefficientReal K k) / (n:ℝ))
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le]
  congr 1
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk]
  rw [←Nat.cast_sum]
  congr 1
  rw [←add_left_inj 1, ←Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Icc_succ_left_eq_Ioc _ _]
  have H : (∑k ∈ Ioc 0 n, idealCoefficient K k) =
      ∑k ∈ Ioc 0 n, Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} := by
    apply sum_congr rfl
    intro k hk
    exact idealCoefficient_pos K k (Nat.ne_of_gt (Finset.mem_Ioc.mp hk).1)
  rw [H, show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff], sum_Ioc_add_eq_sum_Icc n.zero_le,
    ←card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma idealCoefficient_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun m => (idealCoefficientReal K m : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (idealCoefficientReal_nonneg K) zero_le_one hs
  apply isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
  simpa using idealCoefficient_summatory_limit K

 
def realDirichletTerm (f : ArithmeticFunction ℝ) (s : ℝ) : ArithmeticFunction ℝ where
  toFun m := f m / (m : ℝ)^s
  map_zero' := by simp

lemma realDirichletTerm_ofReal (f : ArithmeticFunction ℝ) (s : ℝ) (m : ℕ) :
    (realDirichletTerm f s m : ℂ) = LSeries.term (fun m => (f m : ℂ)) s m := by
  by_cases hm : m = 0
  · subst m
    simp [realDirichletTerm]
  · simp only [realDirichletTerm, ArithmeticFunction.coe_mk,LSeries.term_of_ne_zero hm,
      Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg m),Complex.ofReal_natCast]

lemma idealCoefficient_real_summable {s : ℝ} (hs : 1 < s) :
    Summable (realDirichletTerm (idealCoefficientReal K) s) := by
  apply Complex.summable_ofReal.mp
  simp_rw [realDirichletTerm_ofReal]
  exact idealCoefficient_LSeriesSummable K (by simpa using hs)

lemma idealCoefficient_LSeries_eq (s : ℂ) :
    LSeries (fun m => (idealCoefficientReal K m : ℂ)) s = NumberField.dedekindZeta K s := by
  apply LSeries_congr _ s
  intro m hm
  simp only [idealCoefficientReal,ArithmeticFunction.coe_mk,idealCoefficient_pos K m hm,
    Complex.ofReal_natCast]

 
lemma idealDirichlet_eq_dedekindZeta (s : ℝ) :
    ((∑'m, realDirichletTerm (idealCoefficientReal K) s m : ℝ) : ℂ) =
      NumberField.dedekindZeta K s := by
  rw [Complex.ofReal_tsum, ←idealCoefficient_LSeries_eq]
  apply tsum_congr
  intro m
  exact realDirichletTerm_ofReal _ _ _

end PrimeDegreePackets
end
end

end OAI
