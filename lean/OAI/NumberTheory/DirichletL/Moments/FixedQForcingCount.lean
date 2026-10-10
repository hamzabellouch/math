import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalCount
import OAI.NumberTheory.DirichletL.Moments.RankinRadical

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFixedQForcingCount
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentForcing CenteredMomentChildRows CenteredMomentRankinRadical
open CenteredMomentSecondExceptionalCount CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalLedger CenteredMomentSupport
open CenteredMomentSourceRow
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goodSet (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  (forcingSet c d V).filter (fun i => IsCoprime Q (P i))

def excludedSet (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  (forcingSet c d V).filter (fun i => ¬IsCoprime Q (P i))

def goodIdeal (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ goodSet Q P c d V, P i

def excludedIdeal (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ excludedSet Q P c d V, P i

omit [Fintype ι] [DecidableEq ι] in
lemma prime_product_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) : Squarefree (∏ i ∈ S, P i) := by
  simpa [forcingIdeal, forcingSet] using
    forcingIdeal_squarefree P hp hinj (fun _ => 1) (fun _ => 1) S

omit [Fintype ι] [DecidableEq ι] in
lemma prime_product_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (S : Finset ι) (R : Ideal O) (hR : R ∈ normalizedFactors (∏ i ∈ S, P i)) :
    ∃ i ∈ S, R = P i := by
  simpa [forcingIdeal, forcingSet] using
    forcing_prime_mem P hp (fun _ => 1) (fun _ => 1) S R (by
      simpa [forcingIdeal, forcingSet] using hR)

omit [Fintype ι] [DecidableEq ι] in
lemma goodIdeal_squarefree (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (goodIdeal Q P c d V) :=
  prime_product_squarefree P hp hinj _

omit [Fintype ι] [DecidableEq ι] in
lemma goodIdeal_ne_zero (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : goodIdeal Q P c d V ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)

lemma good_valuation_two (Q : Ideal O) (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι)
    (hi : i ∈ goodSet Q P c d V) :
    CenteredExceptionalCount.valuation (movingIdeal P c d V) (P i) = 2 :=
  forcing_valuation_two P hp hinj c d V i (Finset.mem_filter.mp hi).1

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_split (Q : Ideal O) (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) :
    goodIdeal Q P c d V * excludedIdeal Q P c d V = forcingIdeal P c d V := by
  exact Finset.prod_filter_mul_prod_filter_not _ _ _

lemma prime_dvd_of_not_coprime (Q P : Ideal O) (hP : Prime P) (h : ¬IsCoprime Q P) : P ∣ Q := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hs : Q ⊔ P ≠ ⊤ := by simpa only [Ideal.isCoprime_iff_sup_eq] using h
  have he : P = Q ⊔ P := Ideal.IsMaximal.eq_of_le inferInstance hs le_sup_right
  exact Ideal.dvd_iff_le.mpr (le_sup_left.trans_eq he.symm)

omit [Fintype ι] [DecidableEq ι] in
lemma excludedIdeal_dvd_radical (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) : excludedIdeal Q P c d V ∣ commonRadical Q Q := by
  apply (CenteredMomentDivisorAllocation.squarefree_dvd_iff _ _
    (prime_product_squarefree P hp hinj _)).mpr
  intro R hR
  obtain ⟨i,hi,rfl⟩ := prime_product_mem P hp _ R (Multiset.mem_toFinset.mp hR)
  have hd := prime_dvd_of_not_coprime Q (P i) (hp i) (Finset.mem_filter.mp hi).2
  have hm : P i ∈ IdealMobiusDivisorSum.primeSupport Q := by
    simpa only [IdealMobiusDivisorSum.primeSupport, Multiset.mem_toFinset, mem_normalizedFactors_iff hQ,
      hp i, true_and] using hd
  exact Finset.dvd_prod_of_mem id (Finset.mem_inter.mpr ⟨hm,hm⟩)

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_dvd_good_mul_radical (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) :
    forcingIdeal P c d V ∣ goodIdeal Q P c d V * commonRadical Q Q := by
  rw [←forcing_split Q P c d V]
  exact mul_dvd_mul_left _ (excludedIdeal_dvd_radical Q hQ P hp hinj c d V)

omit [Fintype ι] [DecidableEq ι] in
lemma forcing_norm_le (Q : Ideal O) (hQ : Q ≠ 0)
    (P : ι → Ideal O) (hp : ∀ i, Prime (P i)) (hinj : Function.Injective P)
    (c d : ι → ℕ) (V : Finset ι) :
    (Ideal.absNorm (forcingIdeal P c d V) : ℝ) ≤
      (Ideal.absNorm (goodIdeal Q P c d V) : ℝ) * Ideal.absNorm (commonRadical Q Q) := by
  have hd := map_dvd Ideal.absNorm (forcing_dvd_good_mul_radical Q hQ P hp hinj c d V)
  have hn : (goodIdeal Q P c d V) * commonRadical Q Q ≠ 0 :=
    mul_ne_zero (goodIdeal_ne_zero Q P hp c d V) (commonRadical_ne_zero Q Q)
  have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hn)) hd
  exact_mod_cast (show Ideal.absNorm (forcingIdeal P c d V) ≤
    Ideal.absNorm (goodIdeal Q P c d V) * Ideal.absNorm (commonRadical Q Q) by simpa using hh)

lemma fixed_radical_power_loss (Z M f g r : ℝ) (hZ : 1 < Z)
    (hf : 0 < f) (hg : 0 < g) (hr : 0 < r) (hfg : f ≤ g*r) :
    Z ^ ((M-4*Real.logb Z g)/6) ≤
      r^(2/3:ℝ) * Z^((M-4*Real.logb Z f)/6) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.logb_le_logb_of_le hZ hf hfg
  rw [Real.logb_mul hg.ne' hr.ne'] at hl
  calc
    _ ≤ Z^(Real.logb Z r*(2/3)+(M-4*Real.logb Z f)/6) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = _ := by
      rw [Real.rpow_add hz,Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hr]

theorem actual_forcing_exceptional_count_fixedQ (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι)
    (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m e : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (he : elementCoeff η e ≠ 0) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      goodLambda ∉ Ideal.span {p i} ∧ (2 : O) ∉ Ideal.span {p i} ∧
      Ideal.span {p i} ∣ Ideal.span {e})
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr * Z ^ M) :
    (rows.card : ℝ) ≤ (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ) *
      (768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card * Cr^(1/6:ℝ) *
        Z^((M-4*Real.logb Z (Ideal.absNorm
          (forcingIdeal (fun i => Ideal.span {p i}) c d V):ℝ))/6)) := by
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let G := goodIdeal Q P c d V
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  have hG0 : G ≠ 0 := goodIdeal_ne_zero Q P hp c d V
  have hGn : (0:ℝ) < Ideal.absNorm G := CenteredExceptionalCount.norm_pos hG0
  have hb := separated_exceptional_count η χ Q hQ0 hQ hQ72
    m (movingElement p c d V) e hm hA hmLam hm2 he rows hrows hex G
    (goodIdeal_squarefree Q P hp hinj c d V) (by
      intro R hR
      obtain ⟨i,hi,rfl⟩ := prime_product_mem P hp (goodSet Q P c d V) R hR
      obtain ⟨hif,hQi⟩ := Finset.mem_filter.mp hi
      obtain ⟨hl,h2,hd⟩ := hgood i hif
      refine ⟨hl,h2,hQi,hd,?_⟩
      rw [movingElement_span,good_valuation_two Q P hp hinj c d V i hi])
    Z Cr M (2*Real.logb Z (Ideal.absNorm G:ℝ)) (zero_lt_one.trans hZ) hCr (by
      rw [show (2*Real.logb Z (Ideal.absNorm G:ℝ))/2=Real.logb Z (Ideal.absNorm G:ℝ) by ring,
        Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hGn]) hN
  have hb' : (rows.card:ℝ) ≤ 768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
      Z^((M-4*Real.logb Z (Ideal.absNorm G:ℝ))/6) := by
    have heq : (M-2*(2*Real.logb Z (Ideal.absNorm G:ℝ)))/6 =
        (M-4*Real.logb Z (Ideal.absNorm G:ℝ))/6 := by ring
    simpa only [heq] using hb
  have hf : (0:ℝ) < Ideal.absNorm (forcingIdeal P c d V) := by
    apply CenteredExceptionalCount.norm_pos
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  have hr : (0:ℝ) < Ideal.absNorm (commonRadical Q Q) :=
    CenteredExceptionalCount.norm_pos (commonRadical_ne_zero Q Q)
  have hs := fixed_radical_power_loss Z M _ _ _ hZ hf hGn hr
    (forcing_norm_le Q hQ0 P hp hinj c d V)
  apply hb'.trans
  calc
    _ ≤ (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ))*
        ((Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
          Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal P c d V):ℝ))/6)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

theorem actual_canonical_exceptional_count_fixedQ (η : Character) (χ : RayFourExpansion.RayCharacter)
    (C D : Ideal O) (hC : Supported C) (U : Finset (CommonIndex C D))
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (hη : idealCoeff η C ≠ 0)
    (m : O) (hm : m ≠ 0) (hmLam : goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow (childCharacter η χ) Q m
      (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z)
    (Z Cr M : ℝ) (hZ : 1 < Z) (hCr : 0 ≤ Cr)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Cr*Z^M) :
    (rows.card:ℝ) ≤ (Ideal.absNorm (commonRadical Q Q):ℝ)^(2/3:ℝ)*
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun P:CommonIndex C D => P.val)
          (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U)):ℝ))/6)) := by
  have he : elementCoeff η (primaryGenerator C) ≠ 0 := by
    rw [←idealCoeff_span η (supported_primaryGenerator_ne_zero C hC),primary_span_supported C hC]
    exact hη
  have hinj : Function.Injective (fun P:CommonIndex C D => Ideal.span {commonPrime C D P}) := by
    simpa only [commonPrime_span C D hC] using
      (Subtype.val_injective : Function.Injective (fun P:CommonIndex C D => P.val))
  have hb := actual_forcing_exceptional_count_fixedQ (commonPrime C D) (common_prime_prime C D hC) hinj
    (leftExponent C D) (rightExponent C D) (nonunitPartitionSet C D U) η χ
    Q hQ0 hQ hQ72 m (primaryGenerator C) hm hmLam hm2 he rows hrows hex (by
      intro P _
      rw [commonPrime_span C D hC P]
      refine ⟨common_good C D hC P,CanonicalRowCompletion.good_odd_prime_two_not_mem _
        (common_odd C D hC P),?_⟩
      rw [primary_span_supported C hC]
      exact common_prime_dvd_left C D P) Z Cr M hZ hCr hN
  simpa only [commonPrime_span C D hC] using hb

end SevenEighths.CenteredMomentFixedQForcingCount

end

end OAI
