import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeCount

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryCorrelations

namespace SourceRoughFourier
open Finset
variable {N : ℕ} [NeZero N]
variable {ι : Type*}
noncomputable def poly (s : Finset ι) (w : ι → ℂ)
    (a : ι → ZMod N) (k : ZMod N) : ℂ :=
  ∑ i ∈ s, w i * ZMod.stdAddChar (a i * k)
noncomputable def shortEnvelope (D U : ℕ) (f : ℕ → ℂ) : ℝ :=
  univ.sup' univ_nonempty (fun k : ZMod N =>
    ∑ v ∈ Icc 1 U, ‖poly (Icc 1 D) (fun m => f (v + m))
      (fun m => (m : ZMod N)) k‖)
noncomputable def progressionCoeff (l : ℕ) (b : ℤ) (n : ℕ) : ℂ :=
  if (n : ℤ) ≡ b [ZMOD (l : ℤ)] then (liouville n : ℂ) else 0
end SourceRoughFourier

namespace SourcePrimeFactor
open Finset

def primeCount (P : Finset ℕ) (n : ℕ) : ℕ := (P.filter (fun p => p ∣ n)).card

theorem primeCount_mul {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    {p m : ℕ} (hp : p ∈ P) (hpm : ¬p ∣ m) :
    primeCount P (p * m) = primeCount P m + 1 := by
  have hs : P.filter (fun q => q ∣ p * m) = insert p (P.filter (fun q => q ∣ m)) := by
    ext q
    simp only [mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hq, hqd⟩
      rcases (hP q hq).dvd_mul.mp hqd with hqp | hqm
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq (hP q hq) (hP p hp)).mp hqp)
      · exact Or.inr ⟨hq, hqm⟩
    · rintro (rfl | ⟨hq, hqm⟩)
      · exact ⟨hp, dvd_mul_right q m⟩
      · exact ⟨hq, dvd_mul_of_dvd_right hqm p⟩
  unfold primeCount
  rw [hs, card_insert_of_notMem]
  simpa only [mem_filter, not_and] using fun (_ : p ∈ P) => hpm

theorem primeCount_pos {P : Finset ℕ} {p n : ℕ} (hp : p ∈ P) (hpn : p ∣ n) :
    0 < primeCount P n := card_pos.mpr ⟨p, mem_filter.mpr ⟨hp, hpn⟩⟩

theorem weighted_partition (P : Finset ℕ) (n : ℕ) (z : ℂ) :
    z = (if primeCount P n = 0 then z else 0) +
      ∑ p ∈ P, if p ∣ n then z / (primeCount P n : ℂ) else 0 := by
  classical
  rw [← sum_filter]
  by_cases hc : primeCount P n = 0
  · have hs : P.filter (fun p => p ∣ n) = ∅ := card_eq_zero.mp hc
    simp [hc, hs]
  · have hcz : (primeCount P n : ℂ) ≠ 0 := by exact_mod_cast hc
    simp only [ite_eq_right hc, zero_add, sum_const, nsmul_eq_mul]
    change z = (primeCount P n : ℂ) * (z / (primeCount P n : ℂ))
    field_simp

def binnedRamareCoefficient (P : Finset ℕ) (M : ℕ → ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑p∈P.filter (fun p => p∣n ∧ n/p∈Finset.Ioc (M p) (2*M p)),
    f p*f (n/p)/(primeCount P (n/p)+1:ℂ)

lemma primeCount_mul_le {P : Finset ℕ} (hP : ∀p∈P,Nat.Prime p)
    {p m : ℕ} (hp : p∈P) : primeCount P (p*m)≤primeCount P m+1 := by
  have hs : P.filter (fun q => q∣p*m) ⊆ insert p (P.filter (fun q => q∣m)) := by
    intro q hq
    rcases mem_filter.mp hq with ⟨hq,hdiv⟩
    rcases (hP q hq).dvd_mul.mp hdiv with hqp|hqm
    · exact mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq (hP q hq) (hP p hp)).mp hqp))
    · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hq,hqm⟩))
  exact (Finset.card_le_card hs).trans (card_insert_le ..)

lemma binnedRamare_norm (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (M : ℕ → ℕ) {f : ℕ → ℂ} (hf : OneBounded f) (n : ℕ) :
    ‖binnedRamareCoefficient P M f n‖≤1 := by
  classical
  let S := P.filter (fun p => p∣n ∧ n/p∈Finset.Ioc (M p) (2*M p))
  have hsub : S ⊆ P.filter (fun p => p∣n) := by
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩
  by_cases hc : primeCount P n=0
  · have hz : P.filter (fun p => p∣n)=∅ := card_eq_zero.mp hc
    have hs : S=∅ := Finset.subset_empty.mp (hz ▸ hsub)
    simp only [binnedRamareCoefficient,show P.filter (fun p => p∣n ∧ n/p∈Finset.Ioc (M p) (2*M p))=∅ from hs,sum_empty,norm_zero,zero_le_one]
  · have hcr : (0:ℝ)<primeCount P n := by exact_mod_cast (Nat.pos_of_ne_zero hc)
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑_p∈S,(1:ℝ)/(primeCount P n:ℝ) := by
        apply sum_le_sum
        intro p hp
        have hpn := (mem_filter.mp hp).2.1
        have hpP := (mem_filter.mp hp).1
        have hcnt := primeCount_mul_le hP (m:=n/p) hpP
        rw [Nat.mul_div_cancel' hpn] at hcnt
        rw [norm_div,norm_mul]
        have hd : ‖(primeCount P (n/p)+1:ℂ)‖=(primeCount P (n/p)+1:ℝ) := by
          rw [←Complex.ofReal_natCast (primeCount P (n/p)),←Complex.ofReal_one,←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
        rw [hd]
        apply div_le_div₀ (by positivity)
          ((mul_le_of_le_one_left (norm_nonneg _) (hf p)).trans (hf (n/p))) hcr
        exact_mod_cast hcnt
      _ = (S.card:ℝ)/(primeCount P n:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hcr).mpr (by exact_mod_cast Finset.card_le_card hsub)

lemma binnedRamare_zero_of_rough (P : Finset ℕ) (M : ℕ → ℕ) (f : ℕ → ℂ)
    {n : ℕ} (hc : primeCount P n=0) : binnedRamareCoefficient P M f n=0 := by
  classical
  apply sum_eq_zero
  intro p hp
  have hz := primeCount_pos (mem_filter.mp hp).1 (mem_filter.mp hp).2.1
  omega

lemma binnedRamare_exact (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (M : ℕ → ℕ) {f : ℕ → ℂ} (hm : Multiplicative f) {n : ℕ} (hn : 0<n)
    (hc : 0<primeCount P n) (hsq : ∀p∈P,¬p^2∣n)
    (hcut : ∀p∈P,p∣n → n/p∈Finset.Ioc (M p) (2*M p)) :
    binnedRamareCoefficient P M f n=f n := by
  classical
  have hfilter : P.filter (fun p => p∣n ∧ n/p∈Finset.Ioc (M p) (2*M p))=
      P.filter (fun p => p∣n) := by
    ext p
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hcut p h.1 h.2⟩⟩
  unfold binnedRamareCoefficient
  rw [hfilter]
  have heach : ∀p∈P.filter (fun p => p∣n),
      f p*f (n/p)/(primeCount P (n/p)+1:ℂ)=f n/(primeCount P n:ℂ) := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hp,hpn⟩
    have hp0 := (hP p hp).pos
    have he : p*(n/p)=n := Nat.mul_div_cancel' hpn
    have hnot : ¬p∣n/p := by
      intro hd
      apply hsq p hp
      rw [←he,pow_two]
      exact Nat.mul_dvd_mul_left p hd
    have hco : p.Coprime (n/p) := (hP p hp).coprime_iff_not_dvd.mpr hnot
    have hm0 : 0<n/p := Nat.div_pos (Nat.le_of_dvd hn hpn) hp0
    have hmul := hm p (n/p) hp0 hm0 hco
    rw [he] at hmul
    have hcnt := primeCount_mul hP hp hnot
    rw [he] at hcnt
    rw [←hmul,show (primeCount P (n/p)+1:ℂ)=(primeCount P n:ℂ) by exact_mod_cast hcnt.symm]
  rw [sum_congr rfl heach,sum_const,nsmul_eq_mul]
  change (primeCount P n:ℂ)*(f n/(primeCount P n:ℂ))=f n
  have hcz : (primeCount P n:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hc)
  field_simp

lemma bin_cutoff_same (P : Finset ℕ) (M : ℕ → ℕ) (X E n : ℕ)
    (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E)
    (hn : n∈Finset.Ioc (X+E) (2*(X-E))) {p : ℕ} (hp : p∈P) (hpn : p∣n)
    (hp0 : 0<p) : n/p∈Finset.Ioc (M p) (2*M p) := by
  have he : p*(n/p)=n := Nat.mul_div_cancel' hpn
  apply Finset.mem_Ioc.mpr
  constructor
  · apply (Nat.mul_lt_mul_left hp0).mp
    rw [he]
    exact (hrange p hp).2.trans_lt (mem_Ioc.mp hn).1
  · apply Nat.le_of_mul_le_mul_left (c:=p)
    · rw [he]
      calc n ≤ 2*(X-E) := (mem_Ioc.mp hn).2
           _ ≤ 2*(p*M p) := Nat.mul_le_mul_left 2 (hrange p hp).1
           _ = p*(2*M p) := by ring
    · exact hp0

end SourcePrimeFactor
end OrdinaryCorrelations

end

end OAI
