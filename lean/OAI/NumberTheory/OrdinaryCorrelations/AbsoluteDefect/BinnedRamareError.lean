import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Poly

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

namespace OrdinaryCorrelations.SourcePrimeFactor
open Finset

def binnedRamareError (P : Finset ℕ) (M : ℕ → ℕ) (f : ℕ → ℂ) (X n : ℕ) : ℂ :=
  binnedRamareCoefficient P M f n - if n∈Finset.Ioc X (2*X) then f n else 0

lemma binnedRamareError_norm (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (M : ℕ → ℕ) {f : ℕ → ℂ} (hf : OneBounded f) (X n : ℕ) :
    ‖binnedRamareError P M f X n‖≤2 := by
  unfold binnedRamareError
  apply (norm_sub_le _ _).trans
  have h1 := binnedRamare_norm P hP M hf n
  have h2 : ‖if n∈Finset.Ioc X (2*X) then f n else 0‖≤1 := by split_ifs <;> simp_all [hf n]
  linarith

lemma binnedRamare_support (P : Finset ℕ) (M : ℕ → ℕ) (f : ℕ → ℂ)
    (X E n : ℕ) (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E)
    (hn : n∉Finset.Ioc (X-E) (2*(X+E))) : binnedRamareCoefficient P M f n=0 := by
  classical
  apply sum_eq_zero
  intro p hp
  rcases mem_filter.mp hp with ⟨hp,hpn,hcut⟩
  have he := Nat.mul_div_cancel' hpn
  have hp0 : 0<p := by
    by_contra hh
    have hpz : p=0 := by omega
    subst p
    have hnz : n=0 := Nat.zero_dvd.mp hpn
    subst n
    simp only [Nat.zero_div,Finset.mem_Ioc] at hcut
    omega
  have hlow : X-E<n := by
    calc X-E ≤ p*M p := (hrange p hp).1
         _ < p*(n/p) := Nat.mul_lt_mul_of_pos_left (Finset.mem_Ioc.mp hcut).1 hp0
         _ = n := he
  have hhi : n≤2*(X+E) := by
    calc n = p*(n/p) := he.symm
         _ ≤ p*(2*M p) := Nat.mul_le_mul_left p (Finset.mem_Ioc.mp hcut).2
         _ = 2*(p*M p) := by ring
         _ ≤ 2*(X+E) := Nat.mul_le_mul_left 2 (hrange p hp).2
  exact (hn (Finset.mem_Ioc.mpr ⟨hlow,hhi⟩)).elim

lemma binnedRamareError_support (P : Finset ℕ) (M : ℕ → ℕ) (f : ℕ → ℂ)
    (X E n : ℕ) (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E)
    (hn : n∉Finset.Ioc (X-E) (2*(X+E))) : binnedRamareError P M f X n=0 := by
  have ht : n∉Finset.Ioc X (2*X) := by
    intro hh
    apply hn
    have h := Finset.mem_Ioc.mp hh
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  simp [binnedRamareError,binnedRamare_support P M f X E n hrange hn,ht]

lemma binnedRamareError_zero (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (M : ℕ → ℕ) {f : ℕ → ℂ} (hm : Multiplicative f) (X E n : ℕ)
    (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E)
    (hn : n∈Finset.Ioc (X+E) (2*(X-E))) (hc : 0<primeCount P n)
    (hsq : ∀p∈P,¬p^2∣n) : binnedRamareError P M f X n=0 := by
  have hn0 : 0<n := by have := (Finset.mem_Ioc.mp hn).1; omega
  have ht : n∈Finset.Ioc X (2*X) := by
    have hh := Finset.mem_Ioc.mp hn
    apply Finset.mem_Ioc.mpr
    constructor <;> omega
  have hh := binnedRamare_exact P hP M hm hn0 hc hsq
    (fun p hp hpn => bin_cutoff_same P M X E n hrange hn hp hpn (hP p hp).pos)
  simp [binnedRamareError,hh,ht]

lemma binned_endpoint_count (X E : ℕ) :
    ((Finset.Ioc (X-E) (2*(X+E))) \ (Finset.Ioc (X+E) (2*(X-E)))).card≤6*E := by
  have hs : (Finset.Ioc (X-E) (2*(X+E))) \ (Finset.Ioc (X+E) (2*(X-E))) ⊆
      Finset.Ioc (X-E) (X+E) ∪ Finset.Ioc (2*(X-E)) (2*(X+E)) := by
    intro n hn
    rcases mem_sdiff.mp hn with ⟨hn,hnot⟩
    rcases Finset.mem_Ioc.mp hn with ⟨hlo,hhi⟩
    simp only [Finset.mem_Ioc] at hnot
    simp only [Finset.mem_union,Finset.mem_Ioc]
    omega
  have hh := (Finset.card_le_card hs).trans (card_union_le _ _)
  simp only [Nat.card_Ioc] at hh
  omega

def ramareArithmeticExceptions (P : Finset ℕ) (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter (fun n => primeCount P n=0 ∨ ∃p∈P,p^2∣n)

lemma binnedRamareError_energy (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (M : ℕ → ℕ) {f : ℕ → ℂ} (hf : OneBounded f) (hm : Multiplicative f)
    (X E : ℕ) (hrange : ∀p∈P,X-E≤p*M p ∧ p*M p≤X+E) :
    (∑n∈Finset.Ioc (X-E) (2*(X+E)),‖binnedRamareError P M f X n‖^2) ≤
      4*((ramareArithmeticExceptions P (X-E) (2*(X+E))).card+6*(E:ℝ)) := by
  classical
  let S := Finset.Ioc (X-E) (2*(X+E))
  let A := ramareArithmeticExceptions P (X-E) (2*(X+E))
  let B := S \ Finset.Ioc (X+E) (2*(X-E))
  have hzero : ∀n∈S,n∉A∪B → binnedRamareError P M f X n=0 := by
    intro n hn hnot
    have hnA : n∉A := fun hh => hnot (mem_union_left B hh)
    have hnB : n∉B := fun hh => hnot (mem_union_right A hh)
    have hcentral : n∈Finset.Ioc (X+E) (2*(X-E)) := by
      by_contra hh
      exact hnB (mem_sdiff.mpr ⟨hn,hh⟩)
    have hnS : n∈Finset.Ioc (X-E) (2*(X+E)) := hn
    have har : primeCount P n≠0 ∧ ∀p∈P,¬p^2∣n := by
      simpa only [A,ramareArithmeticExceptions,mem_filter,hnS,true_and,not_or,not_exists,not_and] using hnA
    exact binnedRamareError_zero P hP M hm X E n hrange hcentral (Nat.pos_of_ne_zero har.1) har.2
  have hsub : A∪B ⊆ S := union_subset (filter_subset _ _) sdiff_subset
  have he : (∑n∈S,‖binnedRamareError P M f X n‖^2)=
      ∑n∈A∪B,‖binnedRamareError P M f X n‖^2 := by
    symm
    apply sum_subset hsub
    intro n hn hnot
    rw [hzero n hn hnot]
    simp
  rw [he]
  calc
    _ ≤ ∑_n∈A∪B,(4:ℝ) := by
      apply sum_le_sum
      intro n hn
      have hh := binnedRamareError_norm P hP M hf X n
      nlinarith [norm_nonneg (binnedRamareError P M f X n)]
    _ = 4*((A∪B).card:ℝ) := by simp; ring
    _ ≤ 4*((A.card:ℝ)+(B.card:ℝ)) := by
      gcongr
      exact_mod_cast card_union_le A B
    _ ≤ _ := by
      have hh : (B.card:ℝ)≤6*(E:ℝ) := by exact_mod_cast binned_endpoint_count X E
      dsimp only [A]
      linarith

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
