import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseMulStar

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryAdditiveBilinear

lemma sum_range_cut (g : ℕ → ℂ) (N R : ℕ) (hR : R≤N) :
    (∑n∈range N,if n<R then g n else 0)=∑n∈range R,g n := by
  rw [←sum_filter]
  have hs : (range N).filter (fun n => n<R)=range R := by
    ext n
    simp only [mem_filter,Finset.mem_range]
    omega
  rw [hs]

lemma truncated_pair_sum (N : ℕ) (r s : ℕ) (hr : r≤N) (hs : s≤N)
    (b c : ℕ → ℂ) :
    (∑n∈range N,(if n<r then b n else 0)*star (if n<s then c n else 0))=
      ∑n∈range (min r s),b n*star (c n) := by
  calc
    _ = ∑n∈range N,if n < (min r s) then b n*star (c n) else 0 := by
      apply sum_congr rfl
      intro n hn
      simp only [lt_min_iff]
      split_ifs <;> simp_all
    _ = _ := sum_range_cut _ N (min r s) (by simpa using min_le_min hr hs)

theorem truncated_smoothed_prime_energy (P : Finset ℕ) (u : ℕ → ℂ)
    (hu : ∀n,‖u n‖≤1) (c : ℕ → ℂ) (hc : ∀p,‖c p‖≤1)
    (T : ℕ → ℕ) (D a N K : ℕ) (hT : ∀p∈P,T p≤N) (α : ℝ)
    (hP : ∀p∈P,p≤K) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    (∑n∈range N,‖∑p∈P,if n<T p then
      c p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n) else 0‖^2) ≤
      (N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ) := by
  let b := fun p n => if n<T p then c p*smooth u D (p*(a+n))*phase (α*(p:ℝ)*n) else 0
  let E : ℝ := (2+4*(N:ℝ)*K/D)/κ
  have hE : 0≤E := by dsimp [E]; positivity
  have hb (p n : ℕ) : ‖b p n‖≤1 := by
    dsimp [b]
    split_ifs
    · simp only [norm_mul,norm_phase,mul_one]
      simpa only [one_mul] using
        mul_le_mul (hc p) (smooth_bound u hu D _) (norm_nonneg _) zero_le_one
    · simp
  have hd (p : ℕ) : ‖∑n∈range N,b p n*star (b p n)‖≤(N:ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑n∈range N,(1:ℝ) := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul,norm_star]
        simpa only [one_mul] using
          mul_le_mul (hb p n) (hb p n) (norm_nonneg _) zero_le_one
      _ = _ := by simp
  have ho (p : ℕ) (hp : p∈P) (q : ℕ) (hq : q∈P) (hpq : p≠q) :
      ‖∑n∈range N,b p n*star (b q n)‖≤E := by
    dsimp only [b]
    rw [truncated_pair_sum N (T p) (T q) (hT p hp) (hT q hq)]
    apply (smoothed_pair_bound u hu c hc D p q a (min (T p) (T q)) α
      hκ (hgap p hp q hq hpq)).trans
    have hpk : (p:ℝ)≤K := by exact_mod_cast hP p hp
    have hqk : (q:ℝ)≤K := by exact_mod_cast hP q hq
    have hnk : (min (T p) (T q):ℝ)≤N := by
      exact_mod_cast le_trans (min_le_left (T p) (T q)) (hT p hp)
    apply div_le_div_of_nonneg_right _ hκ.le
    calc
      _ ≤ 2+(N:ℝ)*((2*(K:ℝ))*(2/(D:ℝ))) := by
        gcongr
        · exact le_trans (min_le_left (T p) (T q)) (hT p hp)
        · linarith
      _ = _ := by ring
  have hr (p : ℕ) (hp : p∈P) :
      ∑q∈P,‖∑n∈range N,b p n*star (b q n)‖≤(N:ℝ)+(P.card:ℝ)*E := by
    calc
      _ ≤ ∑q∈P,((if p=q then (N:ℝ) else 0)+E) := by
        apply sum_le_sum
        intro q hq
        by_cases he : p=q
        · subst q
          simpa using (hd p).trans (le_add_of_nonneg_right hE)
        · simpa [he] using ho p hp q hq he
      _ = _ := by simp [sum_add_distrib,hp]
  calc
    _ ≤ ∑p∈P,∑q∈P,‖∑n∈range N,b p n*star (b q n)‖ := energy_le_gram P b N
    _ ≤ ∑p∈P,((N:ℝ)+(P.card:ℝ)*E) := sum_le_sum hr
    _ = _ := by simp [E]; ring

end OrdinaryAdditiveBilinear

end

end OAI
