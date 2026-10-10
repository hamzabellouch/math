import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CofactorNormLeOne
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumMultiplesIoc
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TruncatedWeightedPacket

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

namespace OrdinaryCorrelations.SourcePrimeFactor
open OrdinaryAdditiveBilinear Finset

def globalPacket (P : Finset ℕ) (f u : ℕ → ℂ) (D X : ℕ) (α : ℝ) : ℂ :=
  ∑p∈P,f p*∑n∈range (X/p),
    (f (1+n)/((primeCount P (1+n):ℂ)+1))*smooth u D (p*(1+n))*
      phase (α*(p:ℝ)*(1+n))

def globalCoprimePacket (P : Finset ℕ) (f u : ℕ → ℂ) (D X : ℕ) (α : ℝ) : ℂ :=
  ∑p∈P,f p*∑n∈(range (X/p)).filter (fun n => ¬p∣1+n),
    (f (1+n)/((primeCount P (1+n):ℂ)+1))*smooth u D (p*(1+n))*
      phase (α*(p:ℝ)*(1+n))

def additiveBudget (P : Finset ℕ) (D X A K : ℕ) (κ : ℝ) : ℝ :=
  (((X/A:ℕ):ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card)*
    (((X/A:ℕ):ℝ)*P.card+(P.card:ℝ)^2*((2+4*((X/A:ℕ):ℝ)*K/D)/κ))

theorem global_packet_minor_arc (P : Finset ℕ) (hprime : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : OneBounded f) (hu : ∀n,‖u n‖≤1)
    (D X A K : ℕ) (hA : 0<A) (hN : 0<X/A) (α : ℝ)
    (hlo : ∀p∈P,A≤p) (hhi : ∀p∈P,p≤K)
    (hL : 0<∑p∈P,(p:ℝ)⁻¹) {κ : ℝ} (hκ : 0<κ)
    (hgap : ∀p∈P,∀q∈P,p≠q → κ≤‖1-phase (α*((p:ℝ)-q))‖) :
    ‖globalPacket P f u D X α‖^2 ≤ additiveBudget P D X A K κ := by
  let N := X/A
  let w := fun n => f n/((primeCount P n:ℂ)+1)
  have ha := OrdinaryCofactorWeight.arithmetic_cofactor_second_moment P hprime hN hL f hf
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hw : (∑n∈range N,‖w (1+n)‖^2)≤
      (N:ℝ)*(2/(∑p∈P,(p:ℝ)⁻¹)^2)+2^P.card := by
    rw [sum_range_succ_eq_Icc N (fun n => ‖w n‖^2)]
    have hh := (mul_le_mul_of_nonneg_left ha hNr.le)
    simpa only [N,w,primeCount,←mul_assoc,mul_inv_cancel₀ hNr.ne',
      one_mul,mul_add,mul_div_cancel₀ _ hNr.ne'] using hh
  have hT (p : ℕ) (hp : p∈P) : X/p≤N := Nat.div_le_div_left (hlo p hp) hA
  have hb := truncated_weighted_packet P u w f hu hf (fun p => X/p)
    D 1 N K hT α hhi hκ hgap
  have hh : ‖globalPacket P f u D X α‖^2 ≤ (∑n∈range N,‖w (1+n)‖^2)*
      ((N:ℝ)*P.card+(P.card:ℝ)^2*((2+4*(N:ℝ)*K/D)/κ)) := by
    simpa only [globalPacket,w,Nat.cast_one] using hb
  exact hh.trans (mul_le_mul_of_nonneg_right hw (by positivity))

theorem global_coprime_error (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : OneBounded f) (hu : ∀n,‖u n‖≤1)
    (D X : ℕ) (α : ℝ) :
    ‖globalPacket P f u D X α-globalCoprimePacket P f u D X α‖≤
      (X:ℝ)*∑p∈P,(p:ℝ)⁻¹^2 := by
  let g := fun p n => (f (1+n)/((primeCount P (1+n):ℂ)+1))*
      smooth u D (p*(1+n))*phase (α*(p:ℝ)*(1+n))
  have hg (p n : ℕ) : ‖g p n‖≤1 := by
    simp only [g,norm_mul,norm_phase,mul_one]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (cofactor_norm_le_one P f hf (1+n))).trans (smooth_bound u hu D _)
  have hi : globalPacket P f u D X α-globalCoprimePacket P f u D X α=
      ∑p∈P,f p*∑n∈(range (X/p)).filter (fun n => p∣1+n),g p n := by
    unfold globalPacket globalCoprimePacket
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    rw [←mul_sub]
    congr 1
    have hh := sum_filter_add_sum_filter_not (range (X/p)) (fun n => p∣1+n) (g p)
    change (∑n∈range (X/p),g p n)-(∑n∈(range (X/p)).filter (fun n => ¬p∣1+n),g p n)=_
    rw [←hh]
    ring
  rw [hi]
  calc
    _ ≤ ∑p∈P,‖f p*∑n∈(range (X/p)).filter (fun n => p∣1+n),g p n‖ := norm_sum_le _ _
    _ ≤ ∑p∈P,(X:ℝ)*(p:ℝ)⁻¹^2 := by
      apply sum_le_sum
      intro p hp
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_right (hf p) (norm_nonneg _)).trans
      simp only [one_mul]
      calc
        _ ≤ ∑n∈(range (X/p)).filter (fun n => p∣1+n),‖g p n‖ := norm_sum_le _ _
        _ ≤ ∑n∈(range (X/p)).filter (fun n => p∣1+n),(1:ℝ) := sum_le_sum (fun n hn => hg p n)
        _ ≤ ((X/p:ℕ):ℝ)/p := by simpa using range_divisor_count (X/p) p (hP p hp).pos
        _ ≤ ((X:ℝ)/p)/p := div_le_div_of_nonneg_right Nat.cast_div_le (by positivity)
        _ = _ := by ring
    _ = _ := by rw [mul_sum]

lemma sum_range_succ_Ioc (g : ℕ → ℂ) (N : ℕ) :
    (∑n∈range N,g (1+n))=∑m∈Ioc 0 N,g m := by
  apply sum_bij (fun n _ => 1+n)
  · intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_Ioc]
    omega
  · intro n hn m hm he
    omega
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    exact ⟨m-1,Finset.mem_range.mpr (by omega),by omega⟩
  · intro n hn
    rfl

theorem global_coprime_is_bilinear (P : Finset ℕ) (f u : ℕ → ℂ)
    (D X : ℕ) (α : ℝ) :
    globalCoprimePacket P f u D X α=
      bilinearPart P f (fun m => smooth u D m*phase (α*m)) 0 X := by
  unfold globalCoprimePacket bilinearPart
  simp only [Nat.zero_div,Nat.zero_add,Finset.sum_filter]
  apply sum_congr rfl
  intro p hp
  congr 1
  calc
    _ = ∑n∈range (X/p),if ¬p∣1+n then
        f (1+n)*(smooth u D (p*(1+n))*phase (α*((p*(1+n):ℕ):ℝ)))/
          ((primeCount P (1+n):ℂ)+1) else 0 := by
      apply sum_congr rfl
      intro n hn
      split_ifs <;> try rfl
      have he : α*(p:ℝ)*(1+(n:ℝ))=α*((p*(1+n):ℕ):ℝ) := by push_cast; ring
      rw [he]
      ring
    _ = _ := sum_range_succ_Ioc (fun m => if ¬p∣m then
      f m*(smooth u D (p*m)*phase (α*((p*m:ℕ):ℝ)))/((primeCount P m:ℂ)+1) else 0) (X/p)

end OrdinaryCorrelations.SourcePrimeFactor

end

end OAI
