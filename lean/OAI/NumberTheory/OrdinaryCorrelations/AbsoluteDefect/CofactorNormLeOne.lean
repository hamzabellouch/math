import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SumRangeSuccEqIcc

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

lemma cofactor_norm_le_one (P : Finset ℕ) (f : ℕ → ℂ)
    (hf : ∀n,‖f n‖≤1) (n : ℕ) :
    ‖f n/((OrdinaryCorrelations.SourcePrimeFactor.primeCount P n:ℂ)+1)‖≤1 := by
  rw [norm_div]
  have he : ‖((OrdinaryCorrelations.SourcePrimeFactor.primeCount P n:ℂ)+1)‖=
      ((OrdinaryCorrelations.SourcePrimeFactor.primeCount P n:ℝ)+1) := by norm_cast
  rw [he]
  apply (div_le_iff₀ (by positivity)).mpr
  simpa using (hf n).trans (by linarith [Nat.cast_nonneg (α:=ℝ) (OrdinaryCorrelations.SourcePrimeFactor.primeCount P n)] : (1:ℝ)≤(OrdinaryCorrelations.SourcePrimeFactor.primeCount P n:ℝ)+1)

lemma range_divisor_count (N p : ℕ) (hp : 0<p) :
    (((range N).filter (fun n => p∣1+n)).card:ℝ)≤(N:ℝ)/p := by
  have he := sum_range_succ_eq_Icc N (fun m => if p∣m then (1:ℝ) else 0)
  simp only [←sum_filter,sum_const,nsmul_eq_mul,mul_one] at he
  rw [he,OrdinaryCofactorWeight.card_multiples_Icc N p hp]
  exact Nat.cast_div_le

def coprimeRamarePacket (P : Finset ℕ) (f u : ℕ → ℂ) (D N : ℕ) (α : ℝ) : ℂ :=
  ∑p∈P,f p*∑n∈(range N).filter (fun n => ¬p∣1+n),
    (f (1+n)/((OrdinaryCorrelations.SourcePrimeFactor.primeCount P (1+n):ℂ)+1))*
      smooth u D (p*(1+n))*phase (α*(p:ℝ)*(1+n))

theorem coprime_packet_error (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : ∀n,‖f n‖≤1) (hu : ∀n,‖u n‖≤1)
    (D N : ℕ) (α : ℝ) :
    ‖ramarePacket P f u D N α-coprimeRamarePacket P f u D N α‖≤
      (N:ℝ)*∑p∈P,(p:ℝ)⁻¹ := by
  let g := fun p n => (f (1+n)/((OrdinaryCorrelations.SourcePrimeFactor.primeCount P (1+n):ℂ)+1))*
      smooth u D (p*(1+n))*phase (α*(p:ℝ)*(1+n))
  have hg (p n : ℕ) : ‖g p n‖≤1 := by
    simp only [g,norm_mul,norm_phase,mul_one]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (cofactor_norm_le_one P f hf (1+n))).trans (smooth_bound u hu D _)
  have hi : ramarePacket P f u D N α-coprimeRamarePacket P f u D N α=
      ∑p∈P,f p*∑n∈(range N).filter (fun n => p∣1+n),g p n := by
    unfold ramarePacket coprimeRamarePacket
    rw [←sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    rw [←mul_sub]
    congr 1
    have hh := sum_filter_add_sum_filter_not (range N) (fun n => p∣1+n) (g p)
    change (∑n∈range N,g p n)-(∑n∈(range N).filter (fun n => ¬p∣1+n),g p n)=_
    rw [←hh]
    ring
  rw [hi]
  calc
    _ ≤ ∑p∈P,‖f p*∑n∈(range N).filter (fun n => p∣1+n),g p n‖ := norm_sum_le _ _
    _ ≤ ∑p∈P,(N:ℝ)/p := by
      apply sum_le_sum
      intro p hp
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_right (hf p) (norm_nonneg _)).trans
      simp only [one_mul]
      calc
        _ ≤ ∑n∈(range N).filter (fun n => p∣1+n),‖g p n‖ := norm_sum_le _ _
        _ ≤ ∑n∈(range N).filter (fun n => p∣1+n),(1:ℝ) := sum_le_sum (fun n hn => hg p n)
        _ ≤ _ := by simpa using range_divisor_count N p (hP p hp).pos
    _ = _ := by simp only [mul_sum,div_eq_mul_inv]

theorem coprime_packet_multiplicative (P : Finset ℕ) (hP : ∀p∈P,Nat.Prime p)
    (f u : ℕ → ℂ) (hf : OrdinaryCorrelations.Multiplicative f)
    (D N : ℕ) (α : ℝ) :
    coprimeRamarePacket P f u D N α=
      ∑p∈P,∑n∈(range N).filter (fun n => ¬p∣1+n),
        (f (p*(1+n))/((OrdinaryCorrelations.SourcePrimeFactor.primeCount P (1+n):ℂ)+1))*
          smooth u D (p*(1+n))*phase (α*(p:ℝ)*(1+n)) := by
  unfold coprimeRamarePacket
  apply sum_congr rfl
  intro p hp
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [hf p (1+n) (hP p hp).pos (by omega)
    ((hP p hp).coprime_iff_not_dvd.mpr (mem_filter.mp hn).2)]
  ring

end OrdinaryAdditiveBilinear

end

end OAI
