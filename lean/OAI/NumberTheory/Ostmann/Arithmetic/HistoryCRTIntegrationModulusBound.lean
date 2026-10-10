import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModulusBoundBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open Construction HistorySignedResidues

lemma frequencyProduct_le {N : ℕ} {B : ℝ} {level : ℕ} (hB : 1≤B) (h g : History level)
    (hh : factorBound N B h) (hg : factorBound N B g) :
    (FrequencyPrecision.product (h.frequencies++g.frequencies):ℝ)≤
      B^(h.frequencies.length+g.frequencies.length) := by
  have hs : ∀q∈(h.frequencies++g.frequencies).map Int.natAbs,(q:ℝ)≤B := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hq
    rcases List.mem_append.mp hv with hv | hv
    · simpa only [Nat.cast_natAbs,Int.cast_abs,intSize] using factorBound_frequencies h hh v hv
    · simpa only [Nat.cast_natAbs,Int.cast_abs,intSize] using factorBound_frequencies g hg v hv
  have hp := natProduct_intSize_le (le_trans (by norm_num) hB) _ hs
  have hp' := (abs_le.mp hp).2
  simpa only [FrequencyPrecision.product,Int.cast_natCast,
    List.length_map,List.length_append] using hp'

lemma frequencyModulus_le {N : ℕ} {B : ℝ} {level : ℕ} (hB : 1≤B) (h g : History level)
    (hh : factorBound N B h) (hg : factorBound N B g) (n : ℕ) :
    (frequencyModulus h g n:ℝ)≤B^(2*2^(level+1)*n) := by
  have hp := frequencyProduct_le hB h g hh hg
  have hc : h.frequencies.length+g.frequencies.length≤2*2^(level+1) := by
    have hh := History.frequencies_length h
    have hg := History.frequencies_length g
    omega
  calc
    _ ≤ (B^(h.frequencies.length+g.frequencies.length))^n := by
      simpa only [frequencyModulus,Nat.cast_pow] using
        pow_le_pow_left₀ (Nat.cast_nonneg (FrequencyPrecision.product _)) hp n
    _ = B^((h.frequencies.length+g.frequencies.length)*n) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ hB (Nat.mul_le_mul_right n hc)

def crtCostCoefficient (l n : ℕ) : ℕ := 2+2*2^(l+1)*n+4*4^(l+1)

lemma crtCostCoefficient_pos (l n : ℕ) : 0<crtCostCoefficient l n := by
  unfold crtCostCoefficient
  omega

theorem minimalCRT_le {N : ℕ} {B : ℝ} {level : ℕ} (hB : 1≤B) (h g : History level)
    (hh : factorBound N B h) (hg : factorBound N B g)
    (outside : List ℕ) (hlen : outside.length≤N) (hout : ∀q∈outside,(q:ℝ)≤B)
    (n : ℕ) :
    ((rootModulus h*outsideModulus outside*frequencyModulus h g n*representativeModulus h g:ℕ):ℝ)≤
      B^(crtCostCoefficient level n*(N+1)) := by
  have hb : 0≤B := le_trans (by norm_num) hB
  have hr := rootModulus_le hB h hh
  have ho := outsideModulus_le hB outside hlen hout
  have hf := frequencyModulus_le hB h g hh hg n
  have hp := representativeModulus_le hB h g hh hg
  have hc : N+N+2*2^(level+1)*n+2*(divisorCost h+divisorCost g)≤
      crtCostCoefficient level n*(N+1) := by
    have hd := Nat.add_le_add (divisorCost_le h hh) (divisorCost_le g hg)
    have hextra : 0≤(2*2^(level+1)*n)*N := Nat.zero_le _
    unfold crtCostCoefficient
    nlinarith
  calc
    _ ≤ B^N*B^N*B^(2*2^(level+1)*n)*B^(2*(divisorCost h+divisorCost g)) := by
      push_cast
      gcongr
    _ = B^(N+N+2*2^(level+1)*n+2*(divisorCost h+divisorCost g)) := by
      simp only [pow_add]
    _ ≤ _ := pow_le_pow_right₀ hB hc

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
