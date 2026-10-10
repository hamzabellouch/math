import OAI.NumberTheory.TotientAsymptotic.Mass
import OAI.NumberTheory.TotientAsymptotic.BandComparison

namespace OAI

/-! The finite tail witness extracted from a basic remainder. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def extractTail (x : ℝ) (H : ℕ) (η : RemainderDatum (L x H)) : TailDatum H where
  Q h := if h.val < P H then 1 else remainderPrime η (m x-h.val)
  cofactor := η.cofactor

lemma extractTail_prime {x : ℝ} {H h : ℕ} (η : RemainderDatum (L x H))
    (hh : h ∈ Finset.Ico (P H) H) :
    tailPrime (extractTail x H η) h = remainderPrime η (m x-h) := by
  have hh' := Finset.mem_Ico.mp hh
  simp [tailPrime, extractTail, hh'.2, not_lt.mpr hh'.1]

lemma extractTail_log {x : ℝ} {H h : ℕ} (η : RemainderDatum (L x H))
    (hHm : H ≤ m x) (hh : h ∈ Finset.Ico (P H) H) :
    tailLog (extractTail x H η) h = remainderCoord x η (m x-h) := by
  have hh' := Finset.mem_Ico.mp hh
  have hi : m x-h ≠ 0 := by omega
  simp only [tailLog, extractTail_prime η hh, remainderCoord, hi, ite_false]

lemma bandScale_reversed {x : ℝ} {h : ℕ} (hh : h ≤ m x) :
    bandScale x (m x-h) = alpha (theta x)*h*(rho^h)⁻¹ := by
  simp only [bandScale, Nat.sub_sub_self hh]

lemma extractTail_value {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H))
    (hPH : P H ≤ H) (hHm : H ≤ m x) :
    w (extractTail x H η) = remainderTail x H η := by
  unfold w remainderTail
  change η.cofactor* _ = η.cofactor* _
  congr 1
  apply Finset.prod_bij (fun h _ => m x-h)
  · intro h hh
    have := Finset.mem_Ico.mp hh
    apply Finset.mem_Icc.mpr
    unfold R L
    omega
  · intro h hh k hk heq
    have := Finset.mem_Ico.mp hh
    have := Finset.mem_Ico.mp hk
    omega
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hr : m x-i ∈ Finset.Ico (P H) H := by
      apply Finset.mem_Ico.mpr
      unfold R L at *
      omega
    refine ⟨m x-i, hr, ?_⟩
    unfold L at hi'
    omega
  · intro h hh
    exact extractTail_prime η hh

lemma extractTail_threshold {x : ℝ} {H h : ℕ} (η : RemainderDatum (L x H))
    (hHm : H ≤ m x) (hPh : P H ≤ h) (hhH : h ≤ H) :
    (∑ l ∈ Finset.Ico (P H) h, a (h-l)*tailLog (extractTail x H η) l) =
      ∑ r ∈ Finset.Icc (m x-h+1) (L x H), a (r-(m x-h))*remainderCoord x η r := by
  apply Finset.sum_bij (fun l _ => m x-l)
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    apply Finset.mem_Icc.mpr
    unfold L
    omega
  · intro l hl k hk heq
    have := Finset.mem_Ico.mp hl
    have := Finset.mem_Ico.mp hk
    omega
  · intro r hr
    have hr' := Finset.mem_Icc.mp hr
    refine ⟨m x-r, ?_, ?_⟩
    · apply Finset.mem_Ico.mpr
      unfold L at hr'
      omega
    · unfold L at hr'
      omega
  · intro l hl
    have hl' := Finset.mem_Ico.mp hl
    have hlH : l ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
    rw [extractTail_log η hHm hlH]
    congr 2
    omega

/-- A basic remainder gives one of the actual phase-dependent finite witnesses,
with exactly the same tail totient; no extra tail representatives are counted. -/
theorem extractTail_isWitness {x : ℝ} {H : ℕ} {η : RemainderDatum (L x H)}
    (hη : IsBasicRemainder x H η) (hPH : P H < H) (hHm : H ≤ m x) :
    IsWitness H (theta x) (extractTail x H η) := by
  refine ⟨?_, hη.1, ?_, ?_, ?_⟩
  · intro h hh
    simp [extractTail, hh]
  · intro h hh
    have hh' := Finset.mem_Ico.mp hh
    have hi : m x-h ∈ Finset.Icc 1 (L x H) := by
      apply Finset.mem_Icc.mpr
      unfold L
      omega
    have hp := hη.2.1 (m x-h) hi
    have hhm : h ≤ m x := by omega
    rw [bandScale_reversed hhm] at hp
    simp only [← mul_assoc] at hp
    rw [extractTail_prime η hh, extractTail_log η hHm hh]
    refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
    rw [extractTail_threshold η hHm hh'.1 (by omega)]
    have hsum := hη.2.2.1 (m x-h) (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hi).2⟩)
    have hcoord : 0 ≤ remainderCoord x η (m x-h) := by
      have ha := alpha_pos (theta x)
      have hr := rho_pos
      exact (by positivity : (0 : ℝ) ≤ (9/10 : ℝ)*alpha (theta x)*h*(rho^h)⁻¹).trans hp.2.1
    have hxi : (if m x-h = L x H then 1 else xi x (m x-h)) ≤
        1+(1/10000 : ℝ)*Real.exp (-(h : ℝ)/40) := by
      have he : m x-(m x-h) = h := Nat.sub_sub_self hhm
      split_ifs
      · have ht : 0 ≤ (1/10000 : ℝ)*Real.exp (-(h : ℝ)/40) := by positivity
        linarith
      · simp [xi, he]
    exact hsum.trans (mul_le_mul_of_nonneg_right hxi hcoord)
  · change largestPrimeFactor η.cofactor ≤ tailPrime (extractTail x H η) (P H)
    rw [extractTail_prime η (Finset.mem_Ico.mpr ⟨le_rfl, hPH⟩)]
    exact hη.2.2.2.1
  · change Real.log (η.cofactor : ℝ) ≤ _
    have hb := hη.2.2.2.2
    have hPm : P H ≤ m x := hPH.le.trans hHm
    change Real.log (η.cofactor : ℝ) ≤ Real.exp (2*bandScale x (m x-P H)) at hb
    rw [bandScale_reversed hPm] at hb
    simpa only [mul_assoc] using hb

end TotientAsymptotic

end

end OAI
