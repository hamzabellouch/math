import OAI.NumberTheory.TotientAsymptotic.MassTailSupport

namespace OAI

/-! Reconstructing a basic remainder from its prime prefix and finite tail witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def attachTail (x : ℝ) (H : ℕ) (p : Fin (R x H) → ℕ) (η : TailDatum H) :
    RemainderDatum (L x H) where
  primes k := if hk : k.val < R x H then p ⟨k.val, hk⟩
    else tailPrime η (m x-(k.val+1))
  cofactor := η.cofactor

lemma remainderPrime_attachTail {x : ℝ} {H i : ℕ}
    (p : Fin (R x H) → ℕ) (η : TailDatum H) (hi : i ∈ Finset.Icc 1 (L x H)) :
    remainderPrime (attachTail x H p η) i =
      if hp : i-1 < R x H then p ⟨i-1, hp⟩ else tailPrime η (m x-i) := by
  have hi' := Finset.mem_Icc.mp hi
  have he : i-1+1=i := by omega
  simp only [remainderPrime, hi'.1, hi'.2, and_self, dite_true, attachTail, he]

lemma attachTail_prefix {x : ℝ} {H : ℕ} (hPH : P H ≤ H)
    (p : Fin (R x H) → ℕ) (η : TailDatum H) (i : Fin (R x H)) :
    remainderPrime (attachTail x H p η) (i.val+1) = p i := by
  have hi : i.val+1 ∈ Finset.Icc 1 (L x H) := by
    apply Finset.mem_Icc.mpr
    have := i.isLt
    unfold R L at *
    omega
  rw [remainderPrime_attachTail p η hi]
  simp [i.isLt]

lemma extract_attachTail {x s : ℝ} {H : ℕ} (hPH : P H < H) (hHm : H ≤ m x)
    (p : Fin (R x H) → ℕ) {η : TailDatum H} (hη : IsWitness H s η) :
    extractTail x H (attachTail x H p η) = η := by
  have hQ : (extractTail x H (attachTail x H p η)).Q = η.Q := by
    funext h
    by_cases hh : h.val < P H
    · simp only [extractTail, hh, ite_true]
      exact (hη.1 h hh).symm
    · have hh' : P H ≤ h.val := Nat.le_of_not_gt hh
      have hi : m x-h.val ∈ Finset.Icc 1 (L x H) := by
        apply Finset.mem_Icc.mpr
        have := h.isLt
        unfold L
        omega
      change (if h.val < P H then 1 else remainderPrime (attachTail x H p η) (m x-h.val)) = η.Q h
      rw [ite_eq_right hh, remainderPrime_attachTail p η hi]
      have hp : ¬m x-h.val-1 < R x H := by have := h.isLt; unfold R; omega
      rw [dite_eq_right hp]
      have he : m x-(m x-h.val)=h.val := by have := h.isLt; omega
      rw [he]
      simp [tailPrime, h.isLt]
  cases η
  exact congrArg (fun Q => TailDatum.mk Q _) hQ

lemma attach_extractTail {x : ℝ} {H : ℕ} (hPH : P H ≤ H) (hHm : H ≤ m x)
    (η : RemainderDatum (L x H)) :
    attachTail x H (fun i => remainderPrime η (i.val+1)) (extractTail x H η) = η := by
  have hp : (attachTail x H (fun i => remainderPrime η (i.val+1))
      (extractTail x H η)).primes = η.primes := by
    funext k
    change (if hk : k.val < R x H then remainderPrime η (k.val+1)
      else tailPrime (extractTail x H η) (m x-(k.val+1))) = η.primes k
    have hkL : k.val+1 ∈ Finset.Icc 1 (L x H) := by simp
    have he : remainderPrime η (k.val+1) = η.primes k := by
      simp [remainderPrime, k.isLt]
    split_ifs with hk
    · exact he
    · have hh : m x-(k.val+1) ∈ Finset.Ico (P H) H := by
        apply Finset.mem_Ico.mpr
        have := k.isLt
        unfold L R at *
        omega
      rw [extractTail_prime η hh]
      have hsub : m x-(m x-(k.val+1))=k.val+1 := by
        have := k.isLt
        unfold L at *
        omega
      rw [hsub]
      exact he
  cases η
  exact congrArg (fun p => RemainderDatum.mk p _) hp

/-- Prime-prefix membership is exactly a union over the genuine finite tail
witnesses. This is an equality of admissible data, before any approximation. -/
theorem prefixDatum_iff_attach_witness {x : ℝ} {H d : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (p : Fin (R x H) → ℕ) :
    IsPrefixDatum x H ⟨p,d⟩ ↔ ∃ η ∈ witnesses H (theta x) d,
      IsBasicRemainder x H (attachTail x H p η) := by
  constructor
  · rintro ⟨η, hη, hd, hp⟩
    refine ⟨extractTail x H η, ⟨extractTail_isWitness hη hPH hHm, ?_⟩, ?_⟩
    · rw [extractTail_value η hPH.le hHm]
      exact hd
    · have he : p = fun i => remainderPrime η (i.val+1) := funext hp
      rw [he, attach_extractTail hPH.le hHm]
      exact hη
  · rintro ⟨η, hη, hb⟩
    refine ⟨attachTail x H p η, hb, ?_, fun i => (attachTail_prefix hPH.le p η i).symm⟩
    rw [← extractTail_value (attachTail x H p η) hPH.le hHm,
      extract_attachTail hPH hHm p hη.1]
    exact hη.2

end TotientAsymptotic

end

end OAI
