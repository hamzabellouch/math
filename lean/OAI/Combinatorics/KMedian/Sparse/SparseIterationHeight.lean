import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparseWeightedPartial
import OAI.Combinatorics.KMedian.Rounding.RationalSignedStep
import OAI.Combinatorics.KMedian.Sparse.SparseListTrim
import OAI.Combinatorics.KMedian.Binary.BinaryIntegerHeight

namespace OAI


                                             
section
namespace MetricKMedian.Binary.HasHeight
variable {q r : ℚ} {L : ℕ}
theorem min (hq : HasHeight q L) (hr : HasHeight r L) : HasHeight (min q r) L := by
  rcases le_total q r with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]
end MetricKMedian.Binary.HasHeight

namespace MetricKMedian.RationalWeightedStep
open Binary
variable {n : ℕ}

theorem up_height (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (A B : ℕ)
    (hp : ∀ i, HasHeight (point p i) A) (hr : HasHeight r B) :
    HasHeight (up p i j r) (A+B+1) := by
  exact ((HasHeight.one 0 |>.sub (hp i)).mono (by omega)).min ((hp j |>.div hr).mono (by omega))
theorem down_height (p : Vector ℚ n) (i j : Fin n) (r : ℚ) (A B : ℕ)
    (hp : ∀ i, HasHeight (point p i) A) (hr : HasHeight r B) :
    HasHeight (down p i j r) (A+B+1) := by
  exact ((hp i).mono (by omega)).min (((HasHeight.one 0 |>.sub (hp j)).div hr).mono (by omega))
theorem probability_height (β : Fin n → ℚ) (p : Vector ℚ n) (A B : ℕ)
    (hβ : ∀ i, HasHeight (β i) B) (hp : ∀ i, HasHeight (point p i) A) :
    HasHeight (probability β p) (3*(A+2*B+1)+1) := by
  unfold probability
  split_ifs with h
  · let a := pair p h
    have hr := (hβ a.val.1).div (hβ a.val.2)
    have hu := up_height p a.val.1 a.val.2 _ A (B+B) hp hr
    have hd := down_height p a.val.1 a.val.2 _ A (B+B) hp hr
    convert hd.div (hu.add hd) using 1; ring
  · exact HasHeight.zero _
end MetricKMedian.RationalWeightedStep

namespace MetricKMedian.RationalSignedStep
open Binary RationalWeightedStep
variable {n : ℕ}
theorem probability_height (β : Fin n → ℚ) (p : Vector ℚ n) (A B : ℕ)
    (hβ : ∀ i, HasHeight (β i) B) (hp : ∀ i, HasHeight (point p i) A) :
    HasHeight (probability β p) (3*(A+2*B+1)+1) := by
  unfold probability
  split_ifs with h
  · let a := pair β p h
    have hr := (hβ a.val.1).div (hβ a.val.2)
    have hu := up_height p a.val.1 a.val.2 _ A (B+B) hp hr
    have hd := down_height p a.val.1 a.val.2 _ A (B+B) hp hr
    convert hd.div (hu.add hd) using 1; ring
  · exact HasHeight.zero _
end MetricKMedian.RationalSignedStep

namespace MetricKMedian.SparseWeightedPartial
open Binary RationalWeightedStep
variable {n : ℕ}
theorem features_height (p : Vector ℚ n) (L : ℕ) (hp : ∀ i, HasHeight (point p i) L)
    (a : Fin (n+n*n)) : HasHeight (features p a) (2*L) := by
  unfold features
  generalize finSumFinEquiv.symm a=z
  cases z with
  | inl i => exact (hp i).mono (by omega)
  | inr ij => simpa only [Sum.elim_inr,← two_mul] using (hp (finProdFinEquiv.symm ij).1).mul (hp (finProdFinEquiv.symm ij).2)
end MetricKMedian.SparseWeightedPartial

namespace MetricKMedian.SparseIntegerLaw
open Binary
variable {α : Type} {d : ℕ}

def stepHeight (N d P F : ℕ) := P*N+(((2*(d+1)*(d+1+F*(2*N+1)))*(2*N+1))*(2*N))

theorem step_denominator_height (μ : SparseIntegerLaw α) (v : α → Fin d → ℚ)
    (p : α → ℚ) (hp : ∀ a, 0≤p a ∧ p a≤1) (next : α → Fin 2 → α)
    (N P F : ℕ) (hN : μ.length≤N)
    (hP : ∀ i : Fin μ.length, HasHeight (p μ.states[i.val]) P)
    (hF : ∀ i : Fin μ.length, ∀ b j, HasHeight (v (next μ.states[i.val] b) j) F) :
    (μ.step v p hp next).law.denominator≤μ.law.denominator*(2:ℤ)^(stepHeight N d P F) := by
  have hf : ∀ i : Fin (μ.branch p hp next).length, ∀ j,
      HasHeight (v (μ.branch p hp next).states[i.val] j) F := by
    intro i j
    change HasHeight (v ((Vector.ofFn _)[i.val]) j) F
    simp only [Vector.getElem_ofFn]
    exact hF _ _ j
  have hc := (μ.branch p hp next).compressAuto_denominator v F
    (fun i j => (hf i j).1) (fun i j => (hf i j).2)
  have hb : (μ.branch p hp next).law.denominator≤μ.law.denominator*(2:ℤ)^(P*μ.length) :=
    IntegerBranching.branch_denominator μ.law (fun i => p μ.states[i.val]) (fun i => hp μ.states[i.val]) P (fun i => (hP i).2)
  apply hc.trans
  calc
    _ ≤ (μ.law.denominator*(2:ℤ)^(P*μ.length)) *
        (2:ℤ)^(((2*(d+1)*(d+1+F*((μ.branch p hp next).length+1)))*((μ.branch p hp next).length+1))*(μ.branch p hp next).length) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = μ.law.denominator*(2:ℤ)^(stepHeight μ.length d P F) := by
      simp only [branch,stepHeight,← mul_assoc,Nat.mul_comm 2 μ.length]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ μ.law.denominator_pos.le
      apply pow_le_pow_right₀ (by norm_num)
      unfold stepHeight
      gcongr

theorem encode_length_bound (ea : α → List Bool) (μ : SparseIntegerLaw α) (N H A : ℕ)
    (hn : μ.length≤N) (hd : μ.law.denominator≤(2:ℤ)^H)
    (ha : ∀ i : Fin μ.length, (ea μ.states[i.val]).length≤A) :
    (BinarySparse.encode ea μ).length≤2*(2*(H+4)+1+N*(2*(H+4)+1))+1+N*(2*A+1) := by
  have hd' := Binary.Signed.length_height (by rwa [abs_of_pos μ.law.denominator_pos] : |μ.law.denominator|≤(2:ℤ)^H)
  have hn' : (Binary.encodeList Binary.Signed.encode (List.ofFn μ.law.numerator)).length≤N*(2*(H+4)+1) := by
    apply (Binary.EncodedList.length_bound _ _ (H+4) ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*(H+4)+1) hn
    · intro z hz
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
      exact Binary.Signed.length_height (by rw [abs_of_nonneg (μ.law.numerator_nonneg i)]; exact (μ.law.numerator_le i).trans hd)
  have hs : (Binary.encodeList ea μ.states.toList).length≤N*(2*A+1) := by
    rw [BinarySparse.states_list]
    apply (Binary.EncodedList.length_bound _ _ A ?_).trans
    · simpa only [List.length_ofFn] using Nat.mul_le_mul_right (2*A+1) hn
    · intro a hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ha i
  simp only [BinarySparse.encode,BinarySparse.ed,BinarySparse.raw,BinarySparse.el,IntegerLaw.ListPivot.el,Binary.encodePair_length]
  change 2*(2*(Binary.Signed.encode μ.law.denominator).length+1+
    (Binary.encodeList Binary.Signed.encode (List.ofFn μ.law.numerator)).length)+1+
    (Binary.encodeList ea μ.states.toList).length≤_
  omega

end MetricKMedian.SparseIntegerLaw
end

end OAI
