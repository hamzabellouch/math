import OAI.Combinatorics.ContingencyTables.Machines.InitialFactorialBits
import OAI.Combinatorics.ContingencyTables.Transport.RealKernelApproximation

namespace OAI

/-! # Actual bounded-word initialization of the companion trace

The output is in the literal `PlainIndex` used by the trace chain. Its
ideal rational law is exactly the source's phase-zero law; the bounded
word implementation is within 2^(-h), with an explicit word length.
-/

namespace ContingencyTables.CompanionInitialDraw

open CommonBasesFPRAS ResidualMixture FirstSuccess TwoLiftStates
open CompanionFactorialApplication InitialFactorialLaw InitialFactorialBits
open RealKernelApproximation
open scoped BigOperators Classical
noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

def cellEnum (A : Instance I J) : SmallCell A ≃ Fin (Fintype.card (SmallCell A)) :=
  Fintype.equivFin (SmallCell A)

def cellCapacity (A : Instance I J) (i : Fin (Fintype.card (SmallCell A))) : ℕ :=
  A.b ((cellEnum A).symm i).val.1 ((cellEnum A).symm i).val.2

def indexEquiv (A : Instance I J) :
    {S : Set (Labels A×Bool) // PlainState pairs S} ≃
      PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) where
  toFun S := ⟨⟨S.val,Or.inl S.property⟩,S.property⟩
  invFun S := ⟨S.val.val,S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def idealLaw (A : Instance I J) :
    RationalLaw (PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :=
  equivLaw (indexEquiv A) (companionLaw A)

theorem idealLaw_mass (A : Instance I J)
    (S : PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool)))) :
    ((idealLaw A).mass S:ℝ)=CompanionWarmStart.law A 0 S.val.val :=
  companionLaw_mass A ((indexEquiv A).symm S)

def initialBits (A : Instance I J) (B : ℕ) : ℕ := bitCount (cellCapacity A) B

def draw (A : Instance I J) (B : ℕ) (bits : Fin (initialBits A B) → Bool) :
    PlainIndex (pairs : List ((Labels A×Bool)×(Labels A×Bool))) :=
  indexEquiv A (transversalDraw (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (cellEnum A) B bits)

lemma cellCount_bound (A : Instance I J) : Fintype.card (SmallCell A)≤A.d := by
  exact (Fintype.card_le_of_injective (fun s : SmallCell A => s.val) Subtype.val_injective).trans
    (by simpa only [Fintype.card_prod] using A.hcard)

lemma cellCapacity_bound (A : Instance I J) (i : Fin (Fintype.card (SmallCell A))) :
    cellCapacity A i≤A.W :=
  (A.hsmall _ _ ((cellEnum A).symm i).property).le

theorem initialBits_bound (A : Instance I J) (B : ℕ) :
    initialBits A B≤A.d*(A.W+1)*B := by
  have hh := bitCount_bound (cellCapacity A) B A.W (cellCapacity_bound A)
  exact hh.trans (Nat.mul_le_mul_right B
    (Nat.mul_le_mul_right (A.W+1) (cellCount_bound A)))

theorem draw_error (A : Instance I J) (B : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (initialBits A B) → Bool)) (draw A B))
      (idealLaw A)≤(A.d:ℚ)*(3*A.W+1)/(2*(2:ℚ)^B) := by
  unfold draw initialBits cellCapacity
  have he := mapLaw_equiv_output (indexEquiv A)
    (uniformLaw (α := Fin (bitCount
      (fun i => A.b ((cellEnum A).symm i).val.1 ((cellEnum A).symm i).val.2) B) → Bool))
    (transversalDraw (fun s : SmallCell A => A.b s.val.1 s.val.2) (cellEnum A) B)
  rw [he,idealLaw,variation_equiv]
  have ht := transversalDraw_error (fun s : SmallCell A => A.b s.val.1 s.val.2)
    (cellEnum A) B A.W (fun s => (A.hsmall _ _ s.property).le)
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast cellCount_bound A

def precision (A : Instance I J) (h : ℕ) : ℕ :=
  Nat.clog 2 (A.d*(3*A.W+1)+1)+h

lemma precision_error (A : Instance I J) (h : ℕ) :
    (A.d:ℚ)*(3*A.W+1)/(2*(2:ℚ)^precision A h)≤1/(2:ℚ)^h := by
  have hc : A.d*(3*A.W+1)≤2^Nat.clog 2 (A.d*(3*A.W+1)+1) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have hcr : (A.d:ℚ)*(3*A.W+1)≤(2:ℚ)^Nat.clog 2 (A.d*(3*A.W+1)+1) := by
    exact_mod_cast hc
  unfold precision
  rw [pow_add]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hp := mul_le_mul_of_nonneg_right hcr (show 0≤(2:ℚ)^h by positivity)
  have hp0 : 0≤(2:ℚ)^Nat.clog 2 (A.d*(3*A.W+1)+1)*(2:ℚ)^h := by positivity
  nlinarith [pow_pos (by norm_num : (0:ℚ)<2) h]

/-- The implemented initial word is compared directly to the literal
phase-zero law, so later restart estimates need no initializer oracle. -/
theorem initial_distance (A : Instance I J) (h : ℕ) :
    distance (fun S => ((mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
      (draw A (precision A h))).mass S:ℝ))
      (fun S => CompanionWarmStart.law A 0 S.val.val)≤1/(2:ℝ)^h := by
  have hh := (draw_error A (precision A h)).trans (precision_error A h)
  have he : distance
      (fun S => ((mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
        (draw A (precision A h))).mass S:ℝ))
      (fun S => CompanionWarmStart.law A 0 S.val.val)=
      (variation (mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
        (draw A (precision A h))) (idealLaw A):ℝ) := by
    simp_rw [←idealLaw_mass A]
    simp only [distance,variation,Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_ofNat]
  rw [he]
  have hc : (variation (mapLaw (uniformLaw (α := Fin (initialBits A (precision A h)) → Bool))
      (draw A (precision A h))) (idealLaw A):ℝ)≤((1/(2:ℚ)^h:ℚ):ℝ) := Rat.cast_le.mpr hh
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hc

end
end ContingencyTables.CompanionInitialDraw

end OAI
