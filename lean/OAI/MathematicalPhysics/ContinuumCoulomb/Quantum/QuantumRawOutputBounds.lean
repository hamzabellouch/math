import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCoefficientBounds

namespace OAI

/-! Polynomial magnitude envelopes for every actual physical edge and scalar
offset in the rational four-spin output. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram

theorem field_bond_abs (k : ℕ) (i : ℕ) (a : Fin 2) (J : ℚ)
    (b : Bond) (hb : b ∈ field k i a J) : |(b.2.2:ℝ)| ≤ 65*|(J:ℝ)| := by
  obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
  exact fieldValue_abs k a J e

theorem cross_bond_abs (k : ℕ) (r : ℚ) (i j : ℕ) (a b : Fin 2) (J : ℚ)
    (e : Bond) (he : e ∈ cross k r i j a b J) :
    |(e.2.2:ℝ)| ≤ 3920*|(r:ℝ)| *(1+|(J:ℝ)|) := by
  obtain ⟨p,rfl⟩ := List.mem_ofFn.mp he
  exact crossValue_abs k r a b J _ _

theorem bonds_abs (x : Input) (e : Bond) (he : e ∈ bonds x) :
    |(e.2.2:ℝ)| ≤ 3920*|(x.1.2:ℝ)| *(1+|(x.2.2.2.2:ℝ)|)+26000*|(x.2.2.2.2:ℝ)| := by
  dsimp only [bonds] at he
  split_ifs at he with hp hf
  · rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · exact (cross_bond_abs _ _ _ _ _ _ _ e he).trans
          (le_add_of_nonneg_right (by positivity))
      · have h := (field_bond_abs _ _ _ _ e he).trans
          (mul_le_mul_of_nonneg_left (counterA_abs _ _ _ _) (by norm_num : (0:ℝ) ≤ 65))
        nlinarith [abs_nonneg (x.1.2:ℝ),abs_nonneg (x.2.2.2.2:ℝ)]
    · have h := (field_bond_abs _ _ _ _ e he).trans
        (mul_le_mul_of_nonneg_left (counterB_abs _ _ _ _) (by norm_num : (0:ℝ) ≤ 65))
      nlinarith [abs_nonneg (x.1.2:ℝ),abs_nonneg (x.2.2.2.2:ℝ)]
  · have h := field_bond_abs _ _ _ _ e he
    nlinarith [abs_nonneg (x.1.2:ℝ),abs_nonneg (x.2.2.2.2:ℝ)]
  · simp only [List.not_mem_nil] at he

theorem scalar_abs (x : Input) : |(scalar x:ℝ)| ≤ 685600*|(x.2.2.2.2:ℝ)| := by
  dsimp only [scalar]
  split_ifs
  · simpa only [Rat.cast_neg,abs_neg] using offset_abs x.1.1 _ _ x.2.2.2.2
  · simp only [Rat.cast_neg,abs_neg]
    exact (shiftValue_abs _ _).trans (by nlinarith [abs_nonneg (x.2.2.2.2:ℝ)])
  · nlinarith [abs_nonneg (x.2.2.2.2:ℝ)]

theorem termBondsList_abs (k : ℕ) (r : ℚ) (xs : List Raw) {B : ℝ}
    (_hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B)
    (e : Bond) (he : e ∈ termBondsList ((k,r),xs)) :
    |(e.2.2:ℝ)| ≤ 3920*|(r:ℝ)| *(1+B)+26000*B := by
  obtain ⟨ys,hys,he⟩ := List.mem_flatten.mp he
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hys
  exact (bonds_abs ((k,r),t) e he).trans (by gcongr <;> exact hw t ht)

theorem termScalarList_abs (k : ℕ) (r : ℚ) (xs : List Raw) {B : ℝ}
    (_hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |(termScalarList ((k,r),xs):ℝ)| ≤ 685600*xs.length*B := by
  induction xs with
  | nil => simp [termScalarList]
  | cons t xs ih =>
    have ht := hw t (by simp)
    have hs := ih (by intro u hu; exact hw u (by simp [hu]))
    simp only [termScalarList,List.map_cons,List.sum_cons,Rat.cast_add]
    change |(scalar ((k,r),t):ℝ)+(termScalarList ((k,r),xs):ℝ)| ≤ _
    apply (abs_add_le _ _).trans
    have h := (scalar_abs ((k,r),t)).trans
      (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 685600))
    simpa only [List.length_cons,Nat.cast_add,Nat.cast_one] using
      (show |(scalar ((k,r),t):ℝ)|+|(termScalarList ((k,r),xs):ℝ)| ≤
        685600*((xs.length:ℝ)+1)*B by nlinarith)

def outputBound (n m : ℕ) (R B : ℝ) : ℝ :=
  (6*n+1)*R^2+3920*R*(1+B)+(685600*m+26000)*B+1

theorem fullBonds_abs (n k : ℕ) (r : ℚ) (xs : List Raw) {R B : ℝ}
    (hR : |(r:ℝ)| ≤ R) (hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B)
    (e : Bond) (he : e ∈ fullBonds (n,(k,r),xs)) :
    |(e.2.2:ℝ)| ≤ outputBound n xs.length R B := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  rcases List.mem_append.mp he with hp | ht
  · obtain ⟨ys,hys,he⟩ := List.mem_flatten.mp hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hys
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    change |((r^2:ℚ):ℝ)| ≤ _
    rw [Rat.cast_pow,abs_of_nonneg (sq_nonneg (r:ℝ))]
    have hr2 : (r:ℝ)^2 ≤ R^2 := by nlinarith [abs_le.mp hR]
    unfold outputBound
    nlinarith [sq_nonneg R,(Nat.cast_nonneg n : (0:ℝ) ≤ n),
      (Nat.cast_nonneg xs.length : (0:ℝ) ≤ xs.length)]
  · have h := (termBondsList_abs k r xs hB hw e ht).trans
      (show 3920*|(r:ℝ)| *(1+B)+26000*B ≤ 3920*R*(1+B)+26000*B by gcongr)
    unfold outputBound
    nlinarith [sq_nonneg R,(Nat.cast_nonneg n : (0:ℝ) ≤ n),
      (Nat.cast_nonneg xs.length : (0:ℝ) ≤ xs.length)]

theorem fullScalar_abs (n k : ℕ) (r : ℚ) (xs : List Raw) {R B : ℝ}
    (hR : |(r:ℝ)| ≤ R) (hB : 0 ≤ B) (hw : ∀ t ∈ xs, |(t.2.2.2:ℝ)| ≤ B) :
    |(fullScalar (n,(k,r),xs):ℝ)| ≤ outputBound n xs.length R B := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
  have hr2 : (r:ℝ)^2 ≤ R^2 := by nlinarith [abs_le.mp hR]
  have hs := termScalarList_abs k r xs hB hw
  simp only [fullScalar,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg (by positivity : 0 ≤ (r:ℝ)^2*((n:ℝ)*6))]
  unfold outputBound
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ (n:ℝ)*6 by positivity)
  nlinarith [sq_nonneg R]

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
