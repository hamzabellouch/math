import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileCertificateValues

namespace OAI

/-! Exact rational comparisons for Lemma `free:profile-degree`.
The state is obtained by nine checked blocks of the K=34 recurrence. -/

namespace DefocusingNLS.ProfileCertificate
open RationalComplex

/-- All entrywise comparisons in `free:profile-enclosures`, before taking roots. -/
def CentralBounds (s : State) : Prop :=
  let m := s.value.b
  let u := quotient s.value.a m
  let x := quotient s.derivB.d m
  let y := quotient s.derivZ.d m
  81 < normSq m ∧ normSq m < 100 ∧
  2835/1000 < u.re ∧ u.re < 2837/1000 ∧
  1426/1000 < u.im ∧ u.im < 1428/1000 ∧
  normSq s.value.d < (1/1000000000000 : ℚ)^2 * normSq m ∧
  -811/10000 < x.re ∧ x.re < -810/10000 ∧
  1361/10000 < x.im ∧ x.im < 1363/10000 ∧
  -1/10000 < y.re ∧ y.re < 1/10000 ∧
  1237/10000 < y.im ∧ y.im < 1240/10000 ∧
  (∀ v ∈ [s.derivB.a, s.derivB.b, s.derivB.c, s.derivB.d,
          s.derivZ.a, s.derivZ.b, s.derivZ.c, s.derivZ.d], normSq v < 400*normSq m) ∧
  (∀ e ∈ [s.error.a, s.error.b, s.error.c, s.error.d],
    0 ≤ e ∧ e^2 < 50000^2*normSq m)

theorem central_bounds : CentralBounds result := by
  rw [result_eq_computed]
  simp only [CentralBounds, List.forall_mem_cons]
  decide +kernel

/-- Sylvester's strict inequalities and the denominator/linear-size comparisons. -/
def LinearBounds (s : State) : Prop :=
  let m := s.value.b
  let u := quotient s.value.a m
  let x := quotient s.derivB.d m
  let y := quotient s.derivZ.d m
  let κ : ℚ := (48/1000)^2
  κ < normSq x ∧
  (normSq x-κ)*(normSq y-κ) > (x.re*y.re+x.im*y.im)^2 ∧
  normSq (1 - (⟨0,centerZ/5⟩ : RationalComplex)*u) > (234/100)^2 ∧
  normSq u < (318/100)^2 ∧
  normSq x < (159/1000)^2 ∧ normSq y < (124/1000)^2 ∧
  x.re*y.im-x.im*y.re < 0

theorem linear_bounds : LinearBounds result := by
  rw [result_eq_computed]
  unfold LinearBounds
  decide +kernel

/-- Factorwise rational upper bound for the determinant on the parameter disk. -/
def determinantSqBound : ℚ :=
  ((List.range 34).map fun n =>
    ((n : ℚ)^2+(centerB+radius)^2)*(((n : ℚ)-5)^2+(centerB+radius)^2)).prod /
      (Nat.factorial 34 : ℚ)^4

theorem determinant_bound : determinantSqBound <
    (62/10000000000000 : ℚ)^2 * (normSq result.value.b)^2 := by
  rw [result_eq_computed]
  decide +kernel

theorem propagation_comparisons :
    6/10 < denominatorGap ∧ changeBound < 5/10000000 ∧
    jetError + tailError < 25/1000000000000 ∧
    (283/1000)*radius+25/1000000000000 < 3/1000000000 ∧
    (48/1000)*radius > 25/1000000000000 ∧
    (48/1000)*radius-25/1000000000000 = 91/200000000000 := by
  decide +kernel

end DefocusingNLS.ProfileCertificate

end OAI
