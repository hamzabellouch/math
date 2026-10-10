import OAI.Probability.ClassicalON.ComplexWard

namespace OAI

universe uE uI uJ uK

noncomputable section
open scoped BigOperators ComplexConjugate

namespace MixedAlgebra
variable {I : Type uI} {J : Type uJ} {E : Type uE} {K : Type uK} [Fintype I] [Fintype J] [Fintype E] [CommRing K]

lemma sum_three_rotate (F : I → J → E → K) :
    (∑ i, ∑ j, ∑ e, F i j e) = ∑ e, ∑ i, ∑ j, F i j e := by
  calc _ = ∑ i, ∑ e, ∑ j, F i j e := by
         apply Finset.sum_congr rfl
         intro i _
         exact Finset.sum_comm
       _ = _ := Finset.sum_comm

lemma sum_weighted_separated (A : E → K) (p : I → E → K) (q : J → E → K)
    (a : I → K) (b : J → K) :
    (∑ i, ∑ j, weighted A (p i * q j) * a i * b j) =
      ∑ e, A e * (∑ i, p i e * a i) * (∑ j, q j e * b j) := by
  simp only [weighted, Finset.sum_mul, Pi.mul_apply]
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_current (B : E → K) (p : I → E → K) (a : I → K) :
    (∑ i, a i * weighted B (p i)) = weighted B (fun e => ∑ i, a i * p i e) := by
  simp only [weighted, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma contract_two_current (A B C : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i * r j) * weighted B (q i) * weighted C (s j)) =
      ∑ e, A e * weighted B (fun l => ∑ i, p i e * q i l) *
        weighted C (fun l => ∑ j, r j e * s j l) := by
  rw [sum_weighted_separated]
  simp only [sum_current]

lemma contract_two_two (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i * r j) * weighted B (q i * s j)) =
      ∑ e, ∑ l, A e * B l * (∑ i, p i e * q i l) * (∑ j, r j e * s j l) := by
  have h (i : I) (j : J) : weighted A (p i * r j) * weighted B (q i * s j) =
      ∑ l, B l * (weighted A (p i*r j) * q i l * s j l) := by
    simp only [weighted, Finset.mul_sum, Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [h]
  rw [sum_three_rotate]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_weighted_separated]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma contract_three_current (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*q i*r j) * weighted B (s j)) =
      ∑ e, A e * (∑ i, p i e*q i e) * weighted B (fun l => ∑ j, r j e*s j l) := by
  have h := sum_weighted_separated A (fun i => p i*q i) r (fun _ => 1)
    (fun j => weighted B (s j))
  simpa only [mul_one, Pi.mul_apply, sum_current] using h

lemma contract_four (A : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*q i*r j*s j)) =
      ∑ e, A e * (∑ i, p i e*q i e) * (∑ j, r j e*s j e) := by
  have h := sum_weighted_separated A (fun i => p i*q i) (fun j => r j*s j)
    (fun _ => 1) (fun _ => 1)
  simpa only [mul_one, Pi.mul_apply, mul_assoc] using h

lemma four_grouped (C : Coeffs E K) (u v w z : E → K) :
    four C u v w z =
    (weighted C.a u * weighted C.b v + weighted C.ab (u*v)) *
      (weighted C.a w * weighted C.b z + weighted C.ab (w*z)) +
    (weighted C.aa (u*w) * weighted C.b v * weighted C.b z +
      weighted C.ab (u*z) * weighted C.b v * weighted C.a w +
      weighted C.ab (v*w) * weighted C.a u * weighted C.b z +
      weighted C.bb (v*z) * weighted C.a u * weighted C.a w +
      weighted C.aa (u*w) * weighted C.bb (v*z) +
      weighted C.ab (u*z) * weighted C.ab (v*w) +
      weighted C.aab (u*v*w) * weighted C.b z +
      weighted C.abb (u*v*z) * weighted C.a w +
      weighted C.aab (u*w*z) * weighted C.b v +
      weighted C.abb (v*w*z) * weighted C.a u +
      weighted C.aabb (u*v*w*z)) := by
  unfold four
  ring

lemma contract_current_three (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*r j*s j) * weighted B (q i)) =
      ∑ e, A e * (∑ j, r j e*s j e) * weighted B (fun l => ∑ i, p i e*q i l) := by
  rw [Finset.sum_comm]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using contract_three_current A B r s p q

omit [Fintype J] in
def paired (C : Coeffs E K) (p q : I → E → K) : K :=
  ∑ i, (weighted C.a (p i) * weighted C.b (q i) + weighted C.ab (p i*q i))

omit [Fintype J] in
def kernel (p q : I → E → K) (e l : E) : K := ∑ i, p i e*q i l

lemma four_family_contraction (C : Coeffs E K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, four C (p i) (q i) (r j) (s j)) =
      paired C p q * paired C r s +
    ((∑ e, C.aa e * weighted C.b (kernel p q e) * weighted C.b (kernel r s e)) +
      (∑ e, C.ab e * weighted C.b (kernel p q e) * weighted C.a (kernel s r e)) +
      (∑ e, C.ab e * weighted C.a (kernel q p e) * weighted C.b (kernel r s e)) +
      (∑ e, C.bb e * weighted C.a (kernel q p e) * weighted C.a (kernel s r e)) +
      (∑ e, ∑ l, C.aa e*C.bb l * kernel p q e l * kernel r s e l) +
      (∑ e, ∑ l, C.ab e*C.ab l * kernel p q e l * kernel s r e l) +
      (∑ e, C.aab e * kernel p q e e * weighted C.b (kernel r s e)) +
      (∑ e, C.abb e * kernel p q e e * weighted C.a (kernel s r e)) +
      (∑ e, C.aab e * kernel r s e e * weighted C.b (kernel p q e)) +
      (∑ e, C.abb e * kernel r s e e * weighted C.a (kernel q p e)) +
      (∑ e, C.aabb e * kernel p q e e * kernel r s e e)) := by
  simp only [four_grouped, Finset.sum_add_distrib]
  have hp : (∑ i, ∑ j,
      (weighted C.a (p i)*weighted C.b (q i) + weighted C.ab (p i*q i)) *
      (weighted C.a (r j)*weighted C.b (s j) + weighted C.ab (r j*s j))) =
      paired C p q * paired C r s := by
    simp only [paired, Finset.sum_mul_sum]
  rw [hp, contract_two_current, contract_two_current, contract_two_current,
    contract_two_current, contract_two_two, contract_two_two,
    contract_three_current, contract_three_current, contract_current_three,
    contract_current_three, contract_four]
  rfl

end MixedAlgebra

end

end OAI
