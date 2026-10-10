import OAI.Algebra.AuslanderReiten.Cocycles.CocycleCorners
import OAI.Algebra.AuslanderReiten.Modules.Twist

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

def selected : TIndex → Bool
  | (false, .u) | (false, .v) | (false, .t) => true
  | (true, .e) | (true, .x) | (true, .y) | (true, .z) | (true, .u) | (true, .v) => true
  | _ => false

def z (H : k) : T k q →ₗ[k] T k q :=
  ∑ i : TIndex, (T.coefficient q i).smulRight
    (if selected i then (H * q) • T.vector q i else 0)

theorem z_vector (H : k) (i : TIndex) :
    z q H (T.vector q i) = if selected i then (H * q) • T.vector q i else 0 := by
  simp only [z, LinearMap.sum_apply, LinearMap.smulRight_apply, T.coefficient_vector]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem coefficient_z (H : k) (a : T k q) (i : TIndex) :
    T.coefficient q i (z q H a) =
      if selected i then (H * q) * T.coefficient q i a else 0 := by
  conv_lhs => rw [T.expand q a]
  simp only [map_sum, map_smul, z_vector]
  rw [Finset.sum_eq_single i]
  · by_cases hi : selected i <;> simp [hi, mul_comm]
  · intro j _ hj
    by_cases hs : selected j
    · simp only [ite_eq_left hs, map_smul, T.coefficient_vector, ite_eq_right (Ne.symm hj), smul_zero]
    · simp only [ite_eq_right hs, map_zero, smul_zero]
  · simp

theorem coefficient_twist (H : kˣ) (a : T k q) (i : TIndex) :
    T.coefficient q i (TrivialExtension.twist H a) =
      (H : k) ^ i.weight * T.coefficient q i a := by
  obtain ⟨b, i⟩ := i
  cases b <;> simp [T.coefficient, TIndex.weight]

theorem twist_vector (H : kˣ) (i : TIndex) :
    TrivialExtension.twist H (T.vector q i) = (H : k) ^ i.weight • T.vector q i := by
  apply T.coordinate_ext q
  intro j
  rw [coefficient_twist]
  by_cases hj : j = i <;> simp [hj]

theorem p_twist (H : kˣ) (a b c : T k q) :
    p q (TrivialExtension.twist H a) (TrivialExtension.twist H b) (TrivialExtension.twist H c) =
      (H : k) • TrivialExtension.twist H (p q a b c) := by
  rw [p_apply, p_apply, map_list_sum, List.smul_sum]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hw := (cochain_term_properties t ht).2.2.2.2.2
  have hpow : (H : k) ^ t.first.weight * (H : k) ^ t.second.weight * (H : k) ^ t.third.weight =
      (H : k) * (H : k) ^ t.output.weight := by
    rw [← pow_add, ← pow_add, hw, pow_succ']
  simp only [evalTriple, coefficient_twist, map_smul, twist_vector, smul_smul]
  congr 1
  calc
    _ = ((H : k) ^ t.first.weight * (H : k) ^ t.second.weight * (H : k) ^ t.third.weight) *
      (q ^ t.degree * T.coefficient q t.first a * T.coefficient q t.second b * T.coefficient q t.third c) := by ring
    _ = _ := by rw [hpow]; ring

end ArExplicit.CocycleData

end

end OAI
