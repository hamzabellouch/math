import OAI.Geometry.HeilbronnTriangle.AuxiliarySamplingLaw
import OAI.Geometry.HeilbronnTriangle.ParameterSequence

namespace OAI


noncomputable section

namespace Problem355.AuxiliarySampling

open scoped BigOperators
open Parameters Parameters.PrimeParameterData

namespace Law

variable {q H : ℕ} [Fact q.Prime] (L : Law q H)

theorem density_ratio_le :
    (q : ℝ) ^ 3 / L.size ≤ 2000 ^ 3 * (q : ℝ) * (H : ℝ) ^ 6 := by
  have hs : (0 : ℝ) < L.size := by exact_mod_cast L.size_pos
  have hsize : (q : ℝ) ^ 2 ≤ 2000 ^ 3 * (H : ℝ) ^ 6 * L.size := by
    exact_mod_cast L.size_lower
  apply (div_le_iff₀ hs).mpr
  calc
    (q : ℝ) ^ 3 = (q : ℝ) * (q : ℝ) ^ 2 := by ring
    _ ≤ (q : ℝ) * (2000 ^ 3 * (H : ℝ) ^ 6 * L.size) :=
      mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg q)
    _ = (2000 ^ 3 * (q : ℝ) * (H : ℝ) ^ 6) * L.size := by ring

theorem density_scale_le :
    (q : ℝ) ^ 3 ≤ (2000 ^ 3 * (q : ℝ) * (H : ℝ) ^ 6) * L.size := by
  exact (div_le_iff₀ (by exact_mod_cast L.size_pos : (0 : ℝ) < L.size)).mp
    L.density_ratio_le

end Law

theorem nonempty_parameterLaw {k r : ℕ} (P : PrimeParameterData k r) :
    Nonempty (@Law P.q (P.h ^ 2) ⟨P.auxiliary_prime⟩) := by
  let : Fact P.q.Prime := ⟨P.auxiliary_prime⟩
  apply nonempty_law
  · have hh : 1 ≤ P.h := by have := P.h_ge_three; omega
    exact one_le_pow₀ hh
  · exact P.auxiliary_large

def parameterLaw {k r : ℕ} (P : PrimeParameterData k r) :
    @Law P.q (P.h ^ 2) ⟨P.auxiliary_prime⟩ :=
  Classical.choice (nonempty_parameterLaw P)

section PrimeParameters

variable {k r : ℕ} (P : PrimeParameterData k r) [Fact P.q.Prime]

theorem density_ratio_le_parameter (L : Law P.q (P.h ^ 2)) :
    (P.q : ℝ) ^ 3 / L.size ≤ 2000 ^ 3 * (P.q : ℝ) * (P.h : ℝ) ^ 12 := by
  have h := L.density_ratio_le
  push_cast at h
  convert h using 1 ; ring

theorem sets_nonempty_parameter (L : Law P.q (P.h ^ 2)) (ω : L.Outcome) :
    (L.sets ω).Nonempty := by
  apply Finset.card_pos.mp
  rw [L.sets_card]
  exact L.size_pos

theorem weight_le_four_parameter (L : Law P.q (P.h ^ 2))
    (p : Fin 3 → (Fin 3 → ZMod P.q)) (i j : Fin 3) (hp : p i ≠ p j) :
    LiftingProbability.auxiliaryWeight P.q L.size L.weight L.sets p ≤
      (4 * 2000 ^ 3) * (P.q : ℝ) * (P.h : ℝ) ^ 12 := by
  calc
    LiftingProbability.auxiliaryWeight P.q L.size L.weight L.sets p ≤
        4 * ((P.q : ℝ) ^ 3 / L.size) := L.weight_le_four p i j hp
    _ ≤ 4 * (2000 ^ 3 * (P.q : ℝ) * (P.h : ℝ) ^ 12) :=
      mul_le_mul_of_nonneg_left (density_ratio_le_parameter P L) (by norm_num)
    _ = (4 * 2000 ^ 3) * (P.q : ℝ) * (P.h : ℝ) ^ 12 := by ring

theorem weight_le_two_parameter (L : Law P.q (P.h ^ 2))
    (p : Fin 3 → (Fin 3 → ZMod P.q)) :
    LiftingProbability.auxiliaryWeight P.q L.size L.weight L.sets p ≤
      (2 * 2000 ^ 6) * (P.q : ℝ) ^ 2 * (P.h : ℝ) ^ 24 := by
  have hratio := density_ratio_le_parameter P L
  have hsq : ((P.q : ℝ) ^ 3 / L.size) ^ 2 ≤
      (2000 ^ 3 * (P.q : ℝ) * (P.h : ℝ) ^ 12) ^ 2 := by
    gcongr
  calc
    LiftingProbability.auxiliaryWeight P.q L.size L.weight L.sets p ≤
        2 * ((P.q : ℝ) ^ 3 / L.size) ^ 2 := L.weight_le_two p
    _ ≤ 2 * (2000 ^ 3 * (P.q : ℝ) * (P.h : ℝ) ^ 12) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = (2 * 2000 ^ 6) * (P.q : ℝ) ^ 2 * (P.h : ℝ) ^ 24 := by ring

end PrimeParameters

theorem parameterLaw_density_ratio_le {k r : ℕ} (P : PrimeParameterData k r) :
    (P.q : ℝ) ^ 3 /
        (@Law.size P.q (P.h ^ 2) ⟨P.auxiliary_prime⟩ (parameterLaw P) : ℝ) ≤
      2000 ^ 3 * (P.q : ℝ) * (P.h : ℝ) ^ 12 := by
  let : Fact P.q.Prime := ⟨P.auxiliary_prime⟩
  exact density_ratio_le_parameter P (parameterLaw P)

end Problem355.AuxiliarySampling

end

end OAI
