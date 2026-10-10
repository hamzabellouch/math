import Mathlib
import OAI.Combinatorics.RamseyFive.Bounds.DensityUpper

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence
open scoped LinearAlgebra.Projectivization Classical BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma incidences_eq_degrees (A : Finset (ℙ K V)) (Z : Finset (ℙ K (Dual K V))) :
    (incidences A Z:ℝ) = ∑ a∈A,((Z.filter fun y => Incident a y).card:ℝ) := by
  rw [incidences_eq_sum,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [incidenceEntry,Finset.sum_boole]

lemma density_upper {d : ℕ} (hd : 1≤d) :
    (Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d ≤ 1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hQ : (0:ℝ)<Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  apply (div_le_div_iff₀ hQ hq).mpr
  have hr : (Q (Nat.card K) d:ℝ)=(Nat.card K:ℝ)*Q (Nat.card K) (d-1)+1 := by
    exact_mod_cast Q_recurrence (q := Nat.card K) hd
  nlinarith

theorem poor_joint_count (hdim : finrank K V=5)
    (A : Finset (ℙ K V)) (Z B : Finset (ℙ K (Dual K V)))
    (hpoor : ∀ a∈A,((Z.filter fun y => Incident a y).card:ℝ)≤(Z.card:ℝ)/(8*Nat.card K))
    (hB : B.card≤5*Z.card) :
    (incidences A B:ℝ)≤89*(Nat.card K:ℝ)^4 := by
  let q : ℝ:=Nat.card K
  have hq : 0<q := by
    dsimp [q]
    exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α := K))
  have hs : (incidences A Z:ℝ)≤(A.card:ℝ)*Z.card/(4*q) := by
    rw [incidences_eq_degrees]
    calc
      _ ≤ ∑ a∈A,(Z.card:ℝ)/(8*q) := Finset.sum_le_sum fun a ha => hpoor a ha
      _ = (A.card:ℝ)*Z.card/(8*q) := by simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hp := sparse_rectangle_size (d := 4) hdim (by decide) A Z hs
  have hB' : (B.card:ℝ)≤5*Z.card := by exact_mod_cast hB
  have hprod : (A.card:ℝ)*B.card≤80*q^5 := by
    have hh := mul_le_mul_of_nonneg_left hB' (show (0:ℝ)≤A.card by positivity)
    change (A.card:ℝ)*Z.card≤16*q^5 at hp
    nlinarith
  have hmix := incidence_mixing (d := 4) hdim (by decide) A B
  have hd := density_upper (K := K) (d := 4) (by decide)
  have hmain : ((Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4)*A.card*B.card≤80*q^4 := by
    calc
      _ ≤ (1/q)*((A.card:ℝ)*B.card) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (show (0:ℝ)≤(A.card:ℝ)*B.card by positivity)
      _ ≤ (1/q)*(80*q^5) := mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by field_simp
  have hsqrt : Real.sqrt (q^3*A.card*B.card)≤9*q^4 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have hp' := mul_le_mul_of_nonneg_left hprod (show 0≤q^3 by positivity)
    nlinarith [sq_nonneg (q^4)]
  have hupper := (abs_le.mp hmix).2
  change (incidences A B:ℝ)≤89*q^4
  change (incidences A B:ℝ)-((Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4)*A.card*B.card≤
    Real.sqrt (q^3*A.card*B.card) at hupper
  linarith

end SharpRamseyFive.Marking

end OAI
