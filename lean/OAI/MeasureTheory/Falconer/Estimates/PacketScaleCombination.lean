import OAI.MeasureTheory.Falconer.Incidence.LocalCellIncidence

namespace OAI

/-! Counting the original fine packets produces the pencil-normalized
product estimate used in the regular-set argument. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_packet_scale_combination {m B H J n : ℝ}
    (hB : 0 ≤ B) (hH : 0 ≤ H) (hn : 0 ≤ n)
    (A D F U : Finset (Space 2)) (G : Space 2 → Finset (Space 2))
    (hDA : D ⊆ A) (hD : (D.card:ℝ) ≤ H)
    (hcover : F ⊆ D.biUnion G)
    (hband : ∀ a ∈ A, n ≤ ((G a).card:ℝ) ∧ ((G a).card:ℝ) ≤ 2*n)
    (htotal : (∑ a ∈ A, ((G a).card:ℝ)) ≤ J*(U.card:ℝ))
    (hlocal : m^2 ≤ (F.card:ℝ)*B) :
    m^2*(A.card:ℝ) ≤ 2*J*(U.card:ℝ)*H*B := by
  have hF : (F.card:ℝ) ≤ 2*n*H := by
    calc
      _ ≤ ∑ a ∈ D, ((G a).card:ℝ) := by
        exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ D, 2*n := Finset.sum_le_sum fun a ha => (hband a (hDA ha)).2
      _ = 2*n*(D.card:ℝ) := by simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hD (by positivity)
  have hA : n*(A.card:ℝ) ≤ J*(U.card:ℝ) := by
    calc
      _ = ∑ _a ∈ A, n := by simp; ring
      _ ≤ ∑ a ∈ A, ((G a).card:ℝ) := Finset.sum_le_sum fun a ha => (hband a ha).1
      _ ≤ _ := htotal
  calc
    _ ≤ ((2*n*H)*B)*(A.card:ℝ) :=
      mul_le_mul_of_nonneg_right (hlocal.trans (mul_le_mul_of_nonneg_right hF hB))
        (Nat.cast_nonneg _)
    _ = 2*(n*(A.card:ℝ))*H*B := by ring
    _ ≤ 2*(J*(U.card:ℝ))*H*B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hA (by norm_num)) hH) hB
    _ = _ := by ring

theorem local_cell_packet_scale_combination (N : ℕ) {s t K m M y a H J n : ℝ}
    (hN : 3 ≤ N) (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hH : 0 ≤ H) (hn : 0 ≤ n) (hy : |y| ≤ 1)
    (P A D U : Finset (Space 2)) (T G : Space 2 → Finset (Space 2))
    (hP : P.Nonempty)
    (hcell : ∀ p ∈ P, |p 0-y| ≤ (1/(2:ℝ)^N)/4 ∧ |p 1-a| ≤ (1/(2:ℝ)^N)/4)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K
      (P.image (localPacketPoint (1/(2:ℝ)^N) y a)))
    (hT : ∀ p ∈ P, m ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ M ∧
      NormalizedFiniteBallBound ((1/(2:ℝ)^N)^2) s K (T p) ∧
      ∀ l ∈ T p, |l 0| ≤ 1/2 ∧ TubeIncident ((1/(2:ℝ)^N)^2) p l)
    (hDA : D ⊆ A) (hD : (D.card:ℝ) ≤ H)
    (hcover : ∀ p ∈ P, ∀ l ∈ T p, ∃ b ∈ D, l ∈ G b)
    (hband : ∀ b ∈ A, n ≤ ((G b).card:ℝ) ∧ ((G b).card:ℝ) ≤ 2*n)
    (htotal : (∑ b ∈ A, ((G b).card:ℝ)) ≤ J*(U.card:ℝ)) :
    m^2*(A.card:ℝ) ≤ 2*J*(U.card:ℝ)*H*
      (((K*3^s)*(80*(1/(2:ℝ)^N))^s*M)*(1+(K*3^s)*planarPotentialConstant s t)) := by
  have hM : 0 ≤ M := by
    obtain ⟨p,hp⟩ := hP
    exact (Nat.cast_nonneg _).trans (hT p hp).2.1
  have hpot := planarPotentialConstant_pos hst
  have hk0 := zero_le_one.trans hK
  apply finite_packet_scale_combination (by positivity) hH hn A D (P.biUnion T) U G
    hDA hD ?_ hband htotal
    (local_cell_variable_incidence N hN hs hst hK hm hy P T hP hcell hPball hT)
  intro l hl
  obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
  obtain ⟨b,hb,hlb⟩ := hcover p hp l hl
  exact Finset.mem_biUnion.mpr ⟨b,hb,hlb⟩

end Falconer

end OAI
