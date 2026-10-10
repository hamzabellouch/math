import OAI.MeasureTheory.Falconer.Incidence.PencilSecondMoment

namespace OAI

/-! The baseline incidence estimate for unequal pencil sizes, as needed
before and after weighted packet freezing. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planar_variable_baseline_incidence (N : ℕ) {s t K m M : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      ((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)) := by
  let C := (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hH := pencil_second_moment_bound N hs hst hK P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.1,(hT x hx).2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(C*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun x _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ = ((P.biUnion T).card:ℝ)*(∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) := by
        rw [sum_tubeDegree_sq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  convert hh using 1 <;> ring

theorem packet_size_from_variable_incidence (N : ℕ) {s t K m M n B : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hK : 1 ≤ K) (hm : 0 ≤ m) (hM : 0 ≤ M) (hn : 0 ≤ n)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l)
    (b : Space 2 → ℕ) (hb : ∀ l ∈ P.biUnion T, n ≤ (b l:ℝ))
    (htotal : (∑ l ∈ P.biUnion T, (b l:ℝ)) ≤ B) :
    n*m^2 ≤ B*((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)) := by
  let C := (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarPotentialConstant s t)
  have hC : 0 ≤ C := by
    have hp := planarPotentialConstant_pos hst
    have hk : 0 ≤ K := zero_le_one.trans hK
    dsimp [C]
    positivity
  have hc : n*((P.biUnion T).card:ℝ) ≤ B := by
    calc
      _ = ∑ _l ∈ P.biUnion T, n := by simp; ring
      _ ≤ ∑ l ∈ P.biUnion T, (b l:ℝ) := Finset.sum_le_sum hb
      _ ≤ _ := htotal
  calc
    _ ≤ n*(((P.biUnion T).card:ℝ)*C) := mul_le_mul_of_nonneg_left
      (planar_variable_baseline_incidence N hs hst hK hm P T hP hPchart hPball hT) hn
    _ = (n*((P.biUnion T).card:ℝ))*C := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hC

end Falconer

end OAI
