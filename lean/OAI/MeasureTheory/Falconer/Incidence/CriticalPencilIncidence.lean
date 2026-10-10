import OAI.MeasureTheory.Falconer.Incidence.PencilSecondMoment
import OAI.MeasureTheory.Falconer.Recursion.PlanarCriticalPotential

namespace OAI

/-! The normal-scale incidence estimate, with matching point and pencil
exponents. The loss at the critical potential is linear in the dyadic depth. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_critical_second_moment (N : ℕ) {s K M : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤
      (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarCriticalConstant N s)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let C := K*(80*δ)^s*M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤
        C*(1+K*planarCriticalConstant N s)*(P.card:ℝ) := by
    have hM : 0 ≤ M := (Nat.cast_nonneg _).trans (hT x hx).2.2.1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hpot := finite_dyadic_critical_potential_real P x N hK hs hPball
    calc
      _ ≤ ∑ y ∈ P, C*(1+(1/max (dist x y) δ)^s) := by
        apply Finset.sum_le_sum
        intro y hy
        apply (intersect_tube_power_bound hδ hδ1 hs hK (T x) (T y) x y
          (hPchart x hx).1 (hT x hx).1 (hT x hx).2.2.2
          (hT y hy).2.2.2 (hT x hx).2.1).trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT x hx).2.2.1
          (by positivity)) (by positivity)
      _ = C*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^s) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ C*((P.card:ℝ)+K*planarCriticalConstant N s*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hC
      _ = _ := by ring
  calc
    _ ≤ ∑ _x ∈ P, C*(1+K*planarCriticalConstant N s)*(P.card:ℝ) :=
      Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [C]; ring

theorem planar_critical_variable_incidence (N : ℕ) {s K m M : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      ((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarCriticalConstant N s)) := by
  let C := (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarCriticalConstant N s)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ ∑ x ∈ P, ((T x).card:ℝ) := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hE := pencil_critical_second_moment N hs hK P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.1,(hT x hx).2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(C*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  convert hh using 1 <;> ring

theorem planar_critical_normalized_incidence (N : ℕ) {s K m R : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m ≤ ((P.biUnion T).card:ℝ)*
      (R*K*(80*(1/(2:ℝ)^N))^s*(1+K*planarCriticalConstant N s)) := by
  have hh := planar_critical_variable_incidence N hs hK hm.le P T hP hPchart hPball hT
  apply (mul_le_mul_iff_left₀ hm).1
  convert hh using 1 <;> ring

end Falconer

end OAI
