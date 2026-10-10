import OAI.MeasureTheory.Falconer.Estimates.InterpolatedTubeKernel
import OAI.MeasureTheory.Falconer.Incidence.PencilSecondMoment

namespace OAI

/-! A large pencil improves the elementary incidence estimate. The exponent
is obtained by interpolating the actual packing and regularity kernels. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_interpolated_second_moment (N : ℕ) {s t u θ K M : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K) (hM0 : 0 ≤ M)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤
      ((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let A := (K*(80*δ)^s*M)^θ*(25921:ℝ)^(1-θ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤ A*(1+K*planarPotentialConstant u t)*(P.card:ℝ) := by
    have hpot := finite_dyadic_truncated_potential_real P x N hK hu hut hPball
    calc
      _ ≤ ∑ y ∈ P, A*(1+(1/max (dist x y) δ)^u) := by
        apply Finset.sum_le_sum
        intro y hy
        exact (intersect_tube_interpolated_bound hδ hδ1 hs hK hθ hθ1 he (T x) (T y)
          x y (hPchart x hx).1 (hT x hx).1 (hT x hx).2.1 (hT x hx).2.2.1
          (hT x hx).2.2.2.1 (hT x hx).2.2.2.2 (hT y hy).2.2.2.2).trans
          (mul_le_mul_of_nonneg_left (truncatedPlanarDistance_inverse_power_le hδ hδ1 x y) hA)
      _ = A*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^u) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ A*((P.card:ℝ)+K*planarPotentialConstant u t*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hA
      _ = _ := by ring
  calc
    _ ≤ ∑ _x ∈ P, A*(1+K*planarPotentialConstant u t)*(P.card:ℝ) := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [A]; ring

theorem planar_interpolated_incidence (N : ℕ) {s t u θ K m M : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      (((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)) := by
  let B := ((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
    (1+K*planarPotentialConstant u t)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hM0 : 0 ≤ M := by
    obtain ⟨p,hp⟩ := hP
    exact (Nat.cast_nonneg _).trans (hT p hp).2.1
  have hE := pencil_interpolated_second_moment N hs hu hut hK hM0 hθ hθ1 he P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.2.2.2.1,
      (hT x hx).2.1,(hT x hx).2.2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(B*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  convert hh using 1 <;> ring

end Falconer

end OAI
