import OAI.MeasureTheory.Falconer.Recursion.PlanarCriticalPotential
import OAI.MeasureTheory.Falconer.Estimates.CommonTubePower
import OAI.MeasureTheory.Falconer.Estimates.TubeSecondMoment

namespace OAI

/-! Average critical energy of the point fibers of a tube family.
This is the finite form of Orponen--Shmerkin, Appendix A, equation (A.18). -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def pencilFiberEnergy (N : ℕ) (τ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (l : Space 2) : ℝ :=
  ∑ x ∈ P, ∑ y ∈ P, if l ∈ T x ∧ l ∈ T y then
    (1/max (dist x y) (1/(2:ℝ)^N))^τ else 0

theorem sum_pencilFiberEnergy (N : ℕ) (τ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, pencilFiberEnergy N τ P T l) =
      ∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)*
        (1/max (dist x y) (1/(2:ℝ)^N))^τ := by
  unfold pencilFiberEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have he (l : Space 2) :
      (if l ∈ T x ∧ l ∈ T y then (1/max (dist x y) (1/(2:ℝ)^N))^τ else 0) =
      (if l ∈ T x ∩ T y then (1:ℝ) else 0)*(1/max (dist x y) (1/(2:ℝ)^N))^τ := by
    by_cases hlx : l ∈ T x <;> by_cases hly : l ∈ T y <;> simp [hlx,hly]
  simp_rw [he]
  rw [← Finset.sum_mul,sum_tube_membership (P.biUnion T) (T x ∩ T y)
    (fun l hl => Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hl).1⟩)]

theorem nonnegative_power_le_one_add {a u v : ℝ} (ha : 0 < a)
    (hu : 0 ≤ u) (huv : u ≤ v) : a^u ≤ 1+a^v := by
  by_cases hsmall : a ≤ 1
  · exact (Real.rpow_le_one ha.le hsmall hu).trans (le_add_of_nonneg_right (by positivity))
  · exact (Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hsmall)) huv).trans
      (le_add_of_nonneg_left (by norm_num))

theorem common_tube_weighted_bound {δ s t K M : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hst : s ≤ t)
    (hK : 1 ≤ K) (hM : 0 ≤ M) (P Q : Finset (Space 2)) (x y : Space 2)
    (hx : |x 0| ≤ 1) (hchart : InBoundedLineChart P)
    (hincx : ∀ l ∈ P, TubeIncident δ x l) (hincy : ∀ l ∈ Q, TubeIncident δ y l)
    (hreg : NormalizedFiniteBallBound δ s K P) (hcard : (P.card:ℝ) ≤ M) :
    ((P ∩ Q).card:ℝ)*(1/max (dist x y) δ)^(t-s) ≤
      (K*(80*δ)^s*M)*(1+2*(1/max (dist x y) δ)^t) := by
  let a := 1/max (dist x y) δ
  have ha : 0 < a := one_div_pos.mpr (hδ.trans_le (le_max_right _ _))
  have hk := intersect_tube_power_bound hδ hδ1 hs hK P Q x y hx hchart hincx hincy hreg
  have hkm : (K*(80*δ)^s*(P.card:ℝ)) ≤ K*(80*δ)^s*M :=
    mul_le_mul_of_nonneg_left hcard (by positivity)
  have hpower : a^(t-s)*(1+a^s) ≤ 1+2*a^t := by
    have hlo := nonnegative_power_le_one_add ha (sub_nonneg.mpr hst)
      (show t-s ≤ t by linarith only [hs])
    have he : a^(t-s)*a^s = a^t := by
      rw [← Real.rpow_add ha]
      congr 1
      ring
    rw [mul_add,mul_one,he]
    linarith only [hlo]
  calc
    _ ≤ ((K*(80*δ)^s*(P.card:ℝ))*(1+a^s))*a^(t-s) :=
      mul_le_mul_of_nonneg_right hk (by positivity)
    _ ≤ ((K*(80*δ)^s*M)*(1+a^s))*a^(t-s) := by gcongr
    _ = (K*(80*δ)^s*M)*(a^(t-s)*(1+a^s)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpower (by positivity)

theorem pencil_fiber_energy_average (N : ℕ) {s t K M : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (hK : 1 ≤ K) (hM : 0 ≤ M)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ l ∈ P.biUnion T, pencilFiberEnergy N (t-s) P T l) ≤
      (K*(80*(1/(2:ℝ)^N))^s*M)*(1+2*K*planarCriticalConstant N t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let C := K*(80*δ)^s*M
  let k := fun x y : Space 2 => (1/max (dist x y) δ)^t
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have ht : 0 ≤ t := hs.trans hst
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpotential : (∑ x ∈ P, ∑ y ∈ P, k x y) ≤
      K*planarCriticalConstant N t*(P.card:ℝ)^2 := by
    calc
      _ ≤ ∑ _x ∈ P, K*planarCriticalConstant N t*(P.card:ℝ) :=
        Finset.sum_le_sum fun x _ => finite_dyadic_critical_potential_real P x N hK ht hPball
      _ = _ := by simp; ring
  rw [sum_pencilFiberEnergy]
  calc
    _ ≤ ∑ x ∈ P, ∑ y ∈ P, C*(1+2*k x y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      exact common_tube_weighted_bound hδ hδ1 hs hst hK hM (T x) (T y) x y
        (hPchart x hx).1 (hT x hx).1 (hT x hx).2.2.2 (hT y hy).2.2.2
        (hT x hx).2.1 (hT x hx).2.2.1
    _ = C*((P.card:ℝ)^2+2*(∑ x ∈ P, ∑ y ∈ P, k x y)) := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
        mul_one,← Finset.mul_sum]
      ring
    _ ≤ C*((P.card:ℝ)^2+2*(K*planarCriticalConstant N t*(P.card:ℝ)^2)) := by gcongr
    _ = _ := by dsimp [C]; ring

end Falconer

end OAI
