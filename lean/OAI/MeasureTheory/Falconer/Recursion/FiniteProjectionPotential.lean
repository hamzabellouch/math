import OAI.MeasureTheory.Falconer.Geometry.FiniteProjectionSublevels
import OAI.MeasureTheory.Falconer.Recursion.FiniteCriticalPotential
import OAI.MeasureTheory.Falconer.Recursion.FiniteCountingPotential

namespace OAI

/-! The finite projected-energy average used for the good projections in
Orponen--Shmerkin, Appendix A.4. The critical directional loss is linear in
the dyadic depth; the planar point potential is strictly subcritical. -/
namespace Falconer
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_projection_potential (N : ℕ) {s K : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (I : Finset ℝ) (hI : ∀ c ∈ I, |c| ≤ 1)
    (hball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass I u r ≤ K*r^s*(I.card:ℝ))
    (p q : Space 2) (hdiam : dist p q ≤ 4) :
    (∑ c ∈ I, (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s) ≤
      (I.card:ℝ)+(2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*
        (K*(8/max (dist p q) (1/(2:ℝ)^N))^s*(I.card:ℝ)) := by
  let δ := 1/(2:ℝ)^N
  let D := max (dist p q) δ
  let C := K*(8/D)^s*(I.card:ℝ)
  let a := fun c => |lineParameterProjection c p-lineParameterProjection c q|
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hD : 0 < D := hδ.trans_le (le_max_right _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcounts (j : ℕ) (hj : j ≤ N) :
      ((I.filter fun c => a c < 1/(2:ℝ)^j).card:ℝ) ≤ C*(1/(2:ℝ)^j)^s := by
    have hr : δ ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) hj
    have hh := finite_projection_sublevel hδ hr hs hK I hI hball p q hdiam
    have hsub : I.filter (fun c => a c < 1/(2:ℝ)^j) ⊆
        I.filter (fun c => a c ≤ 1/(2:ℝ)^j) :=
      by
        intro c hc
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2.le⟩
    apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    apply hh.trans_eq
    change K*(8*(1/(2:ℝ)^j)/D)^s*(I.card:ℝ) = _
    rw [show 8*(1/(2:ℝ)^j)/D = (8/D)*(1/(2:ℝ)^j) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    dsimp [C]
    ring
  have ha : Measurable a := by dsimp [a,lineParameterProjection]; fun_prop
  have hh := finite_critical_statistic I a ha (fun _ => abs_nonneg _) N hs hC hcounts
  convert hh using 1
  dsimp [C,D,δ]
  ring

noncomputable def planarProjectionEnergy (N : ℕ) (s c : ℝ) (P : Finset (Space 2)) : ℝ :=
  ∑ p ∈ P, ∑ q ∈ P,
    (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s

theorem finite_projection_energy_average (N : ℕ) {s t KI KP : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 1 ≤ KI) (hKP : 1 ≤ KP)
    (I : Finset ℝ) (P : Finset (Space 2))
    (hI : ∀ c ∈ I, |c| ≤ 1) (hP : InBoundedLineChart P)
    (hIball : ∀ u r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
      scalarBallMass I u r ≤ KI*r^s*(I.card:ℝ))
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t KP P) :
    (∑ c ∈ I, planarProjectionEnergy N s c P) ≤
      (I.card:ℝ)*(P.card:ℝ)^2*
        (1+((2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*KI*(8:ℝ)^s)*KP*planarPotentialConstant s t) := by
  let A := (2:ℝ)^s*(1+(N:ℝ)*(2:ℝ)^s)*KI*(8:ℝ)^s
  let k := fun p q : Space 2 => (1/max (dist p q) (1/(2:ℝ)^N))^s
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpair (p : Space 2) (hp : p ∈ P) (q : Space 2) (hq : q ∈ P) :
      (∑ c ∈ I, (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s) ≤
        (I.card:ℝ)+A*(I.card:ℝ)*k p q := by
    have hd : dist p q ≤ 4 := by
      have h0 := abs_sub (p 0) (q 0)
      have h1 := abs_sub (p 1) (q 1)
      have hg := planar_dist_le_coordinate_sum p q
      linarith only [h0,h1,hg,(hP p hp).1,(hP p hp).2,(hP q hq).1,(hP q hq).2]
    have hh := finite_projection_potential N hs hKI I hI hIball p q hd
    apply hh.trans_eq
    rw [show 8/max (dist p q) (1/(2:ℝ)^N) = 8*(1/max (dist p q) (1/(2:ℝ)^N)) by ring,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) (by positivity)]
    dsimp [A,k]
    ring
  have hpoint (p : Space 2) : (∑ q ∈ P, k p q) ≤ KP*planarPotentialConstant s t*(P.card:ℝ) :=
    finite_dyadic_truncated_potential_real P p N hKP hs hst hPball
  have hpotential : (∑ p ∈ P, ∑ q ∈ P, k p q) ≤ KP*planarPotentialConstant s t*(P.card:ℝ)^2 := by
    calc
      _ ≤ ∑ _p ∈ P, KP*planarPotentialConstant s t*(P.card:ℝ) := Finset.sum_le_sum fun p _ => hpoint p
      _ = _ := by simp; ring
  calc
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ c ∈ I,
        (1/max |lineParameterProjection c p-lineParameterProjection c q| (1/(2:ℝ)^N))^s := by
      unfold planarProjectionEnergy
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((I.card:ℝ)+A*(I.card:ℝ)*k p q) :=
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hpair p hp q hq
    _ = (I.card:ℝ)*(P.card:ℝ)^2+A*(I.card:ℝ)*(∑ p ∈ P, ∑ q ∈ P, k p q) := by
      simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
      ring
    _ ≤ (I.card:ℝ)*(P.card:ℝ)^2+A*(I.card:ℝ)*(KP*planarPotentialConstant s t*(P.card:ℝ)^2) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hpotential (mul_nonneg hA (Nat.cast_nonneg I.card))) _
    _ = _ := by dsimp [A]; ring

end Falconer

end OAI
