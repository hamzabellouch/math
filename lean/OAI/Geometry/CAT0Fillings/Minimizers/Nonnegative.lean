import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Minimizers.Euler
import OAI.Geometry.CAT0Fillings.Calculus.AbsoluteValue

namespace OAI

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.AnalyticMinimizer
variable {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

lemma energy_pos_of_criticalNorm_one {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    {A B p : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (v : H)
    (hv : criticalNorm I p v = 1) : 0 < energy I G A B v := by
  have hI : I v ≠ 0 := by
    intro he
    have hh : criticalNorm I p v = 0 := by
      dsimp [criticalNorm]
      rw [he,lpNorm_congr_ae (Lp.coeFn_zero ℝ 2 μ) _,lpNorm_zero]
    linarith
  exact add_pos_of_nonneg_of_pos (mul_nonneg hA (sq_nonneg _))
    (mul_pos hB (sq_pos_of_pos (norm_pos_iff.mpr hI)))

lemma critical_euler_nonnegative {α H F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [SeparableSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (I : H →L[ℝ] Lp ℝ 2 μ) (G : H →L[ℝ] F)
    (A B : ℝ) {p : ℝ} (hp : 2 < p)
    (hm : ∀ u, MemLp (I u) (ENNReal.ofReal p) μ) (u : H)
    (hu : criticalNorm I p u = 1) (hupos : ∀ᵐ x ∂μ, 0 ≤ I u x)
    (hmin : ∀ v, energy I G A B u*(criticalNorm I p v)^2 ≤ energy I G A B v)
    (ψ : H) : A*inner ℝ (G u) (G ψ)+B*inner ℝ (I u) (I ψ) =
      energy I G A B u*(∫ x, (I u x)^(p-1)*(I ψ x) ∂μ) := by
  rw [critical_euler I G A B hp hm u hu hmin ψ]
  congr 1
  apply integral_congr_ae
  filter_upwards [hupos] with x hx
  rw [abs_of_nonneg hx]
  congr 1
  by_cases hx0 : I u x = 0
  · simp only [hx0,Real.zero_rpow (by linarith : p-1 ≠ 0),mul_zero]
  · have hxp : 0 < I u x := lt_of_le_of_ne hx (Ne.symm hx0)
    calc
      (I u x)^(p-2)*(I u x) = (I u x)^(p-2)*(I u x)^(1:ℝ) := by rw [Real.rpow_one]
      _ = (I u x)^((p-2)+1) := (Real.rpow_add hxp _ _).symm
      _ = (I u x)^(p-1) := by congr 1; ring

end CAT0Fillings.AnalyticMinimizer
end

section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
open AnalyticMinimizer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma nonnegative_euler_of_minimum {A B p S : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hp : 2 < p)
    (hm : ∀ u, MemLp (q.inclusion u) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT))
    (u : q.Sobolev) (hu : criticalNorm q.inclusion p u = 1)
    (hus : energy q.inclusion q.closedGradient A B u < S)
    (hmin : ∀ w, energy q.inclusion q.closedGradient A B u * (criticalNorm q.inclusion p w)^2 ≤
      energy q.inclusion q.closedGradient A B w) :
    ∃ v : q.Sobolev,
      (∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ (q.inclusion v) x) ∧
      criticalNorm q.inclusion p v = 1 ∧
      0 < energy q.inclusion q.closedGradient A B v ∧
      energy q.inclusion q.closedGradient A B v < S ∧
      (∀ w, energy q.inclusion q.closedGradient A B v * (criticalNorm q.inclusion p w)^2 ≤
        energy q.inclusion q.closedGradient A B w) ∧
      (∀ ψ, A*inner ℝ (q.closedGradient v) (q.closedGradient ψ)+B*inner ℝ (q.inclusion v) (q.inclusion ψ) =
        energy q.inclusion q.closedGradient A B v *
          (∫ x, (q.inclusion v x)^(p-1)*(q.inclusion ψ x) ∂MassMeasure.currentMassMeasure hT)) := by
  obtain ⟨v,hv,hvp,hQ,hminv⟩ := q.nonnegative_minimizer hA u hu hmin
  refine ⟨v,hv,hvp,energy_pos_of_criticalNorm_one q.inclusion q.closedGradient hA hB v hvp,
    by simpa only [hQ] using hus,hminv,?_⟩
  exact fun ψ => critical_euler_nonnegative q.inclusion q.closedGradient A B hp hm v hvp hv hminv ψ

end CAT0Fillings.ChartGeometry
end

end OAI
