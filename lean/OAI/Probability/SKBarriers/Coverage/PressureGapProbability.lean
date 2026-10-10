import Mathlib
import OAI.Probability.SKBarriers.Coverage.EnergyTail
import OAI.Probability.SKBarriers.Interpolation.RestrictedConcentration

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem integral_le_off_exception {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) {A : Set Ω} (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 ≤ r) (h1 : ∀ x, f x ≤ 1)
    (hout : ∀ x ∉ A, f x ≤ r) : ∫ x, f x ∂μ ≤ r+μ.real A := by
  calc
    _ ≤ ∫ x, r+A.indicator (fun _ => (1:ℝ)) x ∂μ := by
      apply integral_mono hf ((integrable_const r).add ((integrable_const (1:ℝ)).indicator hA))
      intro x
      by_cases hx : x ∈ A
      · simp only [Pi.add_apply,Set.indicator_of_mem hx]
        linarith [h1 x]
      · simp only [Pi.add_apply,Set.indicator_of_notMem hx,add_zero]
        exact hout x hx
    _ = _ := by
      rw [integral_add (integrable_const r) ((integrable_const (1:ℝ)).indicator hA),
        integral_const,integral_indicator_const _ hA]
      simp only [probReal_univ,smul_eq_mul,mul_one,one_mul]

theorem restrictedLogPartition_upper_tail_linear {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {β a : ℝ} (hβ : β ≠ 0) (ha : 0 ≤ a)
    {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty) :
    (disorderLaw n).real {J | a*(n:ℝ) ≤ restrictedLogPartition β S J-
      ∫ K, restrictedLogPartition β S K ∂disorderLaw n} ≤
      Real.exp (-(4*a^2/(Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ)) := by
  have H := restrictedLogPartition_upper_tail hn hd β (a*(n:ℝ)) hS (by positivity)
  convert H using 1
  congr 1
  change -(4*a^2/(Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ) =
    -(a*(n:ℝ))^2/(2*(Real.pi^2*(β*(d:ℝ))^2*(n:ℝ)/8))
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

theorem replicaGibbsMass_integral_le_of_mean_gap {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    {β η : ℝ} (hβ : β ≠ 0) (hη : 0 ≤ η)
    {S : Finset (ReplicaConfig n d)} (hS : S.Nonempty)
    (hgap : (∫ J, restrictedLogPartition β S J ∂disorderLaw n)-
      (d:ℝ)*(∫ J, logPartition β J ∂disorderLaw n) ≤ -(n:ℝ)*η/2) :
    (∫ J, replicaGibbsMass β J S ∂disorderLaw n) ≤
      Real.exp (-(n:ℝ)*η/4)+2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
  let X := restrictedLogPartition β S
  let EX := ∫ J, X J ∂disorderLaw n
  let EY := ∫ J, logPartition β J ∂disorderLaw n
  let A : Set (Disorder n) := {J | (η/8)*(n:ℝ) ≤ X J-EX}
  let B : Set (Disorder n) := {J | (η/(8*(d:ℝ)))*(n:ℝ) ≤ EY-logPartition β J}
  have hA : MeasurableSet A := isClosed_le continuous_const
    ((continuous_restrictedLogPartition β hS).sub continuous_const) |>.measurableSet
  have hB : MeasurableSet B := isClosed_le continuous_const
    (continuous_const.sub (continuous_logPartition β)) |>.measurableSet
  have hd0 : 0 < (d:ℝ) := by exact_mod_cast hd
  have hdn : (d:ℝ) ≠ 0 := ne_of_gt hd0
  have HA := restrictedLogPartition_upper_tail_linear hn hd hβ (show 0 ≤ η/8 by positivity) hS
  have HB := logPartition_lower_tail_linear hn hβ (show 0 ≤ η/(8*(d:ℝ)) by positivity)
  have heA : -(4*(η/8)^2/(Real.pi^2*β^2*(d:ℝ)^2))*(n:ℝ) =
      -(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2) := by ring
  have heB : -(4*(η/(8*(d:ℝ)))^2/(Real.pi^2*β^2))*(n:ℝ) =
      -(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2) := by field_simp; ring
  rw [heA] at HA
  rw [heB] at HB
  have H := integral_le_off_exception (replicaGibbsMass_integrable β S) (hA.union hB)
    (Real.exp_pos (-(n:ℝ)*η/4)).le (fun J => replicaGibbsMass_le_one β J S) ?_
  · have hAB : (disorderLaw n).real (A∪B) ≤
        2*Real.exp (-(n:ℝ)*η^2/(16*Real.pi^2*β^2*(d:ℝ)^2)) := by
      apply (measureReal_union_le (μ := disorderLaw n) A B).trans
      change (disorderLaw n).real A ≤ _ at HA
      change (disorderLaw n).real B ≤ _ at HB
      linarith
    linarith
  · intro J hJ
    rw [Set.mem_union,not_or] at hJ
    have ha : X J-EX < (η/8)*(n:ℝ) := lt_of_not_ge hJ.1
    have hb : EY-logPartition β J < (η/(8*(d:ℝ)))*(n:ℝ) := lt_of_not_ge hJ.2
    have hb' := mul_lt_mul_of_pos_left hb hd0
    have he : (d:ℝ)*((η/(8*(d:ℝ)))*(n:ℝ)) = η*(n:ℝ)/8 := by field_simp
    rw [he] at hb'
    rw [replicaGibbsMass_eq_exp β J hS]
    apply Real.exp_le_exp.mpr
    change EX-(d:ℝ)*EY ≤ -(n:ℝ)*η/2 at hgap
    change restrictedLogPartition β S J-EX < _ at ha
    linarith

end SK.Analytic

end
end

end

end OAI
