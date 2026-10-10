import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.ThresholdField

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FieldSignalData
open Classical Set
open scoped ContDiff

structure FieldSignalData where
  ψ : (ℝ×ℝ) → ℝ
  χ : (ℝ×ℝ) → ℝ
  smooth : ContDiff ℝ 2 ψ
  compact : HasCompactSupport ψ
  q : ℝ
  K : ℝ
  L : ℝ
  Λ : ℝ
  L_pos : 0<L
  gap : K+2≤L
  ψ_zero : ∀x,K≤‖x‖ → ψ x=0
  χ_range : ∀x,χ x∈Icc (0:ℝ) 1
  χ_one : ∀x,‖x‖≤K+2 → χ x=1
  χ_zero : ∀x,L≤‖x‖ → χ x=0
  Λ_nonneg : 0≤Λ
  χ_lipschitz : ∀x y,|χ x-χ y|≤Λ*(|x.1-y.1|+|x.2-y.2|)

theorem exists_fieldSignalData (ψ : (ℝ×ℝ) → ℝ) (hs : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (q : ℝ) :
    ∃S : FieldSignalData,S.ψ=ψ ∧ S.q=q := by
  obtain ⟨K,hK,hzero⟩ := hc.exists_pos_le_norm
  let χ : ContDiffBump (0 : ℝ×ℝ) := ⟨K+2,K+3,by linarith,by linarith⟩
  obtain ⟨Λ,hΛ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport (χ.contDiff : ContDiff ℝ 1 (χ : (ℝ×ℝ) → ℝ)) (by simp)
  refine ⟨⟨ψ,χ,hs,hc,q,K,K+3,Λ,by linarith,by linarith,hzero,
    fun x => ⟨χ.nonneg,χ.le_one⟩,?_,?_,Λ.coe_nonneg,?_⟩,rfl,rfl⟩
  · intro x hx
    exact χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right,χ] using hx)
  · intro x hx
    exact χ.zero_of_le_dist (by simpa only [dist_zero_right,χ] using hx)
  · intro x y
    have hh := hΛ.dist_le_mul x y
    rw [Real.dist_eq,dist_eq_norm,Prod.norm_def] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ Λ.coe_nonneg
    simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))

namespace FieldSignalData
noncomputable def signal (S : FieldSignalData) (x : ℝ×ℝ) : ℝ := S.q+S.ψ x

noncomputable def realLaw (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.Measure (FlagSite a m D v → ℝ) :=
  sourceSmoothFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n

instance realLaw_probability (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.IsProbabilityMeasure (S.realLaw (a:=a) (m:=m) (v:=v) hD η κ n) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure (sourceSmoothFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n))

noncomputable def bitLaw (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.Measure (FlagSite a m D v → Bool) :=
  sourceBitFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n

instance bitLaw_probability (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.IsProbabilityMeasure (S.bitLaw (a:=a) (m:=m) (v:=v) hD η κ n) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure (sourceBitFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n))

end FieldSignalData
end FieldSignalData

end SimpleAmenable
end
end

end OAI
