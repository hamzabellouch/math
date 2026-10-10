import Mathlib
import OAI.Computability.MinUncut.Estimates.Rest

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
namespace MinUncut.RowNoise
open BinaryFourier
open scoped BigOperators
local instance oddAtomDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

def oddAtom (r : R) (one : W) (f : (R → W) → ℝ) (D : Rest (W := W) r) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun α : Module.Dual F₂ W =>
    if α one=1 then |rowCoefficient r f α D| else 0)

omit [Fintype R] [DecidableEq W] in
lemma oddAtom_nonneg (r : R) (one : W) (f : (R → W) → ℝ) (D : Rest (W := W) r) :
    0 ≤ oddAtom r one f D := by
  have h := Finset.le_sup' (fun α : Module.Dual F₂ W =>
    if α one=1 then |rowCoefficient r f α D| else 0) (Finset.mem_univ 0)
  simp only [LinearMap.zero_apply, zero_ne_one, ite_false] at h
  exact h

omit [Fintype R] [DecidableEq W] in
lemma rowCoefficient_le_oddAtom (r : R) (one : W) (f : (R → W) → ℝ)
    (α : Module.Dual F₂ W) (hα : α one=1) (D : Rest (W := W) r) :
    |rowCoefficient r f α D| ≤ oddAtom r one f D := by
  have h := Finset.le_sup' (fun β : Module.Dual F₂ W =>
    if β one=1 then |rowCoefficient r f β D| else 0) (Finset.mem_univ α)
  rw [ite_eq_left hα] at h
  exact h

omit [Fintype R] [DecidableEq W] in
lemma oddAtom_le (r : R) (one : W) (f : (R → W) → ℝ) (D : Rest (W := W) r)
    {a : ℝ} (ha : 0≤a) (h : ∀ α : Module.Dual F₂ W, α one=1 → |rowCoefficient r f α D|≤a) :
    oddAtom r one f D ≤ a := by
  apply Finset.sup'_le
  intro α _
  split_ifs with hα
  · exact h α hα
  · exact ha

lemma oddAtom_maskProject (r : R) (one : W) (S : Finset R) (f : (R → W) → ℝ)
    (D : Rest (W := W) r) :
    oddAtom r one (maskProject S f) D ≤
      𝔼 E, |maskKernel (restMask r S) D E| * oddAtom r one f E := by
  apply oddAtom_le
  · exact Finset.expect_nonneg (fun E _ => mul_nonneg (abs_nonneg _) (oddAtom_nonneg _ _ _ _))
  intro α hα
  have hα0 : α≠0 := by intro he; simp [he] at hα
  exact rowCoefficient_maskProject_envelope r S f (oddAtom r one f)
    (oddAtom_nonneg _ _ _) α hα0 (rowCoefficient_le_oddAtom _ _ _ α hα) D

lemma oddAtom_maskProject_mean (r : R) (one : W) (S : Finset R) (f : (R → W) → ℝ) :
    (𝔼 D, oddAtom r one (maskProject S f) D) ≤
      (2:ℝ)^Fintype.card R * (𝔼 D, oddAtom r one f D) := by
  exact (Finset.expect_le_expect (fun D _ => oddAtom_maskProject r one S f D)).trans
    (rowEnvelope_mean r S (oddAtom r one f) (oddAtom_nonneg _ _ _))

omit [Fintype R] [DecidableEq W] in
lemma oddAtom_sum {T : Type*} (s : Finset T) (r : R) (one : W)
    (f : T → (R → W) → ℝ) (D : Rest (W := W) r) :
    oddAtom r one (fun B => ∑ t∈s, f t B) D ≤ ∑ t∈s, oddAtom r one (f t) D := by
  apply oddAtom_le
  · exact Finset.sum_nonneg (fun _ _ => oddAtom_nonneg _ _ _ _)
  intro α hα
  simp only [rowCoefficient, Finset.sum_mul, Finset.expect_sum_comm]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun t _ =>
    rowCoefficient_le_oddAtom r one (f t) α hα D))
end MinUncut.RowNoise

end

end OAI
