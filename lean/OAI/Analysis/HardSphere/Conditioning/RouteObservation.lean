import Mathlib

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace HardSphere.Comparison
variable {E P W : Type*} [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace W]

def firstPaths (d : ℕ) (v : Fin (d+2) → E×(P×P)) : Fin (d+1) → P := fun i ↦ (v i.castSucc).2.1
def secondPaths (d : ℕ) (v : Fin (d+2) → E×(P×P)) : Fin (d+1) → P := fun i ↦ (v i.succ).2.2

def observeFirst (d : ℕ) (π : P→E) (p : (Fin (d+2) → E×(P×P))×W) : E×E×(Fin d→E)×W :=
  (π (firstPaths d p.1 0),(p.1 (Fin.last (d+1))).1,fun i ↦ π (firstPaths d p.1 i.succ),p.2)
def observeSecond (d : ℕ) (π : P→E) (p : (Fin (d+2) → E×(P×P))×W) : E×E×(Fin d→E)×W :=
  ((p.1 0).1,π (secondPaths d p.1 (Fin.last d)),fun i ↦ π (secondPaths d p.1 i.castSucc),p.2)

lemma observeFirst_measurable (d : ℕ) {π : P→E} (hπ : Measurable π) : Measurable (observeFirst (W:=W) d π) := by
  unfold observeFirst firstPaths
  fun_prop
lemma observeSecond_measurable (d : ℕ) {π : P→E} (hπ : Measurable π) : Measurable (observeSecond (W:=W) d π) := by
  unfold observeSecond secondPaths
  fun_prop

omit [MeasurableSpace E] [MeasurableSpace P] [MeasurableSpace W] in
lemma observations_eq (d : ℕ) (π : P→E) (v : Fin (d+2) → E×(P×P)) (w : W)
    (h : ∀k,π (v k).2.1=(v k).1 ∧ π (v k).2.2=(v k).1) :
    observeFirst d π (v,w)=observeSecond d π (v,w) := by
  unfold observeFirst observeSecond firstPaths secondPaths
  simp only [(h _).1,(h _).2]
  congr 2

lemma observed_measures_eq (d : ℕ) {π : P→E} (μ : Measure ((Fin (d+2) → E×(P×P))×W))
    (h : ∀ᵐ p ∂μ,∀k,π (p.1 k).2.1=(p.1 k).1 ∧ π (p.1 k).2.2=(p.1 k).1) :
    μ.map (observeFirst d π)=μ.map (observeSecond d π) := by
  apply Measure.map_congr
  filter_upwards [h] with p hp
  exact observations_eq d π p.1 p.2 hp

lemma conditioned_observed_measures_eq (d : ℕ) {π : P→E}
    (μ : Measure ((Fin (d+2) → E×(P×P))×W)) (C : Set ((Fin (d+2) → E×(P×P))×W))
    (h : ∀ᵐ p ∂μ,∀k,π (p.1 k).2.1=(p.1 k).1 ∧ π (p.1 k).2.2=(p.1 k).1) :
    ((μ C)⁻¹ • μ.restrict C).map (observeFirst d π)=
      ((μ C)⁻¹ • μ.restrict C).map (observeSecond d π) := by
  apply observed_measures_eq
  exact Measure.smul_absolutelyContinuous.ae_le
    (ae_restrict_of_ae h)

end HardSphere.Comparison

end
end

end

end OAI
