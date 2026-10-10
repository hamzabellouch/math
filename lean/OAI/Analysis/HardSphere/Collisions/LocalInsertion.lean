import Mathlib
import OAI.Analysis.HardSphere.Collisions.InsertionMassIntegrable
import OAI.Analysis.HardSphere.Cutoffs.CloseLabels

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate
noncomputable section

lemma local_insertion : ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ) (L : Length) (r : ℝ), 0<r →
    ∀ (w : SmoothMultiplier 1 L), (∀ X, conj (w.toFun X)=w.toFun X) →
    (∫ y : Torus L, ‖w.orbital y‖^2)=1 → ∀ (k : ℕ),
    C*w.orbitalBound*k*r^3≤1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → (closeLabels r w Y).card≤k) →
    ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v≤energy u+C*(w.orbitalEnergy+w.orbitalBound*k*r)*‖u.1‖^2 := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  let C : ℝ := 50000*(1+Real.pi^2*M^2)
  have hC : 0<C := by dsimp [C]; positivity
  have hC64 : 64≤C := by dsimp [C]; nlinarith [sq_nonneg (Real.pi*M)]
  have hCB {L : Length} (w : SmoothMultiplier 1 L) : 0≤w.orbitalBound := sq_nonneg _
  refine ⟨C,hC,fun n L r hr w hw hn k hs u hu hk ↦ ?_⟩
  have hwB := hCB w
  have hZ : ∀ᵐ Y ∂volume, u.1 Y≠0 → (3/4:ℝ)≤(orbitalCutoff n r w).fiberMass Y := by
    filter_upwards [hk] with Y hY
    intro hne
    have hj : ((closeLabels r w Y).card:ℝ)≤k := by exact_mod_cast hY hne
    have h1 := mul_le_mul_of_nonneg_right hC64 (show 0≤w.orbitalBound*k*r^3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hj (show 0≤64*w.orbitalBound*r^3 by positivity)
    have hz := localized_mass_lower hr w hn Y
    nlinarith
  have hcost : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons x Y)‖^2≤
      2*w.orbitalEnergy+18432*Real.pi^2*M^2*w.orbitalBound*k*r := by
    filter_upwards [hk] with Y hY
    intro hne
    apply (localized_gradient_integral_le hr hM.le hb w Y).trans
    have hj : ((closeLabels r w Y).card:ℝ)≤k := by exact_mod_cast hY hne
    have hh := mul_le_mul_of_nonneg_left hj
      (show 0≤18432*Real.pi^2*M^2*w.orbitalBound*r from mul_nonneg
        (mul_nonneg (by positivity) (hCB w)) hr.le)
    nlinarith
  obtain ⟨v,hv,hvnorm,hven⟩ := (orbitalCutoff n r w).insertion_from_raw_local
    (orbitalCutoff_clearance n hr w) (orbitalCutoff_real n r w hw)
    (by norm_num : (1/2:ℝ)<3/4) hu hZ hcost
  refine ⟨v,hv,hvnorm,hven.trans ?_⟩
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have he : 0≤w.orbitalEnergy := Finset.sum_nonneg fun j _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  have hk0 : 0≤w.orbitalBound*k*r := by exact mul_nonneg (mul_nonneg (hCB w) (Nat.cast_nonneg k)) hr.le
  have h1 : (2:ℝ)/(3/4)≤C := by linarith
  have h2 : (18432*Real.pi^2*M^2)/(3/4)≤C := by
    dsimp [C]
    nlinarith [sq_nonneg (Real.pi*M)]
  have he1 := mul_le_mul_of_nonneg_right h1 he
  have he2 := mul_le_mul_of_nonneg_right h2 hk0
  nlinarith

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate
noncomputable section

lemma SmoothMultiplier.insertion_from_raw_local_value {n : ℕ} {L : Length} {a C z : ℝ}
    (f : SmoothMultiplier (n+1) L) (hc : InsertionClearance a f)
    (hr : ∀ X, conj (f.toFun X)=f.toFun X) (hz : 1/2<z)
    {u : Jet n L} (hu : u∈dirichletDomain n L a)
    (hZ : ∀ᵐ Y ∂volume, u.1 Y≠0 → z≤f.fiberMass Y)
    (hC : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L, ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2≤C) :
    let v := (f.localNormalization hr).insertionJet u
    v∈dirichletDomain (n+1) L a ∧
      ‖v.1‖=‖u.1‖ ∧ energy v≤energy u+(C/z)*‖u.1‖^2 := by
  refine ⟨?_,?_,?_⟩
  · exact (f.localNormalization hr).insertionJet_mem_domain (f.localNormalization_clearance hr hc) hu
  · apply (f.localNormalization hr).norm_insertionScalar_local
    filter_upwards [hZ] with Y hY
    intro hne
    exact f.localNormalization_mass_eq hr Y (hz.le.trans (hY hne))
  · apply (f.localNormalization hr).energy_insertionJet_local_le u (f.localNormalization_mass_le hr)
    · intro i j
      filter_upwards [hZ] with Y hY
      intro hne
      exact (f.localNormalization hr).insertion_orthogonal_local (f.localNormalization_real hr)
        i j Y (f.localNormalization_mass_eventually hr Y (hz.trans_le (hY hne)))
    · filter_upwards [hZ,hC] with Y hY hCY
      intro hne
      have hz0 : 0<z := by linarith
      rw [le_div_iff₀ hz0,mul_comm]
      calc
        z * ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2 ≤
          f.fiberMass Y * ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L (f.localNormalization hr).toFun p (Fin.cons x Y)‖^2 := by
          apply mul_le_mul_of_nonneg_right (hY hne)
          exact Finset.sum_nonneg fun p _ ↦ integral_nonneg fun x ↦ sq_nonneg _
        _ ≤ ∑ p : Direction (n+1), ∫ x : Torus L,
            ‖coordDerivative (n+1) L f.toFun p (Fin.cons x Y)‖^2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun p _ ↦ f.localNormalization_derivative_le hr p Y (hz.trans_le (hY hne))
        _ ≤ C := hCY hne

lemma SmoothMultiplier.localNormalization_insertion_support {n : ℕ} {L : Length}
    (f : SmoothMultiplier (n+1) L) (hr : ∀ X, conj (f.toFun X)=f.toFun X)
    (u : Jet n L) :
    ∀ᵐ X ∂volume, ((f.localNormalization hr).insertionJet u).1 X≠0 →
      u.1 (Fin.tail X)≠0 ∧ f.toFun X≠0 := by
  filter_upwards [coe_insertionScalar (f.localNormalization hr) u.1] with X hX
  intro hne
  change (f.localNormalization hr).insertionScalar u.1 X≠0 at hne
  rw [hX] at hne
  have hp := mul_ne_zero_iff.mp hne
  refine ⟨hp.2,?_⟩
  have hf := hp.1
  change f.toFun X/(Real.sqrt (safeMass (f.fiberMass (Fin.tail X))):ℂ)≠0 at hf
  exact fun hz ↦ hf (by rw [hz,zero_div])

end
end HardSphere
namespace HardSphere
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate
noncomputable section

lemma local_insertion_supported : ∃ C : ℝ, 0<C ∧ ∀ (n : ℕ) (L : Length) (r : ℝ), 0<r →
    ∀ (w : SmoothMultiplier 1 L), (∀ X, conj (w.toFun X)=w.toFun X) →
    (∫ y : Torus L, ‖w.orbital y‖^2)=1 → ∀ (k : ℕ),
    C*w.orbitalBound*k*r^3≤1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → (closeLabels r w Y).card≤k) →
    ∃ v : Jet (n+1) L, v∈dirichletDomain (n+1) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v≤energy u+C*(w.orbitalEnergy+w.orbitalBound*k*r)*‖u.1‖^2 ∧
      (∀ᵐ X ∂volume, v.1 X≠0 → u.1 (Fin.tail X)≠0 ∧ w.orbital (X 0)≠0) := by
  obtain ⟨M,hM,hb⟩ := exists_transition_bound
  let C : ℝ := 50000*(1+Real.pi^2*M^2)
  have hC : 0<C := by dsimp [C]; positivity
  have hC64 : 64≤C := by dsimp [C]; nlinarith [sq_nonneg (Real.pi*M)]
  have hCB {L : Length} (w : SmoothMultiplier 1 L) : 0≤w.orbitalBound := sq_nonneg _
  refine ⟨C,hC,fun n L r hr w hw hn k hs u hu hk ↦ ?_⟩
  have hwB := hCB w
  have hZ : ∀ᵐ Y ∂volume, u.1 Y≠0 → (3/4:ℝ)≤(orbitalCutoff n r w).fiberMass Y := by
    filter_upwards [hk] with Y hY
    intro hne
    have hj : ((closeLabels r w Y).card:ℝ)≤k := by exact_mod_cast hY hne
    have h1 := mul_le_mul_of_nonneg_right hC64 (show 0≤w.orbitalBound*k*r^3 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hj (show 0≤64*w.orbitalBound*r^3 by positivity)
    have hz := localized_mass_lower hr w hn Y
    nlinarith
  have hcost : ∀ᵐ Y ∂volume, u.1 Y≠0 →
      ∑ p : Direction (n+1), ∫ x : Torus L,
        ‖coordDerivative (n+1) L (orbitalCutoff n r w).toFun p (Fin.cons x Y)‖^2≤
      2*w.orbitalEnergy+18432*Real.pi^2*M^2*w.orbitalBound*k*r := by
    filter_upwards [hk] with Y hY
    intro hne
    apply (localized_gradient_integral_le hr hM.le hb w Y).trans
    have hj : ((closeLabels r w Y).card:ℝ)≤k := by exact_mod_cast hY hne
    have hh := mul_le_mul_of_nonneg_left hj
      (show 0≤18432*Real.pi^2*M^2*w.orbitalBound*r from mul_nonneg
        (mul_nonneg (by positivity) (hCB w)) hr.le)
    nlinarith
  let f := orbitalCutoff n r w
  let v := (f.localNormalization (orbitalCutoff_real n r w hw)).insertionJet u
  obtain ⟨hv,hvnorm,hven⟩ := (orbitalCutoff n r w).insertion_from_raw_local_value
    (orbitalCutoff_clearance n hr w) (orbitalCutoff_real n r w hw)
    (by norm_num : (1/2:ℝ)<3/4) hu hZ hcost
  have hsupport : ∀ᵐ X ∂volume, v.1 X≠0 → u.1 (Fin.tail X)≠0 ∧ w.orbital (X 0)≠0 := by
    filter_upwards [f.localNormalization_insertion_support (orbitalCutoff_real n r w hw) u] with X hX
    intro hnz
    obtain ⟨hOld,hRaw⟩ := hX hnz
    refine ⟨hOld,?_⟩
    change w.orbital (X 0)*(TightCutoff.rawCutoff n L r).toFun X≠0 at hRaw
    exact (mul_ne_zero_iff.mp hRaw).1
  refine ⟨v,hv,hvnorm,hven.trans ?_,hsupport⟩
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have he : 0≤w.orbitalEnergy := Finset.sum_nonneg fun j _ ↦ integral_nonneg fun x ↦ sq_nonneg _
  have hk0 : 0≤w.orbitalBound*k*r := by exact mul_nonneg (mul_nonneg (hCB w) (Nat.cast_nonneg k)) hr.le
  have h1 : (2:ℝ)/(3/4)≤C := by linarith
  have h2 : (18432*Real.pi^2*M^2)/(3/4)≤C := by
    dsimp [C]
    nlinarith [sq_nonneg (Real.pi*M)]
  have he1 := mul_le_mul_of_nonneg_right h1 he
  have he2 := mul_le_mul_of_nonneg_right h2 hk0
  nlinarith

end
end HardSphere

end
end
end
end
end
end

end OAI
