import Mathlib
import OAI.Analysis.Crouzeix.FunctionalComposition
import OAI.Analysis.Crouzeix.PhysicalDensity

namespace OAI

/-! Physical Calculus. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

namespace Conformal.InteriorCollar

variable {U : Set ℂ} (R : InteriorCollar U)

def pullbackDomain (V : Set ℂ) : Set ℂ := ball 0 R.radius ∩ R.h ⁻¹' V

lemma isOpen_pullbackDomain {V : Set ℂ} (hV : IsOpen V) : IsOpen (R.pullbackDomain V) :=
  R.analytic_h.continuousOn.isOpen_inter_preimage isOpen_ball hV

lemma closedDisk_subset_pullbackDomain {V : Set ℂ} (hUV : closure U ⊆ V) :
    closedBall (0 : ℂ) 1 ⊆ R.pullbackDomain V := fun _ hz =>
  ⟨R.closedDisk_subset hz,hUV (R.closed_h.mapsTo hz)⟩

lemma differentiableOn_pullback {V : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V) :
    DifferentiableOn ℂ (f ∘ R.h) (R.pullbackDomain V) :=
  hf.comp (R.analytic_h.differentiableOn.mono inter_subset_left) (fun _ hz => hz.2)

def diskTrace {V : Set ℂ} (hUV : closure U ⊆ V) {m : ℕ} (F : ℂ → Coeff m)
    (hF : ContinuousOn F V) : C(CircleSpace, Coeff m) :=
  ⟨fun t => F (R.h (circleCoordinate t)),
    hF.comp_continuous
      (R.analytic_h.continuousOn.comp_continuous circleCoordinate.continuous
        (fun t => R.closedDisk_subset (mem_closedBall_zero_iff.mpr (norm_circleCoordinate t).le)))
      (fun t => hUV (R.closed_h.mapsTo (mem_closedBall_zero_iff.mpr (norm_circleCoordinate t).le)))⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]

lemma holomorphic_intertwines (A D S : Operator H) (hKU : numericalClosure A ⊆ U)
    (hN : ‖D‖ ≤ 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g V) :
    S * holomorphicEval A V g =
      holomorphicEval D (R.pullbackDomain V) (g ∘ R.h) * S := by
  let W := R.domain ∩ R.f ⁻¹' R.pullbackDomain V
  have hW : IsOpen W := R.analytic_f.continuousOn.isOpen_inter_preimage R.isOpen_domain
    (R.isOpen_pullbackDomain hV)
  have hAW : numericalClosure A ⊆ W := fun z hz =>
    ⟨R.closure_subset_domain (subset_closure (hKU hz)),
      R.closedDisk_subset_pullbackDomain hUV (R.closed_f.mapsTo (subset_closure (hKU hz)))⟩
  have hWV : W ⊆ V := fun z hz => by
    have hh := hz.2.2
    change R.h (R.f z) ∈ V at hh
    rwa [R.inverse.1 hz.1] at hh
  have hfW := R.analytic_f.differentiableOn.mono (show W ⊆ R.domain from inter_subset_left)
  have hgW : DifferentiableOn ℂ ((g ∘ R.h) ∘ R.f) W :=
    (R.differentiableOn_pullback hg).comp hfW (fun z hz => hz.2)
  have hid : holomorphicEval A W ((g ∘ R.h) ∘ R.f) = holomorphicEval A V g := by
    rw [holomorphicEval_congr A hW hAW hgW (hg.mono hWV)
      (fun z hz => congrArg g (R.inverse.1 hz.1)),
      holomorphicEval_restrict A hW hV hAW hWV hg]
  have hiW : S * holomorphicEval A W R.f = D * S := by
    rw [holomorphicEval_restrict A hW R.isOpen_domain hAW inter_subset_left R.analytic_f.differentiableOn]
    exact hI
  have hh := holomorphicEval_comp_intertwines A D S hN hW hAW
    (R.isOpen_pullbackDomain hV) (R.closedDisk_subset_pullbackDomain hUV)
    hfW (R.differentiableOn_pullback hg) (fun z hz => hz.2)
    (fun z hz => R.closed_f.mapsTo (subset_closure (hKU hz))) hiW
  rw [hid] at hh
  exact hh

lemma matrixHolomorphic_intertwines (A D S : Operator H) (hKU : numericalClosure A ⊆ U)
    (hN : ‖D‖ ≤ 1) (hI : S * holomorphicEval A R.domain R.f = D * S)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    tensorOperator S (1 : Coeff m) * matrixHolomorphicEval A V F =
      matrixHolomorphicEval D (R.pullbackDomain V) (F ∘ R.h) * tensorOperator S (1 : Coeff m) := by
  unfold matrixHolomorphicEval
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← tensorOperator_mul, ← tensorOperator_mul, one_mul, mul_one]
  exact congrArg (fun T => tensorOperator T (Matrix.single i j 1))
    (R.holomorphic_intertwines A D S hKU hN hI hV hUV (hF i j))

end Conformal.InteriorCollar

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma h_interiorAngle (t : CircleSpace) :
    R.h (circleCoordinate (C.interiorAngle R t)) = C.boundaryMap t := by
  rw [C.circleCoordinate_interiorAngle]
  exact R.inverse.1 (R.closure_subset_domain (C.boundaryMap_mem_frontier t).1)

local instance physicalCalculusOperatorRealNormedSpace (size : ℕ) :
    NormedSpace ℝ (Operator (Amplification H size)) :=
  NormedSpace.restrictScalars ℝ ℂ _

lemma integral_operatorDensity_holomorphic (hU : IsOpen U) (hc : Convex ℝ U)
    (D : Operator H) (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.boundaryMap t)) ∂circleMeasure) =
      matrixHolomorphicEval D (R.pullbackDomain V) (F ∘ R.h) := by
  let F₀ := R.diskTrace hUV F hF.continuousOn
  have he (t : CircleSpace) : F (C.boundaryMap t) = F₀ (C.interiorAngle R t) := by
    change _ = F (R.h (circleCoordinate (C.interiorAngle R t)))
    rw [C.h_interiorAngle R]
  simp_rw [he]
  rw [C.integral_operatorDensity_pullback R D hD hU hc]
  exact Disk.integral_matrixHolomorphic D hN hD (F := F ∘ R.h)
    (R.isOpen_pullbackDomain hV) (R.closedDisk_subset_pullbackDomain hUV)
    (fun i j => R.differentiableOn_pullback (hF i j))

variable [Nontrivial H]

lemma physical_intertwines (hU : IsOpen U) (hc : Convex ℝ U)
    (A D S : Operator H) (hKU : numericalClosure A ⊆ U)
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    {V : Set ℂ} (hV : IsOpen V) (hUV : closure U ⊆ V)
    {m : ℕ} {F : ℂ → Coeff m} (hF : EntrywiseHolomorphic V F) :
    tensorOperator S (1 : Coeff m) * matrixHolomorphicEval A V F =
      (∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.boundaryMap t)) ∂circleMeasure) *
        tensorOperator S (1 : Coeff m) := by
  rw [C.integral_operatorDensity_holomorphic R hU hc D hN hD hV hUV hF]
  exact R.matrixHolomorphic_intertwines A D S hKU hN hI hV hUV hF

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
