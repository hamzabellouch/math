import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Graphs.AllMaskProductAdmissible

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Filter
open scoped ENNReal RealInnerProductSpace ContDiff Topology Classical
variable {d : ℕ}

noncomputable def actualPolicyAngular
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : SmoothFunctionND (EuclideanSpace ℝ (Fin d)) :=
  actualAngularProduct (policyDescriptorList A N q a t) id L ρ m N sig C J i x

lemma actualPolicyAngular_measurable
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (actualPolicyAngular A N q a t L ρ m sig C J i z.1).1 z.2) :=
  actualAngularProduct_measurable _ _ _ _ _ _ _ _ _ _

lemma actualPolicyAngular_even
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Function.Even (actualPolicyAngular A N q a t L ρ m sig C J i x).1 :=
  actualAngularProduct_even _ _ _ _ _ _ _ _ _ _ _

lemma actualPolicy_card_bound (A : ℕ → ℝ) {N q a t : ℕ} (hN : 1 ≤ N) (hq : 0<q) :
    ((policyDescriptorList A N q a t).card:ℝ) ≤ 8*(N:ℝ)^3 := by
  have hh : ((policyDescriptorList A N q a t).card:ℝ) ≤ ((N:ℝ)+1)^3 := by
    exact_mod_cast policyDescriptorList_card (a:=a) (t:=t) A hq
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ ((N:ℝ)+1)^3 := hh
    _ ≤ (2*(N:ℝ))^3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
    _ = _ := by ring

lemma uniform_actualPolicyAngular_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (M B total : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (sig : ℝ) (hsig : 0<sig) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ),
      (∀ b ∈ policyDescriptorList A N q a t, L b ∈ W) →
      (∑ b ∈ policyDescriptorList A N q a t, (L b).length ≤ total) →
      ∀ (x : EuclideanSpace ℝ (Fin d)), ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualPolicyAngular A N q a t L ρ m sig C J i x).1 w‖ ≤
        D^total*(((2:ℝ)^N)^sig*
          sourceMaskScaleND ((policyDescriptorList A N q a t).sup descriptorLength) ((2:ℝ)^N) sig)^j := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualAngularProduct_derivatives (ι:=PolicyDescriptor) W M B total 3
    hW 8 sig hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb,Filter.eventually_ge_atTop 1] with N hDb hN
  intro A q a t hq L ρ m C J i hL htotal x j hj w hw
  exact hDb (policyDescriptorList A N q a t) id L ρ m C J i _
    (actualPolicy_card_bound A hN hq) hL htotal (fun b hb => Finset.le_sup hb) x j hj w hw

lemma uniform_actualPolicyAngular_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q → t≤N →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (k : ℕ) (x w : EuclideanSpace ℝ (Fin d)), ‖w‖=1 →
      w ∈ tsupport (iteratedFDeriv ℝ k (actualPolicyAngular A N q a t L ρ m sig C J i x).1) →
      ∀ b ∈ policyDescriptorList A N q a t, (x,w) ∈ endpointGood ρ m N sig C J (i+1) b := by
  obtain ⟨N₀,h₀⟩ := uniform_actualAngularProduct_support (d:=d) (ι:=PolicyDescriptor) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf A q a t hq ht m C i L k x w hw hs b hb
  exact h₀ N hN ρ hf m C i (policyDescriptorList A N q a t) id
    (fun e he => policyDescriptor_valid A hq ht he) L k x w hw hs b hb

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
