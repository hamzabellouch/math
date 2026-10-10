import OAI.GroupTheory.PolycyclicRecognition.Algebra.AmbientSemisimpleCocycleReduction
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GaugeComposition
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GaugeFactorSymmetry

namespace OAI

/-! # Removing all moving components for a finite semisimple family

Each correction is central and fixes every component already dealt with.
Their product is one normalized gauge for the original factor system.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative
variable {L Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group Q] [IsMulCommutative Q]

theorem finite_semisimple_cocycle_reduction (F : NonabelianFactorSystem L Q)
    (A : Q → L ≃ₗ⁅ℝ⁆ L) (hact : ∀ q x, F.action q x = A q x)
    (ss : List (L ≃ₗ⁅ℝ⁆ L))
    (hss : ∀ S ∈ ss, Module.End.IsSemisimple S.toLinearMap)
    (hpair : ∀ S ∈ ss, ∀ T ∈ ss, Commute S.toLinearMap T.toLinearMap)
    (hcomm : ∀ S ∈ ss, ∀ q, Commute S.toLinearMap (A q).toLinearMap)
    (hlift : ∀ S ∈ ss, ∃ q₀ : Q, ∃ U : L ≃ₗ⁅ℝ⁆ L,
      IsNilpotent (U.toLinearMap - 1) ∧ Commute S.toLinearMap U.toLinearMap ∧
      (A q₀).toLinearMap = S.toLinearMap * U.toLinearMap) :
    ∃ b : Q → L, ∃ hb : b 1 = 1,
      (∀ q, b q ∈ Subgroup.center L) ∧
      (∀ q x, (F.gauge b hb).action q x = F.action q x) ∧
      ∀ S ∈ ss, ∀ q r, S ((F.gauge b hb).factor q r) = (F.gauge b hb).factor q r := by
  induction ss with
  | nil =>
    refine ⟨fun _ => 1, rfl, fun _ => (Subgroup.center L).one_mem, ?_, by simp⟩
    intro q x
    change (1 : L) * F.action q x * (1 : L)⁻¹ = F.action q x
    simp
  | cons S ss ih =>
    obtain ⟨b, hb, hbZ, hbA, hbfix⟩ := ih
      (fun T hT => hss T (List.mem_cons_of_mem S hT))
      (fun T hT R hR => hpair T (List.mem_cons_of_mem S hT) R (List.mem_cons_of_mem S hR))
      (fun T hT => hcomm T (List.mem_cons_of_mem S hT))
      (fun T hT => hlift T (List.mem_cons_of_mem S hT))
    let F₁ := F.gauge b hb
    have hA₁ : ∀ q x, F₁.action q x = A q x := fun q x => (hbA q x).trans (hact q x)
    obtain ⟨q₀, U, hU, hSU, hAU⟩ := hlift S (by simp)
    obtain ⟨c, hc, hcZ, hcA, hcS, hcT⟩ := ambient_semisimple_cocycle_reduction
      F₁ A hA₁ S (hss S (by simp)) (hcomm S (by simp)) q₀ U hU hSU hAU
    have hcb : c 1 * b 1 = 1 := by rw [hc, hb, one_mul]
    refine ⟨fun q => c q * b q, hcb, fun q => (Subgroup.center L).mul_mem (hcZ q) (hbZ q),
      ?_, ?_⟩
    · intro q x
      rw [← gauge_gauge_action F b c hb hc hcb]
      exact (hcA q x).trans (hbA q x)
    · intro T hT q r
      rw [← gauge_gauge_factor F b c hb hc hcb]
      rcases List.mem_cons.mp hT with hT | hT
      · subst T
        exact hcS q r
      · have hcfix : ∀ t, T (c t) = c t := hcT T
          (hpair S (by simp) T (List.mem_cons_of_mem S hT))
          (hcomm T (List.mem_cons_of_mem S hT)) (hbfix T hT)
        let t := PolynomialExponentialCoordinates.groupAutomorphism (P := P) T
        have hTa : ∀ q x, t (F₁.action q x) = F₁.action q (t x) := by
          intro q x
          change T (F₁.action q x) = F₁.action q (T x)
          rw [hA₁, hA₁]
          exact LinearMap.congr_fun (hcomm T (List.mem_cons_of_mem S hT) q).eq x
        exact gauge_factor_fixed F₁ c hc t.toMonoidHom hTa (hbfix T hT) hcfix q r

end PolycyclicRecognition

end

end OAI
