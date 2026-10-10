import OAI.Analysis.CircleDomains.Topology.CompactPositiveFunctional
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Topology.ContinuousMap.Algebra

namespace OAI

/-! Hahn–Banach separation for a compact family of measures and a
sublinear majorant cost. -/
open Set MeasureTheory
open scoped CompactlySupported
noncomputable section
namespace CircleDomainRigidity

lemma exists_compact_positive_functional_of_majorant_cost
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (p : C_c(X, ℝ) → ℝ)
    (phom : ∀ c : ℝ, 0 < c → ∀ f, p (c • f) = c * p f)
    (padd : ∀ f g, p (f+g) ≤ p f + p g)
    (pneg : ∀ f, (∀ x, 0 ≤ f x) → p (-f) = 0)
    (c : ℝ)
    (pconst : ∀ r : ℝ, r*c ≤ p
      (r • (⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ : C_c(X,ℝ)))) :
    ∃ Λ : C_c(X,ℝ) →ₚ[ℝ] ℝ,
      Λ ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩ = c ∧
      ∀ f, Λ f ≤ p f := by
  classical
  let oneX : C_c(X,ℝ) := ⟨1,HasCompactSupport.of_compactSpace (1 : C(X,ℝ))⟩
  let V : Submodule ℝ C_c(X,ℝ) := Submodule.span ℝ {oneX}
  let x₀ : X := Classical.choice inferInstance
  let ev : C_c(X,ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => f x₀
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let l : V →ₗ[ℝ] ℝ := c • (ev.comp V.subtype)
  have hl (f : V) : l f ≤ p f := by
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp f.property
    change c * ev f.val ≤ p f.val
    rw [← hr]
    simpa [ev,oneX,mul_comm] using pconst r
  obtain ⟨L,hL,hLp⟩ := exists_extension_of_le_sublinear
    (⟨V,l⟩ : C_c(X,ℝ) →ₗ.[ℝ] ℝ) p phom padd hl
  have hpos (f : C_c(X,ℝ)) (hf : 0 ≤ f) : 0 ≤ L f := by
    have hn := hLp (-f)
    rw [pneg f (fun x => hf x),map_neg] at hn
    linarith
  refine ⟨PositiveLinearMap.mk₀ L hpos,?_,hLp⟩
  have he := hL (⟨oneX,Submodule.mem_span_singleton_self oneX⟩ : V)
  change L oneX = c
  simpa [l,ev,oneX] using he

end CircleDomainRigidity

end

end OAI
