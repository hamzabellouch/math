import OAI.NumberTheory.DukePrimeDegree.Entropy.RootFactorConditionalProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.ShiftedRootLeafHolonomy

namespace OAI

/-! # Nested root conditionals when the time origin depends on the transversal -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

theorem factorChart_shifted_nested_conditionals {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1, z.2 + τ z.1))) :
    ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      A.conditionalKernel μ (e (s,w)) =
        ((σ.condKernel s).condKernel w).map (Homeomorph.addRight (τ (s,w))) := by
  let η := σ.map MeasurableEquiv.prodAssoc.symm
  have hm := conditional_map_fibers_embedding η e he
    (fun z => z.2 + τ z.1) (measurable_snd.add (hτ.comp measurable_fst))
  have hm' : ∀ᵐ z ∂η.fst,
      A.conditionalKernel μ (e z) = (η.condKernel z).map (Homeomorph.addRight (τ z)) := by
    filter_upwards [hm] with z hz
    change ((σ.map MeasurableEquiv.prodAssoc.symm).map
      (fun w => (e w.1,w.2 + τ w.1))).condKernel (e z) =
        (η.condKernel z).map (Homeomorph.addRight (τ z)) at hz
    simpa only [←hcoord, RootBox.conditionalKernel] using hz
  have hη : η = (σ.fst ⊗ₘ (σ.condKernel.fst ⊗ₖ σ.condKernel.condKernel)).map
      MeasurableEquiv.prodAssoc.symm := by
    rw [Kernel.disintegrate,Measure.disintegrate]
  have hf : η.fst = σ.fst ⊗ₘ σ.condKernel.fst := by
    rw [hη,Measure.compProd_assoc,Measure.fst_compProd]
  rw [hf] at hm'
  filter_upwards [Measure.ae_ae_of_ae_compProd hm', ae_nested_real_conditionals σ] with s hs hc
  filter_upwards [hs,hc] with w hw hcw
  rw [←hcw]
  exact hw

theorem factorChart_shifted_ae_nested {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (τ : T × B → ℝ) (hτ : Measurable τ)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1,z.2 + τ z.1)))
    {P : RootSlice a b k × ℝ → Prop} (hp : ∀ᵐ z ∂A.coordinateMeasure μ, P z) :
    ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      ∀ᵐ t ∂(σ.condKernel s).condKernel w, P (e (s,w),t + τ (s,w)) := by
  rw [hcoord] at hp
  have hm := (he.measurable.comp measurable_fst).prodMk
    (measurable_snd.add (hτ.comp measurable_fst))
  have h₁ := ae_of_ae_map hm.aemeasurable hp
  have h₂ := ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable h₁
  change ∀ᵐ z ∂σ, P (e (z.1,z.2.1),z.2.2 + τ (z.1,z.2.1)) at h₂
  have h₃ : ∀ᵐ z ∂σ.fst ⊗ₘ σ.condKernel, P (e (z.1,z.2.1),z.2.2 + τ (z.1,z.2.1)) := by
    simpa only [Measure.disintegrate] using h₂
  filter_upwards [Measure.ae_ae_of_ae_compProd h₃] with s hs
  have H : ∀ᵐ z ∂(σ.condKernel s).fst ⊗ₘ (σ.condKernel s).condKernel,
      P (e (s,z.1),z.2 + τ (s,z.1)) := by
    simpa only [Measure.disintegrate] using hs
  exact Measure.ae_ae_of_ae_compProd H

theorem shifted_leaf_restrict (ν κ : Measure ℝ) (V J : Set ℝ)
    (hJ : MeasurableSet J) (a : ℝ)
    (hJV : (Homeomorph.addRight a) '' J ⊆ V)
    (hκ : κ.map (Homeomorph.addRight a) = ν.restrict V) :
    (ν.map (Homeomorph.addRight a).symm).restrict J = κ.restrict J := by
  let f := Homeomorph.addRight a
  have he : κ = (ν.restrict V).map f.symm := by
    rw [←hκ,Measure.map_map f.symm.measurable f.measurable]
    have hid : f.symm ∘ f = id := by
      funext x
      exact f.symm_apply_apply x
    rw [hid,Measure.map_id]
  have hpre : f.symm ⁻¹' J ⊆ V := by
    intro x hx
    exact hJV ⟨f.symm x,hx,f.apply_symm_apply x⟩
  rw [he,Measure.restrict_map f.symm.measurable hJ,
    Measure.restrict_map f.symm.measurable hJ,
    Measure.restrict_restrict (f.symm.measurable hJ),inter_eq_left.mpr hpre]

end DukePrimeDegree

end

end OAI
