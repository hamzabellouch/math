import OAI.NumberTheory.DukePrimeDegree.Geometry.RootFactorHolonomy
import OAI.NumberTheory.DukePrimeDegree.Entropy.NestedRealConditionals
import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafNormalizationInjectivity

namespace OAI

/-!
# The conditional product step for a noncommuting root factor

A measurable change of transverse coordinates preserves the real
conditional. In a genuine root factor chart, the proved neutral
holonomy then makes that conditional independent of the remaining
root coordinates. This is the local step of EK2003, Proposition 8.3.
-/

noncomputable section
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace DukePrimeDegree
open PrimeDegreePackets

variable {T B : Type*} [MeasurableSpace T] [MeasurableSpace B]
  [StandardBorelSpace B] [Nonempty B]

lemma factorChart_nested_conditionals {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n)) [IsFiniteMeasure μ]
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1, z.2))) :
    ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      A.conditionalKernel μ (e (s, w)) = (σ.condKernel s).condKernel w := by
  let η := σ.map MeasurableEquiv.prodAssoc.symm
  have hm := conditional_map_fibers_embedding η e he Prod.snd measurable_snd
  have hm' : ∀ᵐ z ∂η.fst,
      A.conditionalKernel μ (e z) = η.condKernel z := by
    filter_upwards [hm] with z hz
    change ((σ.map MeasurableEquiv.prodAssoc.symm).map (fun w => (e w.1, w.2))).condKernel
      (e z) = (η.condKernel z).map id at hz
    simpa only [←hcoord, Measure.map_id, RootBox.conditionalKernel] using hz
  have hη : η = (σ.fst ⊗ₘ σ.condKernel.fst) ⊗ₘ σ.condKernel.condKernel := by
    calc
      η = (σ.fst ⊗ₘ (σ.condKernel.fst ⊗ₖ σ.condKernel.condKernel)).map
          MeasurableEquiv.prodAssoc.symm := by rw [Kernel.disintegrate, Measure.disintegrate]
      _ = _ := Measure.compProd_assoc
  have hf : η.fst = σ.fst ⊗ₘ σ.condKernel.fst := by rw [hη, Measure.fst_compProd]
  rw [hf] at hm'
  filter_upwards [Measure.ae_ae_of_ae_compProd hm', ae_nested_real_conditionals σ] with s hs hc
  filter_upwards [hs, hc] with w hw hcw
  exact hw.trans hcw

lemma factorChart_ae_nested {n : ℕ} {a b k : Fin n} (hab : a ≠ b)
    (A : RootBox hab k) (μ : Measure (X n))
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1, z.2)))
    {P : RootSlice a b k × ℝ → Prop} (hp : ∀ᵐ z ∂A.coordinateMeasure μ, P z) :
    ∀ᵐ s ∂σ.fst, ∀ᵐ w ∂(σ.condKernel s).fst,
      ∀ᵐ t ∂(σ.condKernel s).condKernel w, P (e (s, w), t) := by
  rw [hcoord] at hp
  have h₁ := ae_of_ae_map (he.measurable.comp measurable_fst |>.prodMk measurable_snd).aemeasurable hp
  have h₂ := ae_of_ae_map MeasurableEquiv.prodAssoc.symm.measurable.aemeasurable h₁
  change ∀ᵐ z ∂σ, P (e (z.1, z.2.1), z.2.2) at h₂
  have h₃ : ∀ᵐ z ∂σ.fst ⊗ₘ σ.condKernel, P (e (z.1, z.2.1), z.2.2) := by
    simpa only [Measure.disintegrate] using h₂
  filter_upwards [Measure.ae_ae_of_ae_compProd h₃] with s hs
  have H : ∀ᵐ z ∂(σ.condKernel s).fst ⊗ₘ (σ.condKernel s).condKernel,
      P (e (s, z.1), z.2) := by simpa only [Measure.disintegrate] using hs
  exact Measure.ae_ae_of_ae_compProd H

theorem rootFactorChart_real_conditionals_constant
    (d : ℕ) (S : Finset (Fin (d + 1) × Fin (d + 1)))
    (hpos : ∀ p ∈ S, p.1 < p.2)
    (hcomp : ∀ i j k : Fin (d + 1), (i, j) ∈ S → (j, k) ∈ S → (i, k) ∈ S)
    {a b k : Fin (d + 1)} (hab : a ≠ b) (habS : (a, b) ∈ S)
    (ell : Fin (d + 1) → ℝ) (hell : ∑ i, ell i = 0) (hneut : ell a = ell b)
    (hdecay : ∀ p ∈ S, p ≠ (a, b) → ell p.1 < ell p.2)
    (A : RootBox hab k) (R : ℝ) (hAR : A.time ⊆ rootLeafWindow R 0)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (σ : Measure (T × (B × ℝ))) [IsFiniteMeasure σ]
    (e : T × B → RootSlice a b k) (he : MeasurableEmbedding e)
    (hcoord : A.coordinateMeasure μ =
      (σ.map MeasurableEquiv.prodAssoc.symm).map (fun z => (e z.1, z.2)))
    (base : T → X (d + 1)) (factor : B → positiveRootGeneratedGroup (S.erase (a, b)))
    (hparam : ∀ s w t, rootQuotientParametrization hab (e (s, w), t) =
      rightAction (base s) ((factor w).val * Matrix.SpecialLinearGroup.transvection hab t)) :
    ∀ᵐ s ∂σ.fst, ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
      ∀ᵐ w ∂(σ.condKernel s).fst, (σ.condKernel s).condKernel w = ν := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hab t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx a b hab
  obtain ⟨N, _hN, hN0, hhol⟩ := exists_nullset_rootFactor_holonomy d S hpos hcomp hab habS
    ell hell hneut hdecay μ hA
  have havoid : ∀ᵐ x ∂μ, x ∉ N := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hN0
  let F := A.leafMeasure R μ
  let P : RootSlice a b k × ℝ → Prop := fun z =>
    A.IsNormalizedRootLeaf R μ z.1 (F z.1) ∧
    0 < F z.1 (Metric.ball z.2 1) ∧
    intrinsicRootLeaf hab μ (rootQuotientParametrization hab z) = basedRealMeasure (F z.1) z.2 ∧
    rootQuotientParametrization hab z ∉ N
  have hP : ∀ᵐ z ∂A.coordinateMeasure μ, P z := by
    have hs := ae_of_ae_map measurable_fst.aemeasurable (A.ae_leafMeasure_spec R hAR μ hfree)
    filter_upwards [hs, A.ae_leafMeasure_ball_pos R hAR μ hfree,
      A.ae_intrinsicRootLeaf_coordinates R hAR μ hfree,
      A.ae_coordinate_of_ambient μ havoid] with z hz hp hb hn
    exact ⟨hz, hp 1 zero_lt_one, hb, hn⟩
  filter_upwards [factorChart_ae_nested hab A μ σ e he hcoord hP,
    factorChart_nested_conditionals hab A μ σ e he hcoord] with s hs hc
  have hgood : ∀ᵐ w ∂(σ.condKernel s).fst,
      (∀ᵐ t ∂(σ.condKernel s).condKernel w, P (e (s, w), t)) ∧
        A.conditionalKernel μ (e (s, w)) = (σ.condKernel s).condKernel w := hs.and hc
  obtain ⟨w₀, hw₀, hc₀⟩ := hgood.exists
  obtain ⟨t₀, ht₀⟩ := hw₀.exists
  refine ⟨(σ.condKernel s).condKernel w₀, inferInstance, ?_⟩
  filter_upwards [hgood] with w hw
  obtain ⟨t, ht⟩ := hw.1.exists
  let s₀ := e (s, w₀)
  let s₁ := e (s, w)
  let : IsLocallyFiniteMeasure (F s₀) := ht₀.1.1
  let : IsLocallyFiniteMeasure (F s₁) := ht.1.1
  have hleaf : F s₀ = F s₁ := by
    apply eq_of_rebasedRealMeasure_eq (F s₀) (F s₁) A.time ht₀.1.2.1 ht.1.2.1
      t₀ t ht₀.2.1 ht.2.1
    rw [←ht₀.2.2.1, ←ht.2.2.1]
    have h₀ := ht₀.2.2.2
    have h₁ := ht.2.2.2
    change rootQuotientParametrization hab (e (s, w₀), t₀) ∉ N at h₀
    change rootQuotientParametrization hab (e (s, w), t) ∉ N at h₁
    change intrinsicRootLeaf hab μ (rootQuotientParametrization hab (e (s, w), t)) =
      basedRealMeasure (intrinsicRootLeaf hab μ
        (rootQuotientParametrization hab (e (s, w₀), t₀))) (t - t₀)
    simp only [hparam] at h₀ h₁ ⊢
    exact hhol (base s) (factor w₀) (factor w) t₀ t h₀ h₁
  have hrestrict := congrArg (fun η : Measure ℝ => η.restrict A.time) hleaf
  rw [ht₀.1.2.2.1, ht.1.2.2.1, hc₀, hw.2] at hrestrict
  exact hrestrict.symm

end DukePrimeDegree

end

end OAI
