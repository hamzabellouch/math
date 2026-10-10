import OAI.NumberTheory.Jacobsthal.Estimates.RawReturnBound

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

lemma measurable_sigma_family {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {Z : Type*} [MeasurableSpace Z] {f : (Σ i, X i) → Z}
    (hf : ∀ i, Measurable (fun x => f (@Sigma.mk ι X i x))) : Measurable f := by
  intro S hS
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro i
  exact hf i hS

noncomputable def sigmaFamilyKernel {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (K : ∀ i, Kernel (X i) (Y i)) : Kernel (Σ i, X i) (Σ i, Y i) where
  toFun z := (K z.1 z.2).map (@Sigma.mk ι Y z.1)
  measurable' := by
    apply measurable_sigma_family
    intro i
    have hm := ((K i).map (@Sigma.mk ι Y i)).measurable
    have he : (fun x : X i => ((K i).map (@Sigma.mk ι Y i)) x) =
        (fun x : X i => (K i x).map (@Sigma.mk ι Y i)) := by
      funext x
      exact Kernel.map_apply _ (measurableSigmaMk i) x
    change Measurable (fun x : X i => ((K i).map (@Sigma.mk ι Y i)) x) at hm
    rw [he] at hm
    exact hm

lemma sigmaFamilyKernel_apply {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (K : ∀ i, Kernel (X i) (Y i)) (i : ι) (x : X i) :
    sigmaFamilyKernel K (@Sigma.mk ι X i x) = (K i x).map (@Sigma.mk ι Y i) := rfl

lemma sigmaFamilyKernel_mass {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (K : ∀ i, Kernel (X i) (Y i)) (i : ι) (x : X i) :
    sigmaFamilyKernel K (@Sigma.mk ι X i x) univ=K i x univ := by
  rw [sigmaFamilyKernel_apply,Measure.map_apply (measurableSigmaMk i) MeasurableSet.univ,preimage_univ]

lemma sigmaFamilyKernel_lintegral {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (K : ∀ i, Kernel (X i) (Y i)) (i : ι) (x : X i)
    {F : (Σ j, Y j) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂sigmaFamilyKernel K (@Sigma.mk ι X i x)) =
      ∫⁻ y, F (@Sigma.mk ι Y i y) ∂K i x := by
  rw [sigmaFamilyKernel_apply,lintegral_map hF (measurableSigmaMk i)]

lemma sigmaFamilyKernel_isFinite_of_bound {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (K : ∀ i, Kernel (X i) (Y i)) {B : ℝ≥0∞} (hB : B < ∞)
    (hK : ∀ i x, K i x univ ≤ B) : IsFiniteKernel (sigmaFamilyKernel K) := by
  refine ⟨⟨B,hB,?_⟩⟩
  rintro ⟨i,x⟩
  rw [sigmaFamilyKernel_mass]
  exact hK i x

instance sigmaFamilyKernel_isMarkov {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (K : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (K i)] : IsMarkovKernel (sigmaFamilyKernel K) := by
  constructor
  rintro ⟨i,x⟩
  constructor
  rw [sigmaFamilyKernel_mass,measure_univ]

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
