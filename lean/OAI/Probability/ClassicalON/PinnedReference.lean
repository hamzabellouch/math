import OAI.Probability.ClassicalON.AmplitudeSplit

namespace OAI

universe uA uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {A : Type uA} [Fintype V]

def glueFamily (B : Set V) (a : B → A) (r : ↥(Bᶜ) → A) : V → A :=
  (Equiv.piEquivPiSubtypeProd (·∈B) (fun _ : V => A)).symm (a,r)

omit [Fintype V] in
@[simp] theorem glueFamily_in (B : Set V) (a : B → A) (r : ↥(Bᶜ) → A) (v : B) :
    glueFamily B a r v=a v := by simp [glueFamily,Equiv.piEquivPiSubtypeProd,v.property]

omit [Fintype V] in
@[simp] theorem glueFamily_out (B : Set V) (a : B → A) (r : ↥(Bᶜ) → A) (v : ↥(Bᶜ)) :
    glueFamily B a r v=r v := by
  simp [glueFamily,Equiv.piEquivPiSubtypeProd,show v.val∉B from v.property]

omit [Fintype V] in
theorem continuous_glueFamily [TopologicalSpace A] (B : Set V) :
    Continuous (fun p : (B → A)×(↥(Bᶜ) → A) => glueFamily B p.1 p.2) :=
  (Homeomorph.piEquivPiSubtypeProd (·∈B) (fun _ : V => A)).symm.continuous

theorem sum_glueFamily [Fintype A] (B : Set V) (a : B → A) (f : (V → A) → ℝ) :
    (∑ r : ↥(Bᶜ) → A,f (glueFamily B a r))=
      ∑ s : V → A,if (fun v : B => s v)=a then f s else 0 := by
  let e := Equiv.piEquivPiSubtypeProd (·∈B) (fun _ : V => A)
  rw [← e.symm.sum_comp (fun s => if (fun v : B => s v)=a then f s else 0)]
  rw [Fintype.sum_prod_type]
  have he (p : B → A) (r : ↥(Bᶜ) → A) : (fun v : B => (e.symm (p,r)) v)=p := by
    funext v
    exact glueFamily_in B p r v
  simp_rw [he]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rfl

section Measure
variable [MeasurableSpace A] [MeasurableSingletonClass A]

def pinProductMeasure (μ : Measure A) (B : Set V) (a : B → A) : Measure (V → A) :=
  Measure.pi (fun v => if h : v∈B then Measure.dirac (a ⟨v,h⟩) else μ)

instance pinProductMeasure_isProbability (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (a : B → A) : IsProbabilityMeasure (pinProductMeasure μ B a) := by
  unfold pinProductMeasure
  have : ∀ v : V,IsProbabilityMeasure (if h : v∈B then Measure.dirac (a ⟨v,h⟩) else μ) := by
    intro v; split <;> infer_instance
  infer_instance

theorem measure_pi_dirac (a : V → A) : (Measure.pi (fun v => Measure.dirac (a v)))=Measure.dirac a := by
  apply Measure.pi_eq
  intro s hs
  by_cases h : ∀ v,a v∈s v
  · simp [h]
  · obtain ⟨v,hv⟩ := not_forall.mp h
    have hn : a∉Set.pi Set.univ s := by
      intro ha
      exact hv (ha v (Set.mem_univ v))
    rw [Measure.dirac_apply,Set.indicator_of_notMem hn]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]

variable [TopologicalSpace A] [CompactSpace A] [T2Space A] [SecondCountableTopology A] [BorelSpace A]

omit [T2Space A] in
theorem integral_pinProductMeasure (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (a : B → A) (f : (V → A) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂pinProductMeasure μ B a)=
      ∫ r,f (glueFamily B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
  let ν (v : V) : Measure A := if h : v∈B then Measure.dirac (a ⟨v,h⟩) else μ
  have : ∀ v,IsProbabilityMeasure (ν v) := by intro v; dsimp [ν]; split <;> infer_instance
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => A) (·∈B)
  have hp := (measurePreserving_piEquivPiSubtypeProd ν (·∈B)).symm e
  have hB : (fun v : B => ν v)=(fun v : B => Measure.dirac (a v)) := by funext v; simp [ν,v.property]
  have hC : (fun v : ↥(Bᶜ) => ν v)=(fun _ : ↥(Bᶜ) => μ) := by
    funext v; simp [ν,show v.val∉B from v.property]
  change (∫ s,f s ∂Measure.pi ν)=_
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]
  change (∫ p : (B → A)×(↥(Bᶜ) → A), f (glueFamily B p.1 p.2)
    ∂(Measure.pi (fun v : B => ν v)).prod (Measure.pi (fun v : ↥(Bᶜ) => ν v)))=_
  rw [hB,hC,measure_pi_dirac]
  have hi : Integrable (fun p : (B → A)×(↥(Bᶜ) → A) => f (glueFamily B p.1 p.2))
      ((Measure.dirac a).prod (Measure.pi (fun _ : ↥(Bᶜ) => μ))) :=
    compact_integrable (hf.comp (continuous_glueFamily B))
  rw [integral_prod _ hi]
  rw [integral_dirac]

omit [MeasurableSingletonClass A] in
theorem integral_pi_split (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (f : (V → A) → ℝ) (hf : Continuous f) :
    (∫ s,f s ∂Measure.pi (fun _ : V => μ))=
      ∫ a,∫ r,f (glueFamily B a r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)
        ∂Measure.pi (fun _ : B => μ) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : V => A) (·∈B)
  have hp := (measurePreserving_piEquivPiSubtypeProd (fun _ : V => μ) (·∈B)).symm e
  rw [← hp.map_eq,integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ (compact_integrable (hf.comp (continuous_glueFamily B)))

omit [MeasurableSingletonClass A] in
theorem integral_pi_restriction (μ : Measure A) [IsProbabilityMeasure μ]
    (B : Set V) (f : (↥(Bᶜ) → A) → ℝ) (hf : Continuous f) :
    (∫ s,f (fun v : ↥(Bᶜ) => s v) ∂Measure.pi (fun _ : V => μ))=
      ∫ r,f r ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
  have hc : Continuous (fun s : V → A => f (fun v : ↥(Bᶜ) => s v)) :=
    hf.comp (continuous_pi (fun v => continuous_apply v.val))
  rw [integral_pi_split μ B _ hc]
  simp only [glueFamily_out]
  simp

end Measure
end ClassicalON

end

end OAI
