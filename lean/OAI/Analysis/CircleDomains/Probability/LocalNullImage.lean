import OAI.Analysis.CircleDomains.Probability.NullImage

namespace OAI

/-!
# Local null-image criterion

Restrict the connected-neighborhood oscillation argument to an open
region. Oscillation need only be controlled on connected open sets
inside that region; no behavior across its boundary is required.
-/

open Set MeasureTheory Metric

namespace CircleDomainRigidity

theorem null_image_inter_open_of_connected_open_oscillation
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyConnectedSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [μ.OuterRegular] {F V : Set X} (hV : IsOpen V) (hF : μ (F ∩ V) = 0)
    (v : X → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (hosc : ∀ U : Set X, U ⊆ V → IsOpen U → IsConnected U →
      ∀ x ∈ F ∩ U, ∀ y ∈ F ∩ U, |v x - v y| ≤ A * μ.real U) :
    volume (v '' (F ∩ V)) = 0 := by
  let ν : Measure V := μ.comap Subtype.val
  let : LocallyConnectedSpace V := hV.locallyConnectedSpace
  have hemb : MeasurableEmbedding (Subtype.val : V → X) :=
    MeasurableEmbedding.subtype_coe hV.measurableSet
  let : ν.OuterRegular := Measure.OuterRegular.comap' μ continuous_subtype_val hemb
  let Fv : Set V := Subtype.val ⁻¹' F
  have hnull : ν Fv = 0 := by
    rw [show ν Fv = μ (Subtype.val '' Fv) from hemb.comap_apply μ Fv]
    simpa only [Fv, Subtype.image_preimage_coe, inter_comm] using hF
  have hoscV : ∀ U : Set V, IsOpen U → IsConnected U →
      ∀ x ∈ Fv ∩ U, ∀ y ∈ Fv ∩ U,
        |v x.val - v y.val| ≤ A * ν.real U := by
    intro U hU hconn x hx y hy
    have hsub : Subtype.val '' U ⊆ V := by
      rintro _ ⟨z, _, rfl⟩
      exact z.property
    have hopen : IsOpen (Subtype.val '' U) := hV.isOpenMap_subtype_val U hU
    have hconnected : IsConnected (Subtype.val '' U) :=
      hconn.image Subtype.val continuous_subtype_val.continuousOn
    have hb := hosc _ hsub hopen hconnected x.val
      ⟨hx.1, x, hx.2, rfl⟩ y.val ⟨hy.1, y, hy.2, rfl⟩
    have hmeasure : ν.real U = μ.real (Subtype.val '' U) := by
      simp only [measureReal_def, ν, hemb.comap_apply]
    rwa [hmeasure]
  have hz := null_image_of_connected_open_oscillation hnull
    (fun x : V => v x.val) hA hoscV
  have himage : (fun x : V => v x.val) '' Fv = v '' (F ∩ V) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, ⟨hx, x.property⟩, rfl⟩
    · rintro ⟨x, ⟨hxF, hxV⟩, rfl⟩
      exact ⟨⟨x, hxV⟩, hxF, rfl⟩
  rwa [himage] at hz

end CircleDomainRigidity

end OAI
