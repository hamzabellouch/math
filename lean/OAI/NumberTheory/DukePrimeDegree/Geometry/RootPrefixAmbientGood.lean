import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixRestrictions

namespace OAI

/-! # One ambient exceptional set for countably many prefix charts -/

noncomputable section
open MeasureTheory Set
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
    {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
    {Pfx : RootPrefixCoordinates n P T} {c : EliminationChain P D}
    {hP : InitialRootPattern P} {hf : c.finalEntries = allPositiveRoots n} {g : G n}

theorem ae_ambient_forall_coordinates (B : RootPrefixBox Pfx c hP hf g)
    (μ : Measure (X n)) {Q : (UpperRootTransverse n × T) × c.Time → Prop}
    (hQ : ∀ᵐ z ∂B.coordinateMeasure μ, Q z) :
    ∀ᵐ x ∂μ, ∀ z ∈ B.domain, Pfx.timeParam c hP hf g z = x → Q z := by
  have hsub : ∀ᵐ z ∂μ.comap B.param, Q z.val :=
    ae_of_ae_map measurable_subtype_coe.aemeasurable hQ
  have hmap : ∀ᵐ x ∂(μ.comap B.param).map B.param,
      ∀ z ∈ B.domain, Pfx.timeParam c hP hf g z = x → Q z := by
    apply B.embedding.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hsub] with z hz
    intro w hw he
    have heq : (⟨w,hw⟩ : B.domain) = z := B.embedding.injective he
    have hwz : w = z.val := congrArg Subtype.val heq
    exact hwz.symm ▸ hz
  rw [B.embedding.measurableEmbedding.map_comap] at hmap
  have H := (ae_restrict_iff' B.range_open.measurableSet).mp hmap
  filter_upwards [H] with x hx
  intro z hz he
  exact hx ⟨⟨z,hz⟩,he⟩ z hz he

theorem ae_ambient_forall_family
    (F : Set (RootPrefixBox Pfx c hP hf g)) (hF : F.Countable)
    (μ : Measure (X n))
    (Q : RootPrefixBox Pfx c hP hf g → (UpperRootTransverse n × T) × c.Time → Prop)
    (hQ : ∀ B ∈ F, ∀ᵐ z ∂B.coordinateMeasure μ, Q B z) :
    ∀ᵐ x ∂μ, ∀ B ∈ F, ∀ z ∈ B.domain,
      Pfx.timeParam c hP hf g z = x → Q B z := by
  have H := (ae_ball_iff hF).mpr (fun B hB => B.ae_ambient_forall_coordinates μ (hQ B hB))
  exact H

end RootPrefixBox
end DukePrimeDegree

end

end OAI
