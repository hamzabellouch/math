import OAI.MeasureTheory.Falconer.Graphs.CommonRowNormalization

namespace OAI

/-! Assemble the common-row rounding into actual pencil families. The
pencil cardinality drops by at most 361, and the complete union grows by
at most 361. No separation assumption is needed on the original union. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def normalizedPencil (δ : ℝ) (p : Space 2) (S : Finset (Space 2)) :
    Finset (Space 2) := (S.image (rowAdjustedLine δ p)).image planarQuarter

noncomputable def normalizedRowPencils (δ : ℝ) (T : Space 2 → Finset (Space 2))
    (p : Space 2) : Finset (Space 2) :=
  normalizedPencil δ (verticalFour p) (T (verticalFour p))

theorem normalizedPencil_card_upper (δ : ℝ) (p : Space 2) (S : Finset (Space 2)) :
    (normalizedPencil δ p S).card ≤ S.card :=
  Finset.card_image_le.trans Finset.card_image_le

theorem normalizedPencil_card_lower {δ : ℝ} (hδ : 0 < δ)
    (p : Space 2) (S : Finset (Space 2)) (hp : |p 0| ≤ 1)
    (hsep : FiniteSeparatedAt δ S)
    (hS : ∀ l ∈ S, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    (S.card:ℝ) ≤ 361*((normalizedPencil δ p S).card:ℝ) := by
  unfold normalizedPencil
  rw [Finset.card_image_of_injective _ planarQuarter_injective]
  exact rowAdjustedLine_pencil_card hδ p S hp hsep hS

theorem normalizedPencil_nonempty {δ : ℝ} (p : Space 2) {S : Finset (Space 2)}
    (hS : S.Nonempty) : (normalizedPencil δ p S).Nonempty :=
  (hS.image _).image _

theorem normalizedPencil_incident {δ : ℝ} (hδ : 0 < δ)
    (p : Space 2) (S : Finset (Space 2)) :
    ∀ l ∈ normalizedPencil δ p S, TubeIncident (δ/4) (verticalQuarter p) l := by
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp ha
  exact quarter_adjusted_incident hδ p m

theorem normalizedPencil_chart {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/8)
    (p : Space 2) (S : Finset (Space 2)) (hp : |p 0| ≤ 1)
    (hchart : InBoundedLineChart S) (hi : ∀ l ∈ S, TubeIncident (3*δ) p l) :
    InBoundedLineChart (normalizedPencil δ p S) := by
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp ha
  exact quarter_adjusted_chart hδ hδsmall p m hp (hchart m hm) (hi m hm)

theorem normalizedPencil_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (p : Space 2) (S : Finset (Space 2))
    (hp : |p 0| ≤ 1) (hsep : FiniteSeparatedAt δ S)
    (hchart : InBoundedLineChart S) (hi : ∀ l ∈ S, TubeIncident (3*δ) p l)
    (hreg : NormalizedFiniteBallBound δ s K S) :
    NormalizedFiniteBallBound (δ/4) s ((361*K*(10:ℝ)^s)*(4:ℝ)^s)
      (normalizedPencil δ p S) := by
  have hpow : 1 ≤ (10:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have hcost : 1 ≤ 361*K*(10:ℝ)^s := by
    have hh := mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
    nlinarith only [hh]
  apply planarQuarter_regular hδ hs hcost
  exact rowAdjustedLine_pencil_regular hδ hs hK p S hp hsep
    (fun l hl => ⟨(hchart l hl).1,hi l hl⟩) hreg

theorem normalizedRowPencils_union (δ : ℝ) (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) :
    (P.image verticalQuarter).biUnion (normalizedRowPencils δ T) =
      (P.biUnion fun p => (T p).image (rowAdjustedLine δ p)).image planarQuarter := by
  simp only [Finset.image_biUnion,normalizedRowPencils,verticalFour_verticalQuarter,
    normalizedPencil,Finset.biUnion_image]

theorem normalizedRowPencils_union_separated {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    FiniteSeparatedAt (δ/4) ((P.image verticalQuarter).biUnion (normalizedRowPencils δ T)) := by
  rw [normalizedRowPencils_union]
  exact planarQuarter_separated _ (rowAdjustedLine_family_separated hδ P T)

theorem normalizedRowPencils_union_card {δ : ℝ} (hδ : 0 < δ)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hp : ∀ p ∈ P, |p 0| ≤ 1)
    (hT : ∀ p ∈ P, ∀ l ∈ T p, |l 0| ≤ 1 ∧ TubeIncident (3*δ) p l) :
    (((P.image verticalQuarter).biUnion (normalizedRowPencils δ T)).card:ℝ) ≤
      361*((P.biUnion T).card:ℝ) := by
  rw [normalizedRowPencils_union,Finset.card_image_of_injective _ planarQuarter_injective]
  exact rowAdjustedLine_family_card hδ P T hp hT

end Falconer

end OAI
