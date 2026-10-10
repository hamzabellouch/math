import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolycyclicInvariantMean
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-! # Right finite expansions and metric Følner sets in the source group

Left-invariant metrics use right expansions of finite sets. Inversion
converts the left Følner sets supplied by an invariant mean into these sets.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped symmDiff

variable {G : Type*} [Group G] [DecidableEq G]

def rightFiniteExpansion (E S : Finset G) : Finset G :=
  S.biUnion (fun g => E.image (· * g))

theorem exists_small_rightExpansion (M : InvariantMean G) (S : Finset G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset G, E.Nonempty ∧
      ((rightFiniteExpansion E S \ E).card : ℝ) < ε * E.card := by
  obtain ⟨A, hA, hsmall⟩ := M.exists_folner_total (S.image Inv.inv) hε
  let E := A.image Inv.inv
  have hE : E.card = A.card := Finset.card_image_of_injective A inv_injective
  have hbound (g : G) : ((E.image (· * g) \ E).card : ℝ) ≤
      ((leftTranslate g⁻¹ A ∆ A).card : ℝ) := by
    have hs : (E.image (· * g) \ E).image Inv.inv ⊆ leftTranslate g⁻¹ A ∆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hy, hyE⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_symmDiff.mpr
      left
      refine ⟨?_, ?_⟩
      · apply Finset.mem_image.mpr
        exact ⟨a, ha, by simp⟩
      · intro hin
        apply hyE
        apply Finset.mem_image.mpr
        exact ⟨(a⁻¹ * g)⁻¹, hin, inv_inv _⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_image_of_injective _
      (inv_injective : Function.Injective (fun g : G => g⁻¹))] at hc
    exact_mod_cast hc
  have hs : rightFiniteExpansion E S \ E ⊆
      S.biUnion (fun g => E.image (· * g) \ E) := by
    intro x hx
    obtain ⟨hx, hxE⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_sdiff.mpr ⟨hxg, hxE⟩⟩
  have hcard : ((rightFiniteExpansion E S \ E).card : ℝ) ≤
      ∑ g ∈ S, ((E.image (· * g) \ E).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hs).trans Finset.card_biUnion_le
  have hsum : (∑ g ∈ S, ((leftTranslate g⁻¹ A ∆ A).card : ℝ)) < ε * E.card := by
    rw [hE]
    convert hsmall using 1
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact inv_injective hab
  exact ⟨E, hA.image Inv.inv, (hcard.trans (Finset.sum_le_sum (fun g _ => hbound g))).trans_lt hsum⟩

variable [MetricSpace G] [IsIsometricSMul G G]

/-- A source metric neighborhood is a right expansion by the finite identity
ball. This is the exact finite set used in the boundary estimate. -/
def finiteMetricNeighborhood (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (E : Finset G) (R : ℝ) : Finset G :=
  rightFiniteExpansion E ((hfinite R).toFinset)

theorem mem_finiteMetricNeighborhood
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (E : Finset G) (R : ℝ) (x : G) :
    x ∈ finiteMetricNeighborhood hfinite E R ↔ ∃ p ∈ E, dist x p ≤ R := by
  constructor
  · intro hx
    obtain ⟨g, hg, hxg⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hxg
    refine ⟨p, hp, ?_⟩
    have hg' : dist g 1 ≤ R := (hfinite R).mem_toFinset.mp hg
    simpa only [mul_one] using (dist_mul_left p g (1 : G)).trans_le hg'
  · rintro ⟨p, hp, hd⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p⁻¹ * x, (hfinite R).mem_toFinset.mpr ?_, ?_⟩
    · change dist (p⁻¹ * x) 1 ≤ R
      have he : dist (p⁻¹ * x) 1 = dist x p := by
        simpa only [mul_one, mul_inv_cancel_left] using
          (dist_mul_left p (p⁻¹ * x) (1 : G)).symm
      rw [he]
      exact hd
    · exact Finset.mem_image.mpr ⟨p, hp, mul_inv_cancel_left p x⟩

omit [IsIsometricSMul G G] in
theorem exists_small_metricNeighborhood (M : InvariantMean G)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : G) R).Finite)
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ E : Finset G, E.Nonempty ∧
      ((finiteMetricNeighborhood hfinite E R \ E).card : ℝ) < ε * E.card :=
  exists_small_rightExpansion M _ hε

end PolycyclicRecognition

end

end OAI
