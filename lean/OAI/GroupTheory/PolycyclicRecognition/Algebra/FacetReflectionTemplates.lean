import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineFacetAgreement
import OAI.GroupTheory.PolycyclicRecognition.Analysis.InwardFacetSegment
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ReflectedSegmentSupport

namespace OAI

/-! # The actual reflected source and target templates

Starting from distinct finite affine labels agreeing near a facet, construct
an inward source segment and prove all the support identities in equation
(reflection-doubling) of `labels.tex`.
-/

noncomputable section
namespace PolycyclicRecognition

open Set

variable {W I B J : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B] [Fintype J]

theorem exists_reflection_templates
    (D : SupportDatum W I B) (A C : templateSymmetryGroup D) (hne : A ≠ C)
    (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (b₁ b₂ p : W)
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ) (hp : ∀ j, α j p ≤ c j)
    (hactive : ∀ j, α j p = c j → ∃ t : ℝ, 0 < t ∧ α j = t • ℓ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ → A.val q + b₁ = C.val q + b₂) :
    ∃ w : W, ℓ w < 0 ∧ C.val w = -A.val w ∧
      ((fun x => x + p) '' segment ℝ 0 w) ⊆ {x | ∀ j, α j x ≤ c j} ∧
      let E := (fun x => x + p) '' segment ℝ 0 w
      let E₁ := A.val '' segment ℝ 0 w
      let E₂ := C.val '' segment ℝ 0 w
      0 < D.templateSupport E ∧ D.templateSupport E₁ = D.templateSupport E ∧
        D.templateSupport E₂ = D.templateSupport E ∧
        D.templateSupport (E₁ ∪ E₂) = 2 * D.templateSupport E := by
  have hfix := linear_eq_on_kernel_of_affine_facet_agreement A.val.toLinearMap
    C.val.toLinearMap b₁ b₂ ℓ p hρ hagree
  obtain ⟨v, hv, href⟩ := exists_reflected_direction_of_finite_labels
    (templateSymmetryGroup D) A C hne ℓ hℓ hfix
  obtain ⟨ε, hε, hinside⟩ := exists_inward_facet_interval α c p v hp (by
    intro j hj
    obtain ⟨t, ht, he⟩ := hactive j hj
    rw [he, LinearMap.smul_apply, smul_eq_mul]
    exact (mul_pos ht hv).le)
  let w := -(ε • v)
  have hwℓ : ℓ w < 0 := by
    dsimp only [w]
    rw [map_neg, map_smul, smul_eq_mul]
    exact neg_neg_of_pos (mul_pos hε hv)
  have hw : w ≠ 0 := by
    intro he
    rw [he, map_zero] at hwℓ
    exact (lt_irrefl 0) hwℓ
  have hwref : C.val w = -A.val w := by
    simp [w, href]
  have hset : ((fun x => x + p) '' segment ℝ 0 w) ⊆
      {x | ∀ j, α j x ≤ c j} := by
    rintro x ⟨y, hy, rfl⟩ j
    rw [segment_eq_image] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have hte : t * ε ∈ Icc (0 : ℝ) ε :=
      ⟨mul_nonneg ht.1 hε.le, by nlinarith [ht.2]⟩
    have hh := hinside (t * ε) hte j
    convert hh using 1
    simp only [w, smul_zero, zero_add, smul_neg, smul_smul]
    abel_nf
  have hc : IsCompact (segment ℝ (0 : W) w) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hsource := D.templateSupport_translate hc ⟨0, left_mem_segment ..⟩ p
  rw [D.templateSupport_segment] at hsource
  obtain ⟨ha, hb, hu, hpos⟩ := D.reflected_segment_support A C hw hwref
  refine ⟨w, hwℓ, hwref, hset, ?_⟩
  simpa only [hsource] using And.intro hpos (And.intro ha (And.intro hb hu))

/-- Near a point with only parallel active constraints, the entire contact
hyperplane remains in the polyhedron. -/
theorem exists_relative_facet_neighborhood
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ) (p : W) (ℓ : W →ₗ[ℝ] ℝ)
    (hp : ∀ j, α j p ≤ c j)
    (hactive : ∀ j, α j p = c j → ∃ t : ℝ, 0 < t ∧ α j = t • ℓ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ →
      ∀ j, α j q ≤ c j := by
  have hevent (j : J) : ∀ᶠ q in nhds p,
      α j p ≠ c j → α j q < c j := by
    by_cases hj : α j p = c j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hj))
    · have hc := (α j).continuous_of_finiteDimensional
      filter_upwards [(isOpen_lt hc continuous_const).mem_nhds (lt_of_le_of_ne (hp j) hj)]
        with q hq
      exact fun _ => hq
  obtain ⟨ρ, hρ, hnear⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hevent)
  refine ⟨ρ, hρ, ?_⟩
  intro q hq hn j
  by_cases hj : α j p = c j
  · obtain ⟨t, _, ht⟩ := hactive j hj
    rw [ht, LinearMap.smul_apply, hq, ← LinearMap.smul_apply, ← ht, hj]
  · exact (hnear (by simpa only [dist_eq_norm] using hn) j hj).le

/-- The reflected source segment contradicts the support inequality obtained
from actual coupled bundles. This is the finite-dimensional last step. -/
theorem affine_labels_eq_of_template_comparison
    (D : SupportDatum W I B) (A C : templateSymmetryGroup D)
    (ℓ : W →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (b₁ b₂ p : W)
    (α : J → W →ₗ[ℝ] ℝ) (c : J → ℝ) (hp : ∀ j, α j p ≤ c j)
    (hactive : ∀ j, α j p = c j → ∃ t : ℝ, 0 < t ∧ α j = t • ℓ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hagree : ∀ q, ℓ q = ℓ p → ‖q - p‖ < ρ → A.val q + b₁ = C.val q + b₂)
    (hcompare : ∀ E : Set W, IsCompact E → Convex ℝ E →
      E ⊆ {x | ∀ j, α j x ≤ c j} → p ∈ E →
      D.templateSupport ((A.val '' ((fun x => x - p) '' E)) ∪
        (C.val '' ((fun x => x - p) '' E))) ≤ D.templateSupport E) : A = C := by
  by_contra hne
  obtain ⟨w, _, _, hinside, hpos, _, _, hdouble⟩ :=
    exists_reflection_templates D A C hne ℓ hℓ b₁ b₂ p α c hp hactive hρ hagree
  let E := (fun x => x + p) '' segment ℝ 0 w
  have hc : IsCompact (segment ℝ (0 : W) w) := by
    rw [segment_eq_image]
    exact isCompact_Icc.image ((continuous_const.sub continuous_id).smul continuous_const |>.add
      (continuous_id.smul continuous_const))
  have hE : IsCompact E := hc.image (continuous_id.add continuous_const)
  have hconv : Convex ℝ E := (convex_segment (0 : W) w).affine_image
    ((AffineMap.id ℝ W) + AffineMap.const ℝ W p)
  have hpE : p ∈ E := ⟨0, left_mem_segment .., zero_add p⟩
  have hsub : (fun x => x - p) '' E = segment ℝ 0 w := by
    ext x
    simp only [E, mem_image]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [add_sub_cancel_right] using hz
    · intro hx
      exact ⟨x + p, ⟨x, hx, rfl⟩, add_sub_cancel_right x p⟩
  have hle := hcompare E hE hconv hinside hpE
  rw [hsub, hdouble] at hle
  linarith

end PolycyclicRecognition

end

end OAI
