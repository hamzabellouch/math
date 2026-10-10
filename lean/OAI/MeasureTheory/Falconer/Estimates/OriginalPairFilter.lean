import OAI.MeasureTheory.Falconer.Measures.SupportPairFilter
import OAI.MeasureTheory.Falconer.Angular.CapTransport

namespace OAI

/-! # Lift the auxiliary filters to the original pair law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

noncomputable def liftedPairFilter (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) (Γ : ℕ → Set (Space k × Space k))
    (N : ℕ) : Set (Space d × Space d) :=
  supportPair μ ν ∩ Prod.map P P ⁻¹' Γ N

theorem liftedPairFilter_measurable (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)}
    (hΓ : ∀ N, MeasurableSet (Γ N)) (N : ℕ) :
    MeasurableSet (liftedPairFilter μ ν P Γ N) :=
  (supportPair_measurable μ ν).inter ((hΓ N).preimage
    (P.continuous.measurable.prodMap P.continuous.measurable))

theorem liftedPairFilter_antitone (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)}
    (hΓ : Antitone Γ) : Antitone (liftedPairFilter μ ν P Γ) := by
  intro N M hNM z hz
  exact ⟨hz.1,hΓ hNM hz.2⟩

theorem liftedPairFilter_limit_mass (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)}
    (hΓ : ∀ N, MeasurableSet (Γ N)) :
    ((μ : Measure (Space d)).prod (ν : Measure (Space d)))
      (⋂ N, liftedPairFilter μ ν P Γ N) =
    (((μ.map P : ProbabilityMeasure (Space k)) : Measure (Space k)).prod
      (ν.map P : Measure (Space k))) (⋂ N, Γ N) := by
  have heq : (⋂ N, liftedPairFilter μ ν P Γ N) =
      (Prod.map P P ⁻¹' (⋂ N, Γ N)) ∩ supportPair μ ν := by
    ext z
    simp only [liftedPairFilter,mem_iInter,mem_inter_iff,mem_preimage]
    exact ⟨fun h => ⟨fun N => (h N).2,(h 0).1⟩,fun h N => ⟨h.2,h.1 N⟩⟩
  rw [heq,supportPair_inter_mass]
  change _ = (((μ : Measure (Space d)).map P).prod ((ν : Measure (Space d)).map P)) _
  rw [Measure.map_prod_map _ _ P.continuous.measurable P.continuous.measurable,
    Measure.map_apply (P.continuous.measurable.prodMap P.continuous.measurable)
      (MeasurableSet.iInter hΓ)]

theorem CapAvailable.lift_original_pair (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) {Γ : ℕ → Set (Space k × Space k)} {c q : ℝ}
    (hc : 0 < c) (hP : ‖P‖ ≤ 1) (hq : 0 ≤ q)
    (hΓ : ∀ N, MeasurableSet (Γ N))
    (hlower : ∀ x ∈ (μ : Measure (Space d)).support,
      ∀ y ∈ (ν : Measure (Space d)).support,
      c ≤ ‖P (radialDirection x y)‖ ∧ c ≤ ‖P (radialDirection y x)‖)
    (hcap : CapAvailable (μ.map P) (ν.map P) Γ q) :
    CapAvailable μ ν (liftedPairFilter μ ν P Γ) q := by
  apply hcap.pullback P μ ν hc hP hq (liftedPairFilter_measurable μ ν P hΓ)
    (fun _ => inter_subset_right)
  intro N z hz
  exact hlower z.1 hz.1.1 z.2 hz.1.2

theorem liftedPairFilter_union_products {ι : Type*} (μ ν : ProbabilityMeasure (Space d))
    (P : Space d →L[ℝ] Space k) (A B : ι → Set (Space k))
    (Γ : ℕ → Set (Space k × Space k)) (N : ℕ)
    (hΓ : Γ N = ⋃ i, A i ×ˢ B i) :
    liftedPairFilter μ ν P Γ N = ⋃ i,
      ((μ : Measure (Space d)).support ∩ P ⁻¹' A i) ×ˢ
        ((ν : Measure (Space d)).support ∩ P ⁻¹' B i) := by
  ext z
  simp only [liftedPairFilter,hΓ,supportPair,mem_inter_iff,mem_preimage,
    mem_iUnion,mem_prod]
  constructor
  · rintro ⟨⟨hx,hy⟩,i,hA,hB⟩
    exact ⟨i,⟨hx,hA⟩,hy,hB⟩
  · rintro ⟨i,⟨hx,hA⟩,hy,hB⟩
    exact ⟨⟨hx,hy⟩,i,hA,hB⟩

end Falconer

end OAI
