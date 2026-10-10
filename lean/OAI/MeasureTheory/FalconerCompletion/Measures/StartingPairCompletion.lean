import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.StartingPairFiltersTransport
import OAI.MeasureTheory.FalconerCompletion.Measures.NormalizedStartingPairCompletion

namespace OAI

/-! Measures and the conditional distance-set completion. -/

section

namespace CurrentFalconer.AssemblyCompletion
open Set Metric MeasureTheory Filter
open scoped ENNReal

theorem starting_pair_completion
    (n : ℕ) (hn : 1≤n) (E E₁ E₂ : Set (Space n))
    (hE : IsCompact E) (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂)
    (hs₁ : E₁⊆E) (hs₂ : E₂⊆E)
    (μ ν : Measure (Space n)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ E₁ᶜ=0) (hν : ν E₂ᶜ=0)
    (δ D : ℝ) (hδ : 0<δ) (hD : 0<D)
    (hsep : ∀ x∈E₁, ∀ y∈E₂, δ≤dist x y ∧ dist x y≤D)
    (w₀ : Space n) (hw₀ : ‖w₀‖=1)
    (hpatch : ∀ x∈E₁, ∀ y∈E₂, ‖direction x y-w₀‖≤1/100)
    (chi C : ℝ) (hchi : 0<chi) (hC : 0≤C)
    (hball₁ : ∀ x : Space n, ∀ r>0, μ (ball x r)≤ENNReal.ofReal (C*r^((n+1:ℝ)/2+chi)))
    (hball₂ : ∀ x : Space n, ∀ r>0, ν (ball x r)≤ENNReal.ofReal (C*r^((n+1:ℝ)/2+chi)))
    (hfilters : StartingPairFilters n μ ν E₁ E₂) :
    (∃ α : Measure ℝ, IsFiniteMeasure α ∧ 0<α univ ∧ α≪volume ∧ α (originalDistances E)ᶜ=0) ∧
      0<volume (originalDistances E)
 := by
  classical
  obtain ⟨a,ha,b,hroot⟩ := exists_root_similarity E hE
  let f := pairSimilarity a ha.ne' b
  let μ' := μ.map f
  let ν' := ν.map f
  have : IsProbabilityMeasure μ' := inferInstance
  have : IsProbabilityMeasure ν' := inferInstance
  have mapf (ρ : Measure (Space n)) (S : Set (Space n)) :
      (ρ.map f) S=ρ (f ⁻¹' S) := f.toMeasurableEquiv.map_apply S
  have hμ' : μ' (f '' E₁)ᶜ=0 := by
    change (μ.map f) (f '' E₁)ᶜ=0
    rw [mapf,preimage_compl,f.injective.preimage_image]
    exact hμ
  have hν' : ν' (f '' E₂)ᶜ=0 := by
    change (ν.map f) (f '' E₂)ᶜ=0
    rw [mapf,preimage_compl,f.injective.preimage_image]
    exact hν
  have hroot' : ∀ x∈(f '' E₁)∪(f '' E₂), ∀ i, 0≤x i ∧ x i<1 := by
    intro x hx i
    rcases hx with hx | hx
    · obtain ⟨x,hx,rfl⟩ := hx
      exact hroot x (hs₁ hx) i
    · obtain ⟨x,hx,rfl⟩ := hx
      exact hroot x (hs₂ hx) i
  have hsep' : ∀ x∈f '' E₁, ∀ y∈f '' E₂, a*δ≤dist x y ∧ dist x y≤a*D := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [pairSimilarity_dist a ha b]
    exact ⟨mul_le_mul_of_nonneg_left (hsep x hx y hy).1 ha.le,
      mul_le_mul_of_nonneg_left (hsep x hx y hy).2 ha.le⟩
  have hpatch' : ∀ x∈f '' E₁, ∀ y∈f '' E₂, ‖direction x y-w₀‖≤1/100 := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    rw [pairSimilarity_direction a ha b]
    exact hpatch x hx y hy
  have hfilters' := startingPairFilters_transport f (pairSimilarity_direction a ha b) μ ν E₁ E₂ hfilters
  obtain ⟨⟨α,hαfinite,hαpos,hαac,hαcar⟩,_⟩ := normalized_starting_pair_completion n hn
    (f '' E) (f '' E₁) (f '' E₂) (hE.image f.continuous) (hE₁.image f.continuous)
    (hE₂.image f.continuous) (image_mono hs₁) (image_mono hs₂) μ' ν' hμ' hν' hroot'
    (a*δ) (a*D) (mul_pos ha hδ) (mul_pos ha hD) hsep' w₀ hw₀ hpatch' chi
    (C*a^(-((n+1:ℝ)/2+chi))) hchi (mul_nonneg hC (Real.rpow_nonneg ha.le _))
    (similarity_ball_bound a ha b μ _ C hC hball₁)
    (similarity_ball_bound a ha b ν _ C hC hball₂) hfilters'
  let : IsFiniteMeasure α := hαfinite
  let g : ℝ → ℝ := fun r=>a⁻¹*r
  have hg : Measurable g := measurable_const.mul measurable_id
  let β := α.map g
  have : IsFiniteMeasure β := inferInstance
  have hβpos : 0<β univ := by
    simpa only [β,Measure.map_apply hg MeasurableSet.univ,preimage_univ] using hαpos
  have hβac : β≪volume := by
    apply (hαac.map hg).trans
    exact (Measure.quasiMeasurePreserving_smul (volume:Measure ℝ) (inv_ne_zero ha.ne')).2
  have hcompact : IsCompact (originalDistances E) := AssemblyLimit.distanceSet_compact hE
  have hβcar : β (originalDistances E)ᶜ=0 := by
    rw [show β (originalDistances E)ᶜ=α (g ⁻¹' (originalDistances E)ᶜ) from
      Measure.map_apply hg hcompact.measurableSet.compl]
    apply measure_mono_null _ hαcar
    intro r hr hrd
    apply hr
    obtain ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,hxy⟩ := hrd
    refine ⟨x,hx,y,hy,?_⟩
    rw [pairSimilarity_dist a ha b] at hxy
    dsimp [g]
    rw [←hxy]
    field_simp
  refine ⟨⟨β,inferInstance,hβpos,hβac,hβcar⟩,?_⟩
  by_contra hnot
  have hz : volume (originalDistances E)=0 := le_antisymm (le_of_not_gt hnot) bot_le
  have hnull : β (originalDistances E)=0 := hβac hz
  have hu := measure_union_le (μ:=β) (originalDistances E) (originalDistances E)ᶜ
  rw [union_compl_self,hnull,hβcar,zero_add] at hu
  exact hβpos.not_ge hu

end CurrentFalconer.AssemblyCompletion
end

namespace Falconer

open MeasureTheory Metric Set
open scoped ENNReal

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def distanceSet {d : ℕ} (E : Set (Space d)) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

theorem distanceSet_eq_norm_sub {d : ℕ} (E : Set (Space d)) :
    distanceSet E = {r | ∃ x ∈ E, ∃ y ∈ E, ‖x - y‖ = r} := by
  simp only [distanceSet, dist_eq_norm]

theorem distanceSet_eq_image {d : ℕ} (E : Set (Space d)) :
    distanceSet E = (fun z : Space d × Space d => dist z.1 z.2) '' (E ×ˢ E) := by
  ext r
  constructor
  · rintro ⟨x, hx, y, hy, hr⟩
    exact ⟨(x, y), ⟨hx, hy⟩, hr⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hr⟩
    exact ⟨x, hx, y, hy, hr⟩

theorem distanceSet_isCompact {d : ℕ} {E : Set (Space d)} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  rw [distanceSet_eq_image]
  exact (hE.prod hE).image (continuous_fst.dist continuous_snd)

theorem distanceSet_measurable {d : ℕ} {E : Set (Space d)} (hE : IsCompact E) :
    MeasurableSet (distanceSet E) := (distanceSet_isCompact hE).measurableSet

theorem distanceSet_positive_of_carried_ac_measure {d : ℕ} (E : Set (Space d))
    (α : Measure ℝ) (hpos : 0 < α univ) (hac : α ≪ volume)
    (hcarried : α (distanceSet E)ᶜ = 0) :
    0 < volume (distanceSet E) := by
  by_contra h
  have hnull : volume (distanceSet E) = 0 := le_antisymm (le_of_not_gt h) bot_le
  have hu := measure_union_le (μ := α) (distanceSet E) (distanceSet E)ᶜ
  rw [union_compl_self, hac hnull, hcarried, zero_add] at hu
  exact hpos.not_ge hu

end Falconer

namespace Falconer

open MeasureTheory Metric Set
open scoped ENNReal

theorem distanceSet_eq_assembly {n : ℕ} (E : Set (Space (n + 1))) :
    distanceSet E = CurrentFalconer.AssemblyCompletion.originalDistances E := rfl

theorem distanceSet_positive_of_starting_pair
    (n : ℕ) (hn : 1 ≤ n) (E E₁ E₂ : Set (Space (n + 1)))
    (hE : IsCompact E) (hE₁ : IsCompact E₁) (hE₂ : IsCompact E₂)
    (hs₁ : E₁ ⊆ E) (hs₂ : E₂ ⊆ E)
    (μ ν : Measure (Space (n + 1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ E₁ᶜ = 0) (hν : ν E₂ᶜ = 0)
    (δ D : ℝ) (hδ : 0 < δ) (hD : 0 < D)
    (hsep : ∀ x ∈ E₁, ∀ y ∈ E₂, δ ≤ dist x y ∧ dist x y ≤ D)
    (w₀ : Space (n + 1)) (hw₀ : ‖w₀‖ = 1)
    (hpatch : ∀ x ∈ E₁, ∀ y ∈ E₂,
      ‖CurrentFalconer.AssemblyCompletion.direction x y - w₀‖ ≤ 1 / 100)
    (chi C : ℝ) (hchi : 0 < chi) (hC : 0 ≤ C)
    (hball₁ : ∀ x : Space (n + 1), ∀ r > 0,
      μ (ball x r) ≤ ENNReal.ofReal (C * r ^ ((n + 1 : ℝ) / 2 + chi)))
    (hball₂ : ∀ x : Space (n + 1), ∀ r > 0,
      ν (ball x r) ≤ ENNReal.ofReal (C * r ^ ((n + 1 : ℝ) / 2 + chi)))
    (hfilters : CurrentFalconer.AssemblyCompletion.StartingPairFilters n μ ν E₁ E₂) :
    0 < volume (distanceSet E) := by
  obtain ⟨⟨α, _hfinite, hpos, hac, hcarried⟩, _⟩ :=
    CurrentFalconer.AssemblyCompletion.starting_pair_completion n hn E E₁ E₂
      hE hE₁ hE₂ hs₁ hs₂ μ ν hμ hν δ D hδ hD hsep w₀ hw₀ hpatch
      chi C hchi hC hball₁ hball₂ hfilters
  apply distanceSet_positive_of_carried_ac_measure E α hpos hac
  simpa only [distanceSet_eq_assembly] using hcarried

end Falconer

end OAI
