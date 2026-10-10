import OAI.Analysis.LipschitzHilbert.Phase.AngularAmplitudeIdentity

namespace OAI

/-! The nonempty eligible root cells of the actual translated grid.
They split the central packet sum exactly. A slope interval no wider
than one root contains at most two roots, including its endpoints. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ σ X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def sourceRootCells (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) : Finset ℤ :=
  (tops.filter (fun t => g.eligible cutoff (precision t) 0)).image
    (fun t => g.index 0 (slope t))

theorem mem_sourceRootCells (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (cell : ℤ) :
    cell ∈ g.sourceRootCells tops slope precision cutoff ↔
      (g.cellTops tops slope precision cutoff 0 cell).Nonempty := by
  constructor
  · rintro h
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
    exact ⟨t,(g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨ht,rfl,he⟩⟩
  · rintro ⟨t,ht⟩
    obtain ⟨ht,hindex,he⟩ := (g.mem_cellTops _ _ _ _ _ _ _).mp ht
    exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨ht,he⟩,hindex⟩

theorem sourceRootCells_card_le_two (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff start : ℝ)
    (hslope : ∀ t ∈ tops, start ≤ slope t ∧ slope t ≤ start+g.rootWidth) :
    (g.sourceRootCells tops slope precision cutoff).card ≤ 2 := by
  let left := ⌊(start-g.origin)/g.rootWidth⌋
  apply (Finset.card_le_card (t := {left,left+1}) ?_).trans Finset.card_le_two
  intro c hc
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc
  have ht' := (Finset.mem_filter.mp ht).1
  obtain ⟨hlo,hhi⟩ := hslope t ht'
  have hlo' : (start-g.origin)/g.rootWidth ≤ (slope t-g.origin)/g.rootWidth :=
    div_le_div_of_nonneg_right (by linarith) g.rootWidth_pos.le
  have hhi' : (slope t-g.origin)/g.rootWidth ≤ (start-g.origin)/g.rootWidth+1 := by
    apply (div_le_iff₀ g.rootWidth_pos).mpr
    rw [add_mul,div_mul_cancel₀ _ g.rootWidth_pos.ne',one_mul]
    linarith
  have h1 : left ≤ g.index 0 (slope t) := by
    simpa only [left,index,pow_zero,mul_one] using Int.floor_mono hlo'
  have h2 : g.index 0 (slope t) ≤ left+1 := by
    simpa only [left,index,pow_zero,mul_one,Int.floor_add_one] using Int.floor_mono hhi'
  simp only [Finset.mem_insert,Finset.mem_singleton]
  omega

theorem sourceRootCells_packet_cover (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s)) :
    ∀ s ∈ packets, g.index 0 (slope (assigned s)) ∈
      g.sourceRootCells tops slope precision cutoff := by
  intro s hs
  apply Finset.mem_image.mpr
  refine ⟨assigned s,Finset.mem_filter.mpr ⟨hassigned s hs,?_⟩,rfl⟩
  exact g.eligible_of_le (hp _ (hassigned s hs)) (Nat.zero_le _) (heligible s hs)

/-- The globally weighted central packet sum is the sum of its actual
nonempty eligible roots; no packet is assigned to an artificial root. -/
theorem sourceBoundarySum_root_decomposition (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ)
    (assigned : σ → τ) (stop : σ → ℕ) (value : σ → E)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (a : ℝ) (x : X) :
    (∑ s ∈ packets,
      ((g.sourceBoundaryCoefficient tops slope precision cutoff weight K gap
        (stop s) (assigned s) a x : ℝ):ℂ) • value s) =
    ∑ c ∈ g.sourceRootCells tops slope precision cutoff,
      ((g.mass tops slope precision cutoff weight 0 c x^a:ℝ):ℂ) •
        g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
          value (fun _ => (a:ℂ)) a x 0 c := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (g.sourceRootCells_packet_cover tops slope precision cutoff hp packets assigned stop
      hassigned heligible)]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [g.sourcePacketAmplitude_equal_coordinates tops slope precision cutoff weight hp hw hK
    gap packets assigned stop value hassigned heligible a x c]
  congr 1
  ext s
  simp only [packetSet,Finset.mem_filter,Nat.zero_le,and_true]

end LipschitzHilbert.AngularGrid

end

end OAI
