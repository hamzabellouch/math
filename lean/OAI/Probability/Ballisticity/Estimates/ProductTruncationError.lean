import Mathlib
import OAI.Probability.Ballisticity.Geometry.SignedStripTruncation

namespace OAI

section

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DirectionalTransience

lemma product_submeasure_error {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure ν₂]
    (h₁ : ν₁ ≤ μ₁) (h₂ : ν₂ ≤ μ₂) (ht₁ : μ₁ Set.univ ≤ 1) (ht₂ : μ₂ Set.univ ≤ 1)
    {ε₁ ε₂ : ℝ≥0∞}
    (he₁ : μ₁ Set.univ ≤ ν₁ Set.univ+ε₁) (he₂ : μ₂ Set.univ ≤ ν₂ Set.univ+ε₂)
    (S : Set (α × β)) :
    μ₁.prod μ₂ S ≤ ν₁.prod ν₂ S+ε₁+ε₂ := by
  let δ₁ := μ₁-ν₁
  let δ₂ := μ₂-ν₂
  have hd₁ : δ₁+ν₁=μ₁ := Measure.sub_add_cancel_of_le h₁
  have hd₂ : δ₂+ν₂=μ₂ := Measure.sub_add_cancel_of_le h₂
  have hδ₁ : δ₁ Set.univ ≤ ε₁ := by
    rw [show δ₁ = μ₁-ν₁ from rfl,Measure.sub_apply MeasurableSet.univ h₁]
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using he₁)
  have hδ₂ : δ₂ Set.univ ≤ ε₂ := by
    rw [show δ₂ = μ₂-ν₂ from rfl,Measure.sub_apply MeasurableSet.univ h₂]
    exact tsub_le_iff_right.mpr (by simpa only [add_comm] using he₂)
  have hν₁ : ν₁ Set.univ ≤ 1 := (h₁ Set.univ).trans ht₁
  have hp₁ : δ₁.prod μ₂ S ≤ ε₁ := by
    calc
      _ ≤ δ₁.prod μ₂ Set.univ := measure_mono (Set.subset_univ _)
      _ = δ₁ Set.univ*μ₂ Set.univ := by rw [←Set.univ_prod_univ,Measure.prod_prod]
      _ ≤ ε₁*1 := mul_le_mul' hδ₁ ht₂
      _ = ε₁ := mul_one _
  have hp₂ : ν₁.prod δ₂ S ≤ ε₂ := by
    calc
      _ ≤ ν₁.prod δ₂ Set.univ := measure_mono (Set.subset_univ _)
      _ = ν₁ Set.univ*δ₂ Set.univ := by rw [←Set.univ_prod_univ,Measure.prod_prod]
      _ ≤ 1*ε₂ := mul_le_mul' hν₁ hδ₂
      _ = ε₂ := one_mul _
  calc
    μ₁.prod μ₂ S = δ₁.prod μ₂ S+ν₁.prod μ₂ S := by rw [←hd₁,Measure.add_prod,Measure.add_apply]
    _ = δ₁.prod μ₂ S+(ν₁.prod δ₂ S+ν₁.prod ν₂ S) := by
      congr 1
      rw [←hd₂,Measure.prod_add,Measure.add_apply]
    _ ≤ ε₁+(ε₂+ν₁.prod ν₂ S) := add_le_add hp₁ (add_le_add hp₂ le_rfl)
    _ = ν₁.prod ν₂ S+ε₁+ε₂ := by ac_rfl
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma rawPairEndpointLaw_truncation {d : ℕ} (ω : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) (k : ℕ) (S : Set (Lattice d × Lattice d)) :
    rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
      (truncatedEndpointLaw e H (k*H) ω x.1).prod (truncatedEndpointLaw e H (k*H) ω x.2) S+
      (1-(κ:ℝ≥0∞)^H)^k+(1-(κ:ℝ≥0∞)^H)^k := by
  let (y : Lattice d) : IsFiniteMeasure (hitKernel (Strip (realPosition (step e)) y H) (Upper (realPosition (step e)) y H) (ω,y)) :=
    ⟨lt_of_le_of_lt (hitKernel_total_le_one (disjoint_strip_upper _ _ _) _) ENNReal.one_lt_top⟩
  apply product_submeasure_error
  · exact truncatedEndpointLaw_le e hH _ _ _
  · exact truncatedEndpointLaw_le e hH _ _ _
  · exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _
  · exact hitKernel_total_le_one (disjoint_strip_upper _ _ _) _
  · exact truncatedEndpointLaw_mass_error ω hκ e x.1 hH k
  · exact truncatedEndpointLaw_mass_error ω hκ e x.2 hH k

lemma rawPairEndpointLaw_compare {d : ℕ} (ω η : Environment d) {κ : ℝ≥0}
    (hκ : ∀ y e, κ ≤ (ω y).1 e) (e : Direction d) (x : Lattice d × Lattice d)
    {H : ℕ} (hH : 0 < H) (k : ℕ)
    (he : Set.EqOn ω η (LatticeBall x.1 (k*H) ∪ LatticeBall x.2 (k*H)))
    (S : Set (Lattice d × Lattice d)) :
    rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
      rawPairEndpointLaw (realPosition (step e)) H η x S+
      (1-(κ:ℝ≥0∞)^H)^k+(1-(κ:ℝ≥0∞)^H)^k := by
  have ht := rawPairEndpointLaw_truncation ω hκ e x hH k S
  rw [truncatedEndpointLaw_locality e hH _ ω η x.1 (he.mono Set.subset_union_left),
    truncatedEndpointLaw_locality e hH _ ω η x.2 (he.mono Set.subset_union_right)] at ht
  exact ht.trans (add_le_add (add_le_add
    ((Measure.prod_mono (truncatedEndpointLaw_le e hH _ _ _) (truncatedEndpointLaw_le e hH _ _ _)) S) le_rfl) le_rfl)

lemma rawPairEndpointLaw_uniform_locality {d : ℕ} {κ : ℝ≥0} (hκ : 0 < κ)
    (e : Direction d) {H : ℕ} (hH : 0 < H) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (ω η : Environment d),
      (∀ y g, κ ≤ (ω y).1 g) → (∀ y g, κ ≤ (η y).1 g) →
      ∀ x : Lattice d × Lattice d,
      Set.EqOn ω η (LatticeBall x.1 N ∪ LatticeBall x.2 N) →
      ∀ S : Set (Lattice d × Lattice d),
      rawPairEndpointLaw (realPosition (step e)) H ω x S ≤
        rawPairEndpointLaw (realPosition (step e)) H η x S+ε ∧
      rawPairEndpointLaw (realPosition (step e)) H η x S ≤
        rawPairEndpointLaw (realPosition (step e)) H ω x S+ε := by
  have hc : 1-(κ:ℝ≥0∞)^H < 1 :=
    ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (pow_ne_zero _ (by exact_mod_cast hκ.ne'))
  have heps : 0 < ε/2 := ENNReal.div_pos_iff.mpr ⟨hε.ne',by norm_num⟩
  obtain ⟨k,hk⟩ := ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hc).eventually_lt_const heps).exists
  have hs : (1-(κ:ℝ≥0∞)^H)^k+(1-(κ:ℝ≥0∞)^H)^k ≤ ε := by
    calc
      _ ≤ ε/2+ε/2 := add_le_add hk.le hk.le
      _ = ε := ENNReal.add_halves ε
  refine ⟨k*H,?_⟩
  intro ω η hω hη x he S
  constructor
  · exact (rawPairEndpointLaw_compare ω η hω e x hH k he S).trans
      (by simpa only [add_assoc] using add_le_add_right hs (rawPairEndpointLaw (realPosition (step e)) H η x S))
  · exact (rawPairEndpointLaw_compare η ω hη e x hH k he.symm S).trans
      (by simpa only [add_assoc] using add_le_add_right hs (rawPairEndpointLaw (realPosition (step e)) H ω x S))
end DirectionalTransience

end

end

end OAI
