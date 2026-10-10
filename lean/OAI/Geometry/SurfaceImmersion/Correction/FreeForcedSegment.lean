import OAI.Geometry.SurfaceImmersion.Geometry.LowJetSegment
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledNonlinearBounds

namespace OAI

/-! The free and forced size estimates keep the whole Taylor segment in
one compact low-jet domain, with uniform bounds at every required order. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma free_forced_size {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    {τ δ A B : ℝ} {m : ℕ} (hτ : 0 < τ) (hδ : 0 ≤ δ) (hδτ : δ ≤ τ) (hB : 0 ≤ B)
    (hXb : WeightedBound Set.univ τ m (A * δ * τ) X)
    (hYb : WeightedBound Set.univ τ m (B * δ ^ 2) Y) :
    WeightedBound Set.univ τ m ((A + B) * δ * τ) (X + Y) := by
  have hb := hXb.add isOpen_univ.uniqueDiffOn hτ.le hX.contDiffOn hY.contDiffOn hYb
  apply hb.mono_const
  calc
    _ ≤ A * δ * τ + B * (δ * τ) := by
      gcongr
      nlinarith
    _ = _ := by ring

lemma free_forced_lowJet_bounds {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} {X Y : RealModes.RField 4}
    (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y)
    {τ δ A B B₀ : ℝ} {m : ℕ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hδ : 0 ≤ δ) (hδτ : δ ≤ τ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hGb : WeightedBound U τ m B₀ (lowJet G))
    (hXb : WeightedBound Set.univ τ (m + 2) (A * δ * τ) X)
    (hYb : WeightedBound Set.univ τ (m + 2) (B * δ ^ 2) Y) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, WeightedBound U τ m (B₀ + A + B)
      (lowJet (fun p => G p + t • (X + Y) (planeCoordinateIsometry p))) := by
  have hs := free_forced_size hX hY hτ hδ hδτ hB hXb hYb
  have hsource := (weightedBound_comp_isometry planeCoordinateIsometry (hX.add hY) hs).restrict_open hU
  intro t ht
  have hb := lowJet_segment_bound hU hG ((hX.add hY).comp planeCoordinateIsometry.contDiff)
    hτ hτ1 (by positivity : 0 ≤ (A + B) * δ * τ) hGb hsource ht
  apply hb.mono_const
  have he : (A + B) * δ * τ / τ ^ 2 = (A + B) * (δ / τ) := by field_simp
  rw [he]
  have hratio : δ / τ ≤ 1 := (div_le_one hτ).2 hδτ
  have hh := mul_le_of_le_one_right (add_nonneg hA hB) hratio
  linarith

theorem free_forced_segment_margin {Q O : Set LowJet}
    (hQ : IsCompact Q) (hO : IsOpen O) (hQO : Q ⊆ O) :
    ∃ (ρ : ℝ) (Q' : Set LowJet), 0 < ρ ∧ IsCompact Q' ∧ Q ⊆ Q' ∧ Q' ⊆ O ∧
      ∀ {U : Set Base}, IsOpen U → ∀ {G : Base → Space} {X Y : RealModes.RField 4},
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y → Set.MapsTo (lowJet G) U Q →
      ∀ {τ δ A B : ℝ}, 0 < τ → τ ≤ 1 → 0 ≤ δ → δ ≤ τ → 0 ≤ A → 0 ≤ B →
      (A + B) * (δ / τ) ≤ ρ →
      WeightedBound Set.univ τ 2 (A * δ * τ) X →
      WeightedBound Set.univ τ 2 (B * δ ^ 2) Y →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, Set.MapsTo
        (lowJet (fun p => G p + t • (X + Y) (planeCoordinateIsometry p))) U Q' := by
  obtain ⟨ρ,Q',hρ,hQ',hQQ',hQ'O,hm⟩ := exists_lowJet_segment_margin hQ hO hQO
  refine ⟨ρ,Q',hρ,hQ',hQQ',hQ'O,?_⟩
  intro U hU G X Y hG hX hY hGQ τ δ A B hτ hτ1 hδ hδτ hA hB hsmall hXb hYb t ht
  have hs := free_forced_size hX hY hτ hδ hδτ hB hXb hYb
  have hsource := (weightedBound_comp_isometry planeCoordinateIsometry (hX.add hY) hs).restrict_open hU
  apply hm hU hG ((hX.add hY).comp planeCoordinateIsometry.contDiff) hGQ hτ hτ1
    (by positivity : 0 ≤ (A + B) * δ * τ) _ hsource t ht
  convert hsmall using 1
  field_simp

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
