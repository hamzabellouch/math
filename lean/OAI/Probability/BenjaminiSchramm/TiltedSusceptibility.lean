import OAI.Probability.BenjaminiSchramm.PeakLayerEstimate
import OAI.Probability.CriticalPercolation.Modular.ModularClusterCount

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

def connectionMeasure (p : unitInterval) (x y : V) : ℝ≥0∞ :=
  G.law p {ω | (G.openGraph ω).Reachable x y}

def tiltedSusceptibility (p : unitInterval) (a : ℝ) (x : V) : ℝ≥0∞ :=
  ∑' y, G.connectionMeasure p x y * G.stabilizerWeight x y ^ a

lemma connectionMeasure_symm (p : unitInterval) (x y : V) :
    G.connectionMeasure p x y = G.connectionMeasure p y x := by
  unfold connectionMeasure
  congr 1
  ext ω
  exact SimpleGraph.reachable_comm

lemma connectionMeasure_aut [Countable V] [Countable E] (p : unitInterval) (φ : G.Aut) (x y : V) :
    G.connectionMeasure p (φ.vertex x) (φ.vertex y) = G.connectionMeasure p x y := by
  unfold connectionMeasure
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    ((G.measurable_reachable _ _).setOf)]
  congr 1
  ext ω
  exact SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)

lemma tiltedSusceptibility_aut [Countable V] [Countable E] (p : unitInterval) (a : ℝ)
    (φ : G.Aut) (x : V) :
    G.tiltedSusceptibility p a (φ.vertex x) = G.tiltedSusceptibility p a x := by
  unfold tiltedSusceptibility
  rw [← φ.vertex.tsum_eq]
  simp only [G.connectionMeasure_aut, Aut.stabilizerWeight]

theorem quarterTiltedSusceptibility_duality [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots, G.tiltedSusceptibility p (1 / 4) x) =
      ∑ x ∈ (G.orbitRepresentatives hq).roots, G.tiltedSusceptibility p (3 / 4) x := by
  rw [show (∑ x ∈ (G.orbitRepresentatives hq).roots, G.tiltedSusceptibility p (1 / 4) x) =
      ∑ y ∈ (G.orbitRepresentatives hq).roots,
        ∑' x, (G.connectionMeasure p x y * G.stabilizerWeight x y ^ (1 / 4 : ℝ)) *
          G.stabilizerWeight y x from
    OrbitRepresentatives.tilted_massTransport_ennreal G (G.orbitRepresentatives hq) hc hl
      (fun x y => G.connectionMeasure p x y * G.stabilizerWeight x y ^ (1 / 4 : ℝ))
      (fun φ x y => by rw [G.connectionMeasure_aut, Aut.stabilizerWeight])]
  apply Finset.sum_congr rfl
  intro y _
  apply tsum_congr
  intro x
  rw [G.connectionMeasure_symm p x y, mul_assoc,
    ← G.stabilizerWeight_inv hc hl y x, ENNReal.inv_rpow,
    ← ENNReal.rpow_neg]
  nth_rw 2 [← ENNReal.rpow_one (G.stabilizerWeight y x)]
  rw [← ENNReal.rpow_add _ _ (G.stabilizerWeight_pos hc hl y x).ne'
    (G.stabilizerWeight_ne_top y x)]
  norm_num

theorem halfTiltedSusceptibility_le_quarter_add_threeQuarter (p : unitInterval) (x : V) :
    G.tiltedSusceptibility p (1 / 2) x ≤
      G.tiltedSusceptibility p (1 / 4) x + G.tiltedSusceptibility p (3 / 4) x := by
  rw [tiltedSusceptibility, tiltedSusceptibility, tiltedSusceptibility, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro y
  rw [← mul_add]
  gcongr
  rcases le_total (G.stabilizerWeight x y) 1 with h | h
  · exact (ENNReal.rpow_le_rpow_of_exponent_ge h (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)).trans
      (le_add_right le_rfl)
  · exact (ENNReal.rpow_le_rpow_of_exponent_le h (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4)).trans
      (le_add_left le_rfl)

theorem uniform_halfTiltedSusceptibility_of_quarter [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval)
    (hfin : ∀ x ∈ (G.orbitRepresentatives hq).roots,
      G.tiltedSusceptibility p (1 / 4) x < ∞) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x, G.tiltedSusceptibility p (1 / 2) x ≤ C := by
  let S := (G.orbitRepresentatives hq).roots
  let C := (∑ x ∈ S, G.tiltedSusceptibility p (1 / 4) x) +
    ∑ x ∈ S, G.tiltedSusceptibility p (3 / 4) x
  have hqfin : (∑ x ∈ S, G.tiltedSusceptibility p (1 / 4) x) < ∞ :=
    ENNReal.sum_lt_top.mpr hfin
  have htfin : (∑ x ∈ S, G.tiltedSusceptibility p (3 / 4) x) < ∞ := by
    rw [← G.quarterTiltedSusceptibility_duality hc hl hq p]
    exact hqfin
  refine ⟨C, ENNReal.add_lt_top.mpr ⟨hqfin,htfin⟩, ?_⟩
  intro x
  obtain ⟨y,hy,φ,rfl⟩ := (G.orbitRepresentatives hq).cover x
  rw [G.tiltedSusceptibility_aut]
  exact (G.halfTiltedSusceptibility_le_quarter_add_threeQuarter p y).trans
    (add_le_add (Finset.single_le_sum (fun _ _ => zero_le) hy)
      (Finset.single_le_sum (fun _ _ => zero_le) hy))

end CriticalPercolation.BondGraph

end

end OAI
