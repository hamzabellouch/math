import OAI.Probability.BenjaminiSchramm.ModularSchur

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

theorem zero_one_tiltedSusceptibility_duality [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots, G.tiltedSusceptibility p 0 x) =
      ∑ x ∈ (G.orbitRepresentatives hq).roots, G.tiltedSusceptibility p 1 x := by
  simp only [tiltedSusceptibility, ENNReal.rpow_zero, ENNReal.rpow_one, mul_one]
  rw [OrbitRepresentatives.tilted_massTransport_ennreal G (G.orbitRepresentatives hq) hc hl
    (G.connectionMeasure p) (fun φ x y => G.connectionMeasure_aut p φ x y)]
  apply Finset.sum_congr rfl
  intro y _
  apply tsum_congr
  intro x
  rw [G.connectionMeasure_symm p x y]

def weightHit (a : ℝ≥0∞) (x : V) : Set (Set E) :=
  {ω | ∃ y, (G.openGraph ω).Reachable x y ∧ a ≤ G.stabilizerWeight x y}

lemma measurableSet_weightHit [Countable V] [Countable E] (a : ℝ≥0∞) (x : V) :
    MeasurableSet (G.weightHit a x) :=
  (Measurable.exists fun y => (G.measurable_reachable x y).and measurable_const).setOf

theorem weightHit_measure_mul_le [Countable V] [Countable E]
    (p : unitInterval) (a : ℝ≥0∞) (x : V) :
    a * G.law p (G.weightHit a x) ≤ G.tiltedSusceptibility p 1 x := by
  have he : G.weightHit a x = ⋃ y, {ω | (G.openGraph ω).Reachable x y ∧
      a ≤ G.stabilizerWeight x y} := by ext ω; simp [weightHit]
  rw [he]
  calc
    _ ≤ a * ∑' y, G.law p {ω | (G.openGraph ω).Reachable x y ∧
        a ≤ G.stabilizerWeight x y} := mul_le_mul' le_rfl (measure_iUnion_le _)
    _ = ∑' y, a * G.law p {ω | (G.openGraph ω).Reachable x y ∧
        a ≤ G.stabilizerWeight x y} := ENNReal.tsum_mul_left.symm
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro y
      by_cases ha : a ≤ G.stabilizerWeight x y
      · simp only [ha, and_true, ENNReal.rpow_one]
        rw [mul_comm]
        exact mul_le_mul' le_rfl ha
      · simp [ha]

end CriticalPercolation.BondGraph

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_fullTiltedSusceptibility_lt_top_of_lt_pc
    [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hc : Connected G) (hl : LocallyFinite G) (hq : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) :
    ∀ x ∈ ((criticalModel G).orbitRepresentatives (criticalModel_quasiTransitive G hq)).roots,
      (criticalModel G).tiltedSusceptibility p 1 x < ⊤ := by
  let H := criticalModel G
  let hHq := criticalModel_quasiTransitive G hq
  have hzero (x : V) : H.tiltedSusceptibility p 0 x < ⊤ := by
    change (criticalModel G).tiltedSusceptibility p 0 x < ⊤
    simp only [CriticalPercolation.BondGraph.tiltedSusceptibility, ENNReal.rpow_zero, mul_one,
      criticalModel_connectionMeasure]
    exact (summable_twoPoint_subcritical G hl hq p hp x).tsum_ofReal_lt_top
  have hsum : (∑ x ∈ (H.orbitRepresentatives hHq).roots, H.tiltedSusceptibility p 1 x) < ⊤ := by
    rw [← H.zero_one_tiltedSusceptibility_duality (criticalModel_connected G hc) hl hHq p]
    exact ENNReal.sum_lt_top.mpr fun x _ => hzero x
  intro x hx
  exact lt_of_le_of_lt (Finset.single_le_sum (fun _ _ => bot_le) hx) hsum

end Percolation.BenjaminiSchramm

end

end OAI
