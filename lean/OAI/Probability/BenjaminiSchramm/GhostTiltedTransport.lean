import OAI.Probability.BenjaminiSchramm.TiltedGhostSusceptibility

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

def ghostAvoid (h : ℝ) (m : ℝ≥0∞) : ℝ≥0∞ :=
  if m = ⊤ then 0 else ENNReal.ofReal (Real.exp (-h * m.toReal))

lemma measurable_ghostAvoid (h : ℝ) : Measurable (ghostAvoid h) := by
  exact measurable_const.ite (measurableSet_eq_fun measurable_id measurable_const)
    ((measurable_const.mul measurable_id.ennreal_toReal).exp.ennreal_ofReal)

lemma ghostAvoid_antitone {h : ℝ} (hh : 0 ≤ h) : Antitone (ghostAvoid h) := by
  intro m n hmn
  by_cases hn : n = ⊤
  · simp [ghostAvoid, hn]
  · have hm : m ≠ ⊤ := ne_top_of_le_ne_top hn hmn
    rw [ghostAvoid, ite_eq_right hn, ghostAvoid, ite_eq_right hm]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (ENNReal.toReal_mono hn hmn) (neg_nonpos.mpr hh)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm

variable {V E : Type*} (G : BondGraph V E)

def ghostHighTransport (h : ℝ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if (G.openGraph ω).Reachable x y ∧ 1 < G.stabilizerWeight x y then
    ghostAvoid h (G.quarterTiltedMass ω x) * G.stabilizerWeight x y ^ (3 / 8 : ℝ)
  else 0

lemma measurable_ghostHighTransport [Countable V] [Countable E]
    (h : ℝ) (x y : V) : Measurable (fun ω => G.ghostHighTransport h ω x y) := by
  exact (((measurable_ghostAvoid h).comp (G.measurable_quarterTiltedMass x)).mul_const _).ite
    ((G.measurable_reachable x y).and measurable_const).setOf measurable_const

lemma ghostHighTransport_aut (h : ℝ) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.ghostHighTransport h (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.ghostHighTransport h ω x y := by
  unfold ghostHighTransport
  rw [Aut.stabilizerWeight, G.quarterTiltedMass_aut]
  congr 1
  exact propext (and_congr (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)) Iff.rfl)

lemma ghostHighTransport_incoming_le
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {h : ℝ} (hh : 0 ≤ h) (ω : Set E) (y : V) :
    (∑' x, G.ghostHighTransport h ω x y * G.stabilizerWeight y x) ≤
      ghostAvoid h (G.quarterTiltedMass ω y) * G.quarterTiltedMass ω y := by
  rw [quarterTiltedMass, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  unfold ghostHighTransport
  by_cases hr : (G.openGraph ω).Reachable x y
  · have hr' := hr.symm
    simp only [hr, hr', true_and, ↓reduceIte]
    by_cases hw : 1 < G.stabilizerWeight x y
    · rw [ite_eq_left hw]
      have hmass : G.quarterTiltedMass ω y ≤ G.quarterTiltedMass ω x := by
        rw [G.quarterTiltedMass_change_base hc hl ω hr']
        calc
          _ = 1 * G.quarterTiltedMass ω y := (one_mul _).symm
          _ ≤ _ := mul_le_mul' (ENNReal.one_le_rpow hw.le (by norm_num)) le_rfl
      have ha := ghostAvoid_antitone hh hmass
      have hrev : G.stabilizerWeight y x ≤ 1 := by
        rw [← G.stabilizerWeight_inv hc hl x y]
        exact ENNReal.inv_le_one.mpr hw.le
      have hp : G.stabilizerWeight x y ^ (3 / 8 : ℝ) * G.stabilizerWeight y x ≤
          G.stabilizerWeight y x ^ (1 / 4 : ℝ) := by
        rw [← G.stabilizerWeight_inv hc hl y x, ENNReal.inv_rpow, ← ENNReal.rpow_neg]
        nth_rw 2 [← ENNReal.rpow_one (G.stabilizerWeight y x)]
        rw [← ENNReal.rpow_add _ _ (G.stabilizerWeight_pos hc hl y x).ne'
          (G.stabilizerWeight_ne_top y x)]
        exact ENNReal.rpow_le_rpow_of_exponent_ge hrev (by norm_num)
      calc
        _ = ghostAvoid h (G.quarterTiltedMass ω x) *
            (G.stabilizerWeight x y ^ (3 / 8 : ℝ) * G.stabilizerWeight y x) := by ac_rfl
        _ ≤ _ := mul_le_mul' ha hp
    · simp [hw]
  · have hr' : ¬ (G.openGraph ω).Reachable y x := fun h => hr h.symm
    simp [hr,hr']

theorem ghostHighTransport_expected_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, ∑' y, G.ghostHighTransport h ω x y ∂G.law p) ≤
      ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p := by
  rw [OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
    (G.ghostHighTransport h) (G.measurable_ghostHighTransport h) (G.ghostHighTransport_aut h)]
  apply Finset.sum_le_sum
  intro y _
  exact lintegral_mono fun ω => G.ghostHighTransport_incoming_le hc hl hh ω y

def ghostWeightedCount (h : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, if (G.openGraph ω).Reachable x y then
    ghostAvoid h (G.quarterTiltedMass ω x) * G.stabilizerWeight x y ^ (3 / 8 : ℝ) else 0

lemma ghostWeightedCount_le (h : ℝ) (ω : Set E) (x : V) :
    G.ghostWeightedCount h ω x ≤
      ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x +
        ∑' y, G.ghostHighTransport h ω x y := by
  rw [quarterTiltedMass, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro y
  unfold ghostHighTransport
  by_cases hr : (G.openGraph ω).Reachable x y
  · simp only [hr, true_and, ↓reduceIte]
    by_cases hw : 1 < G.stabilizerWeight x y
    · rw [ite_eq_left hw]
      exact le_add_left le_rfl
    · rw [ite_eq_right hw, add_zero]
      exact mul_le_mul' le_rfl
        (ENNReal.rpow_le_rpow_of_exponent_ge (le_of_not_gt hw) (by norm_num))
  · simp [hr]

theorem expected_ghostWeightedCount_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.ghostWeightedCount h ω x ∂G.law p) ≤
      2 * ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p := by
  calc
    _ ≤ ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x +
          ∑' y, G.ghostHighTransport h ω x y ∂G.law p := by
      apply Finset.sum_le_sum
      intro x _
      exact lintegral_mono fun ω => G.ghostWeightedCount_le h ω x
    _ = (∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p) +
        ∑ x ∈ (G.orbitRepresentatives hq).roots,
          ∫⁻ ω, ∑' y, G.ghostHighTransport h ω x y ∂G.law p := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact lintegral_add_left
        (((measurable_ghostAvoid h).comp (G.measurable_quarterTiltedMass x)).mul
          (G.measurable_quarterTiltedMass x)) _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add le_rfl (G.ghostHighTransport_expected_le hc hl hq p hh)

end CriticalPercolation.BondGraph

end

end OAI
