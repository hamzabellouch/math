import OAI.Probability.BenjaminiSchramm.ModularSlabs

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitAdjustedHeight (a : V → ℝ) (x y : V) : ℝ :=
  G.modularLogHeight x y + Real.log (a y) - Real.log (a x)

@[simp] lemma orbitAdjustedHeight_self (a : V → ℝ) (x : V) :
    G.orbitAdjustedHeight a x x = 0 := by simp [orbitAdjustedHeight]

lemma orbitAdjustedHeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x v y : V) :
    G.orbitAdjustedHeight a x y = G.orbitAdjustedHeight a x v + G.orbitAdjustedHeight a v y := by
  simp only [orbitAdjustedHeight,G.modularLogHeight_change_base hc hl x v y]
  ring

lemma orbitAdjustedHeight_aut (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x) = a x)
    (φ : G.Aut) (x y : V) :
    G.orbitAdjustedHeight a (φ.vertex x) (φ.vertex y) = G.orbitAdjustedHeight a x y := by
  simp only [orbitAdjustedHeight,Aut.modularLogHeight,ha]

lemma orbitAdjustedHeight_sub_bound (a : V → ℝ) (m M : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x ∧ a x ≤ M) (x y : V) :
    |G.orbitAdjustedHeight a x y - G.modularLogHeight x y| ≤ Real.log M - Real.log m := by
  have hxlo := Real.log_le_log hm (ha x).1
  have hylo := Real.log_le_log hm (ha y).1
  have hxhi := Real.log_le_log (hm.trans_le (ha x).1) (ha x).2
  have hyhi := Real.log_le_log (hm.trans_le (ha y).1) (ha y).2
  have he : G.orbitAdjustedHeight a x y-G.modularLogHeight x y = Real.log (a y)-Real.log (a x) := by
    unfold orbitAdjustedHeight
    ring
  rw [he,abs_le]
  constructor <;> linarith

end CriticalPercolation.BondGraph

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem quarterTiltedClusterMass_le_of_height_bound (h h' : V → ℝ) (D : ℝ)
    (hbound : ∀ x, h x ≤ h' x+D) (ω : Set E) (o : V) :
    quarterTiltedClusterMass G h ω o ≤ ENNReal.ofReal (Real.exp (D/4)) *
      quarterTiltedClusterMass G h' ω o := by
  unfold quarterTiltedClusterMass
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hc : Conn G ω o x
  · simp only [ite_eq_left hc]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith [hbound x]
  · simp only [ite_eq_right hc,mul_zero,le_refl]

theorem quarterMoment_lt_top_of_height_bound (h h' : V → ℝ) (D : ℝ)
    (hbound : ∀ x, h x ≤ h' x+D) (μ : Measure (Set E)) (o : V)
    (hM : (∫⁻ ω, quarterTiltedClusterMass G h' ω o ^ (3/4 : ℝ) ∂μ) < ⊤) :
    (∫⁻ ω, quarterTiltedClusterMass G h ω o ^ (3/4 : ℝ) ∂μ) < ⊤ := by
  have hp (ω : Set E) := ENNReal.rpow_le_rpow
    (quarterTiltedClusterMass_le_of_height_bound G h h' D hbound ω o) (by norm_num : (0 : ℝ) ≤ 3/4)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3/4)] at hp
  apply lt_of_le_of_lt (lintegral_mono hp)
  rw [lintegral_const_mul' _ _
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by simp)) hM

theorem raw_quarterMoment_lt_top_of_orbit_normalization [Nonempty V]
    (hc : Connected G) (hl : LocallyFinite G) (a : V → ℝ) (m M : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x ∧ a x ≤ M) (p : unitInterval) (o : V)
    (hM : (∫⁻ ω, quarterTiltedClusterMass G
      ((criticalModel G).orbitAdjustedHeight a o) ω o ^ (3/4 : ℝ) ∂law p) < ⊤) :
    (∫⁻ ω, (criticalModel G).quarterTiltedMass ω o ^ (3/4 : ℝ) ∂law p) < ⊤ := by
  simp_rw [quarterTiltedMass_eq_logarithmic_mass G hc hl]
  apply quarterMoment_lt_top_of_height_bound G (modularHeight G o)
    ((criticalModel G).orbitAdjustedHeight a o) (Real.log M-Real.log m) ?_ (law p) o hM
  intro x
  have h := (abs_le.mp ((criticalModel G).orbitAdjustedHeight_sub_bound a m M hm ha o x)).1
  change -(Real.log M-Real.log m) ≤ (criticalModel G).orbitAdjustedHeight a o x-
    modularHeight G o x at h
  linarith

end Percolation.BenjaminiSchramm

end

end OAI
