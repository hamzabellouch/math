import OAI.Probability.BenjaminiSchramm.LayerFrontierGeometry
import OAI.Probability.BenjaminiSchramm.OrbitHeightComparison
import OAI.Probability.BenjaminiSchramm.GhostMomentBound

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma modularLayerCount_le_height_band (h : V → ℝ) (R : ℝ) (hR : 1 ≤ R)
    (ω : Set E) (o : V) (k : ℤ) :
    modularLayerCount G h ω o k ≤
      restrictedLayerCount G Set.univ {y | (k : ℝ)-R ≤ h y ∧ h y ≤ (k : ℝ)+R} ω o := by
  let F (y : V) : ℝ≥0∞ := if ((k : ℝ)-R ≤ h y ∧ h y ≤ (k : ℝ)+R) ∧ Conn G ω o y then 1 else 0
  have hlocal (y : {y : V // ⌊h y⌋=k}) : (if Conn G ω o y then (1 : ℝ≥0∞) else 0) ≤ F y := by
    by_cases hy : Conn G ω o y
    · have hlo := Int.floor_le (h (y : V))
      have hhi := Int.lt_floor_add_one (h (y : V))
      rw [y.property] at hlo hhi
      have hb : (k : ℝ)-R ≤ h (y : V) ∧ h (y : V) ≤ (k : ℝ)+R := by
        constructor <;> linarith
      have hh : ((k : ℝ)-R ≤ h (y : V) ∧ h (y : V) ≤ (k : ℝ)+R) ∧ Conn G ω o y := ⟨hb,hy⟩
      simp only [F,ite_eq_left hy,ite_eq_left hh,le_refl]
    · simp only [ite_eq_right hy]
      exact bot_le
  calc
    _ ≤ ∑' y : {y : V // ⌊h y⌋=k}, F y := ENNReal.tsum_le_tsum hlocal
    _ ≤ ∑' y, F y := ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective F
    _ = _ := by
      unfold restrictedLayerCount
      apply tsum_congr
      intro y
      simp only [F,Set.mem_ofPred_eq,Set.inter_univ]

variable [Countable V] [Countable E]

theorem quarterMoment_lt_top_of_height_bands (h : V → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (p : unitInterval) (o : V) (C : ℝ≥0∞) (hC : C < ⊤)
    (hpos : ∀ k : ℝ, 0 ≤ k →
      (∫⁻ ω, (restrictedLayerCount G Set.univ {y | k-R ≤ h y ∧ h y ≤ k+R} ω o)^(3/4 : ℝ) ∂law p) ≤
        C*ENNReal.ofReal (Real.exp (-k/2)))
    (hneg : ∀ k : ℝ, 0 ≤ k →
      (∫⁻ ω, (restrictedLayerCount G Set.univ {y | -k-R ≤ h y ∧ h y ≤ -k+R} ω o)^(3/4 : ℝ) ∂law p) ≤
        C*ENNReal.ofReal (Real.exp (k/16))) :
    (∫⁻ ω, quarterTiltedClusterMass G h ω o^(3/4 : ℝ) ∂law p) < ⊤ := by
  apply quarterTilted_moment_lt_top_of_layer_bounds G p h o C.toReal ENNReal.toReal_nonneg
  · intro k hk
    have hb := hpos k (by exact_mod_cast hk)
    have hm := lintegral_mono (μ := law p) fun ω => ENNReal.rpow_le_rpow
      (modularLayerCount_le_height_band G h R hR ω o k) (by norm_num : (0 : ℝ) ≤ 3/4)
    apply hm.trans
    rw [←ENNReal.ofReal_toReal hC.ne] at hb
    simpa only [←ENNReal.ofReal_mul ENNReal.toReal_nonneg] using hb
  · intro k hk
    have hb := hneg (-(k : ℝ)) (by exact_mod_cast neg_nonneg.mpr hk)
    have hm := lintegral_mono (μ := law p) fun ω => ENNReal.rpow_le_rpow
      (modularLayerCount_le_height_band G h R hR ω o k) (by norm_num : (0 : ℝ) ≤ 3/4)
    apply hm.trans
    rw [←ENNReal.ofReal_toReal hC.ne] at hb
    simpa only [neg_neg,neg_div,←ENNReal.ofReal_mul ENNReal.toReal_nonneg] using hb

theorem raw_quarterMoment_lt_top_of_normalized_bands [Nonempty V]
    (hc : Connected G) (hl : LocallyFinite G) (a : V → ℝ) (m M : ℝ) (hm : 0 < m)
    (ha : ∀ x, m ≤ a x ∧ a x ≤ M) (R : ℝ) (hR : 1 ≤ R)
    (p : unitInterval) (o : V) (C : ℝ≥0∞) (hC : C < ⊤)
    (hpos : ∀ k : ℝ, 0 ≤ k →
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {y | k-R ≤ (criticalModel G).orbitAdjustedHeight a o y ∧
          (criticalModel G).orbitAdjustedHeight a o y ≤ k+R} ω o)^(3/4 : ℝ) ∂law p) ≤
        C*ENNReal.ofReal (Real.exp (-k/2)))
    (hneg : ∀ k : ℝ, 0 ≤ k →
      (∫⁻ ω, (restrictedLayerCount G Set.univ
        {y | -k-R ≤ (criticalModel G).orbitAdjustedHeight a o y ∧
          (criticalModel G).orbitAdjustedHeight a o y ≤ -k+R} ω o)^(3/4 : ℝ) ∂law p) ≤
        C*ENNReal.ofReal (Real.exp (k/16))) :
    (criticalModel G).quarterThreeQuarterMoment p o < ⊤ := by
  exact raw_quarterMoment_lt_top_of_orbit_normalization G hc hl a m M hm ha p o
    (quarterMoment_lt_top_of_height_bands G ((criticalModel G).orbitAdjustedHeight a o)
      R hR p o C hC hpos hneg)

end Percolation.BenjaminiSchramm

end

end OAI
