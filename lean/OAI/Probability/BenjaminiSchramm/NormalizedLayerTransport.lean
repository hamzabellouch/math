import OAI.Probability.BenjaminiSchramm.OrbitHeightComparison
import OAI.Probability.CriticalPercolation.Modular.RandomTiltedTransport

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma orbitAdjustedHeight_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (x y : V) :
    G.orbitAdjustedHeight a y x = -G.orbitAdjustedHeight a x y := by
  have hh := G.orbitAdjustedHeight_change_base hc hl a x y x
  rw [G.orbitAdjustedHeight_self] at hh
  linarith

lemma orbitAdjustedHeight_exp_balance (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (ha : ∀ x, 0 < a x) (x y : V) :
    ENNReal.ofReal (a x)*G.stabilizerWeight y x =
      ENNReal.ofReal (a y)*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) := by
  rw [stabilizerWeight,←ENNReal.ofReal_mul (ha x).le,
    ←ENNReal.ofReal_mul (ha y).le]
  congr 1
  rw [orbitAdjustedHeight,modularLogHeight,Real.exp_sub,Real.exp_add,
    Real.exp_log (G.modularRatio_pos hc hl x y),Real.exp_log (ha x),Real.exp_log (ha y)]
  field_simp [(ha y).ne']

theorem OrbitRepresentatives.random_normalized_tilted_transport [Countable V]
    (R : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (hF : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y)=F ω x y) :
    (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, ∑' y, F ω x y ∂G.law p)) =
      ∑ y ∈ R.roots, ENNReal.ofReal (a y)*
        (∫⁻ ω, ∑' x, F ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ∂G.law p) := by
  have hh := OrbitRepresentatives.random_tilted_transport G R hc hl p
    (fun ω x y => ENNReal.ofReal (a x)*F ω x y)
    (fun x y => measurable_const.mul (hm x y))
    (fun φ ω x y => by rw [ha φ x,hF φ ω x y])
  have hin (ω : Set E) (y : V) :
      (∑' x, (ENNReal.ofReal (a x)*F ω x y)*G.stabilizerWeight y x) =
        ENNReal.ofReal (a y)*(∑' x, F ω x y*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) := by
    rw [←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro x
    calc
      _ = F ω x y*(ENNReal.ofReal (a x)*G.stabilizerWeight y x) := by ring
      _ = F ω x y*(ENNReal.ofReal (a y)*
          ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) := by
        rw [G.orbitAdjustedHeight_exp_balance hc hl a hapos x y]
      _ = _ := by ring
  simp_rw [ENNReal.tsum_mul_left,hin,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hh
  exact hh

def adjustedBandTransport (a : V → ℝ) (l u : ℝ) (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if y ∈ G.cluster ω x ∧ l ≤ G.orbitAdjustedHeight a x y ∧
    G.orbitAdjustedHeight a x y ≤ u then 1 else 0

def adjustedBandCount (a : V → ℝ) (l u : ℝ) (ω : Set E) (x : V) : ℝ≥0∞ :=
  ∑' y, G.adjustedBandTransport a l u ω x y

lemma measurable_adjustedBandTransport [Countable V] [Countable E] (a : V → ℝ) (l u : ℝ) (x y : V) :
    Measurable (fun ω => G.adjustedBandTransport a l u ω x y) := by
  exact Measurable.ite ((G.measurable_reachable x y).and measurable_const).setOf
    measurable_const measurable_const

lemma adjustedBandTransport_aut (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (l u : ℝ)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.adjustedBandTransport a l u (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.adjustedBandTransport a l u ω x y := by
  simp only [adjustedBandTransport,G.orbitAdjustedHeight_aut a ha,
    ←Aut.cluster_image,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma adjustedBandTransport_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (l u : ℝ) (ω : Set E) (x y : V) :
    G.adjustedBandTransport a l u ω x y = G.adjustedBandTransport a (-u) (-l) ω y x := by
  unfold adjustedBandTransport
  rw [G.orbitAdjustedHeight_reverse hc hl a x y]
  congr 1
  apply propext
  constructor
  · rintro ⟨h,hlo,hhi⟩
    exact ⟨h.symm,by linarith,by linarith⟩
  · rintro ⟨h,hlo,hhi⟩
    exact ⟨h.symm,by linarith,by linarith⟩

lemma adjustedBandTransport_weight_bounds (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (l u : ℝ) (ω : Set E) (x y : V) :
    ENNReal.ofReal (Real.exp (-u))*G.adjustedBandTransport a (-u) (-l) ω y x ≤
      G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ∧
    G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) ≤
      ENNReal.ofReal (Real.exp (-l))*G.adjustedBandTransport a (-u) (-l) ω y x := by
  rw [G.adjustedBandTransport_reverse hc hl a l u ω x y]
  unfold adjustedBandTransport
  split_ifs with h
  · simp only [mul_one,one_mul]
    constructor <;> apply ENNReal.ofReal_le_ofReal <;> apply Real.exp_le_exp.mpr
    · exact h.2.1
    · exact h.2.2
  · simp only [mul_zero,zero_mul,le_refl,and_self]

theorem expected_adjustedBandCount_reciprocity [Countable V] [Countable E]
    (R : G.OrbitRepresentatives) (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (a : V → ℝ) (hapos : ∀ x, 0 < a x)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (p : unitInterval) (l u : ℝ) :
    ENNReal.ofReal (Real.exp (-u))*
      (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a (-u) (-l) ω x ∂G.law p)) ≤
      (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) ∧
    (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) ≤
      ENNReal.ofReal (Real.exp (-l))*
        (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a (-u) (-l) ω x ∂G.law p)) := by
  have he := OrbitRepresentatives.random_normalized_tilted_transport G R hc hl a hapos ha p
    (G.adjustedBandTransport a l u) (G.measurable_adjustedBandTransport a l u)
    (G.adjustedBandTransport_aut a ha l u)
  change (∑ x ∈ R.roots, ENNReal.ofReal (a x)*(∫⁻ ω, G.adjustedBandCount a l u ω x ∂G.law p)) = _ at he
  rw [he]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _hy
    have hb (ω : Set E) : ENNReal.ofReal (Real.exp (-u))*G.adjustedBandCount a (-u) (-l) ω y ≤
        ∑' x, G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x)) := by
      rw [adjustedBandCount,←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun x => (G.adjustedBandTransport_weight_bounds hc hl a l u ω x y).1)
    calc
      _ = ENNReal.ofReal (a y)*(∫⁻ ω, ENNReal.ofReal (Real.exp (-u))*
          G.adjustedBandCount a (-u) (-l) ω y ∂G.law p) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        ring
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono hb)
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y _hy
    have hb (ω : Set E) :
        (∑' x, G.adjustedBandTransport a l u ω x y*ENNReal.ofReal (Real.exp (G.orbitAdjustedHeight a y x))) ≤
          ENNReal.ofReal (Real.exp (-l))*G.adjustedBandCount a (-u) (-l) ω y := by
      rw [adjustedBandCount,←ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum (fun x => (G.adjustedBandTransport_weight_bounds hc hl a l u ω x y).2)
    calc
      _ ≤ ENNReal.ofReal (a y)*(∫⁻ ω, ENNReal.ofReal (Real.exp (-l))*
          G.adjustedBandCount a (-u) (-l) ω y ∂G.law p) := mul_le_mul' le_rfl (lintegral_mono hb)
      _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; ring

end CriticalPercolation.BondGraph

end

end OAI
