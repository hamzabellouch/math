import OAI.Probability.BenjaminiSchramm.GeneralCriticalFiniteness
import OAI.Probability.BenjaminiSchramm.NormalizedHalfspace

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

def adjustedFullHit (a : V → ℝ) (x : V) (t : ℝ) : Set (Set E) :=
  {ω | ∃ y, t ≤ G.orbitAdjustedHeight a x y ∧ y ∈ G.cluster ω x}

lemma measurableSet_adjustedFullHit [Countable V] [Countable E]
    (a : V → ℝ) (x : V) (t : ℝ) : MeasurableSet (G.adjustedFullHit a x t) :=
  (Measurable.exists fun y => measurable_const.and (G.measurable_reachable x y)).setOf

lemma adjustedFullHit_antitone (a : V → ℝ) (x : V) :
    Antitone (G.adjustedFullHit a x) := by
  rintro s t hst ω ⟨y,hy,hxy⟩
  exact ⟨y,hst.trans hy,hxy⟩

lemma Aut.adjustedFullHit_preimage (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x) (φ : G.Aut) (x : V) (t : ℝ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.adjustedFullHit a (φ.vertex x) t=
      G.adjustedFullHit a x t := by
  ext ω
  constructor
  · rintro ⟨y,hy,hxy⟩
    obtain ⟨z,rfl⟩ := φ.vertex.surjective y
    exact ⟨z,by simpa only [G.orbitAdjustedHeight_aut a ha] using hy,
      (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mp hxy⟩
  · rintro ⟨y,hy,hxy⟩
    exact ⟨φ.vertex y,by simpa only [G.orbitAdjustedHeight_aut a ha] using hy,
      (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mpr hxy⟩

lemma Aut.adjustedFullHit_real [Countable V] [Countable E]
    (a : V → ℝ) (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (φ : G.Aut) (p : unitInterval) (x : V) (t : ℝ) :
    (G.law p).real (G.adjustedFullHit a (φ.vertex x) t)=
      (G.law p).real (G.adjustedFullHit a x t) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_adjustedFullHit _ _ _),Aut.adjustedFullHit_preimage G a ha φ]

theorem adjustedFullHit_tendsto_zero [Countable V] [Countable E]
    (a : V → ℝ) (p : unitInterval) (x : V) (R : ℝ) (hR : 0 < R)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) :
    Tendsto (fun n : ℕ => (G.law p).real (G.adjustedFullHit a x (R*n))) atTop (𝓝 0) := by
  have hempty (ω : Set E) (hω : (G.cluster ω x).Finite) :
      ω ∉ ⋂ n : ℕ, G.adjustedFullHit a x (R*n) := by
    obtain ⟨B,hB⟩ := (hω.image (G.orbitAdjustedHeight a x)).bddAbove
    obtain ⟨n,hn⟩ := exists_nat_gt (B/R)
    intro hh
    obtain ⟨y,hy,hxy⟩ := Set.mem_iInter.mp hh n
    have hBy := hB ⟨y,hxy,rfl⟩
    have hBn := (div_lt_iff₀ hR).mp hn
    nlinarith
  have hz : G.law p (⋂ n : ℕ, G.adjustedFullHit a x (R*n))=0 := by
    simpa only [not_not,Set.ofPred_mem_eq] using (ae_iff.mp (hfin.mono hempty))
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n : ℕ => (G.measurableSet_adjustedFullHit a x (R*n)).nullMeasurableSet)
    (fun n m hnm => G.adjustedFullHit_antitone a x (by gcongr)) ⟨0,measure_ne_top _ _⟩
  rw [hz] at h
  simpa only [Function.comp_def,measureReal_def,ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

def rootHeightHitProfile (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n : ℕ) : ℝ :=
  ∑ x ∈ O.roots, (G.law p).real (G.adjustedFullHit a x (R*n))

lemma rootHeightHitProfile_nonneg (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n : ℕ) : 0 ≤ G.rootHeightHitProfile O a R p n :=
  Finset.sum_nonneg fun _ _ => measureReal_nonneg

lemma adjustedFullHit_le_rootProfile [Countable V] [Countable E]
    (O : G.OrbitRepresentatives) (a : V → ℝ)
    (ha : ∀ (φ : G.Aut) x, a (φ.vertex x)=a x)
    (R : ℝ) (p : unitInterval) (n : ℕ) (x : V) :
    (G.law p).real (G.adjustedFullHit a x (R*n)) ≤ G.rootHeightHitProfile O a R p n := by
  obtain ⟨y,hy,φ,rfl⟩ := O.cover x
  rw [Aut.adjustedFullHit_real G a ha φ]
  exact Finset.single_le_sum (f := fun z => (G.law p).real (G.adjustedFullHit a z (R*n)))
    (fun _ _ => measureReal_nonneg) hy

lemma rootHeightHitProfile_le_card (O : G.OrbitRepresentatives) (a : V → ℝ)
    (R : ℝ) (p : unitInterval) (n : ℕ) :
    G.rootHeightHitProfile O a R p n ≤ O.roots.card := by
  calc
    _ ≤ ∑ _x ∈ O.roots, (1 : ℝ) := Finset.sum_le_sum fun _ _ => measureReal_le_one
    _ = _ := by simp

theorem rootHeightHitProfile_tendsto_zero [Countable V] [Countable E]
    (O : G.OrbitRepresentatives) (a : V → ℝ) (p : unitInterval)
    (R : ℝ) (hR : 0 < R) (hfin : ∀ x, ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) :
    Tendsto (G.rootHeightHitProfile O a R p) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ∑ x ∈ O.roots, (G.law p).real (G.adjustedFullHit a x (R*n))) atTop (𝓝 0)
  have hh := tendsto_finsetSum O.roots (fun x _ => G.adjustedFullHit_tendsto_zero a p x R hR (hfin x))
  simpa only [Finset.sum_const_zero] using hh

end CriticalPercolation.BondGraph

end

end OAI
