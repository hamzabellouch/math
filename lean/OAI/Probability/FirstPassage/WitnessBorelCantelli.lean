import OAI.Probability.FirstPassage.SpatialEntropyProbability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

namespace PlanarFPP
open Set Finset MeasureTheory Filter

lemma entropy_geometric_bound (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) (hr1 : r ≤ 1) (N : ℕ) :
    a^N*(r^16)^(N/16) ≤ (r^15)⁻¹*(a*r)^N := by
  have hrem : N%16 ≤ 15 := by have hh := Nat.mod_lt N (by omega : 0<16); omega
  have hp : r^15 ≤ r^(N%16) := pow_le_pow_of_le_one hr.le hr1 hrem
  have hid : (r^16)^(N/16)*r^(N%16)=r^N := by
    rw [← pow_mul,← pow_add]
    congr 1
    have hh := Nat.mod_add_div N 16
    omega
  have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ a^N*(r^16)^(N/16) by positivity)
  simp only [mul_assoc] at hh
  rw [hid,← mul_pow] at hh
  calc
    _ ≤ (a*r)^N/r^15 := (le_div_iff₀ (pow_pos hr 15)).mpr (by simpa only [mul_assoc] using hh)
    _ = _ := by ring

theorem summable_witness_entropy (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1) :
    Summable (fun N : ℕ => (196 : ℝ)^N*(r^16)^(N/16)) := by
  have hs := (summable_geometric_of_lt_one (show 0 ≤ 196*r by positivity) hsmall).mul_left ((r^15)⁻¹)
  exact hs.of_nonneg_of_le (fun _ => by positivity) (entropy_geometric_bound 196 r (by norm_num) hr hr1)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem ae_eventually_spatial_long_paths (henv : ExponentialEnvironment P τ)
    (b m₀ am ap K η r : ℝ) (hb : |b| ≤ 1) (ha : am ≤ ap) (hη : 0 < η)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 196*r < 1)
    (hgap : 4*η ≤ (ap-am)/2) (k m : ℕ) (hs : 2 ≤ (2 : ℝ)^k)
    (hstep : max |m₀-((am+ap)/2)*b| |(am+ap)/2| ≤ η*(2 : ℝ)^k)
    (hscale₁ : η*(2 : ℝ)^k < 2*m₀*(2 : ℝ)^m-|((am+ap)/2)| *((2 : ℝ)^k+1))
    (hscale₂ : 3*η*(2 : ℝ)^k+2*|((am+ap)/2)| *((2 : ℝ)^k+1) < K*(2 : ℝ)^k)
    (hBK : ∀ is : List (ℤ×ℤ), P.real {ω | StrictDisjointPaths (spatialListSupport b k m is)
      (is.map (spatialWitnessFamily b m₀ am ap K η k m)) (fun e => τ e ω)} ≤ (r^16)^is.length) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      ∀ blocks : List (List Step), ∀ rest : List Step,
      blocks.length=N → (∀ q ∈ blocks, FullSpatialChunk b k m q) →
      (∀ i ≤ rest.length, chunkInterior b k m (displacement (rest.take i))) →
      ((trace 0 (blocks.flatten++rest)).map traversalEdge).Nodup →
      N*η*(2 : ℝ)^k/2 ≤ defect (fun e => τ e ω) b m₀ ((am+ap)/2) 0 (blocks.flatten++rest) := by
  let _ := henv.probability
  let B (N : ℕ) : Set Ω := {ω | SpatialBadPath (fun e => τ e ω) b m₀ ((am+ap)/2) η k m N}
  have hbound (N : ℕ) (hN : 4 ≤ N) : P.real (B N) ≤ (196 : ℝ)^N*(r^16)^(N/16) :=
    spatial_bad_path_probability henv b m₀ am ap K η (r^16) hb ha hη (by positivity)
      hgap k m hs hstep hscale₁ hscale₂ hBK N hN
  have hsum : Summable (fun N => P.real (B N)) := by
    rw [← summable_nat_add_iff 4]
    have hh := (summable_nat_add_iff 4).mpr (summable_witness_entropy r hr hr1 hsmall)
    exact hh.of_nonneg_of_le (fun _ => measureReal_nonneg) (fun n => hbound (n+4) (by omega))
  have ht : (∑' N, P (B N)) ≠ ⊤ := by
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem ht] with ω hω
  filter_upwards [hω] with N hN
  intro blocks rest hlen hfull hrest hsimple
  by_contra hc
  exact hN ⟨blocks,rest,hlen,hfull,hrest,hsimple,lt_of_not_ge hc⟩

end PlanarFPP

end OAI
