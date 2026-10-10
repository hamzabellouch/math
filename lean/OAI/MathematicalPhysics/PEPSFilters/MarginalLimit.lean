import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.JointCoordinates

namespace OAI

/-! Residual bounds and exact marginal-coordinate limits. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix
open Set Filter
open scoped Topology
open scoped BigOperators
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder
open scoped BigOperators Topology
open Filter Set

open scoped BigOperators
namespace PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity

lemma clipped_residual_bounds {n : Type*} [Fintype n] [DecidableEq n]
    (x r : n → ℝ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hx : (∀ index, 0 ≤ x index) ∧ ∑ index, x index = 1) (hr : ∀ i, 0 ≤ r i)
    (he : ∀ i, x i + b = max b (r i / c)) :
    (∀ i, 0 ≤ r i - c * x i ∧ r i - c * x i ≤ c * b) ∧
    c ≤ ∑ i, r i ∧ (∑ i, r i) - c ≤ (Fintype.card n : ℝ) * c * b := by
  have hi (i : n) : 0 ≤ r i - c * x i ∧ r i - c * x i ≤ c * b := by
    have hh : r i / c ≤ x i + b := (le_max_right b _).trans_eq (he i).symm
    have hhi : r i ≤ (x i + b) * c := (div_le_iff₀ hc).mp hh
    refine ⟨?_, by nlinarith⟩
    by_cases hz : x i = 0
    · simpa [hz] using hr i
    · have hxb : b < x i + b := by have := lt_of_le_of_ne (hx.1 i) (Ne.symm hz); linarith
      have hmax : max b (r i / c) = r i / c := max_eq_right (by
        by_contra h
        have hei := he i
        rw [max_eq_left (le_of_not_ge h)] at hei
        linarith)
      have hri := (div_eq_iff hc.ne').mp ((he i).trans hmax).symm
      nlinarith
  have hs : ∑ i, (r i - c * x i) = (∑ i, r i) - c := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hx.2, mul_one]
  refine ⟨hi, ?_, ?_⟩
  · have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hi i).1)
    rw [hs] at hh
    linarith
  · have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hi i).2)
    rw [hs] at hh
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using hh

lemma clipped_normalized_residual {n : Type*} [Fintype n] [DecidableEq n]
    (x r : n → ℝ) {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hx : (∀ index, 0 ≤ x index) ∧ ∑ index, x index = 1) (hr : ∀ i, 0 ≤ r i)
    (he : ∀ i, x i + b = max b (r i / c)) (i : n) :
    |r i - (∑ k, r k) * x i| ≤ ((Fintype.card n : ℝ) + 1) * b * (∑ k, r k) := by
  obtain ⟨hi, hcR, hR⟩ := clipped_residual_bounds x r hb hc hx hr he
  let R := ∑ k, r k
  have hR0 : 0 ≤ R := (hc.le.trans hcR)
  have hxi : x i ≤ 1 := by
    calc x i ≤ ∑ k, x k := Finset.single_le_sum (fun k _ => hx.1 k) (Finset.mem_univ i)
         _ = 1 := hx.2
  have hbx : (R-c)*x i ≤ (Fintype.card n : ℝ) * c * b :=
    (mul_le_of_le_one_right (sub_nonneg.mpr hcR) hxi).trans hR
  have hcbR : c*b ≤ R*b := mul_le_mul_of_nonneg_right hcR hb.le
  have hnb : 0 ≤ (Fintype.card n : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb.le
  have hncbR : (Fintype.card n : ℝ) * c * b ≤ (Fintype.card n : ℝ) * R * b := by
    nlinarith [mul_le_mul_of_nonneg_left hcR hnb]
  apply abs_le.mpr
  constructor
  · have hlo := (hi i).1
    nlinarith [mul_nonneg hb.le hR0]
  · have hhi := (hi i).2
    have hprod := mul_nonneg (sub_nonneg.mpr hcR) (hx.1 i)
    nlinarith [mul_nonneg hnb hR0]

end PolynomialPEPS.PinnedEntropy.NestedFilter.Stationarity
namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open Matrix Filter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma marginalDiagonal_continuous (i : n) :
    Continuous (fun z : unitary (Matrix n n ℂ) × Matrix n n ℂ => marginalDiagonal z.1 z.2 i) := by
  unfold marginalDiagonal
  have hU : Continuous (fun z : unitary (Matrix n n ℂ) × Matrix n n ℂ => (z.1 : Matrix n n ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hM : Continuous (fun z : unitary (Matrix n n ℂ) × Matrix n n ℂ =>
      star (z.1 : Matrix n n ℂ) * z.2 * (z.1 : Matrix n n ℂ)) :=
    (hU.star.mul continuous_snd).mul hU
  exact Complex.continuous_re.comp ((continuous_apply i).comp ((continuous_apply i).comp hM))

lemma coordinateDensity_continuous : Continuous (coordinateDensity (n := n)) := by
  unfold coordinateDensity Unitary.conjStarAlgAut
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_subtype_val.comp continuous_fst
    · apply continuous_matrix
      intro i k
      by_cases h : i = k
      · subst k
        simp only [Matrix.diagonal_apply_eq]
        exact Complex.continuous_ofReal.comp
          ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))
      · simp only [Matrix.diagonal_apply_ne _ h]
        exact continuous_const
  · exact (continuous_subtype_val.comp continuous_fst).star

lemma clipped_limit_matrix (b : ℕ → ℝ) (p : ℕ → SpectralCoordinate n)
    (ρ : ℕ → Matrix n n ℂ) (s : SpectralCoordinate n) (σ : Matrix n n ℂ)
    (hb : ∀ k, 0 < b k) (hρ : ∀ k, (ρ k).PosSemidef)
    (hbs : Tendsto b atTop (nhds 0)) (hps : Tendsto p atTop (nhds s))
    (hρs : Tendsto ρ atTop (nhds σ))
    (hd : ∀ k, ρ k = Unitary.conjStarAlgAut ℂ _ (p k).1
      (Matrix.diagonal fun i => (marginalDiagonal (p k).1 (ρ k) i : ℂ)))
    (hclip : ∀ k, ∃ c : ℝ, 0 < c ∧ ∀ i, (p k).2.val i + b k =
      max (b k) (marginalDiagonal (p k).1 (ρ k) i / c)) :
    σ = ((σ.trace.re : ℝ) : ℂ) • coordinateDensity s := by
  let r (k : ℕ) (i : n) := marginalDiagonal (p k).1 (ρ k) i
  let R (k : ℕ) := ∑ i, r k i
  have hpU : Tendsto (fun k => (p k).1) atTop (nhds s.1) := hps.fst_nhds
  have hpM : Tendsto (fun k => ((p k).1, ρ k)) atTop (nhds (s.1, σ)) :=
    hpU.prodMk_nhds hρs
  have hri (i : n) : Tendsto (fun k => r k i) atTop (nhds (marginalDiagonal s.1 σ i)) := by
    have ht : Tendsto (fun z : unitary (Matrix n n ℂ) × Matrix n n ℂ => marginalDiagonal z.1 z.2 i)
        (nhds (s.1, σ)) (nhds (marginalDiagonal s.1 σ i)) :=
      (marginalDiagonal_continuous i).tendsto (s.1, σ)
    have hk := ht.comp hpM
    exact hk
  have hR : Tendsto R atTop (nhds σ.trace.re) := by
    have hrall := tendsto_finsetSum Finset.univ (fun i _ => hri i)
    simpa only [sum_marginalDiagonal] using hrall
  have hx (i : n) : Tendsto (fun k => (p k).2.val i) atTop (nhds (s.2.val i)) :=
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).tendsto s).comp hps
  have he (i : n) : marginalDiagonal s.1 σ i = σ.trace.re * s.2.val i := by
    have hleft := ((hri i).sub (hR.mul (hx i))).abs
    have hright : Tendsto (fun k => ((Fintype.card n : ℝ)+1) * b k * R k) atTop (nhds 0) := by
      convert (tendsto_const_nhds.mul hbs).mul hR using 1
      simp
    have hh := le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall (fun k => by
      obtain ⟨c, hc, hci⟩ := hclip k
      exact Stationarity.clipped_normalized_residual (p k).2.val (r k) (hb k) hc
        (p k).2.property (fun j => marginalDiagonal_nonneg (p k).1 (hρ k) j) hci i))
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hh)
  have hg : Tendsto (fun k => Unitary.conjStarAlgAut ℂ _ (p k).1
      (Matrix.diagonal fun i => (r k i : ℂ))) atTop
      (nhds (Unitary.conjStarAlgAut ℂ _ s.1 (Matrix.diagonal fun i => (marginalDiagonal s.1 σ i : ℂ)))) := by
    have hdiag : Tendsto (fun k => Matrix.diagonal fun i => (r k i : ℂ)) atTop
        (nhds (Matrix.diagonal fun i => (marginalDiagonal s.1 σ i : ℂ))) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq]
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hri i)
      · simp only [Matrix.diagonal_apply_ne _ hij]
        exact tendsto_const_nhds
    have hU : Tendsto (fun k => ((p k).1 : Matrix n n ℂ)) atTop
        (nhds (s.1 : Matrix n n ℂ)) := continuous_subtype_val.continuousAt.tendsto.comp hpU
    have hz := (hU.mul hdiag).mul hU.star
    exact hz
  have hσ : σ = Unitary.conjStarAlgAut ℂ _ s.1
      (Matrix.diagonal fun i => (marginalDiagonal s.1 σ i : ℂ)) :=
    tendsto_nhds_unique ((show ρ = (fun k => Unitary.conjStarAlgAut ℂ _ (p k).1
      (Matrix.diagonal fun i => (r k i : ℂ))) from funext hd) ▸ hρs) hg
  calc
    σ = Unitary.conjStarAlgAut ℂ _ s.1
        (Matrix.diagonal fun i => (marginalDiagonal s.1 σ i : ℂ)) := hσ
    _ = ((σ.trace.re : ℝ) : ℂ) • coordinateDensity s := by
      unfold coordinateDensity
      rw [← map_smul]
      congr 1
      ext i j
      by_cases h : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul, he, Complex.ofReal_mul]
      · simp [h]

end PolynomialPEPS.PinnedEntropy.NestedFilter

namespace PolynomialPEPS.PinnedEntropy.NestedFilter
open Filter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator MatrixOrder Topology

theorem exists_maximizer_marginal_coordinates {L q m : ℕ} [NeZero q]
    {X : Fin m → Finset (Vertex L)} (Ω : State L q) (hΩ : Ω ≠ 0)
    (hX : Monotone X) {a : Fin m → ℝ} (ha : ∀ j, 0 < a j) :
    ∃ s : CoordinateFamily q X, IsMaximizer Ω a (coordinateFilters a s) ∧
      ∀ j, let ρ := reducedDensity (output (coordinateFilters a s) Ω) (X j)
        ρ = ((ρ.trace.re : ℝ) : ℂ) • coordinateDensity (s j) := by
  classical
  let b (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  obtain ⟨p, hp⟩ := Classical.axiomOfChoice (fun n =>
    exists_regularized_maximizer_clipped (hb n) Ω hΩ hX ha)
  let (j : Fin m) : CompactSpace (SpectralCoordinate (RegionConfiguration q (X j))) := by
    let := compact_unitary_coordinates (n := RegionConfiguration q (X j))
    let := compact_weight_coordinates (n := RegionConfiguration q (X j))
    infer_instance
  obtain ⟨s, ns, hns, hs⟩ := CompactSpace.tendsto_subseq p
  have hbs : Tendsto (fun n => b (ns n)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop
  have hpair : Tendsto (fun n => (b (ns n), p (ns n))) atTop (nhds (0, s)) :=
    hbs.prodMk_nhds hs
  have hout := ((regularizedRawOutput_jointContinuous Ω ha).tendsto (0, s)).comp hpair
  refine ⟨s, isMaximizer_of_coordinate_max Ω ha s ?_, ?_⟩
  · intro t
    have ht := ((regularizedRawOutput_jointContinuous Ω ha).tendsto (0, t)).comp
      (hbs.prodMk_nhds tendsto_const_nhds)
    have hh := le_of_tendsto_of_tendsto ht.norm hout.norm
      (Filter.Eventually.of_forall (fun n => (hp (ns n)).1 t))
    simpa only [regularizedRawOutput_zero] using hh
  · intro j
    let ρ (k : ℕ) := reducedDensity (regularizedRawOutput (b (ns k)) a (p (ns k)) Ω) (X j)
    let σ := reducedDensity (regularizedRawOutput 0 a s Ω) (X j)
    have hps : Tendsto (fun k => p (ns k) j) atTop (nhds (s j)) :=
      ((continuous_apply j).tendsto s).comp hs
    have hρs : Tendsto ρ atTop (nhds σ) := by
      have hh := ((continuous_reducedDensity (X j)).tendsto (regularizedRawOutput 0 a s Ω)).comp hout
      exact hh
    have hz := clipped_limit_matrix (fun k => b (ns k)) (fun k => p (ns k) j) ρ (s j) σ
      (fun k => hb (ns k)) (fun k => reducedDensity_posSemidef (X j) _) hbs hps hρs
      (fun k => ((hp (ns k)).2.2 j).1) (fun k => ((hp (ns k)).2.2 j).2)
    simpa only [σ, regularizedRawOutput_zero] using hz

end PolynomialPEPS.PinnedEntropy.NestedFilter

end

end OAI
