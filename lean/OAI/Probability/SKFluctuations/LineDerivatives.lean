import Mathlib
import OAI.Probability.SKFluctuations.LowerOnInterval

namespace OAI

/-! Line Derivatives. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.PinnedVariance
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 

structure LineDerivatives (f : E → ℝ) where
  first : E → E → ℝ
  second : E → E → ℝ
  deriv_first : ∀ x v t, HasDerivAt (fun s : ℝ => f (x + s • v)) (first (x + t • v) v) t
  deriv_second : ∀ x v t, HasDerivAt (fun s : ℝ => first (x + s • v) v)
    (second (x + t • v) v) t

theorem convexOn_of_line_second_nonneg {f : E → ℝ} {S : Set E}
    (hS : Convex ℝ S) (hf : Continuous f) (D : LineDerivatives f)
    (h₂ : ∀ x ∈ S, ∀ v, 0 ≤ D.second x v) : ConvexOn ℝ S f := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  let v := y - x
  have hm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • v ∈ S := by
    have he : x + t • v = (1 - t) • x + t • y := by dsimp [v]; module
    rw [he]
    exact hS hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => f (x + t • v)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
      ((hf.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn)
      (fun t _ => (D.deriv_first x v t).hasDerivWithinAt)
      (fun t _ => (D.deriv_second x v t).hasDerivWithinAt)
    intro t ht
    exact h₂ _ (hm t (interior_subset ht)) v
  have h := hc.2 (x := 0) (y := 1) (by simp) (by simp) ha hb hab
  have he : x + b • v = a • x + b • y := by
    have hba : a = 1 - b := by linarith
    rw [hba]
    dsimp [v]
    module
  simpa only [smul_eq_mul, mul_zero, zero_add, mul_one, he, zero_smul, add_zero,
    one_smul, v, add_sub_cancel] using h

noncomputable def LineDerivatives.const_add {f : E → ℝ} (D : LineDerivatives f) (c : ℝ) :
    LineDerivatives (fun x => f x + c) where
  first := D.first
  second := D.second
  deriv_first x v t := (D.deriv_first x v t).add_const c
  deriv_second := D.deriv_second

noncomputable def LineDerivatives.quadraticPotential {U A J : E → ℝ}
    (DU : LineDerivatives U) (DA : LineDerivatives A) (DJ : LineDerivatives J) :
    LineDerivatives (fun p : ℝ × E => U p.2 - p.1 * A p.2 + p.1 ^ 2 / 2 * J p.2) where
  first p w := DU.first p.2 w.2 - (w.1 * A p.2 + p.1 * DA.first p.2 w.2) +
    p.1 * w.1 * J p.2 + p.1 ^ 2 / 2 * DJ.first p.2 w.2
  second p w := DU.second p.2 w.2 - (2 * w.1 * DA.first p.2 w.2 + p.1 * DA.second p.2 w.2) +
    w.1 ^ 2 * J p.2 + 2 * p.1 * w.1 * DJ.first p.2 w.2 + p.1 ^ 2 / 2 * DJ.second p.2 w.2
  deriv_first p w t := by
    have ht : HasDerivAt (fun s : ℝ => p.1 + s * w.1) w.1 t := by
      simpa using ((hasDerivAt_id t).mul_const w.1).const_add p.1
    have h := ((DU.deriv_first p.2 w.2 t).sub (ht.mul (DA.deriv_first p.2 w.2 t))).add
      (((ht.pow 2).div_const 2).mul (DJ.deriv_first p.2 w.2 t))
    apply h.congr_deriv
    simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Pi.pow_apply]
    ring
  deriv_second p w t := by
    have ht : HasDerivAt (fun s : ℝ => p.1 + s * w.1) w.1 t := by
      simpa using ((hasDerivAt_id t).mul_const w.1).const_add p.1
    have h := (((DU.deriv_second p.2 w.2 t).sub
      (((DA.deriv_first p.2 w.2 t).const_mul w.1).add (ht.mul (DA.deriv_second p.2 w.2 t)))).add
      ((ht.mul_const w.1).mul (DJ.deriv_first p.2 w.2 t))).add
      (((ht.pow 2).div_const 2).mul (DJ.deriv_second p.2 w.2 t))
    apply h.congr_deriv
    simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Pi.pow_apply]
    ring

 

theorem block_coercivity {q g j M ε v s : ℝ} (hM : 0 ≤ M)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hj : j ≤ M) (hq : v ^ 2 ≤ q)
    (hb : ∀ s : ℝ, 0 ≤ q - 2 * s * g + s ^ 2 * j) :
    ε / (4 * (M + 1)) * (v ^ 2 + s ^ 2) ≤ q - 2 * s * g + s ^ 2 * (j + ε) := by
  let c := ε / (4 * (M + 1))
  have hden : 0 < 4 * (M + 1) := by positivity
  have hc : 0 < c := div_pos hε hden
  have hcM : c * (4 * (M + 1)) = ε := by dsimp [c]; field_simp
  have hc1 : c ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hsq : 0 ≤ s ^ 2 := sq_nonneg s
  have hbase := hb s
  have htwice := hb (2 * s)
  have hmix := mul_nonneg hc.le htwice
  have hrest := mul_nonneg (by nlinarith : 0 ≤ 1 - 2 * c) hbase
  have hvc := mul_le_mul_of_nonneg_left hq hc.le
  have hjs := mul_le_mul_of_nonneg_left hj hsq
  have hjs' := mul_le_mul_of_nonneg_left hjs hc.le
  have hlast : c * s ^ 2 ≤ (ε - 2 * c * M) * s ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hsq
    nlinarith [mul_nonneg hc.le hM]
  change c * (v ^ 2 + s ^ 2) ≤ _
  nlinarith

end SKFluctuations.PinnedVariance

namespace SKFluctuations.PinnedVariance
open MeasureTheory Filter Set
open scoped Topology

 
theorem quadratic_remainder_lower_bound {B r t s v a₂ j₁ j₂ : ℝ}
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ht : |t| ≤ r)
    (ha : |a₂| ≤ B * v ^ 2) (hj₁ : |j₁| ≤ B * v) (hj₂ : |j₂| ≤ B * v ^ 2) :
    -(3 * r * B * (v ^ 2 + s ^ 2)) ≤ -t * a₂ + 2 * t * s * j₁ + t ^ 2 / 2 * j₂ := by
  have ht2 : t ^ 2 ≤ r := by
    have ht' := abs_le.mp ht
    nlinarith [sq_nonneg (r - |t|), sq_abs t]
  have h1 : |t * a₂| ≤ r * B * v ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ r * (B * v ^ 2) := mul_le_mul ht ha (abs_nonneg _) hr
      _ = _ := by ring
  have h2 : |t ^ 2 / 2 * j₂| ≤ r * B * v ^ 2 / 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ t ^ 2 / 2)]
    have h := mul_le_mul (show t ^ 2 / 2 ≤ r / 2 by linarith) hj₂ (abs_nonneg _) (by positivity)
    nlinarith
  have h3a : |2 * t * s * j₁| ≤ 2 * r * |s| * (B * v) := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  have h3 : |2 * t * s * j₁| ≤ r * B * (s ^ 2 + v ^ 2) := by
    have hsq : 2 * |s| * v ≤ s ^ 2 + v ^ 2 := by
      nlinarith [sq_nonneg (|s| - v), sq_abs s]
    have hmul := mul_le_mul_of_nonneg_left hsq (mul_nonneg hr hB)
    nlinarith
  nlinarith [le_abs_self (t * a₂), neg_le_abs (t ^ 2 / 2 * j₂),
    neg_le_abs (2 * t * s * j₁), mul_nonneg (mul_nonneg hr hB) (sq_nonneg v),
    mul_nonneg (mul_nonneg hr hB) (sq_nonneg s)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_quadraticPotential_slack {U A J : E → ℝ} {M B ε : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hUc : Continuous U) (hAc : Continuous A) (hJc : Continuous J)
    (DU : LineDerivatives U) (DA : LineDerivatives A) (DJ : LineDerivatives J)
    (hJ : ∀ x, J x ≤ M)
    (hstrong : ∀ x v, ‖v‖ ^ 2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2 * s * DA.first x v + s ^ 2 * J x)
    (ha₂ : ∀ x v, |DA.second x v| ≤ B * ‖v‖ ^ 2)
    (hj₁ : ∀ x v, |DJ.first x v| ≤ B * ‖v‖)
    (hj₂ : ∀ x v, |DJ.second x v| ≤ B * ‖v‖ ^ 2) :
    ∃ r : ℝ, 0 < r ∧ ConvexOn ℝ (Ioo (-r) r ×ˢ univ)
      (fun p : ℝ × E => U p.2 - p.1 * A p.2 + p.1 ^ 2 / 2 * (J p.2 + ε)) := by
  let c := ε / (4 * (M + 1))
  let r := c / (4 * (B + 1))
  have hc : 0 < c := div_pos hε (by positivity)
  have hr : 0 < r := div_pos hc (by positivity)
  have hc1 : c ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * (M + 1))).mpr
    nlinarith
  have hrB : r * (4 * (B + 1)) = c := by dsimp [r]; field_simp
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr.le hB]
  have hrc : 3 * r * B ≤ c := by nlinarith [mul_nonneg hr.le hB]
  refine ⟨r, hr, ?_⟩
  let DG := DU.quadraticPotential DA (DJ.const_add ε)
  apply convexOn_of_line_second_nonneg ((convex_Ioo _ _).prod convex_univ)
    (by fun_prop) DG
  intro p hp w
  change 0 ≤ DU.second p.2 w.2 - (2 * w.1 * DA.first p.2 w.2 + p.1 * DA.second p.2 w.2) +
    w.1 ^ 2 * (J p.2 + ε) + 2 * p.1 * w.1 * DJ.first p.2 w.2 +
      p.1 ^ 2 / 2 * DJ.second p.2 w.2
  have hco := block_coercivity (v := ‖w.2‖) (s := w.1) hM hε hε1 (hJ p.2)
    (hstrong p.2 w.2) (hblock p.2 w.2)
  change c * (‖w.2‖ ^ 2 + w.1 ^ 2) ≤ _ at hco
  have hrem := quadratic_remainder_lower_bound (s := w.1) hB hr.le hr1
    (show |p.1| ≤ r by exact abs_le.mpr ⟨hp.1.1.le, hp.1.2.le⟩)
    (ha₂ p.2 w.2) (hj₁ p.2 w.2) (hj₂ p.2 w.2)
  have hcR := mul_le_mul_of_nonneg_right hrc
    (show 0 ≤ ‖w.2‖ ^ 2 + w.1 ^ 2 by positivity)
  nlinarith

end SKFluctuations.PinnedVariance

namespace SKFluctuations.PinnedVariance
open MeasureTheory Filter Set
open scoped Topology
open SKFluctuations.PreKopa

 

theorem variance_le_of_block_hessian {n : ℕ}
    {U A J : (Fin n → ℝ) → ℝ} {M B : ℝ}
    {μ : Measure (Fin n → ℝ)} [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-U x))))
    (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hU : GaussianDominated (fun x => Real.exp (-U x)))
    (hUc : Continuous U) (hAc : Continuous A) (hJc : Continuous J)
    (DU : LineDerivatives U) (DA : LineDerivatives A) (DJ : LineDerivatives J)
    (hAb : ∀ x, |A x| ≤ M) (hJb : ∀ x, |J x| ≤ M)
    (hstrong : ∀ x v, ‖v‖ ^ 2 ≤ DU.second x v)
    (hblock : ∀ x v s, 0 ≤ DU.second x v - 2 * s * DA.first x v + s ^ 2 * J x)
    (ha₂ : ∀ x v, |DA.second x v| ≤ B * ‖v‖ ^ 2)
    (hj₁ : ∀ x v, |DJ.first x v| ≤ B * ‖v‖)
    (hj₂ : ∀ x v, |DJ.second x v| ≤ B * ‖v‖ ^ 2) :
    ProbabilityTheory.variance A μ ≤ ∫ x, J x ∂μ := by
  have hJi : Integrable J μ := (integrable_const M).mono' hJc.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hJb x)
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  obtain ⟨r, hr, hconv⟩ := convexOn_quadraticPotential_slack hM hB hδ hδ1 hUc hAc hJc
    DU DA DJ (fun x => le_trans (le_abs_self _) (hJb x)) hstrong hblock ha₂ hj₁ hj₂
  have hvar := variance_le_of_convex_quadraticPotential (J := fun x => J x + δ)
    (M := M + δ) hμ (by positivity) hr hU hAc (hJc.add continuous_const)
    (fun x => (hAb x).trans (by linarith)) (fun x => by
      calc
        |J x + δ| ≤ |J x| + |δ| := abs_add_le _ _
        _ ≤ M + δ := by rw [abs_of_pos hδ]; linarith [hJb x])
    hconv
  have hvar' : ProbabilityTheory.variance A μ ≤ (∫ x, J x ∂μ) + δ := by
    simpa [integral_add hJi (integrable_const δ)] using hvar
  exact hvar'.trans (by have := min_le_left ε (1 : ℝ); dsimp [δ]; linarith)

 

theorem block_nonneg_of_cauchySchwarz {q g j : ℝ} (hq : 0 ≤ q) (hj : 0 ≤ j)
    (hgj : g ^ 2 ≤ q * j) (s : ℝ) : 0 ≤ q - 2 * s * g + s ^ 2 * j := by
  obtain rfl | hq' := hq.eq_or_lt
  · have hg : g = 0 := by nlinarith [sq_nonneg g]
    simp only [hg, mul_zero, sub_zero, zero_add]
    positivity
  · apply nonneg_of_mul_nonneg_left (b := q) _ hq'
    have h := mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hgj)
    nlinarith [sq_nonneg (q - s * g)]

end SKFluctuations.PinnedVariance

namespace SKFluctuations.NoiseTransfer
open MeasureTheory ProbabilityTheory Set

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure μ] in
theorem real_fst_set (S : Set Ω) : (μ.prod ν).real {p : Ω × Ξ | p.1 ∈ S} = μ.real S := by
  rw [show {p : Ω × Ξ | p.1 ∈ S} = S ×ˢ univ by ext p; simp]
  simp [Measure.real, Measure.prod_prod]

theorem real_snd_set (S : Set Ξ) : (μ.prod ν).real {p : Ω × Ξ | p.2 ∈ S} = ν.real S := by
  rw [show {p : Ω × Ξ | p.2 ∈ S} = univ ×ˢ S by ext p; simp]
  simp [Measure.real, Measure.prod_prod]

 
theorem interval_le_add_noise {F : Ω → ℝ} {G : Ξ → ℝ}
    (hF : Measurable F) (hG : Measurable G) (a c r s : ℝ) :
    μ.real {x | |F x - a| ≤ r} ≤
      ((μ.prod ν).map (fun p => F p.1 + G p.2)).real (Icc (a + c - (r + s)) (a + c + (r + s))) +
        ν.real {y | s < |G y - c|} := by
  have hs : {p : Ω × Ξ | |F p.1 - a| ≤ r} ⊆
      (fun p : Ω × Ξ => F p.1 + G p.2) ⁻¹' Icc (a + c - (r + s)) (a + c + (r + s)) ∪
        {p : Ω × Ξ | s < |G p.2 - c|} := by
    intro p hp
    by_cases hg : s < |G p.2 - c|
    · exact Or.inr hg
    · change |F p.1 - a| ≤ r at hp
      have h1 := abs_le.mp hp
      have h2 := abs_le.mp (le_of_not_gt hg)
      exact Or.inl ⟨by dsimp; linarith, by dsimp; linarith⟩
  calc
    _ = (μ.prod ν).real {p : Ω × Ξ | |F p.1 - a| ≤ r} := (real_fst_set _).symm
    _ ≤ _ := (measureReal_mono hs).trans (measureReal_union_le _ _)
    _ = _ := by
      have heq : (μ.prod ν).real {p : Ω × Ξ | s < |G p.2 - c|} =
          ν.real {y | s < |G y - c|} := real_snd_set (μ := μ) (ν := ν) {y | s < |G y - c|}
      rw [heq]
      congr 1
      exact (congrArg ENNReal.toReal (Measure.map_apply ((hF.comp measurable_fst).add
        (hG.comp measurable_snd)) measurableSet_Icc)).symm

 

theorem tail_le_add_noise {F : Ω → ℝ} {G : Ξ → ℝ}
    (hF : Measurable F) (hG : Measurable G) (a c u s : ℝ) :
    μ.real {x | u ≤ |F x - a|} ≤
      ((μ.prod ν).map (fun p => F p.1 + G p.2)).real {z | u - s ≤ |z - (a + c)|} +
        ν.real {y | s < |G y - c|} := by
  have hs : {p : Ω × Ξ | u ≤ |F p.1 - a|} ⊆
      (fun p : Ω × Ξ => F p.1 + G p.2) ⁻¹' {z | u - s ≤ |z - (a + c)|} ∪
        {p : Ω × Ξ | s < |G p.2 - c|} := by
    intro p hp
    by_cases hg : s < |G p.2 - c|
    · exact Or.inr hg
    · apply Or.inl
      change u ≤ |F p.1 - a| at hp
      have hG' := le_of_not_gt hg
      have htri := abs_sub (F p.1 + G p.2 - (a + c)) (G p.2 - c)
      rw [show F p.1 + G p.2 - (a + c) - (G p.2 - c) = F p.1 - a by ring] at htri
      dsimp
      linarith
  calc
    _ = (μ.prod ν).real {p : Ω × Ξ | u ≤ |F p.1 - a|} := (real_fst_set _).symm
    _ ≤ _ := (measureReal_mono hs).trans (measureReal_union_le _ _)
    _ = _ := by
      have heq : (μ.prod ν).real {p : Ω × Ξ | s < |G p.2 - c|} =
          ν.real {y | s < |G y - c|} := real_snd_set (μ := μ) (ν := ν) {y | s < |G y - c|}
      rw [heq]
      congr 1
      exact (congrArg ENNReal.toReal (Measure.map_apply ((hF.comp measurable_fst).add
        (hG.comp measurable_snd)) (measurableSet_le measurable_const
          ((measurable_id.sub_const _).abs)))).symm

 
theorem strict_tail_le_variance {F : Ω → ℝ} (hF : MemLp F 2 μ) {s : ℝ} (hs : 0 < s) :
    μ.real {x | s < |F x - ∫ y, F y ∂μ|} ≤ variance F μ / s ^ 2 := by
  have h := meas_ge_le_variance_div_sq hF hs
  have hn : 0 ≤ variance F μ / s ^ 2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hh := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_ofReal hn] at hh
  have hsub : {x | s < |F x - ∫ y, F y ∂μ|} ⊆ {x | s ≤ |F x - ∫ y, F y ∂μ|} := by
    intro x hx
    exact le_of_lt (show s < |F x - ∫ y, F y ∂μ| from hx)
  exact (measureReal_mono hsub).trans hh

end SKFluctuations.NoiseTransfer

namespace SKFluctuations.NoiseTransfer
open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem real_map_interval {F : Ω → ℝ} (hF : Measurable F) (a r : ℝ) :
    (μ.map F).real (Icc (a - r) (a + r)) = μ.real {x | |F x - a| ≤ r} := by
  unfold Measure.real
  rw [Measure.map_apply hF measurableSet_Icc]
  apply congrArg (fun S => (μ S).toReal)
  ext x
  simp only [mem_preimage, mem_Icc, mem_ofPred_eq, abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

theorem real_map_absTail {F : Ω → ℝ} (hF : Measurable F) (a u : ℝ) :
    (μ.map F).real {z | u ≤ |z - a|} = μ.real {x | u ≤ |F x - a|} := by
  unfold Measure.real
  have hm : MeasurableSet {z : ℝ | u ≤ |z - a|} :=
    measurableSet_le measurable_const ((measurable_id.sub_const a).abs)
  rw [Measure.map_apply hF hm]
  rfl

end SKFluctuations.NoiseTransfer

namespace SKFluctuations
open NoiseTransfer

theorem augmentedLaw_eq_completed (beta : ℝ) (n : ℕ) :
    augmentedLaw beta n = ((completedLaw beta n).prod (expMeasure 1)).map
      (fun p => completedFreeEnergy beta n p.1 + p.2) := by
  have hp := (measurePreserving_toCompletedDisorder beta n).prod
    (MeasurePreserving.id (expMeasure 1))
  rw [← hp.map_eq, Measure.map_map (by fun_prop) hp.measurable]
  rfl

theorem completed_interval_bound {beta : ℝ} (hb : beta ≠ 0) (n : ℕ)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    (completedLaw beta n).real {g | |completedFreeEnergy beta n g - meanFreeEnergy beta n| ≤ r} ≤
      2 * PreKopa.Density.densityBoundConstant * (r + s) / augmentedSD beta n + 1 / s ^ 2 := by
  have h := interval_le_add_noise (μ := completedLaw beta n) (ν := expMeasure 1)
    (continuous_completedFreeEnergy beta n).measurable measurable_id (meanFreeEnergy beta n) 1 r s
  simp only [id_eq] at h
  rw [← augmentedLaw_eq_completed] at h
  have hn := strict_tail_le_variance (memLp_expMeasure_one 2) hs
  simp only [id_eq, mean_expMeasure_one, variance_expMeasure_one] at hn
  exact h.trans (add_le_add (augmented_interval_mass hb n _ (by positivity)) hn)

theorem completed_tail_bound {beta : ℝ} (hb : beta ≠ 0) (n : ℕ)
    (u : ℝ) {s : ℝ} (hs : 0 < s) :
    (completedLaw beta n).real {g | u ≤ |completedFreeEnergy beta n g - meanFreeEnergy beta n|} ≤
      PreKopa.Density.tailConstant * Real.exp (-PreKopa.tailRate * (u - s) / augmentedSD beta n) +
        1 / s ^ 2 := by
  have h := tail_le_add_noise (μ := completedLaw beta n) (ν := expMeasure 1)
    (continuous_completedFreeEnergy beta n).measurable measurable_id (meanFreeEnergy beta n) 1 u s
  simp only [id_eq] at h
  rw [← augmentedLaw_eq_completed] at h
  have hn := strict_tail_le_variance (memLp_expMeasure_one 2) hs
  simp only [id_eq, mean_expMeasure_one, variance_expMeasure_one] at hn
  exact h.trans (add_le_add (augmented_tail hb n _) hn)

 
theorem freeEnergy_interval_bound {beta : ℝ} (hb : beta ≠ 0) (n : ℕ)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    (disorderLaw n).real {g | |freeEnergy beta n g - meanFreeEnergy beta n| ≤ r} ≤
      2 * PreKopa.Density.densityBoundConstant * (r + 2 * s) / augmentedSD beta n +
        (beta ^ 2 / 2 + 1) / s ^ 2 := by
  have h := interval_le_add_noise (μ := disorderLaw n)
    (ν := gaussianReal 0 (completionVariance beta))
    (continuous_freeEnergy beta n).measurable measurable_id (meanFreeEnergy beta n) 0 r s
  change (disorderLaw n).real _ ≤ ((completedLaw beta n).map (completedFreeEnergy beta n)).real
    (Set.Icc (meanFreeEnergy beta n + 0 - (r + s)) (meanFreeEnergy beta n + 0 + (r + s))) + _ at h
  rw [add_zero, real_map_interval (continuous_completedFreeEnergy beta n).measurable] at h
  have hn := strict_tail_le_variance
    (memLp_id_gaussianReal (μ := 0) (v := completionVariance beta) (2 : NNReal)) hs
  simp only [id_eq, integral_id_gaussianReal, variance_id_gaussianReal] at hn
  have hh := h.trans (add_le_add (completed_interval_bound hb n (by positivity) hs) hn)
  have hc : (completionVariance beta : ℝ) = beta ^ 2 / 2 := rfl
  rw [hc] at hh
  convert hh using 1
  first | rfl | ring_nf

 

theorem freeEnergy_tail_bound {beta : ℝ} (hb : beta ≠ 0) (n : ℕ)
    (u : ℝ) {s : ℝ} (hs : 0 < s) :
    (disorderLaw n).real {g | u ≤ |freeEnergy beta n g - meanFreeEnergy beta n|} ≤
      PreKopa.Density.tailConstant * Real.exp (-PreKopa.tailRate * (u - 2 * s) / augmentedSD beta n) +
        (beta ^ 2 / 2 + 1) / s ^ 2 := by
  have h := tail_le_add_noise (μ := disorderLaw n)
    (ν := gaussianReal 0 (completionVariance beta))
    (continuous_freeEnergy beta n).measurable measurable_id (meanFreeEnergy beta n) 0 u s
  change (disorderLaw n).real _ ≤ ((completedLaw beta n).map (completedFreeEnergy beta n)).real
    {z | u - s ≤ |z - (meanFreeEnergy beta n + 0)|} + _ at h
  rw [add_zero, real_map_absTail (continuous_completedFreeEnergy beta n).measurable] at h
  have hn := strict_tail_le_variance
    (memLp_id_gaussianReal (μ := 0) (v := completionVariance beta) (2 : NNReal)) hs
  simp only [id_eq, integral_id_gaussianReal, variance_id_gaussianReal] at hn
  have hh := h.trans (add_le_add (completed_tail_bound hb n (u - s) hs) hn)
  have hc : (completionVariance beta : ℝ) = beta ^ 2 / 2 := rfl
  rw [hc] at hh
  convert hh using 1
  first | rfl | ring_nf

end SKFluctuations

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

 
def continuation (μ : Measure Ω) (m : ℝ) (F : ℝ → Ω → ℝ) (t : ℝ) : ℝ :=
  Real.log (∫ x, Real.exp (m * F t x) ∂μ) / m

 
def tiltedMean (μ : Measure Ω) (m : ℝ) (F : Ω → ℝ) (A : Ω → ℝ) : ℝ :=
  (∫ x, A x * Real.exp (m * F x) ∂μ) / (∫ x, Real.exp (m * F x) ∂μ)

omit [MeasurableSpace Ω] in
theorem source_lipschitz {F F₁ : ℝ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (F₁ t x) t)
    (hb : ∀ t x, |F₁ t x| ≤ C) (x : Ω) (s t : ℝ) :
    |F s x - F t x| ≤ C * |s - t| := by
  have hl : LipschitzWith ⟨C, hC⟩ (fun t => F t x) :=
    lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t x).differentiableAt) (fun t => by
      change ‖deriv (fun s => F s x) t‖ ≤ C
      rw [(hd t x).deriv, Real.norm_eq_abs]
      exact hb t x)
  exact hl.dist_le_mul s t

omit [MeasurableSpace Ω] in
theorem exponential_local_bound {F F₁ : ℝ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (F₁ t x) t)
    (hb : ∀ t x, |F₁ t x| ≤ C) (m t : ℝ) {s : ℝ} (hs : s ∈ Metric.ball t 1) (x : Ω) :
    Real.exp (m * F s x) ≤ Real.exp (|m| * C) * Real.exp (m * F t x) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hst : |s - t| ≤ 1 := (Metric.mem_ball.mp hs).le
  have hv := (source_lipschitz hC hd hb x s t).trans (by simpa using mul_le_mul_of_nonneg_left hst hC)
  have hm := mul_le_mul_of_nonneg_left hv (abs_nonneg m)
  have h := le_abs_self (m * (F s x - F t x))
  rw [abs_mul] at h
  nlinarith

theorem integrable_weighted {W A : Ω → ℝ} {C : ℝ} (hW : Integrable W μ)
    (hA : Measurable A) (hb : ∀ x, |A x| ≤ C) : Integrable (fun x => A x * W x) μ := by
  apply (hW.norm.const_mul C).mono' (hA.aestronglyMeasurable.mul hW.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖A x * W x‖ ≤ C * ‖W x‖
  rw [norm_mul, Real.norm_eq_abs (A x)]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

 

theorem hasDerivAt_tested_integral {F F₁ A A₁ : ℝ → Ω → ℝ} {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hF : ∀ t, Measurable (F t)) (hF₁ : ∀ t, Measurable (F₁ t))
    (hA : ∀ t, Measurable (A t)) (hA₁ : ∀ t, Measurable (A₁ t))
    (hdF : ∀ t x, HasDerivAt (fun s => F s x) (F₁ t x) t)
    (hdA : ∀ t x, HasDerivAt (fun s => A s x) (A₁ t x) t)
    (hbF : ∀ t x, |F₁ t x| ≤ C)
    (hbA : ∀ t x, |A t x| ≤ B) (hbA₁ : ∀ t x, |A₁ t x| ≤ B)
    (m t : ℝ) (hi : Integrable (fun x => Real.exp (m * F t x)) μ) :
    HasDerivAt (fun s => ∫ x, A s x * Real.exp (m * F s x) ∂μ)
      (∫ x, (A₁ t x + m * A t x * F₁ t x) * Real.exp (m * F t x) ∂μ) t := by
  let D : ℝ → Ω → ℝ := fun s x =>
    (A₁ s x + m * A s x * F₁ s x) * Real.exp (m * F s x)
  have hm (s : ℝ) : AEStronglyMeasurable (fun x => A s x * Real.exp (m * F s x)) μ :=
    ((hA s).mul (((hF s).const_mul m).exp)).aestronglyMeasurable
  have hmD : AEStronglyMeasurable (D t) μ :=
    (((hA₁ t).add (((hA t).const_mul m).mul (hF₁ t))).mul
      (((hF t).const_mul m).exp)).aestronglyMeasurable
  have hbD (x : Ω) (s : ℝ) (hs : s ∈ Metric.ball t 1) : ‖D s x‖ ≤
      ((B + |m| * B * C) * Real.exp (|m| * C)) * Real.exp (m * F t x) := by
    have hcoef : |A₁ s x + m * A s x * F₁ s x| ≤ B + |m| * B * C := by
      calc
        _ ≤ |A₁ s x| + |m * A s x * F₁ s x| := abs_add_le _ _
        _ = |A₁ s x| + |m| * |A s x| * |F₁ s x| := by simp only [abs_mul]
        _ ≤ B + |m| * B * C := add_le_add (hbA₁ s x)
          (mul_le_mul (mul_le_mul_of_nonneg_left (hbA s x) (abs_nonneg _)) (hbF s x)
            (abs_nonneg _) (by positivity))
    dsimp [D]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (B + |m| * B * C) * (Real.exp (|m| * C) * Real.exp (m * F t x)) :=
        mul_le_mul hcoef (exponential_local_bound hC hdF hbF m t hs x)
          (Real.exp_nonneg _) (by positivity)
      _ = _ := by ring
  have hdD (x : Ω) (s : ℝ) : HasDerivAt
      (fun r => A r x * Real.exp (m * F r x)) (D s x) s := by
    have h := (hdA s x).mul (((hdF s x).const_mul m).exp)
    apply h.congr_deriv
    dsimp [D]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball t 1) (bound := fun x =>
      ((B + |m| * B * C) * Real.exp (|m| * C)) * Real.exp (m * F t x))
    (Metric.ball_mem_nhds t (by norm_num)) (Eventually.of_forall hm)
    (integrable_weighted hi (hA t) (hbA t)) hmD
    (Eventually.of_forall hbD) (hi.const_mul _)
    (Eventually.of_forall fun x s _ => hdD x s)).2

theorem hasDerivAt_partition {F F₁ : ℝ → Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ t, Measurable (F t)) (hF₁ : ∀ t, Measurable (F₁ t))
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (F₁ t x) t)
    (hb : ∀ t x, |F₁ t x| ≤ C) (m t : ℝ)
    (hi : Integrable (fun x => Real.exp (m * F t x)) μ) :
    HasDerivAt (fun s => ∫ x, Real.exp (m * F s x) ∂μ)
      (m * ∫ x, F₁ t x * Real.exp (m * F t x) ∂μ) t := by
  have h := hasDerivAt_tested_integral hC (B := 1) (by norm_num) hF hF₁
    (fun _ => measurable_const) (fun _ => measurable_const) hd
    (fun s _ => hasDerivAt_const s (1 : ℝ)) hb (fun _ _ => by simp)
    (fun _ _ => by norm_num) m t hi
  simpa only [one_mul, mul_one, zero_add, mul_assoc, integral_const_mul] using h

theorem partition_pos [IsProbabilityMeasure μ] {F : Ω → ℝ} (m : ℝ)
    (hi : Integrable (fun x => Real.exp (m * F x)) μ) :
    0 < ∫ x, Real.exp (m * F x) ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun _ => Real.exp_nonneg _) hi).mpr
  simp only [Function.support, ne_eq, Real.exp_ne_zero, not_false_eq_true, ofPred_true,
    measure_univ, zero_lt_one]

theorem hasDerivAt_continuation [IsProbabilityMeasure μ] {F F₁ : ℝ → Ω → ℝ} {C m : ℝ}
    (hC : 0 ≤ C) (hm : m ≠ 0)
    (hF : ∀ t, Measurable (F t)) (hF₁ : ∀ t, Measurable (F₁ t))
    (hd : ∀ t x, HasDerivAt (fun s => F s x) (F₁ t x) t)
    (hb : ∀ t x, |F₁ t x| ≤ C) (t : ℝ)
    (hi : Integrable (fun x => Real.exp (m * F t x)) μ) :
    HasDerivAt (continuation μ m F) (tiltedMean μ m (F t) (F₁ t)) t := by
  have h := ((hasDerivAt_partition hC hF hF₁ hd hb m t hi).log (partition_pos m hi).ne').div_const m
  apply h.congr_deriv
  dsimp [tiltedMean]
  field_simp

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

 
theorem hasDerivAt_tiltedMean {F F₁ A A₁ : ℝ → Ω → ℝ} {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hF : ∀ t, Measurable (F t)) (hF₁ : ∀ t, Measurable (F₁ t))
    (hA : ∀ t, Measurable (A t)) (hA₁ : ∀ t, Measurable (A₁ t))
    (hdF : ∀ t x, HasDerivAt (fun s => F s x) (F₁ t x) t)
    (hdA : ∀ t x, HasDerivAt (fun s => A s x) (A₁ t x) t)
    (hbF : ∀ t x, |F₁ t x| ≤ C)
    (hbA : ∀ t x, |A t x| ≤ B) (hbA₁ : ∀ t x, |A₁ t x| ≤ B)
    (m t : ℝ) (hi : Integrable (fun x => Real.exp (m * F t x)) μ) :
    HasDerivAt (fun s => tiltedMean μ m (F s) (A s))
      (tiltedMean μ m (F t) (A₁ t) + m *
        (tiltedMean μ m (F t) (fun x => A t x * F₁ t x) -
          tiltedMean μ m (F t) (A t) * tiltedMean μ m (F t) (F₁ t))) t := by
  have h := (hasDerivAt_tested_integral hC hB hF hF₁ hA hA₁ hdF hdA hbF hbA hbA₁ m t hi).div
    (hasDerivAt_partition hC hF hF₁ hdF hbF m t hi) (partition_pos m hi).ne'
  have h₁ := integrable_weighted hi (hA₁ t) (hbA₁ t)
  have h₂ : Integrable (fun x => (A t x * F₁ t x) * Real.exp (m * F t x)) μ := integrable_weighted hi ((hA t).mul (hF₁ t)) (fun x => show |A t x * F₁ t x| ≤ B * C by
    rw [abs_mul]
    exact mul_le_mul (hbA t x) (hbF t x) (abs_nonneg _) hB)
  have he : (∫ x, (A₁ t x + m * A t x * F₁ t x) * Real.exp (m * F t x) ∂μ) =
      (∫ x, A₁ t x * Real.exp (m * F t x) ∂μ) +
      m * (∫ x, (A t x * F₁ t x) * Real.exp (m * F t x) ∂μ) := by
    rw [← integral_const_mul, ← integral_add h₁ (h₂.const_mul m)]
    congr 1
    funext x
    ring
  apply h.congr_deriv
  rw [he]
  dsimp [tiltedMean]
  field_simp
  ring

 

theorem hasDerivAt_continuation_gradient {F F₁ F₂ : ℝ → Ω → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hF : ∀ t, Measurable (F t)) (hF₁ : ∀ t, Measurable (F₁ t))
    (hF₂ : ∀ t, Measurable (F₂ t))
    (hdF : ∀ t x, HasDerivAt (fun s => F s x) (F₁ t x) t)
    (hdF₁ : ∀ t x, HasDerivAt (fun s => F₁ s x) (F₂ t x) t)
    (hbF₁ : ∀ t x, |F₁ t x| ≤ C) (hbF₂ : ∀ t x, |F₂ t x| ≤ C)
    (m t : ℝ) (hi : Integrable (fun x => Real.exp (m * F t x)) μ) :
    HasDerivAt (fun s => tiltedMean μ m (F s) (F₁ s))
      (tiltedMean μ m (F t) (F₂ t) + m *
        (tiltedMean μ m (F t) (fun x => (F₁ t x) ^ 2) -
          (tiltedMean μ m (F t) (F₁ t)) ^ 2)) t := by
  simpa only [pow_two] using
    hasDerivAt_tiltedMean hC hC hF hF₁ hF₁ hF₂ hdF hdF₁ hbF₁ hbF₁ hbF₂ m t hi

 
def tiltedLaw (μ : Measure Ω) (m : ℝ) (F : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp (m * F x) /
    (∫ y, Real.exp (m * F y) ∂μ)))

theorem tiltedLaw_isProbability {m : ℝ} {F : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (m * F x)) μ) :
    IsProbabilityMeasure (tiltedLaw μ m F) := by
  exact isProbabilityMeasure_tilted hi

theorem integral_tiltedLaw {m : ℝ} {F A : Ω → ℝ}
    (hF : Measurable F) (hi : Integrable (fun x => Real.exp (m * F x)) μ) :
    (∫ x, A x ∂tiltedLaw μ m F) = tiltedMean μ m F A := by
  rw [tiltedLaw, integral_withDensity_eq_integral_toReal_smul
    ((((hF.const_mul m).exp).div_const _).ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_nonneg _) (partition_pos m hi).le), smul_eq_mul]
  rw [tiltedMean, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

theorem tiltedMean_nonneg {m : ℝ} {F A : Ω → ℝ}
    (hi : Integrable (fun x => Real.exp (m * F x)) μ) (hA : ∀ x, 0 ≤ A x) :
    0 ≤ tiltedMean μ m F A := by
  apply div_nonneg _ (partition_pos m hi).le
  exact integral_nonneg fun x => mul_nonneg (hA x) (Real.exp_nonneg _)

theorem tiltedMean_square_sub_nonneg {m : ℝ} {F A : Ω → ℝ} {B : ℝ}
    (hF : Measurable F) (hA : Measurable A)
    (hi : Integrable (fun x => Real.exp (m * F x)) μ) (hb : ∀ x, |A x| ≤ B) :
    0 ≤ tiltedMean μ m F (fun x => A x ^ 2) - (tiltedMean μ m F A) ^ 2 := by
  have := tiltedLaw_isProbability hi
  have hl : MemLp A 2 (tiltedLaw μ m F) :=
    MemLp.of_bound hA.aestronglyMeasurable B (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  have hv := variance_nonneg A (tiltedLaw μ m F)
  rw [variance_eq_sub hl] at hv
  change 0 ≤ (∫ x, A x ^ 2 ∂tiltedLaw μ m F) - (∫ x, A x ∂tiltedLaw μ m F) ^ 2 at hv
  simpa only [integral_tiltedLaw hF hi] using hv

end SKFluctuations.Hierarchy

end

end OAI
