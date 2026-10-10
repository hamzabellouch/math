import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.SplitIfs

namespace OAI

/-!
# Volumes of standard simplices and their products

The simplex-volume calculation below uses Tonelli's theorem and induction on the
dimension.  At first coordinate `t`, the remaining section is a simplex of radius
`r - t`; its volume is integrated over `0 ≤ t ≤ r`.  The Euclidean versions use
the measure-preserving equivalence between coordinate space and `EuclideanSpace`.
The product formula is proved using the product Lebesgue measure under the
canonical splitting of `Fin (p + q)`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProjectionCounterexample

/-- The coordinate standard simplex with nonnegative coordinates and sum at most `r`. -/
def coordinateSimplex (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

theorem coordinateSimplex_measurableSet (n : ℕ) (r : ℝ) :
    MeasurableSet (coordinateSimplex n r) := by
  unfold coordinateSimplex
  measurability

theorem coordinateSimplex_eq_empty_of_neg (n : ℕ) {r : ℝ} (hr : r < 0) :
    coordinateSimplex n r = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx.1 i
  exact (not_lt_of_ge (hsum.trans hx.2)) hr

theorem integral_simplex_slice (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ t in Icc 0 r, ENNReal.ofReal ((r - t) ^ n / (n.factorial : ℝ))) =
      ENNReal.ofReal (r ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
  have hi : IntegrableOn (fun t : ℝ => (r - t) ^ n / (n.factorial : ℝ)) (Icc 0 r) :=
    ContinuousOn.integrableOn_Icc (by fun_prop)
  have hn : 0 ≤ᵐ[volume.restrict (Icc 0 r)]
      (fun t : ℝ => (r - t) ^ n / (n.factorial : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) n) (by positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr,
    intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n) r]
  simp only [sub_self, sub_zero, integral_pow,
    zero_pow (Nat.succ_ne_zero n), sub_zero]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]

theorem volume_coordinateSimplex (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    volume (coordinateSimplex n r) =
      ENNReal.ofReal (r ^ n / (n.factorial : ℝ)) := by
  induction n generalizing r with
  | zero =>
    have h : coordinateSimplex 0 r = univ := by
      ext x
      simp [coordinateSimplex, hr]
    simp [h, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
    have he (p : ℝ × (Fin n → ℝ)) : e.symm p = Fin.cons p.1 p.2 := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [e, MeasurableEquiv.piFinSuccAbove]
    have hslice (t : ℝ) :
        Prod.mk t ⁻¹' (e.symm ⁻¹' coordinateSimplex (n + 1) r) =
        if t ∈ Icc 0 r then coordinateSimplex n (r - t) else ∅ := by
      ext x
      simp only [mem_preimage, he, coordinateSimplex, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_succ]
      split_ifs with ht
      · simp only [mem_ofPred_eq]
        constructor
        · rintro ⟨⟨_, hx⟩, hs⟩
          exact ⟨hx, by linarith⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨ht.1, hx⟩, by linarith⟩
      · simp only [mem_empty_iff_false, iff_false]
        rintro ⟨⟨ht0, hx⟩, hs⟩
        apply ht
        have hsum : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
        exact ⟨ht0, by linarith⟩
    rw [← (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).symm.measure_preimage_equiv]
    change volume (e.symm ⁻¹' coordinateSimplex (n + 1) r) = _
    rw [Measure.volume_eq_prod, Measure.prod_apply
      ((coordinateSimplex_measurableSet (n + 1) r).preimage e.symm.measurable)]
    simp_rw [hslice]
    have hfun : (fun t : ℝ => volume
        (if t ∈ Icc 0 r then coordinateSimplex n (r - t) else ∅)) =
        (Icc 0 r).indicator
          (fun t : ℝ => ENNReal.ofReal ((r - t) ^ n / (n.factorial : ℝ))) := by
      funext t
      by_cases ht : t ∈ Icc 0 r
      · simp [ht, ih (r - t) (sub_nonneg.mpr ht.2)]
      · simp [ht]
    rw [hfun, lintegral_indicator measurableSet_Icc]
    exact integral_simplex_slice n hr

/-- The standard simplex has ordinary Lebesgue volume `1 / n!`. -/
theorem volume_unit_coordinateSimplex (n : ℕ) :
    volume (coordinateSimplex n 1) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  simpa using volume_coordinateSimplex n 1 zero_le_one

/-- Exact volume of a possibly degenerate linear image of the coordinate simplex. -/
theorem volume_linearImage_unit_coordinateSimplex (n : ℕ)
    (f : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    volume (f '' coordinateSimplex n 1) =
      ENNReal.ofReal (|LinearMap.det f| / (n.factorial : ℝ)) := by
  rw [Measure.addHaar_image_linearMap, volume_unit_coordinateSimplex,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- The same volume statement in Euclidean space with its canonical Euclidean measure. -/
theorem volume_unit_euclideanSimplex (n : ℕ) :
    volume {x : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  have hs : MeasurableSet
      {x : EuclideanSpace ℝ (Fin n) | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
    measurability
  rw [← (PiLp.volume_preserving_toLp (Fin n)).measure_preimage hs.nullMeasurableSet]
  exact volume_unit_coordinateSimplex n

/-- Real-valued version of the Euclidean simplex volume. -/
theorem realVolume_unit_euclideanSimplex (n : ℕ) :
    (volume {x : EuclideanSpace ℝ (Fin n) |
      (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}).toReal = 1 / (n.factorial : ℝ) := by
  rw [volume_unit_euclideanSimplex, ENNReal.toReal_ofReal]
  positivity


/-- The coordinate product, with the first `p` and last `q` coordinates separated. -/
def coordinateSimplexProduct (p q : ℕ) : Set (Fin (p + q) → ℝ) :=
  {x | (fun i : Fin p => x (Fin.castAdd q i)) ∈ coordinateSimplex p 1 ∧
    (fun i : Fin q => x (Fin.natAdd p i)) ∈ coordinateSimplex q 1}

/-- The product-volume identity uses the actual product Lebesgue measure. -/
theorem volume_coordinateSimplexProduct (p q : ℕ) :
    volume (coordinateSimplexProduct p q) =
      ENNReal.ofReal (1 / ((p.factorial : ℝ) * (q.factorial : ℝ))) := by
  let e : (Fin (p + q) → ℝ) ≃ᵐ ((Fin p → ℝ) × (Fin q → ℝ)) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (p + q) => ℝ)
      finSumFinEquiv).symm.trans (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))
  have he (x : Fin (p + q) → ℝ) :
      e x = ((fun i : Fin p => x (Fin.castAdd q i)),
        (fun i : Fin q => x (Fin.natAdd p i))) := by
    rfl
  have hm : MeasurePreserving e :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (p + q) => ℝ)
      finSumFinEquiv).symm.trans (volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ))
  have hs : coordinateSimplexProduct p q =
      e ⁻¹' (coordinateSimplex p 1 ×ˢ coordinateSimplex q 1) := by
    ext x
    simp [coordinateSimplexProduct, he]
  rw [hs, hm.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod,
    volume_unit_coordinateSimplex, volume_unit_coordinateSimplex,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (p.factorial : ℝ))]
  congr 1
  ring

/-- Product-simplex volume in the canonical Euclidean coordinates. -/
theorem volume_euclideanSimplexProduct (p q : ℕ) :
    volume {x : EuclideanSpace ℝ (Fin (p + q)) |
      ((∀ i : Fin p, 0 ≤ x (Fin.castAdd q i)) ∧
        ∑ i : Fin p, x (Fin.castAdd q i) ≤ 1) ∧
      ((∀ i : Fin q, 0 ≤ x (Fin.natAdd p i)) ∧
        ∑ i : Fin q, x (Fin.natAdd p i) ≤ 1)} =
      ENNReal.ofReal (1 / ((p.factorial : ℝ) * (q.factorial : ℝ))) := by
  rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp
    (Fin (p + q))).symm.measure_preimage_equiv]
  exact volume_coordinateSimplexProduct p q

end ProjectionCounterexample

end OAI
