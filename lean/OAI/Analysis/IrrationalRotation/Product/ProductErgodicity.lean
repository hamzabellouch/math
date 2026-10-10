import OAI.Analysis.IrrationalRotation.Sampling.ProductCharacters
import OAI.Analysis.IrrationalRotation.Product.IndependentRotation
import OAI.Analysis.IrrationalRotation.Sampling.ErgodicCharacterCriterion
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace OAI

namespace InvariantProjection.ProductRotation

open MeasureTheory

variable {ι : Type*}

theorem integer_affine_independent {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (m : ℤ)
    (heq : v.sum (fun i z => (z : ℝ) * θ i) = m) : v = 0 := by
  by_contra hv
  exact (Invariant233.IndependentRotation.irrational_finsupp_int_sum hθ v hv).ne_int m heq

theorem measurePreserving_product_translation (a : ι → UnitAddCircle) :
    MeasurePreserving (fun x : ι → UnitAddCircle => x + a)
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have hcoord (i : ι) : MeasurePreserving
      (fun x : UnitAddCircle => x + a i) volume volume :=
    measurePreserving_add_right volume _
  refine ⟨Measurable.of_eval (fun i => (measurable_pi_apply i).add_const _), ?_⟩
  change (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))).map
      (fun x i => x i + a i) = _
  rw [Measure.infinitePi_map_pi _ (fun i => (hcoord i).measurable)]
  simp only [(hcoord _).map_eq]

theorem product_rotation_integer_ergodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    {q : ℤ} (hq : q ≠ 0) :
    Ergodic (fun x : ι → UnitAddCircle =>
      fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  apply Invariant233.Characters.ergodic_of_dense_continuous_eigenfunctions
    (measurePreserving_product_translation (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    (0 : ι →₀ ℤ) productCharacter
    (fun v => productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    productCharacter_zero span_productCharacter_closure_eq_top
  · intro v hv
    exact productCharacter_ne_one θ (integer_affine_independent hθ) hv hq
  · intro v _ x
    exact productCharacter_translation v θ q x

theorem product_rotation_ergodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ)) :
    Ergodic (fun x : ι → UnitAddCircle => fun i => x i + (θ i : UnitAddCircle))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  simpa only [Int.cast_one, one_mul] using
    product_rotation_integer_ergodic hθ (q := 1) one_ne_zero

theorem product_rotation_totalErgodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    {n : ℕ} (hn : 0 < n) :
    Ergodic (fun x : ι → UnitAddCircle => fun i => x i + (θ i : UnitAddCircle))^[n]
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  change Ergodic (fun x : ι → UnitAddCircle => x + fun i => (θ i : UnitAddCircle))^[n] _
  rw [add_right_iterate]
  have hcoe : (fun i => (((n : ℝ) * θ i : ℝ) : UnitAddCircle)) =
      n • (fun i => (θ i : UnitAddCircle)) := by
    funext i
    simpa only [Pi.smul_apply, nsmul_eq_mul] using
      (AddCircle.coe_nsmul (p := (1 : ℝ)) (n := n) (x := θ i))
  have he := product_rotation_integer_ergodic hθ (q := (n : ℤ))
    (by exact_mod_cast Nat.ne_of_gt hn)
  simp only [Int.cast_natCast] at he
  change Ergodic (fun x : ι → UnitAddCircle =>
    x + (fun i => (((n : ℝ) * θ i : ℝ) : UnitAddCircle))) _ at he
  rwa [hcoe] at he

end InvariantProjection.ProductRotation

end OAI
