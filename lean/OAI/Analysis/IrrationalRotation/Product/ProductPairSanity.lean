import OAI.Analysis.IrrationalRotation.Model.ProductPairIdentity
import OAI.Analysis.IrrationalRotation.Product.ProductCocycle
import OAI.Analysis.IrrationalRotation.Analysis.TriangularLawProperties
import OAI.Analysis.IrrationalRotation.Rotation.UnrestrictedDiagonal

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.ProductModel

@[simp] theorem cocycleRatio_self (θ c : ℕ → ℝ) (x : Base) (k : ℤ) :
    cocycleRatio θ c x x k = 1 := by
  exact div_self (ne_of_gt (ProductCocycle.cocycleVersion_pos θ c k x))

@[simp] theorem ratioDiagonal_self (θ c : ℕ → ℝ) (x : Base) :
    ratioDiagonal θ c x x = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext k
  change SequenceHilbert.boundedDiagonal
    (fun k => (cocycleRatio θ c x x k : ℂ)) v k = v k
  rw [SequenceHilbert.boundedDiagonal_apply_of_bound _ 1 zero_le_one]
  · simp
  · intro j
    simp

theorem pairIdentity_self_iff (θ c : ℕ → ℝ)
    (F : Base → Fiber →L[ℂ] Fiber) (x : Base) :
    PairIdentity θ c F (x, x) ↔ IsIdempotentElem (F x) := by
  simp only [PairIdentity, cocycleRatio_self, zero_lt_one, le_refl,
    and_self, forall_const, true_and, ratioDiagonal_self, mul_one]
  rw [sub_mul, one_mul, sub_eq_zero]
  exact eq_comm

@[simp] theorem triangularLaw_empty_eq_diagonal :
    triangularLaw ∅ = baseMeasure.map (fun x : Base => (x, x)) := by
  have he : triangularEvent ∅ = Set.univ := by
    ext xy
    simp [triangularEvent]
  rw [triangularLaw, he, Measure.restrict_univ]
  have hs : selectedEndpoint ∅ = fun x _ => x := by
    funext x z i
    simp [selectedEndpoint]
  rw [hs]
  have hm := Measure.map_map (measurable_id.prodMk measurable_id)
    (measurable_fst : Measurable (Prod.fst : EndpointPair → Base))
    (μ := baseMeasure.prod baseMeasure)
  simpa [Function.comp_def] using hm.symm

theorem measurableEmbedding_diagonalPair :
    MeasurableEmbedding (fun x : Base => (x, x)) := by
  have hr : Set.range (fun x : Base => (x, x)) =
      {xy : EndpointPair | xy.1 = xy.2} := by
    ext xy
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro h
      exact ⟨xy.1, Prod.ext rfl h⟩
  apply MeasurableEmbedding.of_measurable_inverse
    (measurable_id.prodMk measurable_id) _ measurable_fst (fun _ => rfl)
  change MeasurableSet (Set.range (fun x : Base => (x, x)))
  rw [hr]
  exact measurableSet_eq_fun measurable_fst measurable_snd

theorem triangularLaw_empty_ae_iff {p : EndpointPair → Prop} :
    (∀ᵐ xy ∂triangularLaw ∅, p xy) ↔ ∀ᵐ x ∂baseMeasure, p (x, x) := by
  rw [triangularLaw_empty_eq_diagonal]
  exact measurableEmbedding_diagonalPair.ae_map_iff

theorem triangularLaw_empty_pairIdentity_iff (θ c : ℕ → ℝ)
    (F : Base → Fiber →L[ℂ] Fiber) :
    (∀ᵐ xy ∂triangularLaw ∅, PairIdentity θ c F xy) ↔
      ∀ᵐ x ∂baseMeasure, IsIdempotentElem (F x) := by
  rw [triangularLaw_empty_ae_iff]
  simp_rw [pairIdentity_self_iff]

end Invariant233.ProductModel

end

end OAI
