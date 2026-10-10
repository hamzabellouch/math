import OAI.Probability.InvariantIsing.Cavity.CavityGaussianRankGram
import OAI.Probability.InvariantIsing.Cavity.CavityConditionedFrame
import OAI.Probability.InvariantIsing.Cavity.CavityHaarSides

namespace OAI

/-! A concrete orthogonal Haar probability from the square Gaussian frame.
This determines the orthogonal orbit law in the Wishart corollary. -/
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
namespace InvariantIsing

def squareFrameOrthogonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Orthogonal N :=
  if h : Aᵀ*A=1 then ⟨A,(Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mpr h⟩ else 1

lemma coe_squareFrameOrthogonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    (squareFrameOrthogonal A : Matrix (Fin N) (Fin N) ℝ)=if Aᵀ*A=1 then A else 1 := by
  classical
  unfold squareFrameOrthogonal
  split <;> simp_all

lemma measurable_squareFrameOrthogonal (N : ℕ) :
    Measurable (squareFrameOrthogonal (N := N)) := by
  classical
  apply Measurable.subtype_mk
  have hh : Measurable (fun A : Matrix (Fin N) (Fin N) ℝ => if Aᵀ*A=1 then A else 1) :=
    Measurable.ite
      ((isClosed_eq (continuous_id.matrix_transpose.matrix_mul continuous_id) continuous_const).measurableSet)
      measurable_id measurable_const
  convert hh using 1
  funext A
  exact coe_squareFrameOrthogonal A

lemma squareFrameOrthogonal_mul {N : ℕ} (U : Orthogonal N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : Aᵀ*A=1) :
    squareFrameOrthogonal ((U : Matrix (Fin N) (Fin N) ℝ)*A)=U*squareFrameOrthogonal A := by
  have hUA : ((U : Matrix (Fin N) (Fin N) ℝ)*A)ᵀ*((U : Matrix (Fin N) (Fin N) ℝ)*A)=1 := by
    rw [cavityGram_left_orthogonal A _ ((Matrix.mem_orthogonalGroup_iff' _ _).mp U.property),hA]
  apply Subtype.ext
  simp only [squareFrameOrthogonal,dite_eq_left hA,dite_eq_left hUA]
  rfl

def orthogonalGaussianLeftHaar (N : ℕ) : Measure (Orthogonal N) :=
  (cavityConditionedFrameLaw N N).map squareFrameOrthogonal

instance squareFrameLaw_probability (N : ℕ) : IsProbabilityMeasure (cavityConditionedFrameLaw N N) := by
  apply cavityConditionedFrameLaw_probability
  rw [cavityArrayGood_probability,cavityGoodGram_probability_one N N le_rfl]
  exact one_ne_zero

instance orthogonalGaussianLeftHaar_probability (N : ℕ) :
    IsProbabilityMeasure (orthogonalGaussianLeftHaar N) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_squareFrameOrthogonal N).aemeasurable).mpr inferInstance

instance orthogonalGaussianLeftHaar_leftInvariant (N : ℕ) :
    (orthogonalGaussianLeftHaar N).IsMulLeftInvariant := by
  constructor
  intro U
  have hact : Measurable (fun A : Matrix (Fin N) (Fin N) ℝ => (U : Matrix (Fin N) (Fin N) ℝ)*A) :=
    ((continuous_cavityFrameAction N N).comp (continuous_const.prodMk continuous_id)).measurable
  rw [orthogonalGaussianLeftHaar,Measure.map_map (measurable_const_mul U)
    (measurable_squareFrameOrthogonal N)]
  have he : (fun A : Matrix (Fin N) (Fin N) ℝ => U*squareFrameOrthogonal A)=ᵐ[cavityConditionedFrameLaw N N]
      (fun A => squareFrameOrthogonal ((U : Matrix (Fin N) (Fin N) ℝ)*A)) := by
    filter_upwards [cavityConditionedFrameLaw_orthonormal N N] with A hA
    exact (squareFrameOrthogonal_mul U A hA).symm
  change (cavityConditionedFrameLaw N N).map (fun A => U*squareFrameOrthogonal A)=_
  rw [Measure.map_congr he]
  change (cavityConditionedFrameLaw N N).map (squareFrameOrthogonal ∘ _)=_
  rw [← Measure.map_map (measurable_squareFrameOrthogonal N) hact,cavityConditionedFrameLaw_rotation]

def orthogonalGaussianHaar (N : ℕ) : Measure (Orthogonal N) := (orthogonalGaussianLeftHaar N).inv

instance orthogonalGaussianHaar_probability (N : ℕ) : IsProbabilityMeasure (orthogonalGaussianHaar N) := by
  unfold orthogonalGaussianHaar Measure.inv
  exact (Measure.isProbabilityMeasure_map_iff measurable_inv.aemeasurable).mpr inferInstance

instance orthogonalGaussianHaar_rightInvariant (N : ℕ) :
    (orthogonalGaussianHaar N).IsMulRightInvariant := by
  unfold orthogonalGaussianHaar
  infer_instance

end InvariantIsing

end

end OAI
