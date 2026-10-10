import Mathlib
import OAI.Probability.SKRatio.Matrices.TruncationGoodSet
import OAI.Probability.SKRatio.Matrices.AbsMulEntryBound

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
namespace SKRatioGaussian
open RealComplex ComplexSpectral
open Matrix MeasureTheory ProbabilityTheory Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma real_symmetric_resolvent_isUnit (D C M : Matrix ι ι ℝ)
    (hD : Dᵀ = D) (hC : Cᵀ = C) (hM : Mᵀ = M)
    (hl : 0 < lowerRayleigh (liftMatrix (1-D*(M-C)*D))) :
    IsUnit (1-D*D*(M-C)) := by
  have hs : (liftMatrix (1-D*(M-C)*D)).IsHermitian := by
    rw [liftMatrix_sub,liftMatrix_one,liftMatrix_mul,liftMatrix_mul,liftMatrix_sub]
    change (1-liftMatrix D*(liftMatrix M-liftMatrix C)*liftMatrix D)ᴴ = _
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,Matrix.conjTranspose_mul,
      liftMatrix_hermitian D hD,liftMatrix_hermitian C hC,liftMatrix_hermitian M hM,mul_assoc]
  have hsu : IsUnit (liftMatrix (1-D*(M-C)*D)) :=
    (hs.posDef_iff_eigenvalues_pos.mpr (fun i => hl.trans_le (eigenvalue_lower_bound hs i))).isUnit
  have hrs := (liftMatrix_isUnit_iff _).mp hsu
  exact ResolventIdentity.inverse_one_sub_square_mul_unit D (M-C) hrs

lemma diagonal_resolvent_identity (d c : ι → ℝ) (M K : Matrix ι ι ℝ)
    (hK : (1-diagonal d*diagonal d*(M-diagonal c))*K=1) (i : ι) :
    K i i = 1+(d i)^2*((M*K) i i-c i*K i i) := by
  have he : (1-diagonal d*diagonal d*(M-diagonal c))*K =
      K-diagonal (fun a => (d a)^2)*(M*K-diagonal c*K) := by
    have hd : diagonal d*diagonal d = diagonal (fun a => (d a)^2) := by
      rw [Matrix.diagonal_mul_diagonal]; congr 1; ext a; simp only [pow_two]
    rw [hd]
    noncomm_ring
  rw [he] at hK
  have hh := congrFun (congrFun hK i) i
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.one_apply_eq] at hh
  nlinarith only [hh]

theorem realTruncatedK_second_loop (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x = (x : ℂ)⁻¹)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) (d c : ι → ℝ) (i : ι) :
    let D := diagonal d
    let C := diagonal c
    let K := realTruncatedK f R hR D C
    let b := ComplexMatrix.kBound f R (liftMatrix D) (liftMatrix C)
    let μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)
    let s := truncationGoodSet r R lo hi D C
    |(∫ g, K (goeMatrix r g) i i ∂μ)-
      (1+(d i)^2*((∫ g, (goeMatrix r g*K (goeMatrix r g)) i i ∂μ)-
        c i*(∫ g, K (goeMatrix r g) i i ∂μ)))| ≤
      (b+1+|(d i)^2*c i| *b)*μ.real sᶜ+
        (|(d i)^2| *b)*(Fintype.card ι:ℝ)*sqrt (2*r)*sqrt (μ.real sᶜ) := by
  intro D C K b μ s
  have hD : Dᵀ=D := Matrix.diagonal_transpose _
  have hC : Cᵀ=C := Matrix.diagonal_transpose _
  have hKL := realTruncatedK_lipschitz f hR D C hD hC
  apply goe_diagonal_inverse_loop hr (fun a => (d a)^2) c i
    (hKL.continuous.comp (goeMatrix_pi_lipschitz r).continuous)
    (fun g a b => (matrix_entry_le_opNorm _ a b).trans
      (realTruncatedK_opNorm f hR D C _ hD hC))
    (truncationGoodSet_measurable r R lo hi D C)
  intro g hg
  apply diagonal_resolvent_identity d c (goeMatrix r g) (K (goeMatrix r g))
  have hunit := real_symmetric_resolvent_isUnit D C (goeMatrix r g) hD hC
    (goeMatrix_transpose r g) (hlo.trans hg.2.1)
  have hid := realTruncatedK_eq_inverse f hlo hf hR D C (goeMatrix r g) hD hC
    (goeMatrix_transpose r g) hg.1.le hg.2.1.le hg.2.2.le
  change (1-D*D*(goeMatrix r g-C))*K (goeMatrix r g)=1
  rw [show K (goeMatrix r g) = _ from hid]
  exact Matrix.mul_nonsing_inv _ (((1-D*D*(goeMatrix r g-C)).isUnit_iff_isUnit_det).mp hunit)

end SKRatioGaussian

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
