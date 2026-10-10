import OAI.InformationTheory.Entanglement.HilbertLawDistance
import OAI.InformationTheory.Entanglement.FiniteLawRecovery

namespace OAI

noncomputable section
open scoped BigOperators ENNReal MeasureTheory InnerProductSpace ComplexOrder MatrixOrder
open MeasureTheory Matrix ContinuousLinearMap
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {T : Type*} [MeasurableSpace T]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} {n e : Type} [Fintype n] [Fintype e] [DecidableEq n] [DecidableEq e]

theorem hilbert_purification_law_recovery (b : HilbertBasis ι ℂ H)
    (v : e → H) (hv : Orthonormal ℂ v) (j₀ : e) (i₀ : n) (B : Matrix e n ℂ) :
    ∃ F : Map e n, ∃ hF : CP F, TracePreserving F ∧
      (∀ W : PositiveMatrixMeasure T n,
        (((W.filter B).hilbertEmbedding b v hv).erase v hv j₀).channel F hF=
          W.filter (CFC.sqrt (Bᴴ*B))) ∧
      ∀ (W : Fin 2 → Fin 2 → PositiveMatrixMeasure T n) (σ : PositiveHilbertMeasure T H b),
        ENNReal.ofReal (cqBitDistance (fun i j => (W i j).filter (CFC.sqrt (Bᴴ*B)))
          ((σ.erase v hv j₀).channel F hF))≤
          hilbertCQDistance b (fun i j => ((W i j).filter B).hilbertEmbedding b v hv) σ := by
  obtain ⟨F,hF,hT,hrec⟩ := finite_branch_law_recovery (T := T) i₀ B
  refine ⟨F,hF,hT,?_,?_⟩
  · intro W
    rw [PositiveMatrixMeasure.hilbertEmbedding_recovered]
    exact hrec W
  · intro W σ
    have hc := cqBitDistance_channel (fun i j => (W i j).filter B) (σ.erase v hv j₀) F hF hT
    simp only [hrec] at hc
    have he := hilbertCQDistance_recovery b v hv j₀
      (fun i j => ((W i j).filter B).hilbertEmbedding b v hv) σ
    simp only [PositiveMatrixMeasure.hilbertEmbedding_recovered] at he
    exact (ENNReal.ofReal_le_ofReal hc).trans he

omit [CompleteSpace H] [DecidableEq n] in
theorem purification_orthonormal_support (x : n → H) (hx : ∃ j, x j≠0) :
    ∃ d : ℕ, ∃ _ : 0<d, ∃ v : Fin d → H, Orthonormal ℂ v ∧
      ∃ B : Matrix (Fin d) n ℂ,
        (∀ j, x j=∑ a, B a j • v a) ∧
        (∀ i j, (Bᴴ*B) i j=inner ℂ (x i) (x j)) := by
  obtain ⟨d,V,B,hx',hgram⟩ := purification_finite_span x
  have hd : 0<d := by
    by_contra h
    have hz : d=0 := by omega
    subst d
    obtain ⟨j,hj⟩ := hx
    apply hj
    rw [← hx' j]
    have hz : WithLp.toLp 2 (fun a : Fin 0 => B a j)=0 := by ext a; exact Fin.elim0 a
    rw [hz,map_zero]
  let v : Fin d → H := fun a => V (EuclideanSpace.basisFun (Fin d) ℂ a)
  refine ⟨d,hd,v,?_,B,?_,hgram⟩
  · rw [orthonormal_iff_ite]
    intro i j
    change inner ℂ (V _) (V _) = _
    rw [V.inner_map_map]
    exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin d) ℂ).orthonormal i j
  · intro j
    rw [← hx' j]
    change V (WithLp.toLp 2 (fun a => B a j))=∑ a, B a j • V (EuclideanSpace.basisFun (Fin d) ℂ a)
    have he := congrArg V ((EuclideanSpace.basisFun (Fin d) ℂ).sum_repr
      (WithLp.toLp 2 (fun a => B a j))).symm
    simpa only [map_sum,map_smul,EuclideanSpace.basisFun_repr,WithLp.ofLp_toLp] using he

end SecretKey

end

end OAI
