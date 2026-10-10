import OAI.Analysis.LipschitzHilbert.Estimates.AmplitudeApproximation

namespace OAI

/-! The same normalized amplitude pieces in the actual L2 quotient,
including null levels and exact finite reconstruction. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal
namespace LipschitzHilbert
variable {X κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem amplitudePiece_memLp (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (i : ℤ) : MemLp (amplitudePiece f i) 2 μ :=
  (hf2.indicator (amplitudeLevel_measurable hf.norm i)).const_smul _

def amplitudeLpPiece (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (i : ℤ) : Lp (EuclideanSpace ℂ κ) 2 μ :=
  (amplitudePiece_memLp μ hf hf2 i).toLp (amplitudePiece f i)

theorem amplitudeLpPiece_zero (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (i : ℤ)
    (hzero : μ.real (amplitudeLevel f i)=0) : amplitudeLpPiece μ hf hf2 i=0 := by
  have hμ : μ (amplitudeLevel f i)=0 :=
    (measureReal_eq_zero_iff (amplitudeLevel_finite μ hf2 i)).mp hzero
  have ha : amplitudePiece f i=ᵐ[μ] 0 := by
    apply ae_iff.mpr
    apply measure_mono_null (t:=amplitudeLevel f i) ?_ hμ
    intro x hx
    by_contra hn
    exact hx (amplitudePiece_supported f i x hn)
  exact ((amplitudePiece_memLp μ hf hf2 i).toLp_congr (MemLp.zero) ha).trans (MemLp.toLp_zero _)

theorem amplitudeApprox_toLp (μ : Measure X) {f : X → EuclideanSpace ℂ κ}
    (hf : Measurable f) (hf2 : MemLp f 2 μ) (I : Finset ℤ) :
    (amplitudeApprox_memLp μ hf hf2 I).toLp (amplitudeApprox f I)=
      ∑ i∈I, (2:ℝ)^i • amplitudeLpPiece μ hf hf2 i := by
  apply Lp.ext
  have hi (i : ℤ) : ((2:ℝ)^i • amplitudeLpPiece μ hf hf2 i : Lp (EuclideanSpace ℂ κ) 2 μ)=ᵐ[μ]
      (2:ℝ)^i • amplitudePiece f i :=
    (Lp.coeFn_smul _ _).trans ((amplitudePiece_memLp μ hf hf2 i).coeFn_toLp.fun_comp
      (fun y => (2:ℝ)^i • y))
  calc
    _ =ᵐ[μ] amplitudeApprox f I := (amplitudeApprox_memLp μ hf hf2 I).coeFn_toLp
    _ =ᵐ[μ] ∑ i∈I, ((2:ℝ)^i • amplitudeLpPiece μ hf hf2 i : Lp (EuclideanSpace ℂ κ) 2 μ) :=
      (eventuallyEq_sum (fun i _ => hi i)).symm
    _ =ᵐ[μ] _ := (Lp.coeFn_finsetSum _ _).symm

end LipschitzHilbert

end

end OAI
