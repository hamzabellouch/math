import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalColumn
import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow CenteredMomentSecondHeightFamily
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentSmooth
open FourierBridge
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance firstWindowDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _

lemma generator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2

def commonWindow (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)
    (t θ X:ℝ)(V:ℝ→ℂ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z

theorem common_window_original_integral (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonWindow D C hC τ t θ X V L z=
      ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
          gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported (allocatedData D C L B).columns)
            ((allocatedData D C L B).coefficient τ fixedBadMask
              (t+2*Real.pi*(w-θ)) T) z:=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then D.beta (C*I) else 0
  have hh:=gauss_column_integral Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    β τ t θ X hX V hVc hVs z
  simp only [generator_span] at hh
  change commonWindow D C hC τ t θ X V L z=
    ∫w:ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      commonGauss D C hC τ (t+2*Real.pi*(w-θ)) L z at hh
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with w
  have he:=normalized_common_gauss_allocation D hS hp C hC hseed τ
    (t+2*Real.pi*(w-θ)) T L z
  rw [←he]
  ring

theorem common_window_original_integrable (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T θ X:ℝ)(hX:0<X)
    (V:ℝ→ℂ)(hVc:HasCompactSupport V)(hVs:ContDiff ℝ ∞ V)(L:Ideal O)(z:O):
    Integrable (fun w:ℝ=>columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask (t+2*Real.pi*(w-θ)) T) z):=by
  let Q:=residualPool C hC.1 D.columns
  let β:=fun I:supportedColumns Q=>if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
    then D.beta (C*I) else 0
  have hh:=(CenteredMomentHeckeWindowEnergy.gauss_column_integrable Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) β τ t θ X hX V hVc hVs z).const_mul
      ((Real.sqrt T:ℂ)⁻¹)
  simp only [generator_span] at hh
  convert hh using 1
  funext w
  rw [←normalized_common_gauss_allocation D hS hp C hC hseed τ (t+2*Real.pi*(w-θ)) T L z]
  change _=(Real.sqrt T:ℂ)⁻¹*(columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
    commonGauss D C hC τ (t+2*Real.pi*(w-θ)) L z)
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
