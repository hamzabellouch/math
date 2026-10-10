import OAI.NumberTheory.DirichletL.Dictionary.InverseRawInitialGates
import OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPadding

namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification Filter IdealMobiusDivisorSum
open DetectorDictionaryInverseRawInitialGates
local notation "O"=>HeckeFamily.O

def shiftedExponent (_data:RowData)(U r:ℝ)(j:Ideal O) : ℝ :=
  r-Real.logb U (j.absNorm:ℝ)

theorem marked_shift_eventually (data:RowData)(eta:ℝ)(heta:0<eta) :
    ∀ᶠU:ℝ in atTop,1<U ∧
      ∀j∈idealDivisors (∏P∈excluded data,P),∀r:ℝ,
        r-eta≤shiftedExponent data U r j ∧ shiftedExponent data U r j≤r ∧
        U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ) := by
  have ht:∀ᶠU:ℝ in atTop,((∏P∈excluded data,P).absNorm:ℝ)≤U^eta :=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with U hU ht
  refine ⟨hU,?_⟩
  intro j hj r
  obtain ⟨hn,hnB⟩:=excluded_divisor_norm data j hj
  have hU0:0<U:=zero_lt_one.trans hU
  have hn0:0<(j.absNorm:ℝ):=zero_lt_one.trans_le hn
  have hl0:0≤Real.logb U (j.absNorm:ℝ):=
    div_nonneg (Real.log_nonneg hn) (Real.log_pos hU).le
  have hl:Real.logb U (j.absNorm:ℝ)≤eta:=
    (Real.logb_le_iff_le_rpow hU hn0).mpr (hnB.trans ht)
  refine ⟨by dsimp [shiftedExponent];linarith,by dsimp [shiftedExponent];linarith,?_⟩
  rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 hU.ne' hn0]

theorem shifted_padding_capacities (r r' ell ρ gap eta:ℝ)
    (hr:0≤r)(hell:0≤ell)(hshift:r-eta≤r')(hshiftup:r'≤r)
    (hfirst:r+2*ell<1)(hsecond:2*r+8*ell<3)
    (hgap:2*gap≤ρ)(hgap₃:2*gap≤3*ρ) :
    -eta≤r' ∧ r'+2*ell≤(1+ρ)-2*gap ∧
      2*r'+8*ell≤3*(1+ρ)-2*gap ∧ r'+ell<1 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem shifted_source_box (r r' ell G eta:ℝ)(hr:0≤r)(hell:0≤ell)
    (_hG:0≤G)(hGell:G≤ell)(hshift:r-eta≤r')(hshiftup:r'≤r)
    (hfirst:r+2*ell<1)(_heta:0≤eta)(hetaSmall:eta≤1/7) :
    -2≤r'+ell-2*G ∧ r'+ell+7*eta≤2 := by
  constructor <;> linarith

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
