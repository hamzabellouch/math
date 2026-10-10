import OAI.NumberTheory.DirichletL.PrimeRows.SelectedUnramified

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def finiteLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  ProbeLocal.continuedCorrection (coordV P.val.absNorm z)
    (coordW P.val.absNorm (idealRowHom u.val P.val) w)
    (coordD P.val.absNorm (idealCoeff η P.val) (idealRowHom u.val P.val) x)
    (continuedMarkedLocal η u P hs x w z)

theorem continuedCompensatedLocal_eq_difference (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ) :
    continuedCompensatedLocal η u P hs x w z B q=
      B*continuedMarkedLocal η u P hs x w z*localNormalization η u P x w z-
        q*finiteLocalCorrection η u P hs x w z := by
  rw [localNormalization_coordinates]
  unfold continuedCompensatedLocal finiteLocalCorrection ProbeLocal.compensatedReplacement ProbeLocal.continuedCorrection
  ring

theorem ramifiedCorrection_eq_marked (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    ramifiedCorrection η u P hs x w z=
      1+(1-coordV P.val.absNorm z)*continuedMarkedLocal η u P hs x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := (supported_prime_data p hp hsp).1
  have hnorm : Ideal.absNorm (Ideal.span {p})=P.val.absNorm := congrArg Ideal.absNorm hspan
  change ramifiedClosed p hp hg (targetMonoid η p) (actualACube η p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) x w z (multiplicity p u.val)=
    1+(1-coordV P.val.absNorm z)*rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
      ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp))) (multiplicity p u.val)
  unfold ramifiedClosed
  rw [hnorm]

theorem finiteLocalCorrection_ramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hP : P.val∣Ideal.span {u.val}) (x w z : ℂ) :
    finiteLocalCorrection η u P hs x w z=ramifiedCorrection η u P hs x w z := by
  rw [ramifiedCorrection_eq_marked]
  unfold finiteLocalCorrection
  rw [row_phase_ramified u P hP]
  simp only [coordW,coordD,star_zero,mul_zero,zero_mul,ProbeLocal.continuedCorrection,
    sub_zero,mul_one,div_one]

theorem finiteLocalCorrection_unramified (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (x w z : ℂ)
    (hV : ‖coordV P.val.absNorm z‖<1)
    (hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1) :
    finiteLocalCorrection η u P hs x w z=idealUnramifiedCorrection η u P x w z := by
  rw [finiteLocalCorrection,continuedMarkedLocal_unramified η u P hs hn x w z hV hR]
  rfl

theorem initial_marked_geometry (η : Character) (P : PrimeIdeal) (x z : ℂ)
    (hx : 3/2<x.re) (hz : 1/6<z.re) :
    ‖coordV P.val.absNorm z‖<1 ∧
      ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 := by
  have hQ : (1:ℝ)<P.val.absNorm := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (1:ℕ)<2) (SmoothMobiusCorrection.prime_norm_two_le P))
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  constructor
  · rw [coordV_norm _ hQ0]
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
  · apply (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
    exact Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)

theorem finiteLocalCorrection_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    finiteLocalCorrection η u P hs x w z=localCorrection η u P x w z := by
  by_cases hP : P.val∣Ideal.span {u.val}
  · rw [finiteLocalCorrection_ramified η u P hs hP]
    exact (localCorrection_eq_ramified η u P hs hP x w z hx hw hz).symm
  · have hg := initial_marked_geometry η P x z hx hz
    rw [finiteLocalCorrection_unramified η u P hs hP x w z hg.1 hg.2]
    exact (localCorrection_unramified_ideal η u P hs (supported_prime_coprime P hs u.val hP)
      x w z hx hw hz).symm

theorem continuedCompensatedLocal_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z B q : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedCompensatedLocal η u P hs x w z B q=compensatedLocalCorrection η u P x w z B q := by
  rw [continuedCompensatedLocal_eq_difference,
    continuedMarkedLocal_eq_initial η u P hs x w z hx hw hz,
    finiteLocalCorrection_eq_initial η u P hs x w z hx hw hz]
  unfold compensatedLocalCorrection markedLocalCorrection
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
