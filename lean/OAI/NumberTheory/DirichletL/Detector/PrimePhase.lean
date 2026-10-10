import OAI.NumberTheory.DirichletL.Detector.PhaseCancellation
import OAI.NumberTheory.DirichletL.Detector.Sextic

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhase
open ActualEisensteinCubic ActualEisensteinCoordinates CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge QuadraticGaussRay FiniteGaussPhase CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem normalizedTraceGauss_eq_normalizedGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) :
    letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
    letI : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
    ConcreteBreveE.normalizedTraceGauss p hp χ =
      ProbeGauss.normalizedGauss χ (quotientTrace p hp) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hn : Real.sqrt (Nat.card (O ⧸ Ideal.span {p}) : ℝ) = ‖eisEmbedding p‖ := by
    change Real.sqrt (Ideal.absNorm (Ideal.span {p}) : ℝ) = _
    rw [← eisEmbedding_norm_sq_eq_absNorm_span, Real.sqrt_sq (norm_nonneg _)]
  simp only [ConcreteBreveE.normalizedTraceGauss, ProbeGauss.normalizedGauss,
    quotientTrace, ← Nat.card_eq_fintype_card, hn]

theorem quadraticRayValue_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    quadraticRayValue (residue p) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  let pp : Unit → O := fun _ => p
  have hpp : ∀ i, pp i ≠ 0 := fun _ => hp
  have hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {pp i})) := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have he := canonicalProductGauss_three_eq_rayValue pp hpp hcop (fun _ => hg) (fun _ => hc)
  rw [canonicalProductGauss_cross_factors pp hpp hcop (fun _ => hg) (fun _ => 3)] at he
  simpa [pp] using he.symm

theorem G_cube_eq_normalizedTraceGauss (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    G (p ^ 3) =
      ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) := by
  rw [G_cube p ho (cubicTwo_isUnit_of_odd p ho)]
  exact quadraticRayValue_eq_normalizedTraceGauss p hp hg hc

theorem normalizedTraceGauss_three_sq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ConcreteBreveE.normalizedTraceGauss p hp (actualSextic (Ideal.span {p}) hg ^ 3) ^ 2 =
      actualSextic (Ideal.span {p}) hg (-1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  let χ := actualSextic (Ideal.span {p}) hg
  have h6 : χ ^ 6 = 1 := (ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 6).mpr (by decide)
  have h3 : χ ^ 3 ≠ 1 := fun h => (by decide : ¬6 ∣ 3)
    ((ProbePrimePower.actualSextic_pow_eq_one_iff _ hg hc 3).mp h)
  have hi : (χ ^ 3)⁻¹ = χ ^ 3 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add]
    exact h6
  have hψ : (quotientTrace p hp).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp
  have he := ProbeGauss.normalizedGauss_inverse_pair (χ ^ 3) (quotientTrace p hp) h3 hψ
  rw [hi, ← pow_two] at he
  rw [normalizedTraceGauss_eq_normalizedGauss]
  rw [he]
  simp only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), ← map_pow]
  norm_num
  rfl

theorem reciprocitySign_self_eq_sextic_neg_one (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ho : EisensteinEPrimaryPhase.odd (residue p)) :
    reciprocitySign p p = actualSextic (Ideal.span {p}) hg (-1) := by
  have hq := QuadraticAllOddCRT.quadraticRayValue_mul (residue p) (residue p) ho ho
  rw [quadraticRayValue_square _ ho] at hq
  have hprod : reciprocitySign p p * quadraticRayValue (residue p) ^ 2 = 1 := by
    simpa only [reciprocitySign, pow_two, mul_assoc] using hq.symm
  have he := normalizedTraceGauss_three_sq p hp hg hc
  rw [← quadraticRayValue_eq_normalizedTraceGauss p hp hg hc] at he
  rw [he] at hprod
  calc
    reciprocitySign p p = reciprocitySign p p * 1 := (mul_one _).symm
    _ = reciprocitySign p p * (reciprocitySign p p * actualSextic (Ideal.span {p}) hg (-1)) := by rw [hprod]
    _ = reciprocitySign p p ^ 2 * actualSextic (Ideal.span {p}) hg (-1) := by ring
    _ = _ := by rw [reciprocitySign_sq p p ho ho, one_mul]

end SevenEighths.ProbePhase
end

end OAI
