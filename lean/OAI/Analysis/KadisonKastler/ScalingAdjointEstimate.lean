import OAI.Analysis.KadisonKastler.ScalingCoisometryEstimates
import OAI.Analysis.KadisonKastler.ModularConjugationData

namespace OAI

/-! # The adjoint reference estimate for scaling coisometries -/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem centralizerProjection_right_norm_le (d : ModularConjugationData M Ω)
    (p : AlgebraProjection M) (hc : ProductStateCentralizes M Ω p.val.val)
    (a : Algebra M) : ‖a.val (p.val.val Ω)‖ ≤ ‖a.val Ω‖ := by
  let R := conjugationOperator d.conjugation p.val.val
  have hR : R ∈ M.commutant := d.right_mem (R := M) le_rfl p.val
  have hcomm : a.val*R=R*a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp hR a.val a.property
  have hfix : R Ω=p.val.val Ω := by
    have hh := d.centralizer_vector p.val (fun b => hc b.val b.property)
    have he : star p.val.val=p.val.val := congrArg (fun b : Algebra M => b.val)
      p.property.isSelfAdjoint.star_eq
    rwa [he] at hh
  have hnorm : ‖R‖ ≤ 1 := by
    rw [norm_conjugationOperator d.conjugation d.involutive]
    exact p.property.norm_le
  calc
    _ = ‖R (a.val Ω)‖ := by
      rw [← hfix]
      exact congrArg norm (congrArg (fun T : H →L[ℂ] H => T Ω) hcomm)
    _ ≤ ‖R‖*‖a.val Ω‖ := R.le_opNorm _
    _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hnorm

theorem centralizerProjection_state_square (p : AlgebraProjection M)
    (hc : ProductStateCentralizes M Ω p.val.val) (a : Algebra M) :
    vectorFunctional Ω (star a*a*p.val)=((‖a.val (p.val.val Ω)‖^2 : ℝ) : ℂ) := by
  have hh := hc (star a*a*p.val).val (star a*a*p.val).property
  change vectorFunctional Ω (p.val*(star a*a*p.val)) =
    vectorFunctional Ω ((star a*a*p.val)*p.val) at hh
  rw [mul_assoc (star a*a),p.property.isIdempotentElem.eq] at hh
  have he : star (a*p.val)*(a*p.val)=p.val*(star a*a*p.val) := by
    rw [star_mul,p.property.isSelfAdjoint.star_eq]
    simp only [mul_assoc]
  rw [← hh,← he,vectorFunctional_star_mul_self]
  simp only [MulMemClass.coe_mul,mul_apply_eq_comp,Complex.ofReal_pow]

theorem StateScales.coisometry_adjoint_vector_bound (d : ModularConjugationData M Ω)
    {r : ℝ} (hr : 0 < r) (v : Algebra M) (hv : v*star v=1)
    (hs : StateScales M Ω r v.val) (a : Algebra M) :
    r*‖a.val ((star v).val Ω)‖^2 ≤ ‖a.val Ω‖^2 := by
  let p : AlgebraProjection M := ⟨star v*v,⟨by
    change (star v*v)*(star v*v)=star v*v
    calc
      _ = star v*(v*star v)*v := by simp only [mul_assoc]
      _ = star v*v := by rw [hv,mul_one],
    IsSelfAdjoint.star_mul_self v⟩⟩
  have hp : ProductStateCentralizes M Ω p.val.val := hs.initial_centralizes v.property hr.ne'
  have hh := hs (star a*a*star v).val (star a*a*star v).property
  change vectorFunctional Ω ((star a*a*star v)*v)=
    (r : ℂ)*vectorFunctional Ω (v*(star a*a*star v)) at hh
  have he : v*(star a*a*star v)=star (a*star v)*(a*star v) := by
    simp only [star_mul,star_star,mul_assoc]
  rw [mul_assoc (star a*a),he,vectorFunctional_star_mul_self] at hh
  change vectorFunctional Ω (star a*a*p.val)=_ at hh
  rw [centralizerProjection_state_square p hp a] at hh
  have heq := congrArg Complex.re hh
  simp only [← Complex.ofReal_pow,← Complex.ofReal_mul,Complex.ofReal_re,
    MulMemClass.coe_mul,mul_apply_eq_comp] at heq
  have hle := centralizerProjection_right_norm_le d p hp a
  nlinarith [norm_nonneg (a.val (p.val.val Ω)),norm_nonneg (a.val Ω)]

end

end KadisonKastler

end OAI
