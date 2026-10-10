import Mathlib
import OAI.Probability.SKGap.Stability.LiteralStableControl
import OAI.Probability.SKGap.Localization.LiteralRegularity
import OAI.Probability.SKGap.Stability.ImplicitTraceControl
import OAI.Probability.SKGap.Localization.LiteralPartial

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

def initialPartialBudget (f : KernelExpr) (R T B : ℝ) : ℝ :=
  B*ratioSmallBudget (.kernel phiExpr.dz) T+
    ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T

def initialTraceFactor (Q T B : ℝ) : ℝ :=
  (T+B)+4*(Q^2+T*(T+B)+(T+B)^2)+2*(Q+T+(T+B))

lemma literalInitial_parameter (J : Interaction n) (j d : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n) :
    (∑α,‖derivativeVector ((literalInitial J j d f z m a c r e).θ α) x‖)=
      ‖derivativeVector a x‖+‖derivativeVector (fun v=>d*c v) x‖ := by
  simp only [Fintype.sum_bool,literalInitial,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma literalInitial_traces (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)) (hn : 0<n)
    {R T B Bs Q E : ℝ} (hT : 0≤T) (hQ : 0≤Q) (hBs : 0≤Bs)
    (he : vectorNorm e≤1) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |Real.sqrt n*c x|≤Bs) (hcf : ∀k,|Real.sqrt n*c (flip x k)|≤Bs)
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
    (hDm : SKGap.opNorm (derivativeMatrix m x)≤T) (hm : ∀i,|m x i|≤1)
    (hW : SmallBound w x B) (hY : SmallBound y x B)
    (hDc : ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤B)
    (hw : w x=(literalInitial J j (Real.sqrt n) f z m a c r e).sourceOf 1 (fun _=>y) x)
    (hwf : ∀k,w (flip x k)=(literalInitial J j (Real.sqrt n) f z m a c r e).sourceOf 1 (fun _=>y) (flip x k))
    (hEz : ‖derivativeMatrix z x-t.fieldMatrix j J‖≤E)
    (hEm : ‖derivativeMatrix m x-t.sourceMatrix j J‖≤E)
    (hQ4 : (∑i,∑k,(derivativeMatrix z x i k)^4)≤Q^4)
    (hdiag : (∑i,(derivativeMatrix z x i i)^2)≤T^2) :
    let D:=literalInitial J j (Real.sqrt n) f z m a c r e
    let C:=initialRegularBudget f j R Bs
    let Cp:=initialPartialBudget f R T B
    TraceControl (D.implicitSourcePrimitive t y x)
      ((2*C+C*B)*initialTraceFactor Q T B+Cp*E) ∧
    TraceControl (D.implicitFieldPrimitive t w y x)
      (|j| *(Cp*E)+|j| *(Cp*(1+2*T)+3*B*((phiExpr.dBudget R+phiExpr.ddBudget R)*T))) := by
  let D:=literalInitial J j (Real.sqrt n) f z m a c r e
  let C:=initialRegularBudget f j R Bs
  have hd : Real.sqrt (n:ℝ)≠0:=(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hp:=literalInitial_partial_small J j (Real.sqrt n) f z m w y a c r e x hd hT he ha haf hD hW hw hwf
  obtain ⟨hreg,har⟩:=literalInitial_regular J j (Real.sqrt n) f z m a c r e x hBs ha haf hc hcf
  have hC : 0≤ initialRegularBudget f j R Bs:=(hreg false).nonneg
  have hparam : (∑α,‖derivativeVector (D.θ α) x‖)≤T+B := by
    rw [literalInitial_parameter]
    exact add_le_add (by linarith [show 0≤SKGap.opNorm (derivativeMatrix z x) from norm_nonneg _]) hDc
  have hrow (i : Fin n) : (∑k,(primaryIncrement D.H x i k)^2)≤T^2 := by
    simpa only [primaryIncrement,D,literalInitial,Fintype.sum_unique,sq_abs] using
      (SKGap.SourceError.matrix_row_square_le (derivativeMatrix z x) i).trans
        (pow_le_pow_left₀ (norm_nonneg _) (le_trans (le_add_of_nonneg_right (norm_nonneg _)) hD) 2)
  have h4 : (∑i,∑k,(primaryIncrement D.H x i k)^4)≤Q^4 := by
    simpa only [primaryIncrement,D,literalInitial,Fintype.sum_unique,show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs] using hQ4
  have hdi : (∑i,(primaryIncrement D.H x i i)^2)≤T^2 := by
    simpa only [primaryIncrement,D,literalInitial,Fintype.sum_unique,sq_abs] using hdiag
  have hseed (s : Bool) : vectorNorm (D.seed s)≤1 := by
    cases s
    · exact he
    · change vectorNorm (fun i=>Real.tanh (r i)/Real.sqrt n)≤1
      have H:=(vectorNorm_tanh r)
      rw [show (fun i=>Real.tanh (r i)/Real.sqrt n)=((Real.sqrt n)⁻¹ • (fun i=>Real.tanh (r i))) by ext i; simp only [Pi.smul_apply,smul_eq_mul];ring,
        vectorNorm_smul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      exact (mul_le_mul_of_nonneg_left H (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq (inv_mul_cancel₀ hd)
  have hZ : (∑α,‖derivativeVector (D.θ α) x‖)+4*(Q^2+T*(T+B)+(T+B)^2)+2*(Q+T+(T+B))≤ initialTraceFactor Q T B := by
    dsimp only [initialTraceFactor]; linarith
  have Hs:=D.implicitSource_control t y x hC hQ hT hT (add_nonneg hT hW.nonneg) hY hp hEz hreg har
    ((parameterIncrement_bound D.θ x).trans hparam) h4 hrow hdi
    hZ
  have Hb : (∑s,C*vectorNorm (D.seed s))≤2*C := by
    simpa only [Fintype.sum_bool,mul_one,two_mul] using add_le_add
      (mul_le_mul_of_nonneg_left (hseed true) hC) (mul_le_mul_of_nonneg_left (hseed false) hC)
  have hcoef:=initial_kernel_bound phiExpr z a r x hT ha haf hD
  have hcoef' : D.implicitCoefficient=fun v i=>phiExpr.eval (z v i) (r i) (a v) := by
    ext v i; rw [literalInitial_coefficient,phiExpr,KernelExpr.eval,moment_base]
  constructor
  · apply Hs.mono
    dsimp only [initialPartialBudget,initialTraceFactor] at *
    rw [←Finset.sum_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr Hb)
      (show 0≤T+B+4*(Q^2+T*(T+B)+(T+B)^2)+2*(Q+T+(T+B)) by positivity [hW.nonneg])]
  · apply D.implicitField_control t w y x hn hT hcoef.row_nonneg hW hp hEm hm hDm
    simpa only [hcoef'] using hcoef.difference
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGap.ImplicitSystem
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma ordinary_matrix_margin (j χ b r δ : ℝ) (X J : E→L[ℝ]E) (q : E)
    (hj : 0≤j) (hr : 0≤r)
    (hself : ∀u v,inner ℝ u (X v)=inner ℝ (X u) v)
    (hStable : ∀v,δ*‖v‖^2≤ inner ℝ v (stableMatrix j b r X J q v))
    (hSmall : |j| *|χ-b| *‖X‖^2≤δ/2) (v : E) :
    (δ/2)*‖v‖^2≤ inner ℝ v ((1-X*(J-(j*χ) • 1)*X) v) := by
  let S:=1+(j*b) • (X*X)-X*J*X
  have hS : ∀u,δ*‖u‖^2≤ inner ℝ u (S u) := by
    intro u
    have hh : inner ℝ u ((X*rank q q*X) u)=(inner ℝ q (X u))^2 := by
      simp only [mul_apply_eq_comp,rank_apply,map_smul,inner_smul_right]
      rw [hself u q,real_inner_comm (X u) q]
      ring
    have hs:=hStable u
    change δ*‖u‖^2≤ inner ℝ u ((S-(2*j*r) • (X*rank q q*X)) u) at hs
    simp only [sub_apply,smul_apply,inner_sub_right,
      inner_smul_right,hh] at hs
    nlinarith [mul_nonneg (by positivity : 0≤2*j*r) (sq_nonneg (inner ℝ q (X u)))]
  have hd : (1-X*(J-(j*χ) • 1)*X)-S=(j*(χ-b)) • (X*X) := by
    dsimp only [S]
    simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,sub_smul]
    module
  have hnorm : ‖(1-X*(J-(j*χ) • 1)*X)-S‖≤δ/2 := by
    rw [hd,norm_smul,Real.norm_eq_abs,abs_mul]
    exact ((mul_le_mul_of_nonneg_left (norm_mul_le X X) (by positivity)).trans_eq
      (by ring)).trans hSmall
  have hp:=SKGap.ImplicitLinear.quadratic_perturbation (1-X*(J-(j*χ) • 1)*X) S hS hnorm v
  convert hp using 1
  ring
end SKGap.ImplicitSystem

namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}
lemma phiSqrt_inner (z r : Fin n→ℝ) (a : ℝ) (u v : Euclid n) :
    inner ℝ u (phiSqrt z r a v)=inner ℝ (phiSqrt z r a u) v := by
  simp only [phiSqrt,EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial,ofLp_toEuclideanCLM,dotProduct,mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma literal_inverse_stability (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hj : 0≤j) (hJ : J.IsSymm) {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (H : LiteralStableAt J j z m a r R ρ δ x) :
    (1-SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1*
      (J-(j*siteMean (fun v i=>phi (z v i) (r i) (a v)) x) • 1)*
      SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1).PosDef := by
  let D:=SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1
  let χ:=siteMean (fun v i=>phi (z v i) (r i) (a v)) x
  have hD : D.IsHermitian := by simp [D,SKGap.pathDiagonal]
  have hM : (J-(j*χ) • 1).IsHermitian :=
    (isHermitian_iff_isSymm.mpr hJ).sub (isHermitian_one.smul (IsSelfAdjoint.all (j*χ)))
  have hHerm : (1-D*(J-(j*χ) • 1)*D).IsHermitian := by
    apply isHermitian_one.sub
    simpa only [hD.eq] using isHermitian_conjTranspose_mul_mul D hM
  apply PosDef.of_dotProduct_mulVec_pos hHerm
  intro v hv
  have hpert:=H.perturbation hn hδ hρ hsmall
  have hsmall' : |j| *|χ-(∑i,scalarVariance (z x i))/(n:ℝ)| *‖phiSqrt (z x) r (a x)‖^2≤δ/2 :=
    (le_add_of_nonneg_right (by positivity)).trans hpert
  have hp:=ordinary_matrix_margin j χ _ (n:ℝ)⁻¹ δ (phiSqrt (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (fun i=>Real.tanh (z x i)))
    hj (by positivity) (phiSqrt_inner _ _ _) H.stable hsmall' (WithLp.toLp 2 v)
  have hrep : toEuclideanCLM (𝕜:=ℝ) (1-D*(J-(j*χ) • 1)*D)=
      1-phiSqrt (z x) r (a x)*(toEuclideanCLM (𝕜:=ℝ) J-(j*χ) • 1)*phiSqrt (z x) r (a x) := by
    simp only [map_sub,map_mul,map_one,map_smul,D,SKGap.pathDiagonal,Real.sqrt_one,one_mul,phiSqrt]
  rw [←hrep,inner_toEuclideanCLM] at hp
  have hnorm : 0<‖(WithLp.toLp 2 v : Euclid n)‖^2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (by simpa using hv))
  simpa only [star_trivial] using lt_of_lt_of_le (mul_pos (half_pos hδ) hnorm) hp
end SKGapCutoff.Recipe

end
end

end OAI
