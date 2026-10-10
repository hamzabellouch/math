import Mathlib
import OAI.Probability.SKGap.Localization.LiteralConstruction
import OAI.Probability.SKGap.Matrix.LiteralTrace
import OAI.Probability.SKGap.Matrix.StartedMatrixEvent

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma realQuadratic_eq_inner (M : Interaction n) (v : Euclid n) :
    SKGap.RealComplex.realQuadratic M v=inner ℝ v (toEuclideanCLM (𝕜:=ℝ) M v) := by
  rw [inner_toEuclideanCLM]
  simp only [SKGap.RealComplex.realQuadratic,dotProduct,mulVec,Finset.mul_sum,mul_assoc]

lemma literal_inverse_margin (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hj : 0≤j) {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (H : LiteralStableAt J j z m a r R ρ δ x) :
    δ/2≤SKGap.ComplexSpectral.lowerRayleigh (SKGap.RealComplex.liftMatrix
      (SKGap.stabilityMatrix (fun i=>phi (z x i) (r i) (a x)) 1
        ((j/n)*∑i,phi (z x i) (r i) (a x)) J)) := by
  have : Nonempty (Fin n):=Fin.pos_iff_nonempty.mp hn
  let D:=SKGap.pathDiagonal (fun i=>phi (z x i) (r i) (a x)) 1
  let χ:=siteMean (fun v i=>phi (z v i) (r i) (a v)) x
  have hq : (j/n)*∑i,phi (z x i) (r i) (a x)=j*χ := by dsimp [χ,siteMean];ring
  have hshift : SKGap.pathShift 1 (j*χ)=(j*χ) • (1:Interaction n) := by
    simp only [SKGap.pathShift,one_mul,Matrix.smul_one_eq_diagonal]
  rw [SKGap.stabilityMatrix_path_rep _ (fun i=>(phi_pos _ _ _).le) (by norm_num),hq,hshift]
  apply SKGap.RealComplex.lowerRayleigh_lift_ge
  intro v
  rw [realQuadratic_eq_inner]
  have hpert:=H.perturbation hn hδ hρ hsmall
  have hsmall' : |j| *|χ-(∑i,scalarVariance (z x i))/(n:ℝ)| *‖phiSqrt (z x) r (a x)‖^2≤δ/2 :=
    (le_add_of_nonneg_right (by positivity)).trans hpert
  have hp:=ordinary_matrix_margin j χ _ (n:ℝ)⁻¹ δ (phiSqrt (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (fun i=>Real.tanh (z x i)))
    hj (by positivity) (phiSqrt_inner _ _ _) H.stable hsmall' v
  have hrep : toEuclideanCLM (𝕜:=ℝ) (1-D*(J-(j*χ) • 1)*D)=
      1-phiSqrt (z x) r (a x)*(toEuclideanCLM (𝕜:=ℝ) J-(j*χ) • 1)*phiSqrt (z x) r (a x) := by
    simp only [map_sub,map_mul,map_one,map_smul,D,SKGap.pathDiagonal,Real.sqrt_one,one_mul,phiSqrt]
  simpa only [←hrep] using hp

lemma literal_closed_word_event (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) (hj : 0≤j) {R ρ δ A L B W C : ℝ} {M Nmax : ℕ}
    (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (hEvent : StartedMatrixEvent j L (Real.exp (R/2)) A (δ/2) B W C M Nmax J) :
    ClosedWordTestBound j (fun i=>phi (z x i) (r i) (a x)) J A W (2*Nmax+5) ∧
    ClosedWordDiagramBound j (fun i=>phi (z x i) (r i) (a x)) J A C (2*M+2*Nmax+4) := by
  apply hEvent.2.2 _
  · intro i
    refine ⟨(phi_pos _ _ _).le,?_⟩
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [H.a_bound]))
  · exact literal_inverse_margin J j z m a r x hn hj hδ hρ hsmall H
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

structure LiteralInitialDiagnostics (D : OrdinaryData n Unit Bool Bool)
    (w y : VectorFields n) (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ))
    (x : Spin n) (B S F A : ℝ) : Prop where
  source : w x=D.sourceOf 1 (fun _=>y) x
  source_flip : ∀k,w (flip x k)=D.sourceOf 1 (fun _=>y) (flip x k)
  field : y x=D.fieldOf 1 (fun _=>w) (fun _=>y) x
  field_flip : ∀k,y (flip x k)=D.fieldOf 1 (fun _=>w) (fun _=>y) (flip x k)
  coefficient_nonneg : ∀i,0≤D.implicitCoefficient x i
  coefficient_bound : ∀i,|D.implicitCoefficient x i|≤A
  inverse_pos : (1-SKGap.pathDiagonal (D.implicitCoefficient x) 1*
    (D.J-(D.j*siteMean D.implicitCoefficient x) • 1)*SKGap.pathDiagonal (D.implicitCoefficient x) 1).PosDef
  source_bound : SmallBound w x B
  field_bound : SmallBound y x B
  partial_bound : SmallBound (D.implicitPartial y) x B
  source_trace : TraceControl (D.implicitSourcePrimitive t y x) S
  field_trace : TraceControl (D.implicitFieldPrimitive t w y x) F

theorem literal_initial_diagnostics (j R ρ δ T L Q E : ℝ) (f : KernelExpr)
    (hj : 0≤j) (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T) (hQ : 0≤Q)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃B≥0,∃S≥0,∃F≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
      (a : Spin n→ℝ) (r e : Fin n→ℝ),J.IsSymm→SKGap.opNorm J≤L→vectorNorm e≤1→
      ∃w y : VectorFields n,∃c : Spin n→ℝ,
        (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
        (∀x (t : SKGap.Noncrossing.Primary.SourceTree (Fin n→ℝ)),
          LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→(∀i,|m x i|≤1)→
          ‖derivativeMatrix z x-t.fieldMatrix j J‖≤E→
          ‖derivativeMatrix m x-t.sourceMatrix j J‖≤E→
          (∑i,∑k,(derivativeMatrix z x i k)^4)≤Q^4→
          (∑i,(derivativeMatrix z x i i)^2)≤T^2→
          LiteralInitialDiagnostics (literalInitial J j (Real.sqrt n) f z m a c r e)
            w y t x B S F (Real.exp (R/2))) := by
  obtain ⟨C,hC,hsol⟩:=literal_implicit_construction j R ρ δ T L f hδ hρ hT hsmall
  let Cp:=initialPartialBudget f R T C
  have hCp : 0≤Cp := by
    dsimp only [Cp,initialPartialBudget]
    exact add_nonneg (mul_nonneg hC (ratioSmallBudget_nonneg _ _ hT))
      (mul_nonneg (ratioSmallBudget_nonneg _ _ hT) (kernelSmallBudget_nonneg _ _ _ hT))
  let Bs:=|literalSizeBudget j δ R L f|
  let Cr:=initialRegularBudget f j R Bs
  let S:=(2*Cr+Cr*C)*initialTraceFactor Q T C+Cp*E
  let F:=|j| *(Cp*E)+|j| *(Cp*(1+2*T)+3*C*((phiExpr.dBudget R+phiExpr.ddBudget R)*T))
  refine ⟨C+Cp,add_nonneg hC hCp,|S|,abs_nonneg _,|F|,abs_nonneg _,?_⟩
  intro n hn J z m a r e hJ hJL he
  obtain ⟨w,y,c,heq,hb⟩:=hsol n hn J z m a r e hJL he
  refine ⟨w,y,c,heq,?_⟩
  intro x t H Hf hD hDm hm hEz hEm hQ4 hdi
  have hd : Real.sqrt (n:ℝ)≠0:=(Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have heqr {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) :=
    (literalEquations_recipe J j (Real.sqrt n) f z m w y a c r e hd v).mp (heq v HV)
  have hsize {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) :
      |Real.sqrt n*c v|≤Bs := by
    have hh:=literal_initial_size J j f z m w y a c r e v hn hδ hρ hsmall hJL he HV (heq v HV)
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    dsimp only [Bs]
    exact le_trans (by linarith [vectorNorm_nonneg (w v),vectorNorm_nonneg (y v)]) (le_abs_self _)
  obtain ⟨hw,hy,hc,hDc⟩:=hb x H Hf hD hDm
  have hp:=literalInitial_partial_small J j (Real.sqrt n) f z m w y a c r e x hd hT he
    H.a_bound (fun k=>(Hf k).a_bound) hD hw (heqr H).1 (fun k=>(heqr (Hf k)).1)
  obtain ⟨hS,hF⟩:=literalInitial_traces J j f z m w y a c r e x t hn hT hQ
    (abs_nonneg _) he H.a_bound (fun k=>(Hf k).a_bound) (hsize H) (fun k=>hsize (Hf k))
    hD hDm hm hw hy hDc (heqr H).1 (fun k=>(heqr (Hf k)).1) hEz hEm hQ4 hdi
  refine ⟨(heqr H).1,(fun k=>(heqr (Hf k)).1),(heqr H).2.1,
    (fun k=>(heqr (Hf k)).2.1),?_,?_,?_,hw.mono (le_add_of_nonneg_right hCp),
      hy.mono (le_add_of_nonneg_right hCp),hp.mono (le_add_of_nonneg_left hC),
      hS.mono (le_abs_self _),hF.mono (le_abs_self _)⟩
  · intro i
    rw [literalInitial_coefficient]
    exact (phi_pos ..).le
  · intro i
    rw [literalInitial_coefficient,abs_of_pos (phi_pos ..)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [H.a_bound]))
  · have hcoef : (literalInitial J j (Real.sqrt n) f z m a c r e).implicitCoefficient=
        fun v i=>phi (z v i) (r i) (a v) := by
      ext v i
      exact literalInitial_coefficient ..
    rw [hcoef]
    exact literal_inverse_stability J j z m a r x hn hj hJ hδ hρ hsmall H
end SKGapCutoff.Recipe

end
end

end OAI
