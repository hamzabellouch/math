import Mathlib
import OAI.Probability.SKGap.Localization.LocalResidualInduction
import OAI.Probability.SKGap.Localization.LiteralLocalInput

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}

def literalResidualBudget (j : ℝ) (f : KernelExpr) (R B : ℝ) (p : ℕ) : ℝ :=
  residualCoefficientBudget j (2+|literalCoefficientBudget f j R B|) p 0

theorem literal_local_weak_residual (j : ℝ) (J : ∀b,Interaction (n b))
    (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
    (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
    (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
    (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
    {K B R Bc Va Vc V S F W C : ℝ}
    (hK : 0≤K) (hB : 0≤B) (hBc : 0≤Bc) (hVa : 0≤Va) (hVc : 0≤Vc)
    (hV : 0≤V) (hS : 0≤S) (hF : 0≤F) (hW : 0≤W) (hC : 0≤C)
    (hop : ∀b,SKGap.opNorm (J b)≤K)
    (hformal : ∀b x,∀q<M,ShapeBound (formalField j (J b) (h b) x q) B)
    (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
    (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤Bc)
    (hDa : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (a b) x‖≤Va)
    (hDc : ∀b x,x∈flipNeighborhood (E b)→‖derivativeVector (fun v=>Real.sqrt (n b:ℝ)*c b v) x‖≤Vc)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x)
    (hdiag : ∀b x,x∈flipNeighborhood (E b)→LiteralInitialDiagnostics
      (literalInitial (J b) j (Real.sqrt (n b:ℝ)) f (fld j (J b) (h b) l.val)
        (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b))
      (w b) (y b) (primaryTree j (J b) (h b) x l.val) x V S F (literalResidualBudget j f R Bc l.val))
    (P : ∀b,Observables (n b)) (hP : ∀b x,0≤P b x) (hp : ∀b,∑x,P b x=1)
    (hm : ∀b x i,conditionalMean (P b) x i=mag j (J b) (h b) 1 x i)
    (hJ : ∀b,(J b).IsSymm)
    (hw : ∀b x,x∈flipNeighborhood (E b)→ClosedWordTestBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) (literalResidualBudget j f R Bc l.val) W (2*(1+2*l.val)+5))
    (hd : ∀b x,x∈flipNeighborhood (E b)→ClosedWordDiagramBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) (literalResidualBudget j f R Bc l.val) C (2*M+2*(1+2*l.val)+4)) :
    LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) l.val x i*w b x i) := by
  let Kt:=2+|literalCoefficientBudget f j R Bc|
  have hKt : 2≤Kt := by dsimp [Kt];linarith [abs_nonneg (literalCoefficientBudget f j R Bc)]
  have hKt0 : 0≤Kt:=by linarith
  have hA : 1≤literalResidualBudget j f R Bc l.val :=
    (by linarith : 1≤Kt).trans (residualCoefficientBudget_ge j hKt0 l.val 0)
  have C:=literal_finite_control j J h l f a c r e w y E hn he
    hK hB hBc hVa hVc hA hV hS hF hW hC hop hformal ha hc hDa hDc heq hdiag
    (1+2*l.val) hw hd
  have H:=literal_full_local_family j J h l f a c r e w y E hn he hBc ha hc heq
  have hclass : literalCoefficientBudget f j R Bc≤Kt := by
    dsimp [Kt];linarith [le_abs_self (literalCoefficientBudget f j R Bc)]
  have HH:=H.mono le_rfl le_rfl le_rfl hclass
  have hwk:=uniform_local_weak_residual l.val 1 hKt l.isLt Sum.inl (fun _ _=>rfl)
    C hP hp hm hn hJ (fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)) HH
  apply hwk.congr_on
  intro b x hx
  rw [(H.initial b x hx).1]

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

theorem literal_complete_diagnostics (j R ρ δ T L Q E : ℝ) (f : KernelExpr)
    (hj : 0≤j) (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T) (hQ : 0≤Q)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃B≥0,∃S≥0,∃F≥0,∃Bc≥0,∃Vc≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
      (a : Spin n→ℝ) (r e : Fin n→ℝ),J.IsSymm→SKGap.opNorm J≤L→vectorNorm e≤1→
      ∃w y : VectorFields n,∃c : Spin n→ℝ,
        (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→|Real.sqrt n*c x|≤Bc) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→
          ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤Vc) ∧
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
  refine ⟨C+Cp,add_nonneg hC hCp,|S|,abs_nonneg _,|F|,abs_nonneg _,Bs,abs_nonneg _,C,hC,?_⟩
  intro n hn J z m a r e hJ hJL he
  obtain ⟨w,y,c,heq,hb⟩:=hsol n hn J z m a r e hJL he
  have hcs {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) :
      |Real.sqrt n*c v|≤Bs := by
    have hh:=literal_initial_size J j f z m w y a c r e v hn hδ hρ hsmall hJL he HV (heq v HV)
    rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
    dsimp only [Bs]
    exact le_trans (by linarith [vectorNorm_nonneg (w v),vectorNorm_nonneg (y v)]) (le_abs_self _)
  refine ⟨w,y,c,heq,fun x H=>hcs H,fun x H Hf hD hDm=>(hb x H Hf hD hDm).2.2.2,?_⟩
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
