import Mathlib
import OAI.Probability.SKGap.Localization.LiteralLocalWeak

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}
theorem literal_local_weak_terminal_targets (j : ℝ) (J : ∀b,Interaction (n b))
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
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) (literalResidualBudget j f R Bc l.val) W (2*(2+2*l.val)+5))
    (hd : ∀b x,x∈flipNeighborhood (E b)→ClosedWordDiagramBound j
      (fun i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x)) (J b) (literalResidualBudget j f R Bc l.val) C (2*M+2*(2+2*l.val)+4)) :
    (∀p≤l.val,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i)) ∧
    LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) l.val x i*y b x i) ∧
    LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) l.val x i*
      (Real.tanh (fld j (J b) (h b) l.val x i)/Real.sqrt (n b:ℝ))) ∧
    LocalUniformMultiplier E (fun b=>siteMean (fun x i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x))) ∧
    LocalUniformMultiplier E (fun b x=>j*onsager j (J b) (h b) l.val x) ∧
    LocalUniformMultiplier E (fun b x=>Real.sqrt (n b:ℝ)*c b x) := by
  let Kt:=2+|literalCoefficientBudget f j R Bc|
  have hKt : 2≤Kt := by dsimp [Kt];linarith [abs_nonneg (literalCoefficientBudget f j R Bc)]
  have hKt0 : 0≤Kt:=by linarith
  have hA : 1≤literalResidualBudget j f R Bc l.val :=
    (by linarith : 1≤Kt).trans (residualCoefficientBudget_ge j hKt0 l.val 0)
  have C:=literal_finite_control j J h l f a c r e w y E hn he
    hK hB hBc hVa hVc hA hV hS hF hW hC hop hformal ha hc hDa hDc heq hdiag
    (2+2*l.val) hw hd
  have H:=literal_full_local_family j J h l f a c r e w y E hn he hBc ha hc heq
  have hclass : literalCoefficientBudget f j R Bc≤Kt := by
    dsimp [Kt];linarith [le_abs_self (literalCoefficientBudget f j R Bc)]
  have HH:=H.mono le_rfl le_rfl le_rfl hclass
  have hb:=residualCoefficientBudget_antitone j hKt0 l.val
  have rule:=local_uniform_residual_rule C hP hp hm hn hJ Sum.inl (fun _ _=>rfl)
    (residualCoefficientBudget j Kt l.val) hb l.val l.isLt
    (fun p _=>hb (Nat.zero_le p))
    (fun p _=>hKt.trans (residualCoefficientBudget_ge j hKt0 l.val p))
    (fun p hp=>le_of_eq (residualCoefficientBudget_step j Kt hp))
  let D:=fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)
  have allw : ∀p≤l.val,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i) := by
    intro p hp
    have H':=HH.mono hp le_rfl le_rfl (residualCoefficientBudget_ge j hKt0 l.val p)
    have hh:=rule p hp D 1 H' (by omega)
    apply hh.congr_on
    intro b x hx
    rw [(H.initial b x hx).1]
  refine ⟨allw,?_,?_,?_,?_,?_⟩
  · have H' := HH.appendAuxiliary
    have hh:=rule l.val le_rfl (fun b=>(D b).appendAuxiliary 1) 2
      (H'.mono le_rfl le_rfl (by norm_num) (residualCoefficientBudget_ge j hKt0 l.val l.val)) (by omega)
    apply hh.congr_on
    intro b x hx
    rw [show 2=1+1 from rfl,OrdinaryData.appendAuxiliary_started_source,(H.initial b x hx).2]
  · have H' := HH.appendPrimary hn hKt l le_rfl
    have hh:=rule l.val le_rfl (fun b=>(D b).appendPrimary 1 l) 2
      (H'.mono le_rfl le_rfl (by norm_num) (residualCoefficientBudget_ge j hKt0 l.val l.val)) (by omega)
    apply hh.congr
    intro b x
    rw [show 2=1+1 from rfl,OrdinaryData.appendPrimary_started_source]
    rfl

  · have hh:=C.means D 1 l.val Kt HH (by omega) (residualCoefficientBudget_ge j hKt0 l.val 0) 0
    apply hh.congr
    intro b x
    congr 1
    ext v i
    dsimp only [D,literalFullData]
    rw [OrdinaryData.unitPullback_auxCoefficient _ l Sum.inr _ _ _ rfl rfl]
    exact literalInitial_coefficient _ _ _ _ _ _ _ _ _ _ _ _
  · exact C.local_onsager_multiplier l.val l.isLt.le
  · refine ⟨Bc,Vc,hBc,hVc,fun b x hx=>hc b x (Or.inl hx),?_⟩
    intro b x hx
    simpa only [norm_derivativeVector_sq] using
      pow_le_pow_left₀ (norm_nonneg _) (hDc b x (Or.inl hx)) 2

end SKGapCutoff.Recipe

end
end

end OAI
