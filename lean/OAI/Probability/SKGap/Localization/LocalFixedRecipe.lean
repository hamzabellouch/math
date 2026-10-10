import Mathlib
import OAI.Probability.SKGap.Gaussian.LiteralWeakTail
import OAI.Probability.SKGap.Localization.StartedFixed

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe.LocalFamilyRecipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
variable {σ : Type} [Fintype σ]
variable {E : ∀a,Set (Spin (n a))} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {Θ : ∀a,κ→Observables (n a)} {w y : ∀a,VectorFields (n a)}
variable {D : ∀a,OrdinaryData (n a) (Fin M) κ σ} {N p : ℕ} {K : ℝ}

lemma appendFixed (H : LocalFamilyRecipe E j J h Θ w y D N p K)
    (v : ∀a,Fin (n a)→ℝ) (hv : ∀a,vectorNorm (v a)≤1) (hK : 1≤K) :
    LocalFamilyRecipe E j J h Θ w y (fun a=>(D a).appendFixed N (v a)) (N+1) p K := by
  refine ⟨by omega,H.interaction,H.coupling,H.primary,H.predecessor,H.parameter,?_,
    fun a x hx=>(H.coefficients a x hx).appendFixed hK (v a),
    fun a=>(D a).appendFixed_Admissible N p (v a) (H.admissible a),?_⟩
  · obtain ⟨S,hS,hs⟩:=H.seed
    refine ⟨S+1,by positivity,fun a=>?_⟩
    rw [(D a).appendFixed_seed N (v a)]
    linarith [hs a,hv a]
  · intro a x hx
    have hp:=(D a).appendFixed_started_prefix (w a) (y a) N (v a) 1 H.positive
    simpa only [hp.1,hp.2] using H.initial a x hx

end SKGapCutoff.Recipe.LocalFamilyRecipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static SKGap.Stein SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ}
theorem literal_local_weak_comparison_targets (j : ℝ) (J : ∀b,Interaction (n b))
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
    ((∀p≤l.val,LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) p x i*w b x i)) ∧
    LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) l.val x i*y b x i) ∧
    LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) l.val x i*
      (Real.tanh (fld j (J b) (h b) l.val x i)/Real.sqrt (n b:ℝ))) ∧
    LocalUniformMultiplier E (fun b=>siteMean (fun x i=>phi (fld j (J b) (h b) l.val x i) (r b i) (a b x))) ∧
    LocalUniformMultiplier E (fun b x=>j*onsager j (J b) (h b) l.val x) ∧
    LocalUniformMultiplier E (fun b x=>Real.sqrt (n b:ℝ)*c b x)) ∧
    LocalUniformWeak E P (fun b x=>j*c b x*(∑i,residual j (J b) (h b) l.val x i*
      (Real.tanh (fld j (J b) (h b) l.val x i)-Real.tanh (r b i)))) := by
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
  have hterms:=literal_local_weak_terminal_targets j J h l f a c r e w y E hn he
    hK hB hBc hVa hVc hV hS hF hW hC hop hformal ha hc hDa hDc heq hdiag P hP hp hm hJ hw hd
  let v:=fun b i=>Real.tanh (r b i)/Real.sqrt (n b:ℝ)
  have hv : ∀b,vectorNorm (v b)≤1 := by
    intro b
    have hs : 0<Real.sqrt (n b:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hn b))
    have hscale : v b=(Real.sqrt (n b:ℝ))⁻¹ • (fun i=>Real.tanh (r b i)):=by
      ext i; simp [v,div_eq_mul_inv,mul_comm]
    rw [hscale,vectorNorm_smul,abs_of_nonneg (inv_nonneg.mpr hs.le)]
    exact (mul_le_mul_of_nonneg_left (vectorNorm_tanh (r b)) (inv_nonneg.mpr hs.le)).trans_eq
      (inv_mul_cancel₀ hs.ne')
  have H':=HH.appendFixed v hv (by linarith : 1≤Kt)
  have hfixed:=rule l.val le_rfl (fun b=>(D b).appendFixed 1 (v b)) 2
    (H'.mono le_rfl le_rfl (by norm_num) (residualCoefficientBudget_ge j hKt0 l.val l.val)) (by omega)
  have hroot : LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) l.val x i*v b i) := by
    apply hfixed.congr
    intro b x
    rw [show 2=1+1 from rfl,OrdinaryData.appendFixed_started_source]
  have hnorm := hterms.2.2.1.sub hroot
  have hnorm' : LocalUniformWeak E P (fun b x=>∑i,residual j (J b) (h b) l.val x i*
      ((Real.tanh (fld j (J b) (h b) l.val x i)-Real.tanh (r b i))/Real.sqrt (n b:ℝ))) := by
    apply hnorm.congr
    intro b x
    simp only [v,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨hterms,?_⟩
  apply ((hnorm'.mul hP hterms.2.2.2.2.2).smul hP j).congr
  intro b x
  rw [normalized_pair_cancel (hn b) (residual j (J b) (h b) l.val)
    (fun x i=>Real.tanh (fld j (J b) (h b) l.val x i)-Real.tanh (r b i)) (c b) x]
  ring

end SKGapCutoff.Recipe

end
end

end OAI
