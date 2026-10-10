import Mathlib
import OAI.Probability.SKGap.Localization.BufferedFlip

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary
variable {n : ℕ}

def literalSusceptibility (z : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ) : Spin n→ℝ :=
  fun x=>Real.sqrt (n:ℝ)*(siteMean (fun v i=>phi (z v i) (r i) (a v)) x-(1-SKGap.overlap r))

lemma literal_middle_error (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) {R ρ δ L : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hJ : SKGap.opNorm J≤L) (he : vectorNorm e≤1)
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (h : LiteralEquations J j f z m w y a c r e x) :
    |j*(1-SKGap.overlap r-siteMean (fun v i=>phi (z v i) (r i) (a v)) x)*
      (∑i,(Real.tanh (z x i)-Real.tanh (r i))*w x i)|≤
      (|j| *|literalSizeBudget j δ R L f|)*ρ*|literalSusceptibility z a r x| := by
  have hh:=literal_initial_size J j f z m w y a c r e x hn hδ hρ hsmall hJ he H h
  have hw : vectorNorm (w x)≤|literalSizeBudget j δ R L f| := by
    have hrest : 0 ≤ vectorNorm (y x) + Real.sqrt (n:ℝ)*|c x| := by
      exact add_nonneg (vectorNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    exact (le_trans (by linarith) hh).trans (le_abs_self _)
  have hp : vectorNorm (fun i=>Real.tanh (z x i)-Real.tanh (r i))≤ρ*Real.sqrt (n:ℝ) :=
    (magnetization_vector_lipschitz (z x) r).trans H.z_near
  have hd : |∑i,(Real.tanh (z x i)-Real.tanh (r i))*w x i|≤
      (ρ*Real.sqrt (n:ℝ))*|literalSizeBudget j δ R L f| :=
    (SKGap.vector_dot_abs_le _ _).trans (mul_le_mul hp hw (vectorNorm_nonneg _) (by positivity))
  rw [abs_mul,abs_mul]
  apply (mul_le_mul_of_nonneg_left hd (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans_eq
  rw [literalSusceptibility,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _),abs_sub_comm]
  ring

lemma primary_auxiliary_global (hn : 0<n) (j : ℝ) (J : Interaction n) (h r : Fin n→ℝ)
    (k : ℕ) (x : Spin n) :
    |j*(1-Primary.onsager j J h k x-SKGap.overlap r)|≤|j| := by
  have hb:=onsager_bounds j J h k x
  have hq:=SKGap.overlap_nonneg r
  have hq1:=(SKGap.overlap_lt_one hn r).le
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith,by linarith⟩)

lemma literalSusceptibility_global_size (hn : 0<n) (j : ℝ) (J : Interaction n)
    (h r : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |literalSusceptibility (fld j J h k)
      (fun v=>j*(1-Primary.onsager j J h k v-SKGap.overlap r)) r x|≤
      (Real.exp (|j|/2)+1)*Real.sqrt (n:ℝ) := by
  have ha:=primary_auxiliary_global hn j J h r k x
  have hphi : |siteMean (fun v i=>phi (fld j J h k v i) (r i)
      (j*(1-Primary.onsager j J h k v-SKGap.overlap r))) x|≤Real.exp (|j|/2) := by
    apply coefficient_mean_value _ _ (Real.exp_pos _).le
    intro i
    rw [abs_of_pos (phi_pos ..)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith))
  have hq : |1-SKGap.overlap r|≤1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (SKGap.overlap_lt_one hn r).le)]
    linarith [SKGap.overlap_nonneg r]
  have H:=(abs_sub _ _).trans (add_le_add hphi hq)
  rw [literalSusceptibility,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (mul_le_mul_of_nonneg_left H (Real.sqrt_nonneg _)).trans_eq (by ring)

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein
variable {n : ℕ}

lemma parameter_fourth_bound (hn : 0<n) (a : Spin n→ℝ) (x : Spin n) {D : ℝ}
    (hD : (n:ℝ)*‖derivativeVector a x‖^2≤D^2) :
    (∑_:Fin n,∑k:Fin n,(halfDiff k a x)^4)≤D^4 := by
  have hn1 : (1:ℝ)≤n:=by exact_mod_cast hn
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ)
    (f:=fun k:Fin n=>(halfDiff k a x)^2) (fun _ _=>sq_nonneg _)
  have he : (∑k:Fin n,(halfDiff k a x)^2)=‖derivativeVector a x‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,derivativeVector]
  rw [he] at hh
  have hp:=mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hq:=pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)) hD 2
  have hs:=mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg ((n:ℝ)*‖derivativeVector a x‖^2))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←pow_mul] at hp ⊢
  have ht:=mul_le_mul_of_nonneg_left hn1 (pow_nonneg (norm_nonneg (derivativeVector a x)) 4)
  have ht':=mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : (0:ℝ)≤n)
  norm_num only at hp
  nlinarith

lemma one_coefficient_derivative_bound (hn : 0<n) (z : VectorFields n)
    (a : Spin n→ℝ) (x : Spin n) (F : Fin n→Args (ι:=Unit) (κ:=Unit)→ℝ)
    (F' : Fin n→Args (ι:=Unit) (κ:=Unit)→Args (ι:=Unit) (κ:=Unit)→L[ℝ]ℝ)
    {L C D : ℝ} (hC : 0≤C) (hD : 0≤D)
    (H : SegmentRegular (fun _:Unit=>z) (fun _:Unit=>a) F F' x L)
    (hz : ShapeBound (derivativeMatrix z x) C)
    (ha : (n:ℝ)*‖derivativeVector a x‖^2≤D^2) :
    SKGap.opNorm (derivativeMatrix (coefficient (fun _:Unit=>z) (fun _:Unit=>a) F) x)≤
      L*C+L*D+12*L*(C^2+D^2) := by
  have hL:=H.nonneg
  let T:Fin n→ℝ:=localPartial (fun _:Unit=>z) (fun _:Unit=>a) F' (.inl ()) x
  let U:Fin n→ℝ:=localPartial (fun _:Unit=>z) (fun _:Unit=>a) F' (.inr ()) x
  let V:Interaction n:=Matrix.of (fun i k=>(1:ℝ)*halfDiff k a x)
  let R:Interaction n:=Matrix.of (taylorError (fun _:Unit=>z) (fun _:Unit=>a) F F' x)
  have hT : SKGap.opNorm (Matrix.diagonal T)≤L :=
    SKGap.opNorm_diagonal_le H.nonneg (fun i=>H.partial_bound i (.inl ()))
  have hU : SKGap.opNorm (Matrix.diagonal U)≤L :=
    SKGap.opNorm_diagonal_le H.nonneg (fun i=>H.partial_bound i (.inr ()))
  have hV : ‖V‖≤D := outer_frobenius_bound (fun _=>by norm_num) hD ha
  have hRpoint (i k:Fin n) : |R i k|≤6*L*((derivativeMatrix z x i k)^2+(halfDiff k a x)^2) := by
    have hh:=taylor_error_bound (fun _:Unit=>z) (fun _:Unit=>a) F F' x i k H.nonneg
      (abs_nonneg (derivativeMatrix z x i k)) (abs_nonneg (halfDiff k a x))
      (by simpa only [Fintype.sum_unique] using local_argument_bound (fun _:Unit=>z) (fun _:Unit=>a) x i k)
      (H.deriv i k) (H.lip i k)
    change |R i k|≤_ at hh
    simp only [sq_abs] at hh
    have hs:=mul_nonneg H.nonneg (sq_nonneg (|derivativeMatrix z x i k|-|halfDiff k a x|))
    simp only [sub_sq,sq_abs] at hs
    nlinarith
  have hR : ‖R‖≤12*L*(C^2+D^2) := by
    have hs : ‖R‖^2≤72*L^2*(2*C^4+D^4) := by
      rw [SKGap.frobenius_sq]
      calc
        _≤∑i,∑k,72*L^2*((derivativeMatrix z x i k)^4+(halfDiff k a x)^4) := by
          apply Finset.sum_le_sum;intro i _
          apply Finset.sum_le_sum;intro k _
          have h:=pow_le_pow_left₀ (abs_nonneg (R i k)) (hRpoint i k) 2
          have ht:=mul_nonneg (sq_nonneg L) (sq_nonneg ((derivativeMatrix z x i k)^2-(halfDiff k a x)^2))
          nlinarith [sq_abs (R i k)]
        _=72*L^2*((∑i,∑k,(derivativeMatrix z x i k)^4)+(∑i,∑k,(halfDiff k a x)^4)) := by
          simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
        _≤72*L^2*(2*C^4+D^4) := mul_le_mul_of_nonneg_left
          (add_le_add (fourth_sum_le hC hz) (parameter_fourth_bound hn a x ha)) (by positivity)
    apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
    simp only [←sq]
    apply hs.trans
    nlinarith [mul_nonneg (sq_nonneg L) (mul_nonneg (sq_nonneg C) (sq_nonneg D)),
      mul_nonneg (sq_nonneg L) (pow_nonneg hD 4)]
  have he : derivativeMatrix (coefficient (fun _:Unit=>z) (fun _:Unit=>a) F) x=
      Matrix.diagonal T*derivativeMatrix z x+Matrix.diagonal U*V+R := by
    ext i k
    simp only [Matrix.add_apply,Matrix.diagonal_mul,R,V,Matrix.of_apply,T,U,taylorError,localPartial]
    rw [coefficient_chain]
    simp only [Fintype.sum_unique]
    ring
  rw [he]
  have hmain : SKGap.opNorm (Matrix.diagonal T*derivativeMatrix z x)≤L*C :=
    (SKGap.opNorm_mul _ _).trans (mul_le_mul hT hz.1 (norm_nonneg _) H.nonneg)
  have hparam : SKGap.opNorm (Matrix.diagonal U*V)≤L*D :=
    (opNorm_le_frobenius _).trans ((SKGap.frobenius_mul_le_opNorm _ _).trans
      (mul_le_mul hU hV (norm_nonneg _) H.nonneg))
  exact (opNorm_add _ _).trans (add_le_add
    ((opNorm_add _ _).trans (add_le_add hmain hparam)) ((opNorm_le_frobenius _).trans hR))

end SKGapCutoff.Recipe

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein

theorem literalSusceptibility_global_derivative (j K B : ℝ) (hK : 0≤K) (hB : 0≤B) (k : ℕ) :
    ∃S≥0,∀n:ℕ,0<n→∀(J:Interaction n) (h r:Fin n→ℝ),SKGap.opNorm J≤K→
      (∀x l,l<k+3→ShapeBound (formalField j J h x l) B)→∀x:Spin n,
      ‖derivativeVector (literalSusceptibility (fld j J h (k+1))
        (fun v=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)) r) x‖≤S := by
  let f:=KernelExpr.atom 0 0 false
  let L:=f.dBudget |j|+f.ddBudget |j|
  let C:=localPrimaryBudget j K B (k+3)
  let D := |j| * averageBudget j K B k
  have hL : 0≤L:=add_nonneg (f.dBudget_nonneg _) (f.ddBudget_nonneg _)
  have hC : 0≤C:=localPrimaryBudget_nonneg hK hB _
  have hD : 0≤D:=mul_nonneg (abs_nonneg _) (averageBudget_nonneg hK hB _)
  refine ⟨L*C+L*D+12*L*(C^2+D^2),by positivity,?_⟩
  intro n hn J h r hop hformal x
  let z:=fld j J h (k+1)
  let a:=fun v:Spin n=>j*(1-onsager j J h (k+1) v-SKGap.overlap r)
  let F:=fun i:Fin n=>fun u:Args (ι:=Unit) (κ:=Unit)=>eval3 f.eval (phiSelect () () u+(0,(r i,0)))
  let F':=fun i:Fin n=>fun u:Args (ι:=Unit) (κ:=Unit)=>
    (f.gradient (phiSelect () () u+(0,(r i,0)))).comp (phiSelect () ())
  have hreg : SegmentRegular (fun _:Unit=>z) (fun _:Unit=>a) F F' x L :=
    fixed_root_kernel_regular f (fun _:Unit=>z) (fun _:Unit=>a) x () () r |j|
      (primary_auxiliary_global hn j J h r (k+1) x)
      (fun v=>primary_auxiliary_global hn j J h r (k+1) (flip x v))
  have hz : ShapeBound (derivativeMatrix z x) C :=
    ((primary_differentiation J h x hn hK hB hop (k+1)
      (fun l hl=>hformal x l (by omega))).2.2.2).mono
      (localPrimaryBudget_bounds hK hB (k+3) ⟨k+1,by omega⟩).1
  have hm : (n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2≤(averageBudget j K B k)^2 := by
    simpa only [onsager,mag,primaryState,scalarVariance,averageBudget] using
      primary_average_differentiation J h x hn hK hB hop k (fun l hl=>hformal x l (by omega))
  have ha : (n:ℝ)*‖derivativeVector a x‖^2≤D^2 := by
    dsimp only [a]
    rw [auxiliary_derivative,norm_smul,Real.norm_eq_abs,abs_neg,mul_pow]
    calc
      _=|j|^2*((n:ℝ)*‖derivativeVector (onsager j J h (k+1)) x‖^2) := by ring
      _≤|j|^2*(averageBudget j K B k)^2 := mul_le_mul_of_nonneg_left hm (sq_nonneg _)
      _=D^2 := by dsimp [D];ring
  have he : coefficient (fun _:Unit=>z) (fun _:Unit=>a) F=(fun v i=>phi (z v i) (r i) (a v)) := by
    funext v i
    simp only [coefficient,F,eval3,phiSelect_apply,Prod.fst_add,Prod.snd_add,
      localArgs,Sum.elim_inl,Sum.elim_inr,zero_add,add_zero,f,KernelExpr.eval,moment_base]
  have hmat:=one_coefficient_derivative_bound hn z a x F F' hC hD hreg hz ha
  rw [he] at hmat
  have hav:=siteMean_derivative_square_bound hn hmat
  have hed : derivativeVector (literalSusceptibility z a r) x=
      Real.sqrt (n:ℝ) • derivativeVector (siteMean (fun v i=>phi (z v i) (r i) (a v))) x := by
    ext i
    simp only [derivativeVector,WithLp.ofLp_toLp,PiLp.smul_apply,literalSusceptibility,halfDiff]
    ring
  change ‖derivativeVector (literalSusceptibility z a r) x‖≤_
  rw [hed,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply nonneg_le_nonneg_of_sq_le_sq (by positivity)
  simpa only [←sq,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using hav

end SKGapCutoff.Recipe

end
end
end

end OAI
