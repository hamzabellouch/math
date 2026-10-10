import Mathlib
import OAI.Probability.SKGap.Stability.LiteralStableControl

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma literalBudget_exists (f : KernelExpr) (R T L : ℝ) (hT : 0≤T) :
    ∃B,LiteralBudget f R T L B := by
  let U:=ratioSmallBudget (.kernel f) T
  let P:=ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T
  let V:=(phiExpr.dBudget R+phiExpr.ddBudget R)*T
  let E:=((RatioExpr.kernel phiExpr.dz).dBudget+(RatioExpr.kernel phiExpr.dz).ddBudget)*T
  let B:=2+Real.sqrt (Real.exp (R/2))+|L|+T+U+P+V+E
  have hs:=Real.sqrt_nonneg (Real.exp (R/2))
  have hU:0≤U:=ratioSmallBudget_nonneg _ _ hT
  have hP:0≤P:=mul_nonneg (ratioSmallBudget_nonneg _ _ hT) (kernelSmallBudget_nonneg _ _ _ hT)
  have hV:0≤V:=mul_nonneg (add_nonneg (phiExpr.dBudget_nonneg _) (phiExpr.ddBudget_nonneg _)) hT
  have hE:0≤E:=mul_nonneg (add_nonneg (RatioExpr.dBudget_nonneg _) (RatioExpr.ddBudget_nonneg _)) hT
  have hB:0≤B:=by dsimp [B]; positivity
  have hsB : Real.sqrt (Real.exp (R/2))≤B:=by dsimp [B]; linarith [abs_nonneg L]
  refine ⟨B,⟨hB,?_,hsB,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · dsimp [B]; linarith [abs_nonneg L]
  · have h:=pow_le_pow_left₀ hs hsB 2
    rwa [Real.sq_sqrt (Real.exp_pos _).le] at h
  · dsimp [B]; linarith [le_abs_self L]
  all_goals dsimp [B]; linarith [abs_nonneg L]

lemma literal_system_extension (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m : VectorFields n) (a : Spin n→ℝ) (r e : Fin n→ℝ)
    (hn : 0<n) {R ρ δ : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃w y : VectorFields n,∃c : Spin n→ℝ,
      ∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x := by
  classical
  let P:=fun x (v : Euclid n×Euclid n×ℝ)=>
    LiteralStableAt J j z m a r R ρ δ x→
      Equations j ((∑i,phi (z x i) (r i) (a x))/(n:ℝ)) (n:ℝ)⁻¹
        (siteMean (initialP f z a r e) x) (phiDiagonal (z x) r (a x))
        (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (initialU f z a r e x)) (WithLp.toLp 2 (m x))
        (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)))
        v.1 v.2.1 v.2.2
  have hex : ∀x,∃v,P x v := by
    intro x
    by_cases H:LiteralStableAt J j z m a r R ρ δ x
    · obtain ⟨v,hv,-⟩:=literal_implicit_exists_unique (z x) r (m x) (a x) j
        (siteMean (initialP f z a r e) x) (toEuclideanCLM (𝕜:=ℝ) J)
        (WithLp.toLp 2 (initialU f z a r e x)) hn hδ hρ H.a_bound H.a_small H.z_near H.m_near hsmall H.stable
      exact ⟨v,fun _=>hv⟩
    · exact ⟨0,fun H'=>False.elim (H H')⟩
  choose v hv using hex
  exact ⟨fun x=>(v x).1.ofLp,fun x=>(v x).2.1.ofLp,fun x=>(v x).2.2,hv⟩

theorem literal_implicit_construction (j R ρ δ T L : ℝ) (f : KernelExpr)
    (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    ∃C≥0,∀n : ℕ,0<n→∀(J : Interaction n) (z m : VectorFields n)
      (a : Spin n→ℝ) (r e : Fin n→ℝ),SKGap.opNorm J≤L→vectorNorm e≤1→
      ∃w y : VectorFields n,∃c : Spin n→ℝ,
        (∀x,LiteralStableAt J j z m a r R ρ δ x→LiteralEquations J j f z m w y a c r e x) ∧
        (∀x,LiteralStableAt J j z m a r R ρ δ x→
          (∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))→
          SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T→
          SKGap.opNorm (derivativeMatrix m x)≤T→
          SmallBound w x C ∧ SmallBound y x C ∧ |Real.sqrt n*c x|≤C ∧
            ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤C) := by
  obtain ⟨B,hB⟩:=literalBudget_exists f R T L hT
  refine ⟨uniformControlBudget j δ B,uniformControlBudget_nonneg hδ hB.nonneg,?_⟩
  intro n hn J z m a r e hJ he
  obtain ⟨w,y,c,h⟩:=literal_system_extension J j f z m a r e hn hδ hρ hsmall
  refine ⟨w,y,c,h,?_⟩
  intro x H Hf hD hDm
  exact literal_initial_control J j f z m w y a c r e x hn hδ hρ hT hsmall hB hJ he
    H Hf hD hDm (h x H) (fun k=>h (flip x k) (Hf k))
end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

lemma initialU_size (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) (he : vectorNorm e≤1) :
    vectorNorm (initialU f z a r e x)≤f.mass := by
  exact (vectorNorm_mul _ e f.mass_nonneg (fun i=>(RatioExpr.kernel f).bounded _ _ _)).trans
    (mul_le_of_le_one_right f.mass_nonneg he)

lemma initialP_size (f : KernelExpr) (z : VectorFields n) (a : Spin n→ℝ)
    (r e : Fin n→ℝ) (x : Spin n) {R : ℝ} (ha : |a x|≤R) (he : vectorNorm e≤1) :
    vectorNorm (initialP f z a r e x)≤
      Real.exp (R/2)*((RatioExpr.kernel f).d .z).mass := by
  rw [initialP_ratio]
  apply (vectorNorm_mul _ _ (Real.exp_pos _).le (fun i=>?_)).trans
    (mul_le_mul_of_nonneg_left ((vectorNorm_mul _ e (RatioExpr.mass_nonneg _)
      (fun i=>RatioExpr.bounded _ _ _ _)).trans
        (mul_le_of_le_one_right (RatioExpr.mass_nonneg _) he)) (Real.exp_pos _).le)
  rw [abs_of_pos (phi_pos _ _ _)]
  exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith))

def literalSizeBudget (j δ R L : ℝ) (f : KernelExpr) : ℝ :=
  let A:=Real.exp (R/2)
  let P:=A*((RatioExpr.kernel f).d .z).mass
  let W:=(1+A*(δ/2)⁻¹*(L+|j| *A+4*|j|))*A*(f.mass+2*|j| *P)
  W+(2*W+P)+((L+|j| *A)*W+|j| *(2*W+P))

lemma literal_initial_size (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) {R ρ δ L : ℝ} (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hJ : SKGap.opNorm J≤L) (he : vectorNorm e≤1)
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (h : LiteralEquations J j f z m w y a c r e x) :
    vectorNorm (w x)+vectorNorm (y x)+Real.sqrt n*|c x|≤literalSizeBudget j δ R L f := by
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hd : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
  have hL : 0≤L:=(norm_nonneg _).trans hJ
  have hscale : (n:ℝ)⁻¹*(Real.sqrt (n:ℝ))^2=1 := by
    rw [Real.sq_sqrt hnR.le,inv_mul_cancel₀ hnR.ne']
  have hχ : |siteMean (fun v i=>phi (z v i) (r i) (a v)) x|≤Real.exp (R/2) := by
    apply coefficient_mean_value _ _ (Real.exp_pos _).le
    intro i
    rw [abs_of_pos (phi_pos _ _ _)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [H.a_bound]))
  have hP:=initialP_size f z a r e x H.a_bound he
  have hp:=scaledMean_size hn (initialP f z a r e) x
    (mul_nonneg (Real.exp_pos _).le (RatioExpr.mass_nonneg _)) hP
  rw [abs_mul,abs_of_nonneg hd.le] at hp
  have heq:=h
  unfold LiteralEquations at heq
  rw [←phiSqrt_square] at heq
  obtain ⟨hw,hc,hy⟩:=implicit_uniform_size j _ _ _ _ (phiSqrt (z x) r (a x))
    (toEuclideanCLM (𝕜:=ℝ) J) (WithLp.toLp 2 (initialU f z a r e x))
    (WithLp.toLp 2 (m x)) (WithLp.toLp 2 (fun i=>Real.tanh (r i)))
    (WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)))
    (WithLp.toLp 2 (fun i=>Real.tanh (z x i))) (WithLp.toLp 2 (w x))
    (WithLp.toLp 2 (y x)) (c x) hδ hd (by positivity) hscale
    (Real.exp_pos _).le hL (by norm_num : (0:ℝ)≤2) f.mass_nonneg
    (mul_nonneg (Real.exp_pos _).le (RatioExpr.mass_nonneg _))
    (phiSqrt_bound _ _ _ H.a_bound) hJ hχ (initialU_size f z a r e x he)
    H.m_size (vectorNorm_tanh r) (vectorNorm_logSlope (z x) r (a x)) hp
    H.stable (H.perturbation hn hδ hρ hsmall) heq
  dsimp only [literalSizeBudget]
  change vectorNorm (w x)≤_ at hw
  change vectorNorm (y x)≤_ at hy
  linarith

end SKGapCutoff.Recipe

end
end

end OAI
