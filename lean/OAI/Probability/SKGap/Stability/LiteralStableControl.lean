import Mathlib
import OAI.Probability.SKGap.Stability.OrdinaryClosure
import OAI.Probability.SKGap.Stability.ImplicitUniformControl
import OAI.Probability.SKGap.Localization.LiteralSystemBridge

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open SKGap.Stein Primary SKGap.ImplicitSystem Matrix
variable {n : ℕ}

structure LiteralStableAt (J : Interaction n) (j : ℝ)
    (z m : VectorFields n) (a : Spin n→ℝ) (r : Fin n→ℝ)
    (R ρ δ : ℝ) (x : Spin n) : Prop where
  a_bound : |a x|≤R
  a_small : |a x|≤ρ
  z_near : vectorNorm (z x-r)≤ρ*Real.sqrt n
  m_near : vectorNorm (m x-(fun i=>Real.tanh (r i)))≤ρ*Real.sqrt n
  m_bound : ∀i,|m x i|≤1
  stable : ∀v,δ*‖v‖^2≤ inner ℝ v
    (stableMatrix j ((∑i,scalarVariance (z x i))/(n:ℝ)) (n:ℝ)⁻¹
      (phiSqrt (z x) r (a x)) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (fun i=>Real.tanh (z x i))) v)

lemma LiteralStableAt.perturbation {J : Interaction n} {j : ℝ}
    {z m : VectorFields n} {a : Spin n→ℝ} {r : Fin n→ℝ}
    {R ρ δ : ℝ} {x : Spin n} (H : LiteralStableAt J j z m a r R ρ δ x)
    (hn : 0<n) (hδ : 0<δ) (hρ : 0≤ρ)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1))) :
    |j| *|siteMean (fun v i=>phi (z v i) (r i) (a v)) x-
      (∑i,scalarVariance (z x i))/(n:ℝ)| *‖phiSqrt (z x) r (a x)‖^2+
      |j*(n:ℝ)⁻¹| *‖phiSqrt (z x) r (a x)‖^2*
      (‖(WithLp.toLp 2 (m x) : Euclid n)+WithLp.toLp 2 (fun i=>Real.tanh (r i))-
        (2:ℝ) • WithLp.toLp 2 (fun i=>Real.tanh (z x i))‖*
          ‖(WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)‖+
       2*‖(WithLp.toLp 2 (fun i=>Real.tanh (z x i)) : Euclid n)‖*
        ‖(WithLp.toLp 2 (fun i=>logSlope (z x i) (r i) (a x)) : Euclid n)+
          WithLp.toLp 2 (fun i=>Real.tanh (z x i))‖)≤δ/2 :=
  (implicit_normalized_perturbation (z x) r (m x) (a x) j (phiSqrt (z x) r (a x))
    hn hρ H.a_bound H.a_small H.z_near H.m_near (phiSqrt_bound _ _ _ H.a_bound)).trans
      (implicit_rho_threshold j R δ ρ hδ hsmall)

lemma LiteralStableAt.m_size {J : Interaction n} {j : ℝ}
    {z m : VectorFields n} {a : Spin n→ℝ} {r : Fin n→ℝ}
    {R ρ δ : ℝ} {x : Spin n} (H : LiteralStableAt J j z m a r R ρ δ x) :
    vectorNorm (m x)≤Real.sqrt n := by
  have h:=vectorNorm_mono (u:=m x) (v:=fun _=>1) (fun i=>by simpa using H.m_bound i)
  simpa only [vectorNorm_const,abs_one,one_mul] using h

lemma frobenius_le_opNorm_sqrt (D : Interaction n) : ‖D‖≤SKGap.opNorm D*Real.sqrt n :=
  frobenius_by_rows D (norm_nonneg _) (fun i=>SKGap.SourceError.matrix_row_square_le D i)

structure LiteralBudget (f : KernelExpr) (R T L B : ℝ) : Prop where
  nonneg : 0≤B
  two : 2≤B
  root : Real.sqrt (Real.exp (R/2))≤B
  square : Real.exp (R/2)≤B^2
  matrix : L≤B
  primary : T≤B
  source : ratioSmallBudget (.kernel f) T≤B
  scalar : ratioSmallBudget ((RatioExpr.kernel f).d .z) T*kernelSmallBudget phiExpr R T≤B
  phi_row : (phiExpr.dBudget R+phiExpr.ddBudget R)*T≤B
  slope_row : ((RatioExpr.kernel phiExpr.dz).dBudget+(RatioExpr.kernel phiExpr.dz).ddBudget)*T≤B

lemma literal_initial_control (J : Interaction n) (j : ℝ) (f : KernelExpr)
    (z m w y : VectorFields n) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    (hn : 0<n) {R ρ δ T L B : ℝ} (hδ : 0<δ) (hρ : 0≤ρ) (hT : 0≤T)
    (hsmall : ρ≤δ/(2*(|j| *Real.exp (R/2)*(3*Real.exp (R/2)+16)+1)))
    (hB : LiteralBudget f R T L B) (hJ : SKGap.opNorm J≤L) (he : vectorNorm e≤1)
    (H : LiteralStableAt J j z m a r R ρ δ x)
    (Hf : ∀k,LiteralStableAt J j z m a r R ρ δ (flip x k))
    (hD : SKGap.opNorm (derivativeMatrix z x)+‖derivativeVector a x‖≤T)
    (hDm : SKGap.opNorm (derivativeMatrix m x)≤T)
    (h : LiteralEquations J j f z m w y a c r e x)
    (hf : ∀k,LiteralEquations J j f z m w y a c r e (flip x k)) :
    SmallBound w x (uniformControlBudget j δ B) ∧
    SmallBound y x (uniformControlBudget j δ B) ∧
    |Real.sqrt n*c x|≤uniformControlBudget j δ B ∧
    ‖derivativeVector (fun v=>Real.sqrt n*c v) x‖≤uniformControlBudget j δ B := by
  let A : VectorFields n:=fun v i=>phi (z v i) (r i) (a v)
  let ell : VectorFields n:=fun v i=>logSlope (z v i) (r i) (a v)
  have hnR : (0:ℝ)<n:=Nat.cast_pos.mpr hn
  have hd : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr hnR
  have hscale : (n:ℝ)⁻¹*(Real.sqrt (n:ℝ))^2=1 := by rw [Real.sq_sqrt hnR.le,inv_mul_cancel₀ hnR.ne']
  have ha:=initial_kernel_bound phiExpr z a r x hT H.a_bound (fun k=>(Hf k).a_bound) hD
  have ha' : CoefficientBound A x (Real.exp (R/2)) ((phiExpr.dBudget R+phiExpr.ddBudget R)*T) := by
    convert! ha using 1
    · ext v i; exact (moment_base _ _ _).symm
    · simp [phiExpr,KernelExpr.mass]
  have hel:=initial_ratio_bound (.kernel phiExpr.dz) z a r x hT hD
  have hel' : CoefficientBound ell x (RatioExpr.kernel phiExpr.dz).mass
      (((RatioExpr.kernel phiExpr.dz).dBudget+(RatioExpr.kernel phiExpr.dz).ddBudget)*T) := by
    convert! hel using 1
    ext v i; exact logSlope_ratio _ _ _
  have hu:=(initialU_small f z a r e x hT he hD).mono hB.source
  have hp:=(initialP_small f z a r e x hT he H.a_bound (fun k=>(Hf k).a_bound) hD).mono hB.scalar
  have hp':=scaledMean_norm hn _ x hp
  have hX {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) : ‖phiSqrt (z v) r (a v)‖≤B := by
    apply (Real.le_sqrt (norm_nonneg _) (Real.exp_pos _).le).mpr (phiSqrt_bound _ _ _ HV.a_bound) |>.trans hB.root
  have hχ {v : Spin n} (HV : LiteralStableAt J j z m a r R ρ δ v) : |siteMean A v|≤B^2 := by
    apply (coefficient_mean_value A v (Real.exp_pos _).le (fun i=>?_) ).trans hB.square
    rw [abs_of_pos (phi_pos _ _ _)]
    exact (phi_le_exp ..).trans (Real.exp_le_exp.mpr (by linarith [HV.a_bound]))
  have hell {v : Spin n} : ‖(WithLp.toLp 2 (ell v) : Euclid n)‖≤B*Real.sqrt n :=
    (vectorNorm_logSlope (z v) r (a v)).trans (mul_le_mul_of_nonneg_right hB.two hd.le)
  have hDA (V : Euclid n) : columnNorm (fun k=>((spin x k/2) •
      (phiSqrt (z x) r (a x)*phiSqrt (z x) r (a x)-
        phiSqrt (z (flip x k)) r (a (flip x k))*phiSqrt (z (flip x k)) r (a (flip x k)))) V)≤B*‖V‖ := by
    simp only [phiSqrt_square]
    exact (diagonal_halfDiff_columns A x ha'.row_nonneg ha'.difference V).trans
      (mul_le_mul_of_nonneg_right hB.phi_row (norm_nonneg _))
  have hDu : columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (initialU f z a r e x) : Euclid n)-WithLp.toLp 2 (initialU f z a r e (flip x k))))≤B := by
    rw [columnNorm_halfDiff]; exact hu.derivative
  have hDχ : columnNorm (fun k=>(spin x k/2)*(siteMean A x-siteMean A (flip x k)))≤B := by
    rw [columnNorm_scalar_halfDiff]
    exact (coefficient_mean_difference A x ha'.row_nonneg ha'.difference).trans hB.phi_row
  have hDm' : columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (m x) : Euclid n)-WithLp.toLp 2 (m (flip x k))))≤B*Real.sqrt n := by
    rw [columnNorm_halfDiff]
    exact (frobenius_le_opNorm_sqrt _).trans (mul_le_mul_of_nonneg_right (hDm.trans hB.primary) hd.le)
  have hDell : columnNorm (fun k=>(spin x k/2) •
      ((WithLp.toLp 2 (ell x) : Euclid n)-WithLp.toLp 2 (ell (flip x k))))≤B*Real.sqrt n := by
    rw [columnNorm_halfDiff]
    exact (frobenius_by_rows _ hel'.row_nonneg hel'.difference).trans
      (mul_le_mul_of_nonneg_right hB.slope_row hd.le)
  have hDp : Real.sqrt n*columnNorm (fun k=>(spin x k/2)*
      (siteMean (initialP f z a r e) x-siteMean (initialP f z a r e) (flip x k)))≤B := by
    rw [columnNorm_scalar_halfDiff]; exact hp'.2
  have hEq : Equations j (siteMean A x) (n:ℝ)⁻¹ (siteMean (initialP f z a r e) x)
      (phiSqrt (z x) r (a x)*phiSqrt (z x) r (a x)) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (initialU f z a r e x)) (WithLp.toLp 2 (m x))
      (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (ell x))
      (WithLp.toLp 2 (w x)) (WithLp.toLp 2 (y x)) (c x) := by
    rw [phiSqrt_square]; exact h
  have hEqf k : Equations j (siteMean A (flip x k)) (n:ℝ)⁻¹ (siteMean (initialP f z a r e) (flip x k))
      (phiSqrt (z (flip x k)) r (a (flip x k))*phiSqrt (z (flip x k)) r (a (flip x k))) (toEuclideanCLM (𝕜:=ℝ) J)
      (WithLp.toLp 2 (initialU f z a r e (flip x k))) (WithLp.toLp 2 (m (flip x k)))
      (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (ell (flip x k)))
      (WithLp.toLp 2 (w (flip x k))) (WithLp.toLp 2 (y (flip x k))) (c (flip x k)) := by
    rw [phiSqrt_square]; exact hf k
  have ht:=implicit_uniform_control j (siteMean A x) ((∑i,scalarVariance (z x i))/(n:ℝ)) (n:ℝ)⁻¹
    (siteMean (initialP f z a r e) x) (phiSqrt (z x) r (a x)) (toEuclideanCLM (𝕜:=ℝ) J)
    (WithLp.toLp 2 (initialU f z a r e x)) (WithLp.toLp 2 (m x))
    (WithLp.toLp 2 (fun i=>Real.tanh (r i))) (WithLp.toLp 2 (ell x))
    (WithLp.toLp 2 (fun i=>Real.tanh (z x i))) (WithLp.toLp 2 (w x)) (WithLp.toLp 2 (y x)) (c x)
    (fun k=>spin x k/2) (fun k=>siteMean A (flip x k)) (fun k=>siteMean (initialP f z a r e) (flip x k))
    (fun k=>c (flip x k)) (fun k=>(∑i,scalarVariance (z (flip x k) i))/(n:ℝ))
    (fun k=>phiSqrt (z (flip x k)) r (a (flip x k)))
    (fun k=>WithLp.toLp 2 (initialU f z a r e (flip x k))) (fun k=>WithLp.toLp 2 (m (flip x k)))
    (fun k=>WithLp.toLp 2 (ell (flip x k))) (fun k=>WithLp.toLp 2 (w (flip x k)))
    (fun k=>WithLp.toLp 2 (y (flip x k))) (fun k=>WithLp.toLp 2 (fun i=>Real.tanh (z (flip x k) i)))
    hδ hd (inv_nonneg.mpr hnR.le) hscale hB.nonneg (hX H) (fun k=>hX (Hf k)) (hJ.trans hB.matrix)
    (hχ H) (fun k=>hχ (Hf k)) hu.size H.m_size (fun k=>(Hf k).m_size) (vectorNorm_tanh r)
    hell (fun _=>hell) hp'.1 H.stable (fun k=>(Hf k).stable)
    (H.perturbation hn hδ hρ hsmall) (fun k=>(Hf k).perturbation hn hδ hρ hsmall)
    hEq hEqf hDA hDu hDχ hDm' hDell hDp
  rw [columnNorm_halfDiff,columnNorm_halfDiff,columnNorm_scalar_halfDiff] at ht
  exact implicit_tuple_small w y c x hd.le (uniformControlBudget_nonneg hδ hB.nonneg) ht
end SKGapCutoff.Recipe

end
end

end OAI
