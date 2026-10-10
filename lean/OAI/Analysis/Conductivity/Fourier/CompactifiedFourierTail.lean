import Mathlib
import OAI.Analysis.Conductivity.Fourier.TorusFourierSmooth

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology

lemma linear_comp_iterated_point_bound {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → G} (g : F →L[ℝ] E)
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) (n : ℕ) (x : F) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤
      ‖iteratedFDeriv ℝ n f (g x)‖*‖g‖^n := by
  rw [g.iteratedFDeriv_comp_right ((contDiff_infty.mp hf) n) x le_rfl]
  simpa using (iteratedFDeriv ℝ n f (g x)).norm_compContinuousLinearMap_le (fun _ => g)

lemma glue_derivative_compact_bound {gap : ℝ} (hg : 0<gap) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ p∈Icc (-gap⁻¹) gap⁻¹,
      ‖iteratedFDeriv ℝ n expNegInvGlue p‖≤C := by
  have hc := (expNegInvGlue.contDiff (n := (⊤:ℕ∞))).continuous_iteratedFDeriv
    (m := n) (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))
  obtain ⟨C,hC⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
  exact ⟨max C gap,hg.le.trans (le_max_right _ _),
    fun p hp => (hC _ ⟨p,hp,rfl⟩).trans (le_max_left _ _)⟩

lemma glue_scaled_iterated_bound {gap d C : ℝ} (hg : 0<gap) (hd : gap≤d)
    (n : ℕ) (hC : 0≤C) (hb : ∀ p∈Icc (-gap⁻¹) gap⁻¹,
      ‖iteratedFDeriv ℝ n expNegInvGlue p‖≤C)
    {z : ℝ×Coord3} (hz : |z.1|≤1) :
    ‖iteratedFDeriv ℝ n (fun z : ℝ×Coord3 => expNegInvGlue (z.1/d)) z‖≤C*gap⁻¹^n := by
  let P : (ℝ×Coord3) →L[ℝ] ℝ := d⁻¹ • ContinuousLinearMap.fst ℝ ℝ Coord3
  have hdpos : 0<d := hg.trans_le hd
  have hdi : d⁻¹≤gap⁻¹ := inv_anti₀ hg hd
  have hpn : ‖P‖≤gap⁻¹ := by
    dsimp [P]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hdpos)]
    exact (mul_le_of_le_one_right (inv_nonneg.mpr hdpos.le)
      (ContinuousLinearMap.norm_fst_le ℝ ℝ Coord3)).trans hdi
  have hpv : P z∈Icc (-gap⁻¹) gap⁻¹ := by
    have hab : |P z|≤gap⁻¹ := by
      change |d⁻¹*z.1|≤_
      rw [abs_mul,abs_of_pos (inv_pos.mpr hdpos)]
      exact (mul_le_of_le_one_right (inv_nonneg.mpr hdpos.le) hz).trans hdi
    exact abs_le.mp hab
  have he : (fun z : ℝ×Coord3 => expNegInvGlue (z.1/d))=expNegInvGlue ∘ P := by
    funext w; simp [P,div_eq_mul_inv,mul_comm]
  rw [he]
  exact (linear_comp_iterated_point_bound P expNegInvGlue.contDiff n z).trans
    (mul_le_mul (hb _ hpv) (pow_le_pow_left₀ (norm_nonneg _) hpn n)
      (by positivity) hC)

lemma flatPhaseMode_shift_snd_bound (s : Fin 3→ℝ) (h : Fin 2→ℤ)
    (phase T δ : ℝ) (n : ℕ) {z : ℝ×Coord3} (hz : δ≤T+z.2 0) :
    ‖iteratedFDeriv ℝ n (fun z : ℝ×Coord3 => flatPhaseMode s h phase (z.2+![T,0,0])) z‖≤
      (torusRate s h+torusSize h)^n*exp (-δ*torusRate s h) := by
  let f : Coord3→ℝ := fun y => flatPhaseMode s h phase (y+![T,0,0])
  let P : (ℝ×Coord3) →L[ℝ] Coord3 := ContinuousLinearMap.snd ℝ ℝ Coord3
  have hf : ContDiff ℝ (↑(⊤:ℕ∞)) f := (flatPhaseMode_smooth s h phase).comp (contDiff_id.add contDiff_const)
  change ‖iteratedFDeriv ℝ n (f ∘ P) z‖≤_
  apply (linear_comp_iterated_point_bound P hf n z).trans
  have hp : ‖P‖^n≤1 := pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ Coord3)
  apply (mul_le_of_le_one_right (norm_nonneg _) hp).trans
  have he : iteratedFDeriv ℝ n f (P z)=iteratedFDeriv ℝ n (flatPhaseMode s h phase) (z.2+![T,0,0]) :=
    iteratedFDeriv_comp_add_right (f := flatPhaseMode s h phase) n _ _
  rw [he]
  apply (flatPhaseMode_iterated_bound s h phase n _).trans
  have hr : 0≤torusRate s h := sqrt_nonneg _
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (add_nonneg hr (torusSize_nonneg h)) _)
  apply exp_le_exp.mpr
  simpa only [Pi.add_apply,Matrix.cons_val_zero] using
    (show -torusRate s h*(z.2 0+T)≤-δ*torusRate s h by nlinarith)

def compactifiedFourierTerm (s : Fin 3→ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2→ℤ)→ℝ) (h : Fin 2→ℤ) (z : ℝ×Coord3) : ℝ :=
  a h*exp (lam*T0) *
    (expNegInvGlue (z.1/(torusRate s h-lam))*flatPhaseMode s h (phase h) (z.2+![T0,0,0]))

def compactifiedFourierTail (s : Fin 3→ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2→ℤ)→ℝ) (z : ℝ×Coord3) : ℝ :=
  ∑' h,compactifiedFourierTerm s lam T0 a phase h z

lemma compactifiedFourierTerm_smooth (s : Fin 3→ℝ) (lam T0 : ℝ)
    (a phase : (Fin 2→ℤ)→ℝ) (h : Fin 2→ℤ) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (compactifiedFourierTerm s lam T0 a phase h) := by
  unfold compactifiedFourierTerm
  exact contDiff_const.mul ((expNegInvGlue.contDiff.comp (contDiff_fst.div_const _)).mul
    ((flatPhaseMode_smooth s h (phase h)).comp (contDiff_snd.add contDiff_const)))

lemma compactifiedFourierTerm_iterated_bound {s : Fin 3→ℝ} {lam T0 gap B δ : ℝ}
    {a phase : (Fin 2→ℤ)→ℝ} (hg : 0<gap) (hB : 0≤B) (ha : ∀ h,|a h|≤B)
    (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h)
    (C : ℕ→ℝ) (hC : ∀ i,0≤C i)
    (hb : ∀ i p,p∈Icc (-gap⁻¹) gap⁻¹ → ‖iteratedFDeriv ℝ i expNegInvGlue p‖≤C i)
    (n : ℕ) (h : Fin 2→ℤ) {z : ℝ×Coord3} (hp : |z.1|≤1) (hx : δ≤T0+z.2 0) :
    ‖iteratedFDeriv ℝ n (compactifiedFourierTerm s lam T0 a phase h) z‖≤
      B*exp (lam*T0)*(∑ i∈Finset.range (n+1),(n.choose i:ℝ)*(C i*gap⁻¹^i)*
        ((torusRate s h+torusSize h)^(n-i)*exp (-δ*torusRate s h))) := by
  have hrate : 0≤torusRate s h := sqrt_nonneg _
  have hsize := torusSize_nonneg h
  by_cases hz : a h=0
  · have he : compactifiedFourierTerm s lam T0 a phase h = 0 := by
      funext w; simp [compactifiedFourierTerm,hz]
    rw [he,iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
    apply mul_nonneg (mul_nonneg hB (exp_nonneg _))
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hC i) (by positivity))) (by positivity)
  have hfun : ContDiff ℝ (↑(⊤:ℕ∞)) (fun z : ℝ×Coord3 =>
      expNegInvGlue (z.1/(torusRate s h-lam))*flatPhaseMode s h (phase h) (z.2+![T0,0,0])) :=
    (expNegInvGlue.contDiff.comp (contDiff_fst.div_const _)).mul
      ((flatPhaseMode_smooth s h (phase h)).comp (contDiff_snd.add contDiff_const))
  change ‖iteratedFDeriv ℝ n ((a h*exp (lam*T0)) •
      (fun z : ℝ×Coord3 => expNegInvGlue (z.1/(torusRate s h-lam))*
        flatPhaseMode s h (phase h) (z.2+![T0,0,0]))) z‖≤_
  rw [iteratedFDeriv_const_smul_apply (((contDiff_infty.mp hfun) n).contDiffAt),norm_smul,
    Real.norm_eq_abs,abs_mul,abs_of_pos (exp_pos _)]
  apply mul_le_mul (mul_le_mul_of_nonneg_right (ha h) (exp_nonneg _)) _ (norm_nonneg _)
    (mul_nonneg hB (exp_nonneg _))
  apply (norm_iteratedFDeriv_mul_le
    (expNegInvGlue.contDiff.comp (contDiff_fst.div_const _))
    ((flatPhaseMode_smooth s h (phase h)).comp (contDiff_snd.add contDiff_const)) z
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).trans
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul (mul_le_mul_of_nonneg_left
    (glue_scaled_iterated_bound hg (by linarith [hr h hz]) i (hC i) (hb i) hp)
    (Nat.cast_nonneg _)) (flatPhaseMode_shift_snd_bound s h (phase h) T0 δ (n-i) hx)
    (norm_nonneg _) (by positivity [hC i])

theorem compactifiedFourierTail_smooth {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {lam T0 gap B δ : ℝ} {a phase : (Fin 2→ℤ)→ℝ}
    (hg : 0<gap) (hB : 0≤B) (ha : ∀ h,|a h|≤B) (hδ : 0<δ)
    (hr : ∀ h,a h≠0 → lam+gap≤torusRate s h) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (compactifiedFourierTail s lam T0 a phase)
      (Ioo (-1) 1 ×ˢ {x : Coord3 | δ-T0<x 0}) := by
  choose C hC hb using fun n => glue_derivative_compact_bound hg n
  apply local_smooth_tsum (isOpen_Ioo.prod (axial_halfspace_open _))
    ((convex_Ioo (𝕜 := ℝ) (-1 : ℝ) 1).isPreconnected.prod (axial_halfspace_connected _))
    (compactifiedFourierTerm_smooth s lam T0 a phase)
    (fun n h => B*exp (lam*T0)*(∑ i∈Finset.range (n+1),(n.choose i:ℝ)*(C i*gap⁻¹^i)*
      ((torusRate s h+torusSize h)^(n-i)*exp (-δ*torusRate s h))))
  · intro n
    apply Summable.mul_left
    exact summable_sum (fun i _ => (flatMode_derivative_summable hs (n-i) hδ).mul_left _)
  · intro n h z hz
    apply compactifiedFourierTerm_iterated_bound hg hB ha hr C hC hb n h
    · exact (abs_lt.mpr hz.1).le
    · have hx := hz.2
      dsimp at hx
      linarith

lemma compactifiedFourierTail_of_pos {s : Fin 3→ℝ} {lam T0 : ℝ}
    {a phase : (Fin 2→ℤ)→ℝ}
    (hr : ∀ h,a h≠0 → lam<torusRate s h) {p : ℝ} (hp : 0<p) (x : Coord3) :
    compactifiedFourierTail s lam T0 a phase (p,x)=
      exp (lam*(T0+1/p))*flatFourier s a phase (x+![T0+1/p,0,0]) := by
  unfold compactifiedFourierTail flatFourier
  rw [←tsum_mul_left]
  apply tsum_congr
  intro h
  by_cases ha : a h=0
  · simp [compactifiedFourierTerm,ha]
  have hd : 0<torusRate s h-lam := sub_pos.mpr (hr h ha)
  have hglue : expNegInvGlue (p/(torusRate s h-lam))=exp (-(torusRate s h-lam)/p) := by
    simp only [expNegInvGlue,ite_eq_right (not_le.mpr (div_pos hp hd)),inv_div]
    congr 1
    ring
  have he : exp (lam*T0)*exp (-(torusRate s h-lam)/p)*exp (-torusRate s h*T0)=
      exp (lam*(T0+1/p))*exp (-torusRate s h*(T0+1/p)) := by
    rw [←exp_add,←exp_add,←exp_add]
    congr 1
    ring
  simp only [compactifiedFourierTerm,hglue,flatPhaseMode_translation]
  calc
    _= a h*(exp (lam*T0)*exp (-(torusRate s h-lam)/p)*exp (-torusRate s h*T0))*
        flatPhaseMode s h (phase h) x := by ring
    _= _ := by rw [he]; ring

lemma compactifiedFourierTail_of_nonpos {s : Fin 3→ℝ} {lam T0 : ℝ}
    {a phase : (Fin 2→ℤ)→ℝ}
    (hr : ∀ h,a h≠0 → lam<torusRate s h) {p : ℝ} (hp : p≤0) (x : Coord3) :
    compactifiedFourierTail s lam T0 a phase (p,x)=0 := by
  calc
    _ = ∑' h : Fin 2→ℤ,(0:ℝ) := by
      apply tsum_congr
      intro h
      by_cases ha : a h=0
      · simp [compactifiedFourierTerm,ha]
      have hd : 0<torusRate s h-lam := sub_pos.mpr (hr h ha)
      simp only [compactifiedFourierTerm,
        expNegInvGlue.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hp hd.le),zero_mul,mul_zero]
    _ = 0 := tsum_zero

end ScalarConductivity

end
end

end OAI
