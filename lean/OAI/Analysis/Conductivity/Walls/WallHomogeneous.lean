import Mathlib
import OAI.Analysis.Conductivity.Sobolev.WallParticular

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [ProperSpace E] in
lemma wallAlong_mul (d : E) {f g : E × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (p : E × ℝ) :
    wallAlong d (fun q => f q*g q) p=wallAlong d f p*g p+f p*wallAlong d g p := by
  simp only [wallAlong,fderiv_fun_mul (hf p) (hg p),add_apply,
    smul_apply,smul_eq_mul]
  ring

omit [ProperSpace E] in
lemma wallDerivative_const (c : ℝ) (p : E × ℝ) : wallDerivative (fun _ => c) p=0 := by
  simp [wallDerivative]

omit [ProperSpace E] in
lemma wallDerivative_pullback {a : E → ℝ} (ha : Differentiable ℝ a) (p : E × ℝ) :
    wallDerivative (fun q => a q.1) p=0 := by
  change (fderiv ℝ (a ∘ Prod.fst) p) (0,1)=0
  rw [fderiv_comp p (ha p.1) differentiableAt_fst,fderiv_fst]
  change (fderiv ℝ a p.1) 0=0
  exact map_zero _

omit [ProperSpace E] in
lemma wall_mixed_commute (d : E) {v : E × ℝ → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (p : E × ℝ) :
    wallDerivative (wallAlong d v) p=wallAlong d (wallDerivative v) p := by
  have hv2 : ContDiff ℝ 2 v := hv.of_le (show ((2 : ℕ∞) : WithTop ℕ∞)≤↑(⊤ : ℕ∞) from WithTop.coe_le_coe.mpr le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ v) p :=
    (hv2.fderiv_right (show (1 : WithTop ℕ∞)+1≤2 by norm_num)).contDiffAt.differentiableAt (by norm_num)
  unfold wallDerivative wallAlong
  rw [fderiv_clm_apply hd (differentiableAt_const _),fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hv2.contDiffAt.isSymmSndFDerivAt (by simp) (0,1) (d,0)

def wallHomogeneousNumerator (d : E) (v : E × ℝ → ℝ) (a : E → ℝ) (p : E × ℝ) : ℝ :=
  -2*a p.1*(wallAlong d v p-wallAlong d v (p.1,0))-
    wallAlong d (fun q => a q.1) p*(v p-v (p.1,0))

lemma wallHomogeneousNumerator_smooth (d : E) {v : E × ℝ → ℝ} {a : E → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (wallHomogeneousNumerator d v a) := by
  exact ((contDiff_const.mul (ha.comp contDiff_fst)).mul
    ((wallAlong_smooth d hv).sub ((wallAlong_smooth d hv).comp (contDiff_fst.prodMk contDiff_const)))).sub
    ((wallAlong_smooth d (ha.comp contDiff_fst)).mul
      (hv.sub (hv.comp (contDiff_fst.prodMk contDiff_const))))

omit [ProperSpace E] in
lemma wallHomogeneousNumerator_zero (d : E) (v : E × ℝ → ℝ) (a : E → ℝ) (x : E) :
    wallHomogeneousNumerator d v a (x,0)=0 := by
  simp only [wallHomogeneousNumerator,sub_self,mul_zero]

omit [ProperSpace E] in
lemma wallDerivative_pullback_along (d : E) {a : E → ℝ}
    (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) (p : E × ℝ) :
    wallDerivative (wallAlong d (fun q => a q.1)) p=0 := by
  have he : wallDerivative (fun q : E × ℝ => a q.1)=fun _ => 0 :=
    funext (wallDerivative_pullback (ha.differentiable (by simp)))
  rw [wall_mixed_commute d (v := fun q => a q.1) (ha.comp contDiff_fst),he]
  simp [wallAlong]

theorem wall_homogeneous_flux_equations (d : E) {v : E × ℝ → ℝ} {a : E → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a) (p : E × ℝ) :
    wallDerivative (fun q : E × ℝ => a q.1) p=0 ∧
    wallAlong d (fun q => a q.1*wallDerivative v q) p+
      wallDerivative (fun q => a q.1*wallAlong d v q+
        wallHomogeneousNumerator d v a q) p=0 := by
  have hvd := hv.differentiable (by simp)
  have had := ha.differentiable (by simp)
  have hAc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun q : E × ℝ => a q.1) := ha.comp contDiff_fst
  have hA := hAc.differentiable (by simp)
  have hs := (wallAlong_smooth d hv).differentiable (by simp)
  have hz := (wallDerivative_smooth hv).differentiable (by simp)
  have has := (wallAlong_smooth d hAc).differentiable (by simp)
  have hv₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => v (x,0)) :=
    hv.comp (contDiff_id.prodMk contDiff_const)
  have hvs₀ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : E => wallAlong d v (x,0)) :=
    (wallAlong_smooth d hv).comp (contDiff_id.prodMk contDiff_const)
  refine ⟨wallDerivative_pullback had p,?_⟩
  rw [wallAlong_mul d hA hz,
    wallDerivative_add (f := fun q => a q.1*wallAlong d v q) (hA.mul hs) ((wallHomogeneousNumerator_smooth d hv ha).differentiable (by simp)),
    wallDerivative_mul hA hs,wallDerivative_pullback had]
  have hneg : Differentiable ℝ (fun q : E × ℝ => -2*a q.1) := (differentiable_const (-2)).mul hA
  have hsub : Differentiable ℝ (fun q : E × ℝ => wallAlong d v q-wallAlong d v (q.1,0)) :=
    hs.sub ((hvs₀.comp contDiff_fst).differentiable (by simp))
  have hsubv : Differentiable ℝ (fun q : E × ℝ => v q-v (q.1,0)) :=
    hvd.sub ((hv₀.comp contDiff_fst).differentiable (by simp))
  change _+(_+_+wallDerivative (fun q => -2*a q.1*(wallAlong d v q-wallAlong d v (q.1,0))-
    wallAlong d (fun q => a q.1) q*(v q-v (q.1,0))) p)=0
  rw [wallDerivative_sub (f := fun q => -2*a q.1*(wallAlong d v q-wallAlong d v (q.1,0)))
      (g := fun q => wallAlong d (fun q => a q.1) q*(v q-v (q.1,0)))
      (hneg.mul hsub) (has.mul hsubv),
    wallDerivative_mul hneg hsub,wallDerivative_mul has hsubv,
    wallDerivative_pullback (a := fun x => -2*a x) (((differentiable_const (-2)).mul had)),
    wallDerivative_sub (f := wallAlong d v) (g := fun q => wallAlong d v (q.1,0)) hs ((hvs₀.comp contDiff_fst).differentiable (by simp)),
    wallDerivative_sub (f := v) (g := fun q => v (q.1,0)) hvd ((hv₀.comp contDiff_fst).differentiable (by simp)),
    wallDerivative_pullback (hvs₀.differentiable (by simp)),
    wallDerivative_pullback (hv₀.differentiable (by simp)),
    wallDerivative_pullback_along d ha,wall_mixed_commute d hv]
  ring

theorem wall_homogeneous_extension (d : E) {v : E × ℝ → ℝ} {a : E → ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (ha : ContDiff ℝ (↑(⊤ : ℕ∞)) a)
    (hz : ∀ x, wallDerivative v (x,0)=0) (x : E)
    (hzz : wallDerivative (wallDerivative v) (x,0)≠0) :
    let H := fun p => wallQuotient (wallHomogeneousNumerator d v a) p/
      wallQuotient (wallDerivative v) p
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) H (x,0) ∧
      (∀ᶠ p in 𝓝 (x,0), H p*wallDerivative v p=wallHomogeneousNumerator d v a p) := by
  let G := wallHomogeneousNumerator d v a
  have hG := wallHomogeneousNumerator_smooth d hv ha
  have hvz := wallDerivative_smooth hv
  have hG0 := wallHomogeneousNumerator_zero d v a
  have hq : wallQuotient (wallDerivative v) (x,0)≠0 := by
    simpa only [wallQuotient_zero] using hzz
  refine ⟨(wall_ratio_extension hG hvz hG0 hz x hzz).1,?_⟩
  filter_upwards [(wallQuotient_smooth hvz).continuous.continuousAt.eventually_ne hq] with p hp
  exact wall_ratio_multiply hG hvz hG0 hz p hp

end

open Set MeasureTheory Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

lemma unit_interval_integral_abs_bound {f : ℝ → ℝ} {M : ℝ}
    (hf : ∀ t∈Icc (0:ℝ) 1, |f t|≤M) : |∫ t in Icc (0:ℝ) 1,f t|≤M := by
  have hh := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc (0:ℝ) 1)) (f := f) (C := M)
    (ae_restrict_of_forall_mem measurableSet_Icc (fun t ht => by simpa only [Real.norm_eq_abs] using hf t ht))
  simpa [Measure.real] using hh

omit [ProperSpace E] in
lemma wallQuotient_abs_bound {f : E × ℝ → ℝ} {p : E × ℝ} {M : ℝ}
    (hf : ∀ t∈Icc (0:ℝ) 1, |wallDerivative f (p.1,t*p.2)|≤M) :
    |wallQuotient f p|≤M := unit_interval_integral_abs_bound hf

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] in
lemma wallPrimitive_abs_bound {f : E × ℝ → ℝ} {p : E × ℝ} {M : ℝ}
    (hf : ∀ t∈Icc (0:ℝ) 1, |f (p.1,t*p.2)|≤M) :
    |wallPrimitive f p|≤|p.2| * M := by
  rw [wallPrimitive,abs_mul]
  exact mul_le_mul_of_nonneg_left (unit_interval_integral_abs_bound hf) (abs_nonneg _)

omit [ProperSpace E] in
lemma wallQuotient_lower_bound {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {p : E × ℝ} {c : ℝ}
    (h : ∀ t∈Icc (0:ℝ) 1,c≤wallDerivative f (p.1,t*p.2)) :
    c≤wallQuotient f p := by
  have hi : IntegrableOn (fun t : ℝ => wallDerivative f (p.1,t*p.2)) (Icc (0:ℝ) 1) :=
    ((wallDerivative_smooth hf).continuous.comp
      (continuous_const.prodMk (continuous_id.mul continuous_const))).continuousOn.integrableOn_compact isCompact_Icc
  have hh := integral_mono_ae (integrable_const (μ := volume.restrict (Icc (0:ℝ) 1)) c) hi
    (ae_restrict_of_forall_mem measurableSet_Icc h)
  simpa [wallQuotient] using hh

omit [ProperSpace E] in
theorem wall_ratio_abs_bound {f g : E × ℝ → ℝ}
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) {p : E × ℝ} {ε c : ℝ} (hc : 0<c)
    (hf : ∀ t∈Icc (0:ℝ) 1,|wallDerivative f (p.1,t*p.2)|≤ε)
    (hgrad : ∀ t∈Icc (0:ℝ) 1,c≤wallDerivative g (p.1,t*p.2)) :
    |wallQuotient f p/wallQuotient g p|≤ε/c := by
  have hq := wallQuotient_lower_bound hg hgrad
  rw [abs_div,abs_of_pos (hc.trans_le hq)]
  exact div_le_div₀ ((abs_nonneg _).trans (wallQuotient_abs_bound hf)) (wallQuotient_abs_bound hf) hc hq

omit [ProperSpace E] in
lemma wallAlong_zero_trace (d : E) {f : E × ℝ → ℝ}
    (hf : Differentiable ℝ f) (hz : ∀ x,f (x,0)=0) (x : E) :
    wallAlong d f (x,0)=0 := by
  have hin : HasFDerivAt (fun q : E => (q,(0:ℝ)))
      (ContinuousLinearMap.inl ℝ E ℝ) x := (ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt
  have hc := (hf (x,0)).hasFDerivAt.comp x hin
  have hc0 : HasFDerivAt (fun _ : E => (0:ℝ))
      ((fderiv ℝ f (x,0)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
    simpa only [Function.comp_def,hz] using hc
  have hi := hc0.unique (hasFDerivAt_const (0:ℝ) x)
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L d) hi
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,
    zero_apply,wallAlong] using hv

lemma wallAlong_primitive (d : E) {f : E × ℝ → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (p : E × ℝ) :
    wallAlong d (wallPrimitive f) p=wallPrimitive (wallAlong d f) p := by
  have hA := wallPrimitive_smooth hf
  have hd : wallDerivative (wallAlong d (wallPrimitive f))=wallAlong d f := by
    funext q
    rw [wall_mixed_commute d hA]
    congr 1
    exact funext (wallDerivative_primitive hf)
  have hh := wallQuotient_identity (wallAlong_smooth d hA) p.1 p.2
  rw [wallAlong_zero_trace d (hA.differentiable (by simp)) (wallPrimitive_zero f),sub_zero] at hh
  simpa only [wallQuotient,wallPrimitive,hd] using hh

end ScalarConductivity

end

end OAI
