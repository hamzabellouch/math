import OAI.Geometry.Riemannian.HarmonicCore.BoundaryBarrier

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main

lemma second_deriv_nonpos_at_localMax {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : deriv (deriv f) x ≤ 0 := by
  obtain ⟨s,hs,hfs⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hs
  let I := Icc (x-δ/2) (x+δ/2)
  have hI : I ∈ 𝓝 x := Icc_mem_nhds (by linarith) (by linarith)
  have hxI : x ∈ I := mem_of_mem_nhds hI
  have hII : I ⊆ s := by
    intro y hy
    apply hsub
    change |y-x| < δ
    rcases hy with ⟨hy₁,hy₂⟩
    rw [abs_lt]
    constructor <;> linarith
  have hfu : ContDiffOn ℝ 2 f I := hfs.mono hII
  have hu : UniqueDiffOn ℝ I := uniqueDiffOn_Icc (by linarith)
  have h0 : deriv f x = 0 := hm.deriv_eq_zero
  have ht := Real.taylor_tendsto (f:=f) (n:=2) (convex_Icc _ _) hxI hfu
  rw [nhdsWithin_eq_nhds.mpr hI] at ht
  have he (y : ℝ) : taylorWithinEval f 2 I x y =
      f x + (deriv (deriv f) x)*(y-x)^2/2 := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num : (0:WithTop ℕ∞)≤2)) hxI,
      iteratedDerivWithin_eq_iteratedDeriv hu (hf.of_le (by norm_num : (1:WithTop ℕ∞)≤2)) hxI,
      iteratedDerivWithin_eq_iteratedDeriv hu hf hxI]
    simp [iteratedDeriv_succ,h0]
    ring
  have ht' := ht.mono_left (nhdsWithin_le_nhds (s:=Ioi x))
  have hle : ∀ᶠ y in 𝓝[>] x,
      (f y-taylorWithinEval f 2 I x y)/(y-x)^2 ≤ -(deriv (deriv f) x)/2 := by
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hxy
    rw [he,div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hxy))]
    nlinarith
  have hh := le_of_tendsto ht' hle
  linarith

lemma hessian_nonpos_at_localMax {f : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) (v : E3) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ 0 := by
  let c : ℝ → E3 := fun t ↦ x + t • v
  have hc : ContDiff ℝ 2 c := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc0 : c 0 = x := by simp [c]
  have hfc : ContDiffAt ℝ 2 (f ∘ c) 0 := (hc0 ▸ hf).comp 0 hc.contDiffAt
  have hm' : IsLocalMax (f ∘ c) 0 := (hc0 ▸ hm).comp_continuous hc.continuous.continuousAt
  have hd (t : ℝ) : deriv c t = v := by
    simpa [c] using ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)).deriv
  have hdd : iteratedDeriv 2 c 0 = 0 := by simp [iteratedDeriv_succ,funext hd]
  have ht := iteratedDeriv_vcomp_two (hc0 ▸ hf) hc.contDiffAt
  have hh := second_deriv_nonpos_at_localMax hfc hm'
  rw [show deriv (deriv (f ∘ c)) 0 = iteratedDeriv 2 (f ∘ c) 0 by
    simp [iteratedDeriv_succ]] at hh
  rw [ht,hc0,hdd,hd,map_zero,add_zero,iteratedFDeriv_two_apply] at hh
  exact hh

namespace SmoothMetric3

lemma coordinate_expansion (v : E3) : (∑ i, v i • coordinateVector i) = v := by
  ext j
  simp [coordinateVector,Pi.single_apply]

lemma hessian_coordinates (f : E3 → ℝ) (x v w : E3) :
    (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j) * v i * w j) =
      fderiv ℝ (fderiv ℝ f) x v w := by
  nth_rw 2 [← coordinate_expansion v,← coordinate_expansion w]
  simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

open scoped MatrixOrder Matrix.Norms.L2Operator in
lemma laplacian_nonpos_at_localMax (g : SmoothMetric3) {f : E3 → ℝ} {x : E3}
    (hf : ContDiffAt ℝ 2 f x) (hm : IsLocalMax f x) : g.laplacian f x ≤ 0 := by
  let H : M3 := fun i j ↦ -fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j)
  have hH : H.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      change -fderiv ℝ (fderiv ℝ f) x (coordinateVector j) (coordinateVector i) =
        -fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j)
      exact congrArg Neg.neg
        ((hf.isSymmSndFDerivAt (by norm_num)).eq (coordinateVector j) (coordinateVector i))
    · intro v
      let w : E3 := WithLp.toLp 2 v
      have h := hessian_nonpos_at_localMax hf hm w
      rw [← hessian_coordinates f x w w] at h
      change (∑ i, ∑ j, fderiv ℝ (fderiv ℝ f) x (coordinateVector i) (coordinateVector j) *
        v i * v j) ≤ 0 at h
      change 0 ≤ ∑ i, v i * ∑ j, -fderiv ℝ (fderiv ℝ f) x
        (coordinateVector i) (coordinateVector j) * v j
      simpa only [Finset.mul_sum,neg_mul,mul_neg,Finset.sum_neg_distrib,
        neg_nonneg,mul_comm,mul_left_comm,mul_assoc] using h
  obtain ⟨X,hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    (g.positive x).inv.posSemidef.nonneg
  change (g.coeff x)⁻¹ = Xᴴ*X at hX
  have htr := (hH.mul_mul_conjTranspose_same X).trace_nonneg
  rw [Matrix.trace_mul_cycle,← hX] at htr
  have hid : ((g.coeff x)⁻¹ * H).trace = -g.laplacian f x := by
    unfold Matrix.trace Matrix.diag laplacian
    simp only [Matrix.mul_apply]
    simp only [coordDeriv,hm.fderiv_eq_zero,_root_.zero_apply,mul_zero,
      Finset.sum_const_zero,sub_zero,iteratedFDeriv_two_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,H,mul_neg,Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [(hf.isSymmSndFDerivAt (by norm_num)).eq]
  rw [hid] at htr
  linarith

def coordinateBarrier (L : ℝ) (x : E3) : ℝ := Real.exp (L * x 0)

lemma coordinateBarrier_smooth (L : ℝ) : ContDiff ℝ ∞ (coordinateBarrier L) := by
  have hp : ContDiff ℝ ∞ (fun x : E3 ↦ x 0) :=
    (EuclideanSpace.proj 0 : E3 →L[ℝ] ℝ).contDiff
  exact (contDiff_const.mul hp).exp

lemma fderiv_coordinateBarrier (L : ℝ) (x : E3) :
    fderiv ℝ (coordinateBarrier L) x =
      (Real.exp (L*x 0)*L) • EuclideanSpace.proj 0 := by
  have hh := (((EuclideanSpace.proj 0 : E3 →L[ℝ] ℝ).hasFDerivAt (x:=x)).const_mul L).exp
  change fderiv ℝ (fun y : E3 ↦ Real.exp (L*y 0)) x = _
  simpa only [PiLp.proj_apply,smul_smul] using hh.fderiv

lemma laplacian_coordinateBarrier (g : SmoothMetric3) (L : ℝ) (x : E3) :
    g.laplacian (coordinateBarrier L) x =
      Real.exp (L*x 0)*L * (L*(g.coeff x)⁻¹ 0 0 -
        ∑ i, ∑ j, (g.coeff x)⁻¹ i j * g.christoffel x 0 i j) := by
  have hfd : fderiv ℝ (coordinateBarrier L) =
      fun y ↦ (coordinateBarrier L y * L) • EuclideanSpace.proj 0 :=
    funext (fderiv_coordinateBarrier L)
  have hsd : fderiv ℝ (fderiv ℝ (coordinateBarrier L)) x =
      (fderiv ℝ (fun y ↦ coordinateBarrier L y * L) x).smulRight (EuclideanSpace.proj 0) := by
    rw [hfd]
    exact fderiv_smul_const ((coordinateBarrier_smooth L).differentiable (by simp) x |>.mul_const L) (EuclideanSpace.proj 0 : E3 →L[ℝ] ℝ)
  unfold laplacian coordDeriv
  simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,hsd,
    fderiv_mul_const ((coordinateBarrier_smooth L).differentiable (by simp) x) L,
    fderiv_coordinateBarrier,ContinuousLinearMap.smulRight_apply,smul_eq_mul,
    _root_.smul_apply,PiLp.proj_apply,coordinateVector]
  simp [Fin.sum_univ_three]
  ring

lemma exists_positive_barrier (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Metric.closedBall (0:E3) R,
      0 < g.laplacian (coordinateBarrier L) x := by
  have hc : IsCompact (Metric.closedBall (0:E3) R) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0:E3) R).Nonempty := ⟨0,by simpa using hR⟩
  obtain ⟨y,hy,hmin⟩ := hc.exists_isMinOn hne (g.inverse_contDiff 0 0).continuous.continuousOn
  let a := (g.coeff y)⁻¹ 0 0
  have ha : 0 < a := (g.positive y).inv.diag_pos
  let B : E3 → ℝ := fun x ↦ ∑ i, ∑ j, (g.coeff x)⁻¹ i j * g.christoffel x 0 i j
  have hB : Continuous B := by
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    exact (g.inverse_contDiff i j).continuous.mul (g.christoffel_contDiff 0 i j).continuous
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hB.continuousOn
  let L := (|C|+1)/a
  have hL : 0 < L := div_pos (by positivity) ha
  refine ⟨L,hL,fun x hx ↦ ?_⟩
  rw [g.laplacian_coordinateBarrier]
  apply mul_pos (mul_pos (Real.exp_pos _) hL)
  have hax : a ≤ (g.coeff x)⁻¹ 0 0 := hmin hx
  have hBx : B x ≤ |C| := (le_abs_self _).trans ((hC x hx).trans (le_abs_self C))
  have hLa : L*a = |C|+1 := div_mul_cancel₀ _ ha.ne'
  nlinarith

lemma strict_maximum_principle_closedBall (g : SmoothMetric3) (R M : ℝ) (hR : 0 ≤ R)
    {u : E3 → ℝ} (hu : ContinuousOn u (Metric.closedBall 0 R))
    (hs : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 u x)
    (hl : ∀ x ∈ Metric.ball (0:E3) R, 0 < g.laplacian u x)
    (hb : ∀ x ∈ Metric.sphere (0:E3) R, u x ≤ M) :
    ∀ x ∈ Metric.closedBall (0:E3) R, u x ≤ M := by
  obtain ⟨p,hp,hm⟩ := (isCompact_closedBall (0:E3) R).exists_isMaxOn
    ⟨0,by simpa using hR⟩ hu
  have hbd : p ∈ Metric.sphere (0:E3) R := by
    by_contra h
    have hlt : dist p 0 < R := lt_of_le_of_ne hp (by simpa [Metric.mem_sphere] using h)
    have hloc : IsLocalMax u p := hm.isLocalMax (mem_of_superset (Metric.isOpen_ball.mem_nhds hlt) Metric.ball_subset_closedBall)
    have hn := g.laplacian_nonpos_at_localMax (hs p hlt) hloc
    exact (not_lt_of_ge hn) (hl p hlt)
  exact fun x hx ↦ (hm hx).trans (hb p hbd)

lemma maximum_principle_closedBall (g : SmoothMetric3) (R M : ℝ) (hR : 0 ≤ R)
    {u : E3 → ℝ} (hu : ContinuousOn u (Metric.closedBall 0 R))
    (hs : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 u x)
    (hl : ∀ x ∈ Metric.ball (0:E3) R, 0 ≤ g.laplacian u x)
    (hb : ∀ x ∈ Metric.sphere (0:E3) R, u x ≤ M) :
    ∀ x ∈ Metric.closedBall (0:E3) R, u x ≤ M := by
  obtain ⟨L,hL,hlb⟩ := g.exists_positive_barrier R hR
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E3) R).exists_bound_of_continuousOn
    (coordinateBarrier_smooth L).continuous.continuousOn
  intro x hx
  have he (ε : ℝ) (hε : 0 < ε) : u x ≤ M+ε*C := by
    let v := u + ε • coordinateBarrier L
    have hv : ContinuousOn v (Metric.closedBall 0 R) :=
      hu.add ((coordinateBarrier_smooth L).continuous.continuousOn.const_smul ε)
    have hvs : ∀ y ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 v y :=
      fun y hy ↦ (hs y hy).add (((coordinateBarrier_smooth L).of_le (by norm_cast)).contDiffAt.const_smul ε)
    have hvl : ∀ y ∈ Metric.ball (0:E3) R, 0 < g.laplacian v y := by
      intro y hy
      change 0 < g.laplacian (u + ε • coordinateBarrier L) y
      have hsb : ContDiffAt ℝ 2 (ε • coordinateBarrier L) y :=
        ((coordinateBarrier_smooth L).of_le (by norm_cast)).contDiffAt.const_smul ε
      rw [laplacian_add_at g (hs y hy) hsb,laplacian_smul _ (coordinateBarrier_smooth L)]
      exact add_pos_of_nonneg_of_pos (hl y hy) (mul_pos hε (hlb y (Metric.ball_subset_closedBall hy)))
    have hvb : ∀ y ∈ Metric.sphere (0:E3) R, v y ≤ M+ε*C := by
      intro y hy
      have hyC := hC y (Metric.sphere_subset_closedBall hy)
      have hyb : coordinateBarrier L y ≤ C := (le_abs_self _).trans hyC
      exact add_le_add (hb y hy) (mul_le_mul_of_nonneg_left hyb hε.le)
    have hux : u x ≤ v x := le_add_of_nonneg_right (mul_nonneg hε.le (Real.exp_pos _).le)
    exact hux.trans (g.strict_maximum_principle_closedBall R (M+ε*C) hR hv hvs hvl hvb x hx)
  have ht : Tendsto (fun ε : ℝ ↦ M+ε*C) (𝓝[>] (0:ℝ)) (𝓝 M) := by
    have hc : Continuous (fun ε : ℝ ↦ M+ε*C) := by fun_prop
    simpa using (hc.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact he ε hε

lemma harmonic_comparison_closedBall (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R)
    {u v : E3 → ℝ}
    (hu : ContinuousOn u (Metric.closedBall 0 R))
    (hv : ContinuousOn v (Metric.closedBall 0 R))
    (hsu : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 u x)
    (hsv : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 v x)
    (hlu : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian u x = 0)
    (hlv : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian v x = 0)
    (hb : ∀ x ∈ Metric.sphere (0:E3) R, u x ≤ v x) :
    ∀ x ∈ Metric.closedBall (0:E3) R, u x ≤ v x := by
  have hdiff : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian (u + (-1:ℝ) • v) x = 0 := by
    intro x hx
    have hn : ContDiffAt ℝ 2 ((-1:ℝ) • v) x := (hsv x hx).const_smul (-1:ℝ)
    rw [g.laplacian_add_at (hsu x hx) hn,
      g.laplacian_smul_at (hsv x hx) (-1:ℝ),hlu x hx,hlv x hx]
    ring
  have hmax := g.maximum_principle_closedBall R 0 hR
    (hu.add (hv.const_smul (-1:ℝ)))
    (fun x hx ↦ (hsu x hx).add ((hsv x hx).const_smul (-1:ℝ)))
    (fun x hx ↦ (hdiff x hx).ge)
    (fun x hx ↦ by simpa using sub_nonpos.mpr (hb x hx))
  intro x hx
  have hh := hmax x hx
  simpa using hh

lemma harmonic_unique_closedBall (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R)
    {u v : E3 → ℝ}
    (hu : ContinuousOn u (Metric.closedBall 0 R))
    (hv : ContinuousOn v (Metric.closedBall 0 R))
    (hsu : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 u x)
    (hsv : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 v x)
    (hlu : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian u x = 0)
    (hlv : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian v x = 0)
    (hb : ∀ x ∈ Metric.sphere (0:E3) R, u x = v x) :
    Set.EqOn u v (Metric.closedBall (0:E3) R) := by
  have huv := g.harmonic_comparison_closedBall R hR hu hv hsu hsv hlu hlv
    (fun x hx ↦ (hb x hx).le)
  have hvu := g.harmonic_comparison_closedBall R hR hv hu hsv hsu hlv hlu
    (fun x hx ↦ (hb x hx).ge)
  exact fun x hx ↦ (huv x hx).antisymm (hvu x hx)

lemma harmonic_positive_closedBall (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R)
    {u : E3 → ℝ} (hu : ContinuousOn u (Metric.closedBall 0 R))
    (hsu : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 u x)
    (hlu : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian u x = 0)
    (hb : ∀ x ∈ Metric.sphere (0:E3) R, 0 ≤ u x) :
    ∀ x ∈ Metric.closedBall (0:E3) R, 0 ≤ u x := by
  exact g.harmonic_comparison_closedBall R hR continuousOn_const hu
    (fun _ _ ↦ contDiffAt_const) hsu (fun x _ ↦ g.laplacian_const 0 x) hlu hb

lemma harmonic_constant_closedBall (g : SmoothMetric3) (R c : ℝ) (hR : 0 ≤ R)
    {u : E3 → ℝ} (hu : ContinuousOn u (Metric.closedBall 0 R))
    (hsu : ∀ x ∈ Metric.ball (0:E3) R, ContDiffAt ℝ 2 u x)
    (hlu : ∀ x ∈ Metric.ball (0:E3) R, g.laplacian u x = 0)
    (hb : ∀ x ∈ Metric.sphere (0:E3) R, u x = c) :
    ∀ x ∈ Metric.closedBall (0:E3) R, u x = c := by
  exact g.harmonic_unique_closedBall R hR hu continuousOn_const hsu
    (fun _ _ ↦ contDiffAt_const) hlu (fun x _ ↦ g.laplacian_const c x) hb

end SmoothMetric3

end HarmonicCounterexample.Main

end

end OAI
