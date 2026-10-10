import Mathlib
import OAI.Analysis.Conductivity.Fourier.AnalyticNullEuclidean

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Laplacian InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι]

lemma laplacian_trace_fderiv (b : OrthonormalBasis ι ℝ E) (f : E → ℝ) (x : E) :
    Δ f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (b i) (b i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  apply Finset.sum_congr rfl
  intro i hi
  exact (bilinearIteratedFDerivTwo_eq_iteratedFDeriv (𝕜 := ℝ) _ x (b i) (b i)).symm

omit [FiniteDimensional ℝ E] in
lemma clm_sum_sq_positive (b : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℝ)
    {w : E} (hw : L w ≠ 0) : 0 < ∑ i, (L (b i))^2 := by
  have hnon : 0 ≤ ∑ i, (L (b i))^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  apply lt_of_le_of_ne hnon
  intro hz
  have he : ∀ i, L (b i)=0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg (L (b i)))).mp hz.symm i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp this
  apply hw
  rw [←b.sum_repr w,map_sum]
  simp [he]

theorem harmonic_gradient_multiplier_fderiv_zero (b : OrthonormalBasis ι ℝ E)
    {u v lam : E → ℝ} {x w : E}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hlam : DifferentiableAt ℝ lam x)
    (he : (fun y => fderiv ℝ v y) =ᶠ[𝓝 x] (fun y => lam y • fderiv ℝ u y))
    (hlu : Δ u x=0) (hlv : Δ v x=0) (hw : fderiv ℝ u x w ≠ 0) :
    fderiv ℝ lam x=0 := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  have hdv : DifferentiableAt ℝ (fderiv ℝ v) x :=
    (hv.fderiv_right (by norm_num)).differentiableAt one_ne_zero
  have hh (p q : E) :
      fderiv ℝ (fderiv ℝ v) x p q =
        fderiv ℝ lam x p * fderiv ℝ u x q +
        lam x * fderiv ℝ (fderiv ℝ u) x p q := by
    have hd := (hlam.hasFDerivAt.smul hdu.hasFDerivAt).congr_of_eventuallyEq he
    have hp := congrArg (fun T : E →L[ℝ] E →L[ℝ] ℝ => T p q) hd.fderiv
    simpa only [add_apply,ContinuousLinearMap.smulRight_apply,
      smul_apply,smul_eq_mul,add_comm] using hp
  have hs (p q : E) :
      fderiv ℝ lam x p * fderiv ℝ u x q = fderiv ℝ lam x q * fderiv ℝ u x p := by
    have huv := hv.isSymmSndFDerivAt (by norm_num) p q
    have huu := hu.isSymmSndFDerivAt (by norm_num) p q
    change fderiv ℝ (fderiv ℝ v) x p q = fderiv ℝ (fderiv ℝ v) x q p at huv
    change fderiv ℝ (fderiv ℝ u) x p q = fderiv ℝ (fderiv ℝ u) x q p at huu
    rw [hh,hh,huu] at huv
    linarith
  let k := fderiv ℝ lam x w / fderiv ℝ u x w
  have hk (p : E) : fderiv ℝ lam x p = k*fderiv ℝ u x p := by
    dsimp [k]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hw).2
    simpa only [div_mul_eq_mul_div] using hs p w
  have htrace : Δ v x = k*(∑ i, (fderiv ℝ u x (b i))^2)+lam x*Δ u x := by
    simp_rw [laplacian_trace_fderiv b,hh,hk]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hk0 : k=0 := by
    rw [hlu,hlv,mul_zero,add_zero] at htrace
    exact (mul_eq_zero.mp htrace.symm).resolve_right
      (ne_of_gt (clm_sum_sq_positive b (fderiv ℝ u x) hw))
  ext p
  simp [hk,hk0]

theorem harmonic_rank_one_affine (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} {U : Set E} {w : E}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : ContDiffOn ℝ 2 u U) (hv : ContDiffOn ℝ 2 v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0)
    (hw : ∀ x∈U, fderiv ℝ u x w ≠ 0)
    (hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q =
      fderiv ℝ u x q*fderiv ℝ v x p) :
    ∃ α β : ℝ, ∀ x∈U, v x=α*u x+β := by
  let lam : E → ℝ := fun x => fderiv ℝ v x w / fderiv ℝ u x w
  have hua (x : E) (hx : x∈U) : ContDiffAt ℝ 2 u x :=
    (hu x hx).contDiffAt (hU.mem_nhds hx)
  have hva (x : E) (hx : x∈U) : ContDiffAt ℝ 2 v x :=
    (hv x hx).contDiffAt (hU.mem_nhds hx)
  have hdlam (x : E) (hx : x∈U) : DifferentiableAt ℝ lam x := by
    have hn : DifferentiableAt ℝ (fun y => fderiv ℝ v y w) x :=
      ((hva x hx).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero).clm_apply (differentiableAt_const w)
    have hd : DifferentiableAt ℝ (fun y => fderiv ℝ u y w) x :=
      ((hua x hx).fderiv_right (by norm_num) |>.differentiableAt one_ne_zero).clm_apply (differentiableAt_const w)
    simpa only [lam,div_eq_mul_inv,Pi.mul_def,Function.comp_def] using
      hn.mul ((hasDerivAt_inv (hw x hx)).differentiableAt.comp x hd)
  have hprop (x : E) (hx : x∈U) : fderiv ℝ v x=lam x • fderiv ℝ u x := by
    ext p
    simp only [smul_apply,smul_eq_mul,lam,div_mul_eq_mul_div]
    apply (eq_div_iff (hw x hx)).2
    nlinarith [hr x hx p w]
  have hzero : EqOn (fderiv ℝ lam) 0 U := by
    intro x hx
    apply harmonic_gradient_multiplier_fderiv_zero b (hua x hx) (hva x hx) (hdlam x hx)
      _ (hlu x hx) (hlv x hx) (hw x hx)
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hprop y hy
  obtain ⟨α,hα⟩ := hU.exists_is_const_of_fderiv_eq_zero hc
    (fun x hx => (hdlam x hx).differentiableWithinAt) hzero
  obtain ⟨β,hβ⟩ := hU.exists_eq_add_of_fderiv_eq hc
    (hv.differentiableOn (by norm_num))
    ((hu.differentiableOn (by norm_num)).const_mul α) (by
      intro x hx
      rw [hprop x hx,hα x hx]
      simpa using (((hua x hx).differentiableAt (by norm_num)).hasFDerivAt.const_mul α).fderiv.symm)
  exact ⟨α,β,hβ⟩

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Laplacian InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

def HarmonicPairRegularOn (u v : E → ℝ) (O : Set E) : Prop :=
  (∃ p q : E, ∀ x∈O, fderiv ℝ u x p*fderiv ℝ v x q-
    fderiv ℝ u x q*fderiv ℝ v x p ≠ 0) ∨
  (∃ w : E, ∃ α β : ℝ, ∀ x∈O, fderiv ℝ u x w ≠ 0 ∧ v x=α*u x+β) ∨
  (∃ w : E, ∃ α β : ℝ, ∀ x∈O, fderiv ℝ v x w ≠ 0 ∧ u x=α*v x+β) ∨
  (∃ α β : ℝ, ∀ x∈O, u x=α ∧ v x=β)

omit [MeasurableSpace E] [BorelSpace E] in
lemma noncritical_harmonic_rank_patch (b : OrthonormalBasis ι ℝ E)
    {u v : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hu : AnalyticOnNhd ℝ u U) (hv : AnalyticOnNhd ℝ v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0)
    (hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q=
      fderiv ℝ u x q*fderiv ℝ v x p)
    {x w : E} (hx : x∈U) (hw : fderiv ℝ u x w ≠ 0) :
    ∃ r>0, Metric.ball x r⊆U ∧ ∃ α β : ℝ,
      ∀ y∈Metric.ball x r, fderiv ℝ u y w ≠ 0 ∧ v y=α*u y+β := by
  have hn := ((analytic_directional_fderiv hu w) x hx).continuousAt.eventually_ne hw
  obtain ⟨r,hr0,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hx) hn)
  have hbU : Metric.ball x r⊆U := fun y hy => (hball hy).1
  have hbn : ∀ y∈Metric.ball x r, fderiv ℝ u y w ≠ 0 := fun y hy => (hball hy).2
  obtain ⟨α,β,he⟩ := harmonic_rank_one_affine b Metric.isOpen_ball
    (convex_ball x r).isPreconnected (hu.contDiffOn_of_completeSpace.mono hbU) (hv.contDiffOn_of_completeSpace.mono hbU)
    (fun y hy => hlu y (hbU hy)) (fun y hy => hlv y (hbU hy)) hbn
    (fun y hy => hr y (hbU hy))
  exact ⟨r,hr0,hbU,α,β,fun y hy => ⟨hbn y hy,he y hy⟩⟩

omit [BorelSpace E] in
theorem analytic_harmonic_ae_regular (b : OrthonormalBasis ι ℝ E)
    (μ : Measure E) (hnull : AnalyticNullProperty E μ)
    {u v : E → ℝ} {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : AnalyticOnNhd ℝ u U) (hv : AnalyticOnNhd ℝ v U)
    (hlu : ∀ x∈U, Δ u x=0) (hlv : ∀ x∈U, Δ v x=0) :
    ∀ᵐ x∂μ, x∈U → ∃ r>0, Metric.ball x r⊆U ∧
      HarmonicPairRegularOn u v (Metric.ball x r) := by
  classical
  by_cases hminor : ∃ x∈U, ∃ p q : E,
    fderiv ℝ u x p*fderiv ℝ v x q-fderiv ℝ u x q*fderiv ℝ v x p ≠ 0
  · obtain ⟨a,ha,p,q,hne⟩ := hminor
    let M : E → ℝ := fun x => fderiv ℝ u x p*fderiv ℝ v x q-
      fderiv ℝ u x q*fderiv ℝ v x p
    have hM : AnalyticOnNhd ℝ M U := analytic_gradient_minor hu hv p q
    have hz := hnull U M hU hc hM ⟨a,ha,hne⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hMx : M x ≠ 0 := by simpa [hxu] using hx
    have hn := (hM x hxu).continuousAt.eventually_ne hMx
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hU.mem_nhds hxu) hn)
    exact ⟨r,hr,fun y hy => (hb hy).1,Or.inl ⟨p,q,fun y hy => (hb hy).2⟩⟩
  have hr : ∀ x∈U, ∀ p q, fderiv ℝ u x p*fderiv ℝ v x q=
      fderiv ℝ u x q*fderiv ℝ v x p := by
    intro x hx p q
    by_contra hn
    exact hminor ⟨x,hx,p,q,sub_ne_zero.mpr hn⟩
  by_cases hdu : ∃ x∈U, ∃ w, fderiv ℝ u x w ≠ 0
  · obtain ⟨a,ha,w,hw⟩ := hdu
    have hz := hnull U (fun x => fderiv ℝ u x w) hU hc
      (analytic_directional_fderiv hu w) ⟨a,ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ u x w ≠ 0 := by simpa [hxu] using hx
    obtain ⟨r,hr0,hb,α,β,he⟩ := noncritical_harmonic_rank_patch b hU hu hv hlu hlv hr hxu hn
    exact ⟨r,hr0,hb,Or.inr (Or.inl ⟨w,α,β,he⟩)⟩
  by_cases hdv : ∃ x∈U, ∃ w, fderiv ℝ v x w ≠ 0
  · obtain ⟨a,ha,w,hw⟩ := hdv
    have hz := hnull U (fun x => fderiv ℝ v x w) hU hc
      (analytic_directional_fderiv hv w) ⟨a,ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ v x w ≠ 0 := by simpa [hxu] using hx
    have hr' : ∀ x∈U, ∀ p q, fderiv ℝ v x p*fderiv ℝ u x q=
        fderiv ℝ v x q*fderiv ℝ u x p := by
      intro x hx p q
      nlinarith [hr x hx p q]
    obtain ⟨r,hr0,hb,α,β,he⟩ := noncritical_harmonic_rank_patch b hU hv hu hlv hlu hr' hxu hn
    exact ⟨r,hr0,hb,Or.inr (Or.inr (Or.inl ⟨w,α,β,he⟩))⟩
  have hdu0 : EqOn (fderiv ℝ u) 0 U := by
    intro x hx
    ext w
    by_contra hn
    exact hdu ⟨x,hx,w,hn⟩
  have hdv0 : EqOn (fderiv ℝ v) 0 U := by
    intro x hx
    ext w
    by_contra hn
    exact hdv ⟨x,hx,w,hn⟩
  obtain ⟨α,hα⟩ := hU.exists_is_const_of_fderiv_eq_zero hc hu.differentiableOn hdu0
  obtain ⟨β,hβ⟩ := hU.exists_is_const_of_fderiv_eq_zero hc hv.differentiableOn hdv0
  exact ae_of_all μ (fun x hx => by
    obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    exact ⟨r,hr,hb,Or.inr (Or.inr (Or.inr ⟨α,β,fun y hy => ⟨hα y (hb hy),hβ y (hb hy)⟩⟩))⟩)

end ScalarConductivity

end

end OAI
