import OAI.Analysis.NumericalRange.Main

namespace OAI

/-! Intrinsic domains, optimal similarities and matrix-valued boundary representations. -/

noncomputable section
namespace CompleteCrouzeix
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

lemma convex_exteriorCoordinate_support {U : Set ℂ}
    (hU : IsOpen U) (hcv : Convex ℝ U) (hne : U.Nonempty)
    (E : ExteriorCoordinate U) :
    ∀ t ∈ sphere (0 : ℂ) 1, ∀ z ∈ closure U,
      0 ≤ (conj (t * deriv (exteriorMap E.leading E.constant E.regular) t) *
        (exteriorMap E.leading E.constant E.regular t - z)).re := by
  let G := exteriorMap E.leading E.constant E.regular
  have hreg : interior (closure U) = U :=
    (hcv.interior_closure_eq_interior_of_nonempty_interior
      (by rwa [hU.interior_eq])).trans hU.interior_eq
  have hbound (w : ℂ) (hw : ‖w‖ = 1) : G w ∈ frontier U :=
    E.boundary_image ▸ mem_image_of_mem G (mem_sphere_zero_iff_norm.mpr hw)
  intro t ht z hz
  have htn : ‖t‖ = 1 := mem_sphere_zero_iff_norm.mp ht
  have htX : E.radius⁻¹ < ‖t‖ := by
    rw [htn]
    exact inv_lt_one_of_one_lt₀ E.radius_gt
  have hGt : DifferentiableAt ℂ G t :=
    (exteriorCoordinate_analytic E t htX).differentiableAt
  have hpnot : G t ∉ interior (closure U) := by
    rw [hreg]
    exact (hU.frontier_eq ▸ hbound t htn).2
  obtain ⟨L, hLne, hL⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hcv.closure hpnot (by rwa [hreg])
  let N := t * deriv G t
  have hN : N ≠ 0 := mul_ne_zero
    (by intro he; simp [he] at htn) (E.noncritical t htX)
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => exp ((s:ℂ)*I)*t)
      (exp ((s:ℂ)*I)*I*t) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp.mul_const I).cexp.mul_const t)
  have he : HasDerivAt (fun s : ℝ => G (exp ((s:ℂ)*I)*t)) (I*N) 0 := by
    simpa only [N,ofReal_zero,zero_mul,Complex.exp_zero,one_mul,
      Function.comp_def,smul_eq_mul,mul_assoc] using
      (show HasDerivAt G (deriv G t) (exp (((0:ℝ):ℂ)*I)*t)
        from by simpa using hGt.hasDerivAt).scomp 0 (hd 0)
  have heL : HasDerivAt (fun s : ℝ => L (G (exp ((s:ℂ)*I)*t))) (L (I*N)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 he
  have hmL : IsLocalMax (fun s : ℝ => L (G (exp ((s:ℂ)*I)*t))) 0 := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [ofReal_zero,zero_mul,Complex.exp_zero,one_mul] using
      hL _ (hbound _ (by rw [norm_mul,norm_exp_ofReal_mul_I,htn,one_mul])).1
  have htan : L (I*N) = 0 := hmL.hasDerivAt_eq_zero heL
  have hdr : HasDerivAt (fun r : ℝ => (r:ℂ)*t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).ofReal_comp.mul_const t
  have hger : HasDerivAt (fun r : ℝ => G ((r:ℂ)*t)) N 1 := by
    simpa only [N,ofReal_one,one_mul,Function.comp_def,smul_eq_mul] using
      (show HasDerivAt G (deriv G t) (((1:ℝ):ℂ)*t)
        from by simpa using hGt.hasDerivAt).scomp 1 hdr
  have hgrL : HasDerivAt (fun r : ℝ => L (G ((r:ℂ)*t))) (L N) 1 :=
    L.hasFDerivAt.comp_hasDerivAt 1 hger
  have hrc : ContinuousAt (fun r : ℝ => ‖(r:ℂ)*t‖) 1 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in 𝓝 1, E.radius⁻¹ < ‖(r:ℂ)*t‖ :=
    hrc.eventually (lt_mem_nhds (by simpa using htX))
  have hm : IsLocalMaxOn (fun r : ℝ => L (G ((r:ℂ)*t))) (Iic 1) 1 := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      (lt_mem_nhds (zero_lt_one : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with r hrx hr0 hr1
    change r ≤ 1 at hr1
    by_cases hre : r = 1
    · subst r; exact le_rfl
    · have hrlt : r < 1 := lt_of_le_of_ne hr1 hre
      have hball : (r:ℂ)*t ∈ ball (0:ℂ) 1 := by
        simp only [mem_ball_zero_iff,norm_mul,Complex.norm_real,
          Real.norm_eq_abs,abs_of_pos hr0,htn,mul_one]
        exact hrlt
      simpa only [ofReal_one,one_mul] using
        hL _ (subset_closure ((E.interior_iff _ hrx).mpr hball))
  have hy : (-1:ℝ) ∈ posTangentConeAt (Iic (1:ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic (1:ℝ)).segment_subset <;> simp
  have hnonpos := hm.hasFDerivWithinAt_nonpos hgrL.hasFDerivAt.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul] at hnonpos
  have hLN : 0 < L N := by
    have hn : L N ≠ 0 := by
      intro hzero
      apply hLne
      ext w
      change L w = 0
      rw [real_linear_normal hN htan w,hzero,zero_div,zero_mul]
    exact lt_of_le_of_ne (by linarith) (Ne.symm hn)
  have hle : L (z-G t) ≤ 0 := by
    rw [map_sub]
    exact sub_nonpos.mpr (hL z hz)
  rw [real_linear_normal hN htan (z-G t)] at hle
  have hratio : 0 < L N / ‖N‖^2 :=
    div_pos hLN (sq_pos_of_pos (norm_pos_iff.mpr hN))
  have hle' : (conj N*(z-G t)).re ≤ 0 := by nlinarith
  change 0 ≤ (conj N*(G t-z)).re
  have heq : (conj N*(G t-z)).re = -(conj N*(z-G t)).re := by
    rw [show G t-z = -(z-G t) by ring,mul_neg,neg_re]
  rw [heq]
  linarith
end CompleteCrouzeix
end

end OAI
