import OAI.Analysis.NumericalRange.ConvexExterior

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_26 u_27

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

section
lemma invertedExterior_local_chart {K : Set ℂ} {a p : ℂ}
    (hK : IsCompact K) {χ : ℂ → ℂ} (hχ0 : χ 0 = p)
    (hχa : AnalyticAt ℂ χ 0) (hχd : deriv χ 0 ≠ 0) (hpa : p ≠ a)
    (hχs : ∀ᶠ z : ℂ in 𝓝 0, χ z ∈ K ↔ 0 ≤ z.im) :
    ∃ ψ : ℂ → ℂ, ψ 0 = (p-a)⁻¹ ∧ AnalyticAt ℂ ψ 0 ∧ deriv ψ 0 ≠ 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, ψ z ∈ invertedExterior K a ↔ 0 < z.im) ∧
      (∀ᶠ z : ℂ in 𝓝 0, z.im = 0 → ψ z ∈ frontier (invertedExterior K a)) := by
  let ψ : ℂ → ℂ := fun z => (χ (-z)-a)⁻¹
  have hne : χ (-(0 : ℂ))-a ≠ 0 := by simpa [hχ0] using sub_ne_zero.mpr hpa
  have hχan : AnalyticAt ℂ χ (-(0 : ℂ)) := by simpa using hχa
  have han : AnalyticAt ℂ (fun z : ℂ => -z) 0 := analyticAt_id.neg
  have ha : AnalyticAt ℂ ψ 0 := ((hχan.comp han).sub analyticAt_const).inv hne
  have hdχ := hχa.differentiableAt.hasDerivAt
  have hd := ((hdχ.comp_of_eq 0 (hasDerivAt_id (0 : ℂ)).neg (by simp)).sub_const a).inv hne
  have hψd : deriv ψ 0 ≠ 0 := by
    have hed : deriv ψ 0 = -(deriv χ 0 * -1) / (χ (-0)-a)^2 := hd.deriv
    rw [hed]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero hχd (neg_ne_zero.mpr one_ne_zero)))
      (pow_ne_zero 2 hne)
  have hcn : ContinuousAt (fun z : ℂ => -z) 0 := continuousAt_id.neg
  have hsn : ∀ᶠ z : ℂ in 𝓝 0, χ (-z) ∈ K ↔ 0 ≤ (-z).im :=
    hcn.tendsto.eventually (by simpa using hχs)
  have hen : ∀ᶠ z : ℂ in 𝓝 0, χ (-z)-a ≠ 0 :=
    ((hχan.continuousAt.comp hcn).sub continuousAt_const).eventually_ne hne
  have hs : ∀ᶠ z : ℂ in 𝓝 0, ψ z ∈ invertedExterior K a ↔ 0 < z.im := by
    filter_upwards [hsn,hen] with z hz hn
    have he : a+(ψ z)⁻¹ = χ (-z) := by dsimp [ψ]; rw [inv_inv]; ring
    change ψ z = 0 ∨ a+(ψ z)⁻¹ ∉ K ↔ 0 < z.im
    rw [he,or_iff_right (inv_ne_zero hn),hz]
    simp
  refine ⟨ψ,by simp [ψ,hχ0],ha,hψd,hs,?_⟩
  exact local_side_frontier (invertedExterior_open hK)
    (ha.eventually_analyticAt.mono (fun z hz => hz.continuousAt)) hs

open Set Filter Metric Complex
open scoped Topology

lemma barrier_interior_disk_coordinate {ι : Type u_26} [Fintype ι] {c : ℝ} (hc : 0 < c)
    (l : ι → ℂ →L[ℝ] ℝ) (b : ι → ℝ) {a : ℂ} (ha : convexBarrier c l b a < 1) :
    Nonempty (DiskCoordinate {z | convexBarrier c l b z < 1} a) := by
  let U := {z | convexBarrier c l b z < 1}
  have hU : IsOpen U := convexBarrier_sublevel_open c l b
  have hcv : Convex ℝ U := convexBarrier_sublevel_convex hc.le l b
  have := hcv.contractibleSpace ⟨a,ha⟩
  apply analytic_domain_disk_coordinate hU (by change SimplyConnectedSpace U; infer_instance)
    ((convexBarrier_sublevel_bounded hc l b).subset (fun z hz => show convexBarrier c l b z ≤ 1 from le_of_lt hz)) ha
  intro p hp
  have hpq : convexBarrier c l b p = 1 := by
    simpa only [U,convexOn_frontier_sublevel (convexBarrier_convex hc.le l b)
      (convexBarrier_continuous c l b) ha,mem_ofPred_eq] using hp
  exact convexBarrier_local_analytic_chart hc.le l b ha hpq

lemma barrier_exterior_disk_coordinate {ι : Type u_27} [Fintype ι] {c : ℝ} (hc : 0 < c)
    (l : ι → ℂ →L[ℝ] ℝ) (b : ι → ℝ) {a : ℂ} (ha : convexBarrier c l b a < 1) :
    Nonempty (DiskCoordinate (invertedExterior (closure {z | convexBarrier c l b z < 1}) a) 0) := by
  let U := {z | convexBarrier c l b z < 1}
  have hU : IsOpen U := convexBarrier_sublevel_open c l b
  have hcv : Convex ℝ U := convexBarrier_sublevel_convex hc.le l b
  have hcl : closure U = {z | convexBarrier c l b z ≤ 1} :=
    convexOn_closure_sublevel (convexBarrier_convex hc.le l b) (convexBarrier_continuous c l b) ha
  have hK : IsCompact (closure U) := isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closure,hcl ▸ convexBarrier_sublevel_bounded hc l b⟩
  have haK : a ∈ interior (closure U) := hU.subset_interior_closure ha
  have := invertedExterior_simplyConnected hcv.closure (subset_closure ha)
  apply analytic_domain_disk_coordinate (invertedExterior_open hK) (by change SimplyConnectedSpace (invertedExterior (closure U) a); infer_instance)
    (invertedExterior_bounded haK) (zero_mem_invertedExterior (closure U) a)
  intro p hp
  obtain ⟨hp0,hzp⟩ := invertedExterior_frontier hU hK ha hp
  let z := a+p⁻¹
  have hzq : convexBarrier c l b z = 1 := by
    simpa only [U,convexOn_frontier_sublevel (convexBarrier_convex hc.le l b)
      (convexBarrier_continuous c l b) ha,mem_ofPred_eq] using hzp
  have hza : z ≠ a := by dsimp [z]; simpa using inv_ne_zero hp0
  obtain ⟨χ,hχ0,hχa,hχd,_,_,hχc⟩ := convexBarrier_local_analytic_closed_chart hc.le l b ha hzq
  have hχK : ∀ᶠ t : ℂ in 𝓝 0, χ t ∈ closure U ↔ 0 ≤ t.im := by simpa only [hcl,mem_ofPred_eq] using hχc
  obtain ⟨ψ,hψ0,hψa,hψd,hψs,hψb⟩ := invertedExterior_local_chart hK hχ0 hχa hχd hza hχK
  refine ⟨ψ,?_,hψa,hψd,hψs,hψb⟩
  simpa [z] using hψ0
end

section

def exteriorCorrection (G : ℂ → ℂ) (w t : ℂ) : ℂ :=
  t * deriv (dslope G w) t / dslope G w t

lemma analyticAt_dslope_self {G : ℂ → ℂ} {w : ℂ} (hG : AnalyticAt ℂ G w) :
    AnalyticAt ℂ (dslope G w) w := by
  obtain ⟨p,hp⟩ := hG
  exact hp.has_fpower_series_dslope_fslope.analyticAt

lemma analyticOnNhd_dslope {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hG : AnalyticOnNhd ℂ G U) {w : ℂ} (hw : w ∈ U) :
    AnalyticOnNhd ℂ (dslope G w) U := by
  apply (differentiableOn_dslope (hU.mem_nhds hw)).mpr hG.differentiableOn |>.analyticOnNhd hU

lemma dslope_ne_zero_of_injOn {G : ℂ → ℂ} {U : Set ℂ}
    (hi : InjOn G U) {w t : ℂ} (hw : w ∈ U) (ht : t ∈ U)
    (hd : deriv G w ≠ 0) : dslope G w t ≠ 0 := by
  by_cases htw : t = w
  · subst t; simpa using hd
  · rw [dslope_of_ne _ htw, slope_def_field]
    exact div_ne_zero (sub_ne_zero.mpr (fun he => htw (hi ht hw he)))
      (sub_ne_zero.mpr htw)

def exteriorMap (a b : ℂ) (h : ℂ → ℂ) (t : ℂ) : ℂ := a*t+b+h t⁻¹

lemma reciprocal_simple_zero_laurent {H : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hHa : AnalyticOnNhd ℂ H (ball 0 R)) (hHi : InjOn H (ball 0 R))
    (hH0 : H 0 = 0) (hHd : deriv H 0 ≠ 0) (c : ℂ) :
    ∃ a : ℂ, ∃ h : ℂ → ℂ, a ≠ 0 ∧ AnalyticOnNhd ℂ h (ball 0 R) ∧
      ∀ t : ℂ, R⁻¹ < ‖t‖ → exteriorMap a c h t = c+(H t⁻¹)⁻¹ := by
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  let k := dslope H 0
  have hka : AnalyticOnNhd ℂ k (ball 0 R) := analyticOnNhd_dslope isOpen_ball hHa h0
  have hkn : ∀ z ∈ ball 0 R, k z ≠ 0 := fun z hz => dslope_ne_zero_of_injOn hHi h0 hz hHd
  let q : ℂ → ℂ := fun z => (k z)⁻¹
  have hqa : AnalyticOnNhd ℂ q (ball 0 R) := fun z hz => (hka z hz).inv (hkn z hz)
  let h := dslope q 0
  refine ⟨q 0,h,inv_ne_zero (hkn 0 h0),analyticOnNhd_dslope isOpen_ball hqa h0,?_⟩
  intro t ht
  have ht0 : t ≠ 0 := by intro he; simp [he] at ht; exact (not_lt_of_ge hR.le) ht
  have hinv : t⁻¹ ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hR).mpr ht
  have hk : t⁻¹*k t⁻¹ = H t⁻¹ := by simpa [k,hH0,smul_eq_mul] using sub_smul_dslope H 0 t⁻¹
  have hq : t⁻¹*h t⁻¹ = q t⁻¹-q 0 := by simpa [h,smul_eq_mul] using sub_smul_dslope q 0 t⁻¹
  have he : H t⁻¹ ≠ 0 := by
    intro hh
    exact (inv_ne_zero ht0) (hHi hinv h0 (hh.trans hH0.symm))
  dsimp [exteriorMap]
  rw [← hk]
  dsimp [q]
  have hq' : h t⁻¹ = t*((k t⁻¹)⁻¹-(k 0)⁻¹) := by
    calc _ = t*(t⁻¹*h t⁻¹) := by rw [← mul_assoc,mul_inv_cancel₀ ht0,one_mul]
         _ = _ := by rw [hq]
  rw [hq',mul_inv_rev]
  simp only [inv_inv]
  ring


open Set Filter Metric Complex
open scoped Topology

structure ExteriorCoordinate (U : Set ℂ) where
  radius : ℝ
  radius_gt : 1 < radius
  leading : ℂ
  constant : ℂ
  regular : ℂ → ℂ
  leading_ne : leading ≠ 0
  analytic_regular : AnalyticOnNhd ℂ regular (ball 0 radius)
  injective : InjOn (exteriorMap leading constant regular) {t | radius⁻¹ < ‖t‖}
  noncritical : ∀ t, radius⁻¹ < ‖t‖ → deriv (exteriorMap leading constant regular) t ≠ 0
  boundary_image : exteriorMap leading constant regular '' sphere 0 1 = frontier U
  interior_iff : ∀ t, radius⁻¹ < ‖t‖ →
    (exteriorMap leading constant regular t ∈ U ↔ t ∈ ball 0 1)
  outside : ∀ t, 1 < ‖t‖ → exteriorMap leading constant regular t ∉ closure U

lemma exteriorCoordinate_of_disk_inversion {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hK : IsCompact (closure U)) (hc : c ∈ U)
    (hreg : interior (closure U) = U)
    (D : DiskCoordinate (invertedExterior (closure U) c) 0) :
    Nonempty (ExteriorCoordinate U) := by
  let V := invertedExterior (closure U) c
  let H := D.fromDisk
  obtain ⟨R,hR,hRD⟩ := D.exists_inverse_radius
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hRinv : R⁻¹ < 1 := (inv_lt_one₀ hR0).mpr hR
  have hHa : AnalyticOnNhd ℂ H (ball 0 R) := D.analytic_from.mono hRD
  have hHi : InjOn H (ball 0 R) := D.inverse_injective.mono hRD
  have hH0 : H 0 = 0 := D.inverse_base (zero_mem_invertedExterior (closure U) c)
  have hHd : ∀ z ∈ ball (0 : ℂ) R, deriv H z ≠ 0 := fun z hz => D.inverse_noncritical z (hRD hz)
  have h0 : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR0
  obtain ⟨a,h,ha,hah,he⟩ := reciprocal_simple_zero_laurent hR0 hHa hHi hH0 (hHd 0 h0) c
  let G := exteriorMap a c h
  let X := {t : ℂ | R⁻¹ < ‖t‖}
  have hX : IsOpen X := isOpen_lt continuous_const continuous_norm
  have ht0 : ∀ t ∈ X, t ≠ 0 := by
    intro t ht hn
    have hp := inv_pos.mpr hR0
    simp only [X,mem_ofPred_eq,hn,norm_zero] at ht
    linarith
  have hinv : ∀ t ∈ X, t⁻¹ ∈ ball (0 : ℂ) R := by
    intro t ht
    rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr (ht0 t ht)) hR0).mpr ht
  have hHn : ∀ t ∈ X, H t⁻¹ ≠ 0 := by
    intro t ht hn
    exact (inv_ne_zero (ht0 t ht)) (hHi (hinv t ht) h0 (hn.trans hH0.symm))
  have hGX : ∀ t ∈ X, G t = c+(H t⁻¹)⁻¹ := he
  have hGi : InjOn G X := by
    intro s hs t ht hst
    rw [hGX s hs,hGX t ht] at hst
    exact inv_injective (hHi (hinv s hs) (hinv t ht) (inv_injective (add_left_cancel hst)))
  have hGd : ∀ t ∈ X, deriv G t ≠ 0 := by
    intro t ht
    have hdH := (hHa t⁻¹ (hinv t ht)).differentiableAt.hasDerivAt
    have hdi := hasDerivAt_inv (ht0 t ht)
    have hdHinv := (hdH.comp t hdi).inv (hHn t ht)
    have hdc := hdHinv.const_add c
    have hevt : G =ᶠ[𝓝 t] (fun z => c+(H z⁻¹)⁻¹) := by
      filter_upwards [hX.mem_nhds ht] with z hz
      exact hGX z hz
    have hdd := hdc.congr_of_eventuallyEq hevt
    rw [hdd.deriv]
    exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (hHd _ (hinv t ht))
      (neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (ht0 t ht)))))) (pow_ne_zero 2 (hHn t ht))
  have hGb : G '' sphere 0 1 = frontier U := by
    apply Subset.antisymm
    · rintro z ⟨t,ht,rfl⟩
      have htn : ‖t‖ = 1 := mem_sphere_zero_iff_norm.mp ht
      have htX : t ∈ X := by change R⁻¹ < ‖t‖; rwa [htn]
      have hit : t⁻¹ ∈ sphere (0 : ℂ) 1 := by simp [htn]
      have hHv : H t⁻¹ ∈ frontier V := D.inverse_sphere_frontier (invertedExterior_open hK) ▸ mem_image_of_mem H hit
      rw [hGX t htX]
      exact (invertedExterior_frontier_iff hU hK hreg (hHn t htX)).mp hHv
    · intro z hz
      have hzc : z ≠ c := by intro hec; exact (hU.frontier_eq ▸ hz).2 (hec ▸ hc)
      let w := (z-c)⁻¹
      have hw0 : w ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hzc)
      have hwe : c+w⁻¹ = z := by dsimp [w]; rw [inv_inv]; ring
      have hwv : w ∈ frontier V := (invertedExterior_frontier_iff hU hK hreg hw0).mpr (hwe ▸ hz)
      obtain ⟨s,hs,hse⟩ := D.inverse_sphere_frontier (invertedExterior_open hK) ▸ hwv
      have hsn : ‖s‖ = 1 := mem_sphere_zero_iff_norm.mp hs
      have htX : s⁻¹ ∈ X := by simp [X,hsn,hRinv]
      refine ⟨s⁻¹,?_,?_⟩
      · simp [hsn]
      · rw [hGX s⁻¹ htX,inv_inv]
        change c+(D.fromDisk s)⁻¹ = z
        rw [hse,hwe]
  have hinner : ∀ t ∈ X, G t ∈ U ↔ t ∈ ball (0 : ℂ) 1 := by
    intro t ht
    have hcl := invertedExterior_mem_closure_iff (K := closure U) (a := c) (hHn t ht)
    rw [hreg,← hGX t ht, D.inverse_mem_closure_iff (hRD (hinv t ht))] at hcl
    have htpos := norm_pos_iff.mpr (ht0 t ht)
    rw [mem_closedBall_zero_iff,norm_inv] at hcl
    rw [mem_ball_zero_iff]
    have he : ‖t‖⁻¹ ≤ 1 ↔ 1 ≤ ‖t‖ := (inv_le_one₀ htpos)
    rw [he] at hcl
    simpa only [not_not, not_le] using (not_congr hcl.symm)
  have hout : ∀ t, 1 < ‖t‖ → G t ∉ closure U := by
    intro t ht
    have htX : t ∈ X := lt_trans hRinv ht
    have hib : t⁻¹ ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff,norm_inv]
      exact (inv_lt_one₀ (norm_pos_iff.mpr (ht0 t htX))).mpr ht
    have hv : H t⁻¹ ∈ V := D.inverse_ball t⁻¹ hib
    rw [hGX t htX]
    exact hv.resolve_left (hHn t htX)
  exact ⟨⟨R,hR,a,c,h,ha,hah,hGi,hGd,hGb,hinner,hout⟩⟩
end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

lemma complex_real_decomposition {N : ℂ} (hN : N ≠ 0) (z : ℂ) :
    z = (z/N).re • N + (z/N).im • (I*N) := by
  rw [Complex.real_smul,Complex.real_smul]
  calc
    z = (z/N)*N := (div_mul_cancel₀ z hN).symm
    _ = _ := by
      conv_lhs => rw [← re_add_im (z/N)]
      simp only [div_eq_mul_inv]
      ring

lemma real_linear_normal {L : ℂ →L[ℝ] ℝ} {N : ℂ} (hN : N ≠ 0)
    (htan : L (I*N) = 0) (z : ℂ) :
    L z = (L N / ‖N‖^2)*(conj N*z).re := by
  have he := congrArg L (complex_real_decomposition hN z)
  rw [map_add,map_smul,map_smul,htan,smul_zero,add_zero] at he
  rw [he,smul_eq_mul]
  rw [Complex.div_re,Complex.normSq_eq_norm_sq]
  simp only [mul_re,conj_re,conj_im,neg_mul,sub_neg_eq_add]
  ring

lemma analytic_convex_boundary_normal {q : ℂ → ℝ} (hq : ConvexOn ℝ univ q)
    {G : ℂ → ℂ} {t : ℂ} (ht : ‖t‖ = 1)
    (hG : DifferentiableAt ℂ G t) (hGd : deriv G t ≠ 0)
    (hqd : DifferentiableAt ℝ q (G t)) (hqne : fderiv ℝ q (G t) ≠ 0)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → q (G z) = 1)
    (hin : ∀ᶠ r : ℝ in 𝓝[Iic 1] 1, q (G ((r:ℂ)*t)) ≤ 1) :
    ∀ z : ℂ, q z ≤ 1 → 0 ≤ (conj (t*deriv G t)*(G t-z)).re := by
  let L := fderiv ℝ q (G t)
  let N := t*deriv G t
  have hN : N ≠ 0 := mul_ne_zero (by intro h; simp [h] at ht) hGd
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => exp ((s:ℂ)*I)*t)
      (exp ((s:ℂ)*I)*I*t) s := by
    simpa using (((hasDerivAt_id s).ofReal_comp.mul_const I).cexp.mul_const t)
  have he : HasDerivAt (fun s : ℝ => G (exp ((s:ℂ)*I)*t)) (I*N) 0 := by
    simpa only [N,ofReal_zero,zero_mul,Complex.exp_zero,one_mul,Function.comp_def,smul_eq_mul,
      mul_assoc] using
      (show HasDerivAt G (deriv G t) (exp (((0:ℝ):ℂ)*I)*t) from by simpa using hG.hasDerivAt).scomp 0 (hd 0)
  have hderq : HasDerivAt (fun s : ℝ => q (G (exp ((s:ℂ)*I)*t))) (L (I*N)) 0 :=
    (show HasFDerivAt q L (G (exp (((0:ℝ):ℂ)*I)*t)) from by simpa [L] using hqd.hasFDerivAt).comp_hasDerivAt 0 he
  have hconst : (fun s : ℝ => q (G (exp ((s:ℂ)*I)*t))) = fun _ => (1:ℝ) := by
    funext s
    exact hb _ (by rw [norm_mul,norm_exp_ofReal_mul_I,ht,one_mul])
  rw [hconst] at hderq
  have htan : L (I*N) = 0 := hderq.unique (hasDerivAt_const 0 1)
  have hdr : HasDerivAt (fun r : ℝ => (r:ℂ)*t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).ofReal_comp.mul_const t
  have hger : HasDerivAt (fun r : ℝ => G ((r:ℂ)*t)) N 1 := by
    simpa only [N,ofReal_one,one_mul,Function.comp_def,smul_eq_mul] using
      (show HasDerivAt G (deriv G t) (((1:ℝ):ℂ)*t) from by simpa using hG.hasDerivAt).scomp 1 hdr
  have hqr : HasDerivAt (fun r : ℝ => q (G ((r:ℂ)*t))) (L N) 1 :=
    (show HasFDerivAt q L (G (((1:ℝ):ℂ)*t)) from by simpa [L] using hqd.hasFDerivAt).comp_hasDerivAt 1 hger
  have hm : IsLocalMaxOn (fun r : ℝ => q (G ((r:ℂ)*t))) (Iic 1) 1 := by
    filter_upwards [hin] with r hr
    simpa only [ofReal_one,one_mul,hb t ht] using hr
  have hy : (-1:ℝ) ∈ posTangentConeAt (Iic (1:ℝ)) 1 := by
    apply mem_posTangentConeAt_of_segment_subset
    apply (convex_Iic (1:ℝ)).segment_subset <;> simp
  have hnonpos := hm.hasFDerivWithinAt_nonpos hqr.hasFDerivAt.hasFDerivWithinAt hy
  simp only [ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul] at hnonpos
  have hLN : 0 < L N := by
    have hn : L N ≠ 0 := by
      intro hz
      apply hqne
      ext z
      change L z = 0
      rw [real_linear_normal hN htan z,hz,zero_div,zero_mul]
    exact lt_of_le_of_ne (by linarith) (Ne.symm hn)
  intro z hz
  have hs := convexOn_fderiv_support hq hqd z
  rw [hb t ht] at hs
  have hle : L (z-G t) ≤ 0 := hs.trans (by linarith)
  rw [real_linear_normal hN htan (z-G t)] at hle
  have hratio : 0 < L N / ‖N‖^2 := div_pos hLN (sq_pos_of_pos (norm_pos_iff.mpr hN))
  have hle' : (conj N*(z-G t)).re ≤ 0 := by nlinarith
  change 0 ≤ (conj N*(G t-z)).re
  have heq : (conj N*(G t-z)).re = -(conj N*(z-G t)).re := by
    rw [show G t-z = -(z-G t) by ring,mul_neg,neg_re]
  rw [heq]
  linarith


end CompleteCrouzeix

end

end OAI
