import OAI.Geometry.Symplectic.MorseBounds.SmoothODE
import OAI.Geometry.Symplectic.MorseBounds.Dynamics

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.ManifoldFlow
open Set Filter Metric
open scoped Topology ContDiff Manifold
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma smooth_extension_near {W : E → E} {U : Set E} (hU : IsOpen U)
    (hW : ContDiffOn ℝ ∞ W U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ V =ᶠ[𝓝 x₀] W := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx₀)
  let f : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  refine ⟨fun x => f x • W x, ?_, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ tsupport f
    · exact f.contDiff.contDiffAt.smul
        ((hW x (hsub (by simpa [f.tsupport_eq] using hx))).contDiffAt
          (hU.mem_nhds (hsub (by simpa [f.tsupport_eq] using hx))))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      have hn : ∀ᶠ y in 𝓝 x, y ∉ tsupport f :=
        isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hn] with y hy
      have hz : f y = 0 := Function.notMem_support.mp (fun h => hy (subset_closure h))
      simp [hz]
  · filter_upwards [f.eventuallyEq_one] with y hy
    simp [hy]

lemma exists_local_smooth_flow_on {W : E → E} {U : Set E} (hU : IsOpen U)
    (hW : ContDiffOn ℝ ∞ W U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ Φ : ℝ × E → E,
      ContDiffOn ℝ ∞ Φ (Ioo (-ε) ε ×ˢ ball x₀ r) ∧
      (∀ x ∈ ball x₀ r, Φ (0, x) = x) ∧
      (∀ t ∈ Ioo (-ε) ε, ∀ x ∈ ball x₀ r, Φ (t, x) ∈ U) ∧
      ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ ball x₀ r,
        HasDerivAt (fun s => Φ (s, x)) (W (Φ (t, x))) t := by
  obtain ⟨V, hV, heq⟩ := smooth_extension_near hU hW hx₀
  obtain ⟨r, hr, ε, hε, Φ, hΦ, hi, hd⟩ := MorseArnold.SmoothODE.exists_local_smooth_flow hV x₀
  have hbase : ((0 : ℝ), x₀) ∈ Ioo (-ε) ε ×ˢ ball x₀ r :=
    ⟨⟨neg_lt_zero.mpr hε, hε⟩, mem_ball_self hr⟩
  have hc := (hΦ.continuousOn _ hbase).continuousAt
    ((isOpen_Ioo.prod isOpen_ball).mem_nhds hbase)
  have hh : ∀ᶠ p in 𝓝 ((0 : ℝ), x₀), V (Φ p) = W (Φ p) ∧ Φ p ∈ U := by
    have ht := hc.tendsto
    rw [hi x₀ (mem_ball_self hr)] at ht
    exact ht (heq.and (hU.mem_nhds hx₀))
  obtain ⟨δ, hδ, hs⟩ := Metric.mem_nhds_iff.mp hh
  let a := min δ ε
  let b := min δ r
  have ha : 0 < a := lt_min hδ hε
  have hb : 0 < b := lt_min hδ hr
  have hsub : Ioo (-a) a ×ˢ ball x₀ b ⊆ Ioo (-ε) ε ×ˢ ball x₀ r := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    exact ⟨⟨lt_of_le_of_lt (neg_le_neg (min_le_right δ ε)) ht.1,
      ht.2.trans_le (min_le_right δ ε)⟩, ball_subset_ball (min_le_right δ r) hx⟩
  have hδsub : Ioo (-a) a ×ˢ ball x₀ b ⊆ ball ((0 : ℝ), x₀) δ := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨by simpa [Real.dist_eq] using (abs_lt.mpr ht).trans_le (min_le_left δ ε),
      (show dist x x₀ < b from hx).trans_le (min_le_left δ r)⟩
  refine ⟨b, hb, a, ha, Φ, hΦ.mono hsub, ?_, ?_, ?_⟩
  · intro x hx
    exact hi x (ball_subset_ball (min_le_right δ r) hx)
  · intro t ht x hx
    exact (hs (hδsub ⟨ht, hx⟩)).2
  · intro t ht x hx
    rw [← (hs (hδsub ⟨ht, hx⟩)).1]
    exact hd t (hsub (a := (t,x)) ⟨ht,hx⟩).1 x (hsub (a := (t,x)) ⟨ht,hx⟩).2

variable {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def chartField (V : (x : M) → TangentSpace 𝓘(ℝ, E) x) (p : M) (y : E) : E :=
  tangentCoordChange 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) p).symm y) p
    ((extChartAt 𝓘(ℝ, E) p).symm y) (V ((extChartAt 𝓘(ℝ, E) p).symm y))

omit [FiniteDimensional ℝ E] in
lemma chartField_smooth (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) (p : M) :
    ContDiffOn ℝ ∞ (chartField V p) (extChartAt 𝓘(ℝ, E) p).target := by
  intro y hy
  let c := extChartAt 𝓘(ℝ, E) p
  have hcy : c.symm y ∈ c.source := c.map_target hy
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm y :=
    (contMDiffOn_extChartAt_symm p y hy).contMDiffAt
      ((isOpen_extChartAt_target p).mem_nhds hy)
  have hsec := (Bundle.Trivialization.contMDiffAt_iff
    (IB := 𝓘(ℝ, E)) (IM := 𝓘(ℝ, E)) (n := ∞)
    (f := fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) (x₀ := c.symm y)
    (e := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p)
    (show (⟨c.symm y, V (c.symm y)⟩ : TangentBundle 𝓘(ℝ, E) M) ∈
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).source from by
        simpa only [TangentBundle.trivializationAt_source, mem_preimage, c, extChartAt_source] using hcy)).mp
    (hV.contMDiffAt (x := c.symm y))
  exact (hsec.2.comp y hc).contDiffAt.contDiffWithinAt

omit [FiniteDimensional ℝ E] in
lemma chart_integralCurve (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (p : M) {f : ℝ → E} {t : ℝ} (ht : f t ∈ (extChartAt 𝓘(ℝ, E) p).target)
    (hd : HasDerivAt f (chartField V p (f t)) t) :
    HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) p).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (V ((extChartAt 𝓘(ℝ, E) p).symm (f t)))) := by
  let xₜ : M := (extChartAt 𝓘(ℝ, E) p).symm (f t)
  have hft1 : xₜ ∈ (extChartAt 𝓘(ℝ, E) p).source :=
    (extChartAt 𝓘(ℝ, E) p).map_target ht
  have hft2 := mem_extChartAt_source (I := 𝓘(ℝ, E)) xₜ
  refine ⟨(continuousAt_extChartAt_symm'' ht).comp hd.continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  change HasFDerivAt
    (((extChartAt 𝓘(ℝ, E) xₜ) ∘ (extChartAt 𝓘(ℝ, E) p).symm) ∘ f)
    ((1 : ℝ →L[ℝ] ℝ).smulRight (V xₜ)) t
  apply HasDerivAt.hasFDerivAt
  erw [← tangentCoordChange_self (I := 𝓘(ℝ, E)) (x := xₜ) (z := xₜ) (v := V xₜ) hft2,
    ← tangentCoordChange_comp (x := p) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hd
  rw [← (extChartAt 𝓘(ℝ, E) p).right_inv ht]
  exact (hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩).hasFDerivAt (by simp)

theorem exists_local_smooth_manifold_flow
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ ε > (0 : ℝ), ∃ Φ : ℝ × M → M,
      ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ (Ioo (-ε) ε ×ˢ U) ∧
      (∀ x ∈ U, Φ (0, x) = x) ∧
      ∀ x ∈ U, IsMIntegralCurveOn (fun t => Φ (t, x)) V (Ioo (-ε) ε) := by
  let c := extChartAt 𝓘(ℝ, E) p
  obtain ⟨r, hr, ε, hε, ψ, hs, hi, hm, hd⟩ := exists_local_smooth_flow_on
    (isOpen_extChartAt_target p) (chartField_smooth V hV p)
    (c.map_source (mem_extChartAt_source p))
  let U := c.source ∩ c ⁻¹' ball (c p) r
  have hU : IsOpen U := (continuousOn_extChartAt p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) isOpen_ball
  have hp : p ∈ U := ⟨mem_extChartAt_source p, mem_ball_self hr⟩
  let Φ : ℝ × M → M := fun q => c.symm (ψ (q.1, c q.2))
  refine ⟨U, hU, hp, ε, hε, Φ, ?_, ?_, ?_⟩
  · intro q hq
    have hchart : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c q.2 :=
      contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using hq.2.1)
    have hcoord : ContDiffAt ℝ ∞ ψ (q.1, c q.2) :=
      (hs (q.1, c q.2) ⟨hq.1, hq.2.2⟩).contDiffAt
        ((isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨hq.1, hq.2.2⟩)
    have hpair : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ).prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (q.1, c q.2)) q :=
      contMDiffAt_fst.prodMk (hchart.comp q contMDiffAt_snd)
    have hout : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c.symm (ψ (q.1, c q.2)) :=
      (contMDiffOn_extChartAt_symm p _ (hm q.1 hq.1 (c q.2) hq.2.2)).contMDiffAt
        ((isOpen_extChartAt_target p).mem_nhds (hm q.1 hq.1 (c q.2) hq.2.2))
    have hcoordM : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ ψ (q.1, c q.2) := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hcoord.contMDiffAt
    exact (hout.comp q (hcoordM.comp q hpair)).contMDiffWithinAt
  · intro x hx
    dsimp [Φ]
    rw [hi (c x) hx.2, c.left_inv hx.1]
  · intro x hx t ht
    exact (chart_integralCurve V p (hm t ht (c x) hx.2) (hd t ht (c x) hx.2)).hasMFDerivWithinAt

lemma compact_uniform_time [CompactSpace M] (U : M → Set M)
    (hU : ∀ p, IsOpen (U p)) (hp : ∀ p, p ∈ U p)
    (ε : M → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ δ > (0 : ℝ), ∀ x, ∃ p, x ∈ U p ∧ δ ≤ ε p := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨x, hp x⟩)
  by_cases hne : s.Nonempty
  · obtain ⟨p, hps, hmin⟩ := s.exists_min_image ε hne
    refine ⟨ε p, hε p, ?_⟩
    intro x
    obtain ⟨q, hqs, hxq⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨q, hxq, hmin q hqs⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    obtain ⟨q, hqs, _⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact (hne ⟨q, hqs⟩).elim

theorem exists_global_integral_curves [T2Space M] [CompactSpace M]
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V := by
  choose U hU hp ε hε Φ hΦ hi hd using exists_local_smooth_manifold_flow V hV
  obtain ⟨δ, hδ, hcover⟩ := compact_uniform_time U hU hp ε hε
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (hV.of_le (by simp)) hδ
  intro x
  obtain ⟨p, hxp, hδp⟩ := hcover x
  exact ⟨fun t => Φ p (t,x), hi p x hxp,
    (hd p x hxp).mono (Ioo_subset_Ioo (neg_le_neg hδp) hδp)⟩

omit [FiniteDimensional ℝ E] in
theorem flow_law_of_integral_curves [T2Space M]
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (Φ : ℝ × M → M) (hi : ∀ x, Φ (0,x) = x)
    (hd : ∀ x, IsMIntegralCurve (fun t => Φ (t,x)) V) :
    ∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x)) := by
  intro s t x
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (hV.of_le (by simp)) ((hd x).comp_add t) (hd (Φ (t,x))) (by simp [hi])
  exact congrFun he s

lemma uniform_smooth_near_zero [T2Space M] [CompactSpace M]
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (Φ : ℝ × M → M) (hi : ∀ x, Φ (0,x) = x)
    (hd : ∀ x, IsMIntegralCurve (fun t => Φ (t,x)) V) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Ioo (-δ) δ, ∀ x,
      ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ (t,x) := by
  choose U hU hp ε hε ψ hψ hψi hψd using exists_local_smooth_manifold_flow V hV
  obtain ⟨δ, hδ, hcover⟩ := compact_uniform_time U hU hp ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht x
  obtain ⟨p, hxp, hδp⟩ := hcover x
  have ht' : t ∈ Ioo (-ε p) (ε p) := Ioo_subset_Ioo (neg_le_neg hδp) hδp ht
  have heq : EqOn Φ (ψ p) (Ioo (-ε p) (ε p) ×ˢ U p) := by
    rintro ⟨s,y⟩ ⟨hs,hy⟩
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      (t₀ := 0) ⟨neg_lt_zero.mpr (hε p), hε p⟩ (hV.of_le (by simp))
      ((hd y).isMIntegralCurveOn _) (hψd p y hy) (by rw [hi, hψi p y hy]) hs
  have hnhds : Ioo (-ε p) (ε p) ×ˢ U p ∈ 𝓝 (t,x) :=
    (isOpen_Ioo.prod (hU p)).mem_nhds ⟨ht', hxp⟩
  exact ((hψ p (t,x) ⟨ht',hxp⟩).contMDiffAt hnhds).congr_of_eventuallyEq
    (heq.eventuallyEq_of_mem hnhds)

omit [TopologicalSpace M] in
lemma flow_nat_mul (Φ : ℝ × M → M) (hi : ∀ x, Φ (0,x) = x)
    (hadd : ∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) (n : ℕ) (a : ℝ) (x : M) :
    Φ ((n : ℝ)*a,x) = (fun y => Φ (a,y))^[n] x := by
  induction n with
  | zero => simp [hi]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, add_comm ((n : ℝ)*a), hadd, ih,
      Function.iterate_succ_apply']

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
lemma smooth_of_uniform_short_time (Φ : ℝ × M → M) (hi : ∀ x, Φ (0,x) = x)
    (hadd : ∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ t ∈ Ioo (-δ) δ, ∀ x,
      ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ (t,x)) :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ := by
  rintro ⟨t,x⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (|t| / δ)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (abs_nonneg t) hδ.le) hN
  have ht : t / (N : ℝ) ∈ Ioo (-δ) δ := by
    apply abs_lt.mp
    rw [abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
    exact (div_lt_iff₀ hδ).mp hN |>.trans_eq (mul_comm _ _)
  have hiter : ∀ k : ℕ,
      ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × M => (fun y => Φ (q.1 / (N : ℝ), y))^[k] q.2) (t,x) := by
    intro k
    induction k with
    | zero => exact contMDiffAt_snd
    | succ k ih =>
      have htM : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ) ∞
          (fun q : ℝ × M => q.1 / (N : ℝ)) (t,x) := contMDiffAt_fst.div_const _
      simpa only [Function.iterate_succ_apply', Function.comp_def] using
        (hs _ ht _).comp (t,x) (htM.prodMk ih)
  have heq : Φ = (fun q : ℝ × M => (fun y => Φ (q.1 / (N : ℝ), y))^[N] q.2) := by
    funext q
    have hh := flow_nat_mul Φ hi hadd N (q.1 / (N : ℝ)) q.2
    have hm : (N : ℝ) * (q.1 / (N : ℝ)) = q.1 := by field_simp
    rwa [hm] at hh
  rw [heq]
  exact hiter N

theorem exists_compact_smooth_flow [T2Space M] [CompactSpace M]
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ∃ Φ : ℝ × M → M,
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) ∧
      ∀ x, IsMIntegralCurve (fun t => Φ (t,x)) V := by
  choose γ hi hd using exists_global_integral_curves V hV
  let Φ : ℝ × M → M := fun q => γ q.2 q.1
  have hadd := flow_law_of_integral_curves V hV Φ hi hd
  obtain ⟨δ,hδ,hs⟩ := uniform_smooth_near_zero V hV Φ hi hd
  exact ⟨Φ, smooth_of_uniform_short_time Φ hi hadd hδ hs, hi, hadd, hd⟩

end
end MorseArnold.ManifoldFlow

namespace MorseArnold.ManifoldFlow
open scoped Manifold ContDiff

def CompactSmoothFlowExistence : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [CompactSpace M]
    (V : (x : M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)) →
    ∃ Φ : ℝ × M → M,
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Φ ∧
      (∀ x, Φ (0, x) = x) ∧
      (∀ s t x, Φ (s + t, x) = Φ (s, Φ (t, x))) ∧
      ∀ x, IsMIntegralCurve (fun t => Φ (t, x)) V

theorem compactSmoothFlowExistence : CompactSmoothFlowExistence := by
  intro n M _ _ _ _ _ V hV
  exact exists_compact_smooth_flow V hV

end MorseArnold.ManifoldFlow

namespace MorseArnold.ManifoldFlow
open Filter Topology Set
open scoped Manifold ContDiff
variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [T2Space M] in
lemma compact_core_uniform_time (K : Set M) (hK : IsCompact K) (U : M → Set M)
    (hU : ∀ p, IsOpen (U p)) (hp : ∀ p, p ∈ U p)
    (ε : M → ℝ) (hε : ∀ p, 0 < ε p) :
    ∃ δ > (0 : ℝ), ∀ x ∈ K, ∃ p, x ∈ U p ∧ δ ≤ ε p := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U hU (by
    intro x hx
    exact mem_iUnion.mpr ⟨x, hp x⟩)
  by_cases hne : s.Nonempty
  · obtain ⟨p, hps, hmin⟩ := s.exists_min_image ε hne
    refine ⟨ε p, hε p, ?_⟩
    intro x hx
    obtain ⟨q, hqs, hxq⟩ := mem_iUnion₂.mp (hs hx)
    exact ⟨q, hxq, hmin q hqs⟩
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    obtain ⟨q, hqs, _⟩ := mem_iUnion₂.mp (hs hx)
    exact (hne ⟨q, hqs⟩).elim

theorem exists_core_global_integral_curves
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (K U : Set M) (hK : IsCompact K) (hcov : K ∪ U = univ)
    (Ψ : ℝ × M → M) (hi : ∀ x ∈ U, Ψ (0,x) = x)
    (hd : ∀ x ∈ U, IsMIntegralCurve (fun t => Ψ (t,x)) V) :
    ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ V := by
  choose W hW hp ε hε Φ hΦ hΦi hΦd using exists_local_smooth_manifold_flow V hV
  obtain ⟨δ, hδ, hcover⟩ := compact_core_uniform_time K hK W hW hp ε hε
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (hV.of_le (by simp)) hδ
  intro x
  have hx : x ∈ K ∪ U := by rw [hcov]; exact mem_univ x
  rcases hx with hx | hx
  · obtain ⟨p, hxp, hδp⟩ := hcover x hx
    exact ⟨fun t => Φ p (t,x), hΦi p x hxp,
      (hΦd p x hxp).mono (Ioo_subset_Ioo (neg_le_neg hδp) hδp)⟩
  · exact ⟨fun t => Ψ (t,x), hi x hx, (hd x hx).isMIntegralCurveOn _⟩

lemma core_uniform_smooth_near_zero
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hcov : K ∪ U = univ)
    (Ψ : ℝ × M → M)
    (hΨ : ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Ψ (univ ×ˢ U))
    (hΨi : ∀ x ∈ U, Ψ (0,x) = x)
    (hΨd : ∀ x ∈ U, IsMIntegralCurve (fun t => Ψ (t,x)) V)
    (Φ : ℝ × M → M) (hi : ∀ x, Φ (0,x) = x)
    (hd : ∀ x, IsMIntegralCurve (fun t => Φ (t,x)) V) :
    ∃ δ > (0 : ℝ), ∀ t ∈ Ioo (-δ) δ, ∀ x,
      ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ (t,x) := by
  choose W hW hp ε hε ψ hψ hψi hψd using exists_local_smooth_manifold_flow V hV
  obtain ⟨δ, hδ, hcover⟩ := compact_core_uniform_time K hK W hW hp ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht x
  have hx : x ∈ K ∪ U := by rw [hcov]; exact mem_univ x
  rcases hx with hx | hx
  · obtain ⟨p, hxp, hδp⟩ := hcover x hx
    have ht' : t ∈ Ioo (-ε p) (ε p) := Ioo_subset_Ioo (neg_le_neg hδp) hδp ht
    have heq : EqOn Φ (ψ p) (Ioo (-ε p) (ε p) ×ˢ W p) := by
      rintro ⟨s,y⟩ ⟨hs,hy⟩
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨neg_lt_zero.mpr (hε p), hε p⟩ (hV.of_le (by simp))
        ((hd y).isMIntegralCurveOn _) (hψd p y hy) (by rw [hi, hψi p y hy]) hs
    have hnhds : Ioo (-ε p) (ε p) ×ˢ W p ∈ 𝓝 (t,x) :=
      (isOpen_Ioo.prod (hW p)).mem_nhds ⟨ht', hxp⟩
    exact ((hψ p (t,x) ⟨ht',hxp⟩).contMDiffAt hnhds).congr_of_eventuallyEq
      (heq.eventuallyEq_of_mem hnhds)
  · have heq : EqOn Φ Ψ (univ ×ˢ U) := by
      rintro ⟨s,y⟩ ⟨_,hy⟩
      exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
        (hV.of_le (by simp)) (hd y) (hΨd y hy) (by rw [hi, hΨi y hy])) s
    have hnhds : univ ×ˢ U ∈ 𝓝 (t,x) :=
      (isOpen_univ.prod hU).mem_nhds ⟨mem_univ t, hx⟩
    exact ((hΨ (t,x) ⟨mem_univ t,hx⟩).contMDiffAt hnhds).congr_of_eventuallyEq
      (heq.eventuallyEq_of_mem hnhds)

theorem exists_compact_core_smooth_flow
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (K U : Set M) (hK : IsCompact K) (hU : IsOpen U) (hcov : K ∪ U = univ)
    (Ψ : ℝ × M → M)
    (hΨ : ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Ψ (univ ×ˢ U))
    (hΨi : ∀ x ∈ U, Ψ (0,x) = x)
    (hΨd : ∀ x ∈ U, IsMIntegralCurve (fun t => Ψ (t,x)) V) :
    ∃ Φ : ℝ × M → M,
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) ∧
      (∀ x, IsMIntegralCurve (fun t => Φ (t,x)) V) ∧
      ∀ t x, x ∈ U → Φ (t,x) = Ψ (t,x) := by
  choose γ hi hd using exists_core_global_integral_curves V hV K U hK hcov Ψ hΨi hΨd
  let Φ : ℝ × M → M := fun q => γ q.2 q.1
  have hadd := flow_law_of_integral_curves V hV Φ hi hd
  obtain ⟨δ,hδ,hs⟩ := core_uniform_smooth_near_zero V hV K U hK hU hcov Ψ hΨ hΨi hΨd Φ hi hd
  refine ⟨Φ, smooth_of_uniform_short_time Φ hi hadd hδ hs, hi, hadd, hd, ?_⟩
  intro t x hx
  exact congrFun (isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    (hV.of_le (by simp)) (hd x) (hΨd x hx) (by rw [hi, hΨi x hx])) t

end MorseArnold.ManifoldFlow

namespace MorseArnold.ManifoldFlow
open Filter Topology Set
open scoped Manifold ContDiff

def CompactCoreSmoothFlowExistence : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
    (V : (x : M) → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)) →
    ∀ (K U : Set M), IsCompact K → IsOpen U → K ∪ U = univ →
    ∀ Ψ : ℝ × M → M,
      ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Ψ (univ ×ˢ U) →
      (∀ x ∈ U, Ψ (0,x) = x) →
      (∀ x ∈ U, IsMIntegralCurve (fun t => Ψ (t,x)) V) →
    ∃ Φ : ℝ × M → M,
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Φ ∧
      (∀ x, Φ (0, x) = x) ∧
      (∀ s t x, Φ (s + t, x) = Φ (s, Φ (t, x))) ∧
      (∀ x, IsMIntegralCurve (fun t => Φ (t, x)) V) ∧
      ∀ t x, x ∈ U → Φ (t,x) = Ψ (t,x)

end MorseArnold.ManifoldFlow

namespace MorseArnold.ManifoldFlow
 theorem compactCoreSmoothFlowExistence : CompactCoreSmoothFlowExistence := by
  intro n M _ _ _ _ V hV K U hK hU hcov Ψ hΨ hΨi hΨd
  exact exists_compact_core_smooth_flow V hV K U hK hU hcov Ψ hΨ hΨi hΨd
end MorseArnold.ManifoldFlow

end

end OAI
