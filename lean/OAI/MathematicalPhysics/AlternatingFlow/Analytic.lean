import OAI.MathematicalPhysics.AlternatingFlow.Construction

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace Analytic

lemma spatial_fderiv_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) := by
  exact (hF.comp ((contDiff_fst.fst).prodMk contDiff_snd)).fderiv contDiff_snd (by simp)

lemma dx_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i : Fin 3) :
    ContDiff ℝ ∞ (Function.uncurry (dx i F)) :=
  (spatial_fderiv_smooth F hF).clm_apply contDiff_const

noncomputable def fullDt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : Field E := fun t x => fderiv ℝ (fun s => F s x) t 1

lemma fullDt_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) :
    ContDiff ℝ ∞ (Function.uncurry (fullDt F)) := by
  exact ((hF.comp (contDiff_snd.prodMk contDiff_fst.snd)).fderiv contDiff_fst (by simp)).clm_apply
    contDiff_const

lemma dt_eq_full {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) (ht : 0 ≤ t) (x : Space) :
    dt F t x = fullDt F t x := by
  unfold dt fullDt
  have hd : DifferentiableAt ℝ (fun s => F s x) t :=
    ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
  rw [fderivWithin_eq_fderiv (uniqueDiffOn_Ici _ _ ht) hd]

lemma smooth_classical (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ClassicalRegularity U (fun _ _ => 0) := by
  refine ⟨fun x => ?_, fun t _ => ?_, fun t _ i => ?_, fun t _ => differentiable_const _, ?_⟩
  · exact ((hU.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)).differentiableOn
  · exact (hU.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  · exact ((dx_smooth U hU i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  · intro T _
    refine ⟨hU.continuous.continuousOn, ?_, fun i => (dx_smooth U hU i).continuous.continuousOn,
      fun i j => (dx_smooth (dx j U) (dx_smooth U hU j) i).continuous.continuousOn,
      continuousOn_const, ?_⟩
    · apply (fullDt_smooth U hU).continuous.continuousOn.congr
      intro z hz
      exact dt_eq_full U hU z.1 hz.1.1 z.2
    · intro i
      change ContinuousOn (fun z : ℝ × Space => fderiv ℝ (fun _ : Space => (0 : ℝ)) z.2 (e i)) _
      simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ × Space => (0 : ℝ))
        (timeCylinder T))

lemma residual_navierStokes (ν : ℝ) (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (h0 : ∀ x, U 0 x = 0) (hd : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    NavierStokes ν (residual ν U) U (fun _ _ => 0) := by
  refine ⟨smooth_classical U hU, h0, fun t ht x => ⟨hd t ht x, ?_⟩⟩
  have hp : grad (fun _ _ => 0) t x = 0 := by
    ext i
    simp [grad, dx, EuclideanSpace.equiv]
  rw [hp, residual]
  abel

lemma advection_smooth (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ContDiff ℝ ∞ (Function.uncurry (advection U)) :=
  (spatial_fderiv_smooth U hU).clm_apply hU

lemma laplacian_smooth (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    ContDiff ℝ ∞ (Function.uncurry (laplacian U)) := by
  change ContDiff ℝ ∞ (fun z : ℝ × Space => ∑ i : Fin 3, dx i (dx i U) z.1 z.2)
  apply ContDiff.sum
  intro i _
  exact dx_smooth (dx i U) (dx_smooth U hU i) i

lemma residual_smooth (ν : ℝ) (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U)) :
    Smooth (residual ν U) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space =>
      fullDt U z.1 z.2 + advection U z.1 z.2 - ν • laplacian U z.1 z.2) :=
    ((fullDt_smooth U hU).add (advection_smooth U hU)).sub
      ((laplacian_smooth U hU).const_smul ν)
  apply hf.contDiffOn.congr
  intro z hz
  simp only [Function.uncurry, residual, dt_eq_full U hU z.1 hz.1]

lemma dx_supported {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hF : ∀ t, Function.support (F t) ⊆ K) (i : Fin 3) :
    ∀ t, Function.support (dx i F t) ⊆ K := by
  intro t x hx
  exact (closure_minimal (hF t) hK) ((Spatial.d_tsupport i (F t)) (subset_closure hx))

lemma outside_dt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) (K : Set Space) (hF : ∀ t, Function.support (F t) ⊆ K)
    (t : ℝ) (x : Space) (hx : x ∉ K) : dt F t x = 0 := by
  have he : (fun s => F s x) = fun _ => 0 := by
    funext s
    exact Function.notMem_support.1 (fun hx' => hx (hF s hx'))
  simp [dt, he]

lemma residual_supported (ν : ℝ) (U : Velocity) (K : Set Space) (hK : IsClosed K)
    (hU : ∀ t, Function.support (U t) ⊆ K) :
    ∀ t, Function.support (residual ν U t) ⊆ K := by
  intro t x hx
  by_contra hn
  have hUx : U t x = 0 := Function.notMem_support.1 (fun hx' => hn (hU t hx'))
  have hΔ : laplacian U t x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact Function.notMem_support.1 (fun hx' => hn (dx_supported (dx i U) K hK
      (dx_supported U K hK hU i) i t hx'))
  exact hx (by simp [residual, outside_dt U K hU t x hn, advection, hUx, hΔ])

lemma finite_bound {E : Type*} [NormedAddCommGroup E]
    (F : Field E) (hF : Continuous (Function.uncurry F)) (K : Set Space) (hK : IsCompact K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (T : ℝ) :
    ∃ C : ℝ≥0, ∀ t ∈ Set.Icc 0 T, ∀ x, ‖F t x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨⟨max 0 C, le_max_left _ _⟩, fun t ht x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC (t, x) ⟨ht, hx⟩).trans (le_max_right _ _)
  · have hz : F t x = 0 := Function.notMem_support.1 (fun hx' => hx (hs t hx'))
    simp only [hz, norm_zero]
    exact le_max_left _ _

lemma finite_lipschitz (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) (T : ℝ) :
    ∃ C : ℝ≥0, ∀ t ∈ Set.Icc 0 T, LipschitzWith C (U t) := by
  have hder : ∀ t, Function.support (fderiv ℝ (U t)) ⊆ K :=
    fun t => (support_fderiv_subset ℝ).trans (closure_minimal (hs t) hK.isClosed)
  obtain ⟨C, hC⟩ := finite_bound (fun t x => fderiv ℝ (U t) x)
    (spatial_fderiv_smooth U hU).continuous K hK hder T
  refine ⟨C, fun t ht => lipschitzWith_of_nnnorm_fderiv_le
    ((hU.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) ?_⟩
  intro x
  exact_mod_cast hC t ht x

end Analytic
end AlternatingNS

namespace AlternatingNS
namespace Analytic

lemma trajectory_unique (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) (γ δ : ℝ → Space) (hγ : IsTrajectory U a γ) (hδ : IsTrajectory U a δ)
    (T : ℝ) (hT : 0 ≤ T) : γ T = δ T := by
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  have hc (β : ℝ → Space) (hβ : IsTrajectory U a β) : ContinuousOn β (Set.Icc 0 T) :=
    HasDerivWithinAt.continuousOn (fun t ht => (hβ.2 t ht.1).mono Set.Icc_subset_Ici_self)
  apply ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hC t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (hc γ hγ) (fun t ht => (hγ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun _ _ => Set.mem_univ _) (hc δ hδ)
    (fun t ht => (hδ.2 t ht.1).mono (Set.Ici_subset_Ici.mpr ht.1))
    (fun _ _ => Set.mem_univ _) (hγ.1.trans hδ.1.symm) ⟨hT, le_rfl⟩

lemma finite_trajectory (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) (T : ℝ) (hT : 0 ≤ T) :
    ∃ γ : ℝ → Space, γ 0 = a ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (U t (γ t)) (Set.Icc 0 T) t := by
  obtain ⟨L, hL⟩ := finite_bound U hU.continuous K hK hs T
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  let t₀ : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hpl : IsPicardLindelof U t₀ a (L * ⟨T, hT⟩) 0 L C := by
    refine ⟨fun t ht => (hC t ht).lipschitzOnWith, fun x _ => ?_,
      fun t ht x _ => hL t ht x, ?_⟩
    · exact (hU.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
    · change (L : ℝ) * max (T - 0) (0 - 0) ≤ (L : ℝ) * T - 0
      simp [max_eq_left hT]
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma finite_trajectory_unique (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (γ δ : ℝ → Space) (T : ℝ) (h0 : γ 0 = δ 0)
    (hγ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt γ (U t (γ t)) (Set.Icc 0 T) t)
    (hδ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt δ (U t (δ t)) (Set.Icc 0 T) t) :
    Set.EqOn γ δ (Set.Icc 0 T) := by
  obtain ⟨C, hC⟩ := finite_lipschitz U hU K hK hs T
  have hd (β : ℝ → Space)
      (hβ : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt β (U t (β t)) (Set.Icc 0 T) t) :
      ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt β (U t (β t)) (Set.Ici t) t := by
    intro t ht
    apply (hβ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    exact Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (fun y hy => ⟨ht.1.trans hy.1, hy.2⟩)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun t ht => (hC t ⟨ht.1, ht.2.le⟩).lipschitzOnWith)
    (HasDerivWithinAt.continuousOn hγ) (hd γ hγ) (fun _ _ => Set.mem_univ _)
    (HasDerivWithinAt.continuousOn hδ) (hd δ hδ) (fun _ _ => Set.mem_univ _) h0

lemma global_trajectory (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (a : Space) : ∃ γ, IsTrajectory U a γ := by
  classical
  have hex (n : ℕ) := finite_trajectory U hU K hK hs a ((n : ℝ) + 1) (by positivity)
  choose α hα₀ hα using hex
  have coherent (n m : ℕ) (t : ℝ) (ht : 0 ≤ t) (hn : t ≤ (n : ℝ) + 1)
      (hm : t ≤ (m : ℝ) + 1) : α n t = α m t := by
    apply finite_trajectory_unique U hU K hK hs (α n) (α m) t
      ((hα₀ n).trans (hα₀ m).symm)
      (fun s hs => (hα n s ⟨hs.1, hs.2.trans hn⟩).mono
        (Set.Icc_subset_Icc le_rfl hn))
      (fun s hs => (hα m s ⟨hs.1, hs.2.trans hm⟩).mono
        (Set.Icc_subset_Icc le_rfl hm)) ⟨ht, le_rfl⟩
  let γ : ℝ → Space := fun t => α ⌈t⌉₊ t
  have agrees (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 ((n : ℝ) + 1)) : γ t = α n t :=
    coherent _ _ t ht.1 (by linarith [Nat.le_ceil t]) ht.2
  refine ⟨γ, ?_, fun t ht => ?_⟩
  · exact hα₀ _
  · obtain ⟨n, hn⟩ := exists_nat_gt t
    have htn : t < (n : ℝ) + 1 := by linarith
    have hmem : Set.Icc 0 ((n : ℝ) + 1) ∈ 𝓝[Set.Ici 0] t := by
      filter_upwards [self_mem_nhdsWithin,
        (nhdsWithin_le_nhds (Iio_mem_nhds htn))] with s hs hs'
      exact ⟨hs, hs'.le⟩
    have he := agrees n t ⟨ht, htn.le⟩
    rw [he]
    apply ((hα n t ⟨ht, htn.le⟩).mono_of_mem_nhdsWithin hmem).congr_of_eventuallyEq
    · filter_upwards [hmem] with s hs
      exact agrees n s hs
    · exact he

theorem global_material_flow (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) :
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory U a (X a)) ∧
      (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) := by
  classical
  choose X hX using global_trajectory U hU K hK hs
  exact ⟨X, hX, fun a γ hγ t ht => trajectory_unique U hU K hK hs a γ (X a) hγ (hX a) t ht⟩

end Analytic
end AlternatingNS

namespace AlternatingNS
namespace Construction

noncomputable def force (ν : ℝ) (M : Machine) (w : List ℕ) : Velocity :=
  residual ν (velocity M w)

theorem smooth_forced_simulation (ν : ℝ) (M : Machine) (hM : M.WellFormed)
    (w : List ℕ) (hw : M.ValidInput w) :
    Smooth (force ν M w) ∧ Smooth (velocity M w) ∧
    SupportedIn (force ν M w) Spatial.box ∧ SupportedIn (velocity M w) Spatial.box ∧
    NavierStokes ν (force ν M w) (velocity M w) (fun _ _ => 0) ∧
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory (velocity M w) a (X a)) ∧
      (∀ a γ, IsTrajectory (velocity M w) a γ → ∀ t, 0 ≤ t → γ t = X a t) ∧
      ((∃ t : ℝ, 0 ≤ t ∧ 0 < X observedParticle t 0) ↔ M.Halts w) := by
  have hU := velocity_smooth M w
  have hK := Spatial.box_compact
  have hs := velocity_supported M w
  refine ⟨Analytic.residual_smooth ν _ hU, hU.contDiffOn,
    fun t _ => Analytic.residual_supported ν _ _ hK.isClosed hs t,
    fun t _ => hs t,
    Analytic.residual_navierStokes ν _ hU (velocity_rest M w) (velocity_div M w), ?_⟩
  obtain ⟨X, hX, hu⟩ := Analytic.global_material_flow _ hU _ hK hs
  refine ⟨X, hX, hu, ?_⟩
  have he : ∀ t, 0 ≤ t → path M w t = X observedParticle t :=
    hu _ _ (path_isTrajectory M hM w hw)
  rw [← path_reachability M w]
  exact ⟨fun ⟨t, ht, hp⟩ => ⟨t, ht, by rw [he t ht]; exact hp⟩,
    fun ⟨t, ht, hp⟩ => ⟨t, ht, by rw [← he t ht]; exact hp⟩⟩

end Construction
end AlternatingNS
namespace AlternatingNS
namespace Analytic

noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def zeroExtend (K : Set Space) (g : C(K, E)) (x : Space) : E := by
  classical
  exact if hx : x ∈ K then g ⟨x, hx⟩ else 0

omit [NormedSpace ℝ E] in
lemma zeroExtend_memLp (K : Set Space) (hK : IsCompact K) (g : C(K, E)) :
    MemLp (zeroExtend K g) 2 (volume : Measure Space) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hm : StronglyMeasurable (zeroExtend K g) :=
    g.continuous.stronglyMeasurable.dite stronglyMeasurable_const hK.measurableSet
  have hs : HasCompactSupport (zeroExtend K g) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hx'
    exact hx (by simp [zeroExtend, hx'])
  apply hs.memLp_of_bound hm.aestronglyMeasurable ‖g‖
  filter_upwards [] with x
  by_cases hx : x ∈ K
  · simpa [zeroExtend, hx] using g.norm_coe_le_norm ⟨x, hx⟩
  · simp [zeroExtend, hx]

def compactToL2 (K : Set Space) (hK : IsCompact K) [CompactSpace K] :
    C(K, E) →L[ℝ] Lp E 2 (volume : Measure Space) := by
  classical
  let A : C(K, E) →ₗ[ℝ] Lp E 2 (volume : Measure Space) :=
    { toFun := fun g => (zeroExtend_memLp K hK g).toLp (zeroExtend K g)
      map_add' := by
        intro g h
        apply Lp.ext
        filter_upwards [(zeroExtend_memLp K hK (g + h)).coeFn_toLp,
          Lp.coeFn_add ((zeroExtend_memLp K hK g).toLp _) ((zeroExtend_memLp K hK h).toLp _),
          (zeroExtend_memLp K hK g).coeFn_toLp, (zeroExtend_memLp K hK h).coeFn_toLp]
          with x hx hx' hg hh
        simp only [hx, hx', Pi.add_apply, hg, hh]
        by_cases hk : x ∈ K <;> simp [zeroExtend, hk]
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [(zeroExtend_memLp K hK (c • g)).coeFn_toLp,
          Lp.coeFn_smul c ((zeroExtend_memLp K hK g).toLp _),
          (zeroExtend_memLp K hK g).coeFn_toLp] with x hx hx' hg
        simp only [RingHom.id_apply, hx, hx', Pi.smul_apply, hg]
        by_cases hk : x ∈ K <;> simp [zeroExtend, hk] }
  let B : Lp ℝ 2 (volume : Measure Space) :=
    indicatorConstLp 2 hK.measurableSet hK.measure_ne_top 1
  apply A.mkContinuous ‖B‖
  intro g
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul (g := B)
  filter_upwards [(zeroExtend_memLp K hK g).coeFn_toLp, indicatorConstLp_coeFn
    (p := 2) (hs := hK.measurableSet) (hμs := hK.measure_ne_top) (c := (1 : ℝ))] with x hx hb
  change ‖((zeroExtend_memLp K hK g).toLp _) x‖ ≤ _
  rw [hx, hb]
  by_cases hk : x ∈ K
  · simpa [zeroExtend, hk] using g.norm_coe_le_norm ⟨x, hk⟩
  · simp [zeroExtend, hk]

lemma compactToL2_coe (K : Set Space) (hK : IsCompact K) [CompactSpace K] (g : C(K, E)) :
    ∀ᵐ x ∂(volume : Measure Space), compactToL2 K hK g x = zeroExtend K g x :=
  (zeroExtend_memLp K hK g).coeFn_toLp

def onCompact (F : Field E) (hF : Continuous (Function.uncurry F)) (K : Set Space)
    (t : ℝ) : C(K, E) :=
  ⟨fun x => F t x, hF.comp (continuous_const.prodMk continuous_subtype_val)⟩

omit [NormedSpace ℝ E] in
lemma onCompact_continuous (F : Field E) (hF : Continuous (Function.uncurry F))
    (K : Set Space) : Continuous (onCompact F hF K) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

lemma compactToL2_onCompact (F : Field E) (hF : Continuous (Function.uncurry F))
    (K : Set Space) (hK : IsCompact K) [CompactSpace K]
    (hs : ∀ t, Function.support (F t) ⊆ K) (t : ℝ) :
    ∀ᵐ x ∂(volume : Measure Space), compactToL2 K hK (onCompact F hF K t) x = F t x := by
  classical
  filter_upwards [compactToL2_coe K hK (onCompact F hF K t)] with x hx
  rw [hx]
  by_cases hk : x ∈ K
  · simp only [zeroExtend, dite_eq_left hk]
    rfl
  · have hz : F t x = 0 := Function.notMem_support.1 (fun hx => hk (hs t hx))
    simp [zeroExtend, hk, hz]

lemma onCompact_hasDerivAt [CompleteSpace E] (F : Field E)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (K : Set Space) [CompactSpace K] (t : ℝ) :
    HasDerivAt (onCompact F hF.continuous K)
      (onCompact (fullDt F) (fullDt_smooth F hF).continuous K t) t := by
  let H := onCompact F hF.continuous K
  let G := onCompact (fullDt F) (fullDt_smooth F hF).continuous K
  have hG : Continuous G := onCompact_continuous _ _ _
  have he (s : ℝ) : H s = H 0 + ∫ r in (0 : ℝ)..s, G r := by
    ext x
    change F s x = F 0 x + (ContinuousMap.evalCLM ℝ x) (∫ r in (0 : ℝ)..s, G r)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm (hG.intervalIntegrable 0 s)]
    have hd (r : ℝ) : HasDerivAt (fun t => F t x) (fullDt F r x) r :=
      ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable
        (by simp) r).hasFDerivAt.hasDerivAt
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r (_ : r ∈ Set.uIcc 0 s) => hd r)
      (((fullDt_smooth F hF).continuous.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable 0 s)
    change F s x = F 0 x + ∫ r in (0 : ℝ)..s, fullDt F r x
    rw [hi]
    abel
  have h : HasDerivAt (fun s => H 0 + ∫ r in (0 : ℝ)..s, G r) (G t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 t)
      (hG.stronglyMeasurableAtFilter volume (𝓝 t)) hG.continuousAt).const_add (H 0)
  rwa [← funext he] at h

lemma iterate_dx_smooth (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (i : Fin 3) (n : ℕ) : ContDiff ℝ ∞ (Function.uncurry ((dx i)^[n] F)) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dx_smooth _ ih i

lemma spatial_smooth (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (α : MultiIndex) : ContDiff ℝ ∞ (Function.uncurry (spatial α F)) :=
  iterate_dx_smooth _ (iterate_dx_smooth _ (iterate_dx_smooth F hF 2 _) 1 _) 0 _

lemma iterate_dx_supported (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (i : Fin 3) (n : ℕ) :
    ∀ t, Function.support ((dx i)^[n] F t) ⊆ K := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact dx_supported _ K hK ih i

lemma spatial_supported (F : Field E) (K : Set Space) (hK : IsClosed K)
    (hs : ∀ t, Function.support (F t) ⊆ K) (α : MultiIndex) :
    ∀ t, Function.support (spatial α F t) ⊆ K :=
  iterate_dx_supported _ K hK
    (iterate_dx_supported _ K hK (iterate_dx_supported F K hK hs 2 _) 1 _) 0 _

lemma fullDt_supported (F : Field E) (K : Set Space)
    (hs : ∀ t, Function.support (F t) ⊆ K) :
    ∀ t, Function.support (fullDt F t) ⊆ K := by
  intro t x hx
  by_contra hk
  have he : (fun s => F s x) = fun _ => 0 := by
    funext s
    exact Function.notMem_support.1 (fun hx' => hk (hs s hx'))
  exact hx (by simp [fullDt, he])

lemma smooth_continuousInH (F : Field E) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (F t) ⊆ K)
    (k : ℕ) (T : ℝ) : ContinuousInH k F T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  intro α _
  let hα := (spatial_smooth F hF α).continuous
  refine ⟨fun t => compactToL2 K hK (onCompact (spatial α F) hα K t), ?_, ?_⟩
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · intro t _
    exact compactToL2_onCompact _ hα K hK (spatial_supported F K hK.isClosed hs α) t

lemma smooth_C1InL2 (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K)
    (T : ℝ) : C1InL2 U T := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let H := onCompact U hU.continuous K
  let G := onCompact (fullDt U) (fullDt_smooth U hU).continuous K
  refine ⟨fun t => compactToL2 K hK (H t), fun t => compactToL2 K hK (G t), ?_, ?_, ?_, ?_, ?_⟩
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · exact ((compactToL2 K hK).continuous.comp (onCompact_continuous _ _ K)).continuousOn
  · intro t _
    exact ((compactToL2 K hK).hasFDerivAt.comp_hasDerivAt t
      (onCompact_hasDerivAt U hU K t)).hasDerivWithinAt
  · intro t _
    exact compactToL2_onCompact U hU.continuous K hK hs t
  · intro t ht
    filter_upwards [compactToL2_onCompact (fullDt U) (fullDt_smooth U hU).continuous
      K hK (fullDt_supported U K hs) t] with x hx
    rw [hx, dt_eq_full U hU t ht.1]

theorem smooth_energyClass (U : Velocity) (hU : ContDiff ℝ ∞ (Function.uncurry U))
    (K : Set Space) (hK : IsCompact K) (hs : ∀ t, Function.support (U t) ⊆ K) :
    EnergyClass U (fun _ _ => 0) := by
  refine ⟨?_, ?_⟩
  · intro T _
    obtain ⟨C, hC⟩ := finite_bound U hU.continuous K hK hs T
    exact ⟨smooth_continuousInH U hU K hK hs 2 T, smooth_C1InL2 U hU K hK hs T,
      smooth_continuousInH (fun _ _ => (0 : ℝ)) contDiff_const K hK
        (fun _ => by simp) 1 T, C, hC⟩
  · intro T _
    obtain ⟨C, hC⟩ := finite_bound U hU.continuous K hK hs T
    obtain ⟨D, hD⟩ := finite_bound (fun t x => fderiv ℝ (U t) x)
      (spatial_fderiv_smooth U hU).continuous K hK
      (fun t => (support_fderiv_subset ℝ).trans (closure_minimal (hs t) hK.isClosed)) T
    exact ⟨C + D, fun t ht x => add_le_add (hC t ht x) (hD t ht x)⟩

end
end Analytic

namespace Construction

theorem velocity_energyClass (M : Machine) (w : List ℕ) :
    EnergyClass (velocity M w) (fun _ _ => 0) :=
  Analytic.smooth_energyClass _ (velocity_smooth M w) _ Spatial.box_compact (velocity_supported M w)

end Construction
end AlternatingNS

end OAI
