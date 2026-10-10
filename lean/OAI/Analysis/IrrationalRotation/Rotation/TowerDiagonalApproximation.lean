import OAI.Analysis.IrrationalRotation.Rotation.RotationLInfinity
import OAI.Analysis.IrrationalRotation.Rotation.RotationSetProjections

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.Rotation.TowerDiagonalApproximation

private def indicatorClass (s : Set Circle) (hs : MeasurableSet s) :
    Lp ℂ ∞ circleMeasure :=
  indicatorConstLp ∞ hs (measure_ne_top circleMeasure s) (1 : ℂ)

private theorem setProjection_eq_representation (θ : ℝ) (s : Set Circle)
    (hs : MeasurableSet s) :
    setProjection θ s hs = lInfinityRepresentation θ (indicatorClass s hs) := by
  symm
  apply lInfinityRepresentation_eq_measurable_of_ae
  exact indicatorConstLp_coeFn

private theorem coe_sum_ae {ι : Type*} (t : Finset ι)
    (a : ι → Lp ℂ ∞ circleMeasure) :
    (fun x => (∑ i ∈ t, a i) x) =ᵐ[circleMeasure] fun x => ∑ i ∈ t, a i x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Lp.coeFn_zero ℂ ∞ circleMeasure
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (a i) (∑ j ∈ t, a j), ih] with x hx hsum
      simpa only [Pi.add_apply, hsum] using hx

private theorem step_coe_ae {ι : Type*} [Fintype ι]
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i)) (c : ι → ℂ) :
    (fun x => (∑ i, c i • indicatorClass (s i) (hs i)) x) =ᵐ[circleMeasure]
      fun x => ∑ i, (s i).indicator (fun _ => c i) x := by
  classical
  have hi : ∀ i, (c i • indicatorClass (s i) (hs i)) =ᵐ[circleMeasure]
      (s i).indicator (fun _ => c i) := by
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (indicatorClass (s i) (hs i)),
      indicatorConstLp_coeFn (p := ∞) (μ := circleMeasure) (hs := hs i)
        (hμs := measure_ne_top circleMeasure (s i)) (c := (1 : ℂ))] with x hx hxind
    rw [hx]
    change c i * indicatorClass (s i) (hs i) x = _
    change indicatorClass (s i) (hs i) x = _ at hxind
    rw [hxind]
    by_cases hxs : x ∈ s i <;> simp [Set.indicator, hxs]
  filter_upwards [coe_sum_ae Finset.univ (fun i => c i • indicatorClass (s i) (hs i)),
    ae_all_iff.mpr hi] with x hx hxi
  exact hx.trans (Finset.sum_congr rfl (fun i _ => hxi i))

private theorem sum_setProjection_eq {ι : Type*} [Fintype ι] (θ : ℝ)
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i)) (c : ι → ℂ) :
    (∑ i, c i • setProjection θ (s i) (hs i)) =
      lInfinityRepresentation θ (∑ i, c i • indicatorClass (s i) (hs i)) := by
  simp_rw [setProjection_eq_representation]
  change (∑ i, c i • lInfinityRepresentationCLM θ (indicatorClass (s i) (hs i))) =
    lInfinityRepresentationCLM θ (∑ i, c i • indicatorClass (s i) (hs i))
  simp only [map_sum, map_smul]

theorem norm_sum_setProjection_sub_representation_le
    {ι : Type*} [Fintype ι] (θ : ℝ)
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hpartition : ∀ x : Circle, ∃! i, x ∈ s i)
    (c : ι → ℂ) (a : C(Circle, ℂ)) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ i x, x ∈ s i → ‖c i - a x‖ ≤ ε) :
    ‖(∑ i, c i • setProjection θ (s i) (hs i)) - representation θ a‖ ≤ ε := by
  classical
  let b : Lp ℂ ∞ circleMeasure := ∑ i, c i • indicatorClass (s i) (hs i)
  have hb : ‖b - ContinuousMap.toLp ∞ circleMeasure ℂ a‖ ≤ ε := by
    have hbound : ∀ᵐ x ∂circleMeasure,
        ‖(b - ContinuousMap.toLp ∞ circleMeasure ℂ a) x‖ ≤ ε := by
      filter_upwards [Lp.coeFn_sub b (ContinuousMap.toLp ∞ circleMeasure ℂ a),
        step_coe_ae s hs c, ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) circleMeasure a]
        with x hx hstep ha
      obtain ⟨i, hxi, huniq⟩ := hpartition x
      have hsum : (∑ j, (s j).indicator (fun _ => c j) x) = c i := by
        rw [Finset.sum_eq_single i]
        · exact Set.indicator_of_mem hxi _
        · intro j _ hji
          exact Set.indicator_of_notMem (fun hxj => hji (huniq j hxj)) _
        · simp
      change b x = _ at hstep
      simpa only [hx, Pi.sub_apply, hstep, hsum, ha] using happrox i x hxi
    have h := Lp.norm_le_of_ae_bound hε hbound
    simpa using h
  rw [sum_setProjection_eq, ← lInfinityRepresentation_continuous θ a]
  change ‖lInfinityRepresentationCLM θ b -
    lInfinityRepresentationCLM θ (ContinuousMap.toLp ∞ circleMeasure ℂ a)‖ ≤ ε
  rw [← map_sub]
  exact (norm_lInfinityRepresentation_le θ _).trans hb

theorem sum_setProjection_mem {ι : Type*} [Fintype ι] (θ : ℝ)
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i)) (c : ι → ℂ)
    (A : StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert))
    (hA : ∀ i, setProjection θ (s i) (hs i) ∈ A) :
    (∑ i, c i • setProjection θ (s i) (hs i)) ∈ A := by
  exact A.sum_mem (fun i _ => A.smul_mem (hA i) (c i))

theorem exists_coefficients_of_small_oscillation
    {ι : Type*} [Fintype ι] (θ : ℝ)
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hpartition : ∀ x : Circle, ∃! i, x ∈ s i)
    (a : C(Circle, ℂ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ i x y, x ∈ s i → y ∈ s i → ‖a x - a y‖ ≤ ε) :
    ∃ c : ι → ℂ, (∀ i, ‖c i‖ ≤ ‖a‖) ∧
      ‖(∑ i, c i • setProjection θ (s i) (hs i)) - representation θ a‖ ≤ ε := by
  classical
  let c : ι → ℂ := fun i => if h : (s i).Nonempty then a h.choose else 0
  have hc (i : ι) (x : Circle) (hx : x ∈ s i) :
      ‖c i - a x‖ ≤ ε := by
    have hi : (s i).Nonempty := ⟨x, hx⟩
    simpa only [c, dite_eq_left hi] using hosc i hi.choose x hi.choose_spec hx
  refine ⟨c, ?_, norm_sum_setProjection_sub_representation_le θ s hs hpartition c a hε hc⟩
  intro i
  by_cases hi : (s i).Nonempty
  · simpa only [c, dite_eq_left hi] using a.norm_coe_le_norm hi.choose
  · simp only [c, dite_eq_right hi, norm_zero]
    exact norm_nonneg a

theorem exists_mesh_for_norm_approximation
    {ι : Type*} [Fintype ι] (θ : ℝ) (a : C(Circle, ℂ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i)),
      (∀ x : Circle, ∃! i, x ∈ s i) →
      (∀ i x y, x ∈ s i → y ∈ s i → dist x y < δ) →
      ∃ c : ι → ℂ, (∀ i, ‖c i‖ ≤ ‖a‖) ∧
        ‖(∑ i, c i • setProjection θ (s i) (hs i)) - representation θ a‖ ≤ ε := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous a.continuous) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs hp hmesh
  apply exists_coefficients_of_small_oscillation θ s hs hp a hε.le
  intro i x y hx hy
  simpa only [dist_eq_norm] using (hmod (hmesh i x y hx hy)).le

theorem tendsto_sum_setProjection_of_error
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (θ : ℝ)
    (s : ∀ n, ι n → Set Circle) (hs : ∀ n i, MeasurableSet (s n i))
    (hpartition : ∀ n x, ∃! i, x ∈ s n i)
    (c : ∀ n, ι n → ℂ) (a : C(Circle, ℂ)) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ n i x, x ∈ s n i → ‖c n i - a x‖ ≤ ε n) :
    Tendsto (fun n => ∑ i, c n i • setProjection θ (s n i) (hs n i))
      atTop (𝓝 (representation θ a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun n => norm_sum_setProjection_sub_representation_le θ (s n) (hs n)
      (hpartition n) (c n) a (hε n) (happrox n)) hεlim

theorem tendsto_sum_setProjection_apply_of_error
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (θ : ℝ)
    (s : ∀ n, ι n → Set Circle) (hs : ∀ n i, MeasurableSet (s n i))
    (hpartition : ∀ n x, ∃! i, x ∈ s n i)
    (c : ∀ n, ι n → ℂ) (a : C(Circle, ℂ)) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (happrox : ∀ n i x, x ∈ s n i → ‖c n i - a x‖ ≤ ε n)
    (v : Hilbert) :
    Tendsto (fun n => (∑ i, c n i • setProjection θ (s n i) (hs n i)) v)
      atTop (𝓝 (representation θ a v)) := by
  exact ((ContinuousLinearMap.apply ℂ Hilbert v).continuous.continuousAt.tendsto).comp
    (tendsto_sum_setProjection_of_error ι θ s hs hpartition c a ε hε hεlim happrox)

theorem norm_sum_setProjection_le
    {ι : Type*} [Fintype ι] (θ : ℝ)
    (s : ι → Set Circle) (hs : ∀ i, MeasurableSet (s i))
    (hpartition : ∀ x : Circle, ∃! i, x ∈ s i)
    (c : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    ‖∑ i, c i • setProjection θ (s i) (hs i)‖ ≤ C := by
  have h := norm_sum_setProjection_sub_representation_le θ s hs hpartition c
    (0 : C(Circle, ℂ)) hC (fun i x _ => by simpa using hc i)
  simpa only [representation_zero, sub_zero] using h

theorem exists_contractive_V_approximants
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (θ : ℝ)
    (s : ∀ n, ι n → Set Circle) (hs : ∀ n i, MeasurableSet (s n i))
    (hpartition : ∀ n x, ∃! i, x ∈ s n i)
    (hmesh : ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ i x y, x ∈ s n i → y ∈ s n i → dist x y < δ)
    (A : ℕ → StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert))
    (hA : ∀ n i, setProjection θ (s n i) (hs n i) ∈ A n) :
    ∃ B : ℕ → Hilbert →L[ℂ] Hilbert,
      (∀ n, B n ∈ A n) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
      Tendsto B atTop (𝓝 (V θ)) ∧
      (∀ v : Hilbert, Tendsto (fun n => B n v) atTop (𝓝 (V θ v))) := by
  classical
  let c : ∀ n, ι n → ℂ := fun n i =>
    if h : (s n i).Nonempty then character h.choose else 0
  let B : ℕ → Hilbert →L[ℂ] Hilbert :=
    fun n => ∑ i, c n i • setProjection θ (s n i) (hs n i)
  have hc (n : ℕ) (i : ι n) : ‖c n i‖ ≤ 1 := by
    by_cases hi : (s n i).Nonempty
    · simp only [c, dite_eq_left hi, character_norm, le_refl]
    · simp only [c, dite_eq_right hi, norm_zero, zero_le_one]
  have hBnorm (n : ℕ) : ‖B n‖ ≤ 1 :=
    norm_sum_setProjection_le θ (s n) (hs n) (hpartition n) (c n) zero_le_one (hc n)
  have hlim : Tendsto B atTop (𝓝 (V θ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous character.continuous)
      (ε / 2) (half_pos hε)
    filter_upwards [hmesh δ hδ] with n hn
    have hb : ‖B n - representation θ character‖ ≤ ε / 2 := by
      apply norm_sum_setProjection_sub_representation_le θ (s n) (hs n)
        (hpartition n) (c n) character (half_pos hε).le
      intro i x hx
      have hi : (s n i).Nonempty := ⟨x, hx⟩
      have hdist := hmod (hn i hi.choose x hi.choose_spec hx)
      simpa only [c, dite_eq_left hi, dist_eq_norm] using hdist.le
    have hb' : dist (B n) (V θ) ≤ ε / 2 := by
      simpa only [dist_eq_norm, V] using hb
    exact hb'.trans_lt (half_lt_self hε)
  refine ⟨B, fun n => sum_setProjection_mem θ (s n) (hs n) (c n) (A n) (hA n),
    hBnorm, hlim, ?_⟩
  intro v
  exact ((ContinuousLinearMap.apply ℂ Hilbert v).continuous.continuousAt.tendsto).comp hlim

theorem exists_contractive_V_approximants_of_tower_levels
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (θ : ℝ)
    (s : ∀ n, ι n → Set Circle) (hs : ∀ n i, MeasurableSet (s n i))
    (hpartition : ∀ n x, ∃! i, x ∈ s n i)
    (base : ℕ → Set Circle) (b : ∀ n, ι n → Set Circle)
    (k : ∀ n, ι n → ℤ)
    (hsub : ∀ n i, b n i ⊆ base n)
    (hlevel : ∀ n i, s n i = action θ (k n i) '' b n i)
    (hbase : ∀ δ > 0, ∀ᶠ n in atTop,
      ∀ x ∈ base n, ∀ y ∈ base n, dist x y < δ)
    (A : ℕ → StarSubalgebra ℂ (Hilbert →L[ℂ] Hilbert))
    (hA : ∀ n i, setProjection θ (s n i) (hs n i) ∈ A n) :
    ∃ B : ℕ → Hilbert →L[ℂ] Hilbert,
      (∀ n, B n ∈ A n) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
      Tendsto B atTop (𝓝 (V θ)) ∧
      (∀ v : Hilbert, Tendsto (fun n => B n v) atTop (𝓝 (V θ v))) := by
  apply exists_contractive_V_approximants ι θ s hs hpartition _ A hA
  intro δ hδ
  filter_upwards [hbase δ hδ] with n hn
  intro i x y hx hy
  rw [hlevel] at hx hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  simpa only [action, dist_add_right] using hn u (hsub n i hu) v (hsub n i hv)

end Invariant233.Rotation.TowerDiagonalApproximation

end

end OAI
