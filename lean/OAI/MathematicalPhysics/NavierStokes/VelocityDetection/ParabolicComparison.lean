import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Model
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.UniformDerivatives

namespace OAI

noncomputable section
namespace VelocityDetection.ParabolicComparison
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators

theorem second_deriv_nonneg {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra hn
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge hn
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmin, hmax] with y hy₁ hy₂
    exact le_antisymm hy₂ hy₁
  have hz : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  linarith

theorem deriv_nonpos_at_past_min {f : ℝ → ℝ} {t f' : ℝ} (ht : 0 < t)
    (hf : HasDerivAt f f' t) (hmin : ∀ s ∈ Icc 0 t, f t ≤ f s) : f' ≤ 0 := by
  apply le_of_tendsto (hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE t))
  filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds ht), self_mem_nhdsWithin] with s hs hs'
  change s < t at hs'
  have ha := hmin s ⟨hs.le, hs'.le⟩
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) (sub_nonpos.mpr hs'.le)

def UniformTails {n : ℕ} (ρ : ScalarField n) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε → ∃ K : Set (Coord n), IsCompact K ∧
    ∀ t ∈ Icc (0 : ℝ) T, ∀ X ∉ K, |ρ t X| < ε

end VelocityDetection.ParabolicComparison
end

noncomputable section
namespace VelocityDetection.ParabolicComparison
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped ZeroAtInfty

theorem compact_C0_uniform_tails {E : Type*} [TopologicalSpace E]
    {S : Set C₀(E, ℝ)} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set E, IsCompact K ∧ ∀ f ∈ S, ∀ X ∉ K, |f X| < ε := by
  classical
  obtain ⟨A, _, hA, hcover⟩ := hS.finite_cover_balls (half_pos hε)
  have ht (f : C₀(E, ℝ)) : ∃ K : Set E, IsCompact K ∧
      ∀ X ∉ K, |f X| < ε / 2 := by
    have hh := Metric.tendsto_nhds.mp (zero_at_infty f) (ε / 2) (half_pos hε)
    obtain ⟨K, hK, hKsub⟩ := Filter.mem_cocompact.mp hh
    refine ⟨K, hK, fun X hX => ?_⟩
    simpa only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero] using hKsub hX
  choose K hK htail using ht
  refine ⟨⋃ f ∈ A, K f, hA.isCompact_biUnion (fun f _ => hK f), ?_⟩
  intro f hf X hX
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hcover hf)
  have hXg : X ∉ K g := fun hh => hX (mem_iUnion₂.mpr ⟨g, hg, hh⟩)
  have hdist : dist (f X) (g X) < ε / 2 :=
    (BoundedContinuousFunction.dist_coe_le_dist X).trans_lt (Metric.mem_ball.mp hfg)
  have hgt := htail g X hXg
  calc
    |f X| = |f X - g X + g X| := by rw [sub_add_cancel]
    _ ≤ |f X - g X| + |g X| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hdist hgt
    _ = ε := add_halves ε

theorem uniformTails_of_continuous_C0 {n : ℕ} (ρ : ℝ → C₀(Coord n, ℝ))
    (hρ : ContinuousOn ρ (Ici 0)) :
    UniformTails (fun t X => ρ t X) := by
  intro T hT ε hε
  obtain ⟨K, hK, ht⟩ := compact_C0_uniform_tails
    (isCompact_Icc.image_of_continuousOn (hρ.mono (fun _ ht => ht.1))) hε
  exact ⟨K, hK, fun t ht' X hX => ht (ρ t) (mem_image_of_mem ρ ht') X hX⟩

theorem spatialD_twice_eq_deriv {n : ℕ} (ρ : ScalarField n) (i : Fin n)
    (t : ℝ) (X : Coord n) :
    spatialD i (spatialD i ρ) t X =
      deriv (deriv (fun s => ρ t (update X i s))) (X i) := by
  simp only [spatialD, update_idem, update_self]

theorem spatial_minimum {n : ℕ} {ρ : ScalarField n} {t : ℝ} {X : Coord n}
    (hρ : Continuous (ρ t)) (hmin : ∀ Y, ρ t X ≤ ρ t Y) :
    (∀ i, spatialD i ρ t X = 0) ∧ 0 ≤ laplacian ρ t X := by
  have hm (i : Fin n) : IsLocalMin (fun s => ρ t (update X i s)) (X i) := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [update_eq_self] using hmin (update X i s)
  refine ⟨fun i => (hm i).deriv_eq_zero, ?_⟩
  unfold laplacian
  apply Finset.sum_nonneg
  intro i _
  rw [spatialD_twice_eq_deriv]
  exact second_deriv_nonneg (hm i) (hρ.comp (by fun_prop : Continuous (fun s => update X i s))).continuousAt

theorem nonnegative_of_uniformTails {n : ℕ} {ν : ℝ} {a : VectorField n}
    {g ρ : ScalarField n} (hν : 0 ≤ ν) (hρ : ContDiff ℝ 2 (uncurry ρ))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection a ρ t X = ν * laplacian ρ t X + g t X)
    (hinit : ∀ X, 0 ≤ ρ 0 X) (hg : ∀ t, 0 ≤ t → ∀ X, 0 ≤ g t X)
    (htails : UniformTails ρ) : ∀ t, 0 ≤ t → ∀ X, 0 ≤ ρ t X := by
  intro T hT X
  by_contra hneg
  have hvneg : ρ T X < 0 := lt_of_not_ge hneg
  let ε : ℝ := -ρ T X / (2 * (1 + T))
  have hε : 0 < ε := div_pos (neg_pos.mpr hvneg) (by linarith)
  have hmul : ε * (1 + T) = -ρ T X / 2 := by
    dsimp [ε]
    field_simp
  let v : ℝ × Coord n → ℝ := fun q => ρ q.1 q.2 + ε * (1 + q.1)
  have hv : v (T, X) < 0 := by
    dsimp [v]
    rw [hmul]
    linarith
  obtain ⟨K, hK, houtside⟩ := htails T hT ε hε
  let K' := insert X K
  have hK' : IsCompact K' := hK.insert X
  have hvc : Continuous v := hρ.continuous.add
    (continuous_const.mul (continuous_const.add continuous_fst))
  obtain ⟨q, hq, hmin⟩ := (isCompact_Icc.prod hK').exists_isMinOn
    ⟨(T, X), ⟨⟨hT, le_rfl⟩, mem_insert X K⟩⟩ hvc.continuousOn
  have hqneg : v q < 0 := (hmin ⟨⟨hT, le_rfl⟩, mem_insert X K⟩).trans_lt hv
  have ht0 : 0 < q.1 := by
    apply lt_of_le_of_ne hq.1.1
    intro he
    have hh := hinit q.2
    have he' : q.1 = 0 := he.symm
    dsimp [v] at hqneg
    rw [he'] at hqneg
    nlinarith
  have hminX : ∀ Y, ρ q.1 q.2 ≤ ρ q.1 Y := by
    intro Y
    have hh : v q ≤ v (q.1, Y) := by
      by_cases hY : Y ∈ K'
      · exact hmin ⟨hq.1, hY⟩
      · have hYK : Y ∉ K := fun h => hY (mem_insert_of_mem X h)
        have hsmall := houtside q.1 hq.1 Y hYK
        have hlow : -ε < ρ q.1 Y := (abs_lt.mp hsmall).1
        have hpos : 0 < v (q.1, Y) := by
          dsimp [v]
          nlinarith [mul_nonneg hε.le hq.1.1]
        exact hqneg.le.trans hpos.le
    dsimp [v] at hh
    linarith
  have hρq : Continuous (ρ q.1) :=
    hρ.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨hgrad, hlap⟩ := spatial_minimum hρq hminX
  have hadv : advection a ρ q.1 q.2 = 0 := by
    simp only [advection, hgrad, mul_zero, Finset.sum_const_zero]
  have htime : HasDerivAt (fun s => v (s, q.2))
      (deriv (fun s => ρ s q.2) q.1 + ε) q.1 := by
    have hd : Differentiable ℝ (fun s => ρ s q.2) :=
      (hρ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)
    have heps := (((hasDerivAt_const q.1 (1 : ℝ)).add (hasDerivAt_id q.1)).const_mul ε)
    simpa only [v, Pi.add_def, id_eq, zero_add, mul_one] using (hd q.1).hasDerivAt.add heps
  have htimemin : ∀ s ∈ Icc 0 q.1, v (q.1, q.2) ≤ v (s, q.2) := by
    intro s hs
    exact hmin ⟨⟨hs.1, hs.2.trans hq.1.2⟩, hq.2⟩
  have hnonpos := deriv_nonpos_at_past_min ht0 htime htimemin
  have hpde := heq q.1 ht0.le q.2
  rw [hadv] at hpde
  have hsource := hg q.1 ht0.le q.2
  nlinarith [mul_nonneg hν hlap]

theorem nonnegative_of_continuous_C0 {n : ℕ} {ν : ℝ} {a : VectorField n}
    {g : ScalarField n} (ρ : ℝ → C₀(Coord n, ℝ)) (hν : 0 ≤ ν)
    (hc : ContinuousOn ρ (Ici 0))
    (hρ : ContDiff ℝ 2 (fun q : ℝ × Coord n => ρ q.1 q.2))
    (heq : ∀ t, 0 ≤ t → ∀ X,
      deriv (fun s => ρ s X) t + advection a (fun s Y => ρ s Y) t X =
        ν * laplacian (fun s Y => ρ s Y) t X + g t X)
    (hinit : ∀ X, 0 ≤ ρ 0 X) (hg : ∀ t, 0 ≤ t → ∀ X, 0 ≤ g t X) :
    ∀ t, 0 ≤ t → ∀ X, 0 ≤ ρ t X :=
  nonnegative_of_uniformTails hν hρ heq hinit hg (uniformTails_of_continuous_C0 ρ hc)

end VelocityDetection.ParabolicComparison
end

end OAI
