import Mathlib

namespace OAI

/-! Existence estimates for closed Hilbert-space operators and radial cutoff energy. -/

noncomputable section
open Bundle Set Filter
open scoped Manifold Bundle Topology BoundedContinuousFunction

open scoped ComplexConjugate
open LinearPMap

namespace NadelHilbert

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

 

lemma mem_graph_of_adjoint_pairing
    (T : E →ₗ.[ℂ] F) (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (u : E) (f : F)
    (hpair : ∀ v : T.adjoint.domain,
      inner ℂ u (T.adjoint v) = inner ℂ f (v : F)) :
    ∃ x : T.domain, (x : E) = u ∧ T x = f := by
  let G : Submodule ℂ (WithLp 2 (E × F)) :=
    T.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  have hGclosed : IsClosed (G : Set (WithLp 2 (E × F))) :=
    hTclosed.preimage (WithLp.prod_continuous_ofLp 2 E F)
  have hGdouble : G.orthogonal.orthogonal = G := by
    rw [Submodule.orthogonal_orthogonal_eq_closure,
      hGclosed.submodule_topologicalClosure_eq]
  have hz : WithLp.toLp 2 (u, f) ∈ G := by
    rw [← hGdouble]
    apply (Submodule.mem_orthogonal' _ _).2
    intro v hv
    have hinner (x : T.domain) :
        inner ℂ v.ofLp.1 (x : E) + inner ℂ v.ofLp.2 (T x) = 0 := by
      have hx : WithLp.toLp 2 ((x : E), T x) ∈ G := by
        change ((x : E), T x) ∈ T.graph
        exact T.mem_graph_iff.mpr ⟨x, rfl, rfl⟩
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp] using
        (G.mem_orthogonal' v).mp hv _ hx
    have hadjpair : ∀ x : T.domain,
        inner ℂ (-v.ofLp.1) (x : E) = inner ℂ v.ofLp.2 (T x) := by
      intro x
      rw [inner_neg_left]
      linear_combination - (hinner x)
    have hvdom : v.ofLp.2 ∈ T.adjoint.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨-v.ofLp.1, hadjpair⟩
    have hadj : T.adjoint ⟨v.ofLp.2, hvdom⟩ = -v.ofLp.1 :=
      LinearPMap.adjoint_apply_eq hTdense _ hadjpair
    have hh := hpair ⟨v.ofLp.2, hvdom⟩
    rw [hadj, inner_neg_right] at hh
    simp only [WithLp.prod_inner_apply]
    rw [← hh]
    exact add_neg_cancel _
  change (u, f) ∈ T.graph at hz
  exact T.mem_graph_iff.mp hz

 

theorem exists_solution_of_adjoint_estimate
    (T : E →ₗ.[ℂ] F) (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (f : F) (C : ℝ) (hC : 0 ≤ C)
    (hest : ∀ v : T.adjoint.domain,
      ‖inner ℂ f (v : F)‖ ≤ C * ‖T.adjoint v‖) :
    ∃ u : T.domain, T u = f ∧ ‖(u : E)‖ ≤ C := by
  let A : T.adjoint.domain →ₗ[ℂ] E := T.adjoint.toFun
  let b : T.adjoint.domain →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ f).comp T.adjoint.domain.subtype
  have hker : A.ker ≤ b.ker := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    have hAv : T.adjoint v = 0 := LinearMap.mem_ker.mp hv
    change ‖inner ℂ f (v : F)‖ ≤ 0
    simpa only [hAv, norm_zero, mul_zero] using hest v
  let l : A.range →ₗ[ℂ] ℂ :=
    (A.ker.liftQ b hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hl (v : T.adjoint.domain) (hv : A v ∈ A.range) :
      l ⟨A v, hv⟩ = inner ℂ f (v : F) := by
    dsimp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hlbound (y : A.range) : ‖l y‖ ≤ C * ‖y‖ := by
    obtain ⟨v, hv⟩ := y.property
    have hy : y = ⟨A v, LinearMap.mem_range_self A v⟩ := Subtype.ext hv.symm
    rw [hy, hl]
    exact hest v
  let L : StrongDual ℂ A.range := l.mkContinuous C hlbound
  obtain ⟨L', hL', hnorm⟩ := exists_extension_norm_eq A.range L
  let u : E := (InnerProductSpace.toDual ℂ E).symm L'
  have hupair (v : T.adjoint.domain) :
      inner ℂ u (T.adjoint v) = inner ℂ f (v : F) := by
    change inner ℂ ((InnerProductSpace.toDual ℂ E).symm L') (A v) = _
    rw [InnerProductSpace.toDual_symm_apply]
    rw [hL' ⟨A v, LinearMap.mem_range_self A v⟩]
    exact hl v _
  have hunorm : ‖u‖ ≤ C := by
    calc
      ‖u‖ = ‖L'‖ := (InnerProductSpace.toDual ℂ E).symm.norm_map L'
      _ = ‖L‖ := hnorm
      _ ≤ C := l.mkContinuous_norm_le hC hlbound
  obtain ⟨x, hx, hTx⟩ := mem_graph_of_adjoint_pairing T hTdense hTclosed u f hupair
  exact ⟨x, hTx, hx ▸ hunorm⟩

variable {G : Type*}
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

 
def closedKernel (S : F →ₗ.[ℂ] G) : Submodule ℂ F :=
  S.graph.comap ((LinearMap.id : F →ₗ[ℂ] F).prod (0 : F →ₗ[ℂ] G))

omit [CompleteSpace F] [CompleteSpace G] in
lemma mem_closedKernel_iff (S : F →ₗ.[ℂ] G) (v : F) :
    v ∈ closedKernel S ↔ ∃ hv : v ∈ S.domain, S ⟨v, hv⟩ = 0 := by
  change (v, 0) ∈ S.graph ↔ _
  rw [S.mem_graph_iff]
  constructor
  · rintro ⟨x, rfl, hx⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hv, hSv⟩
    exact ⟨⟨v, hv⟩, rfl, hSv⟩

omit [CompleteSpace F] [CompleteSpace G] in
lemma isClosed_closedKernel (S : F →ₗ.[ℂ] G) (hS : S.IsClosed) :
    IsClosed (closedKernel S : Set F) :=
  hS.preimage (continuous_id.prodMk continuous_const)

 

omit [CompleteSpace G] in
theorem exists_solution_of_complex_estimate
    (T : E →ₗ.[ℂ] F) (S : F →ₗ.[ℂ] G)
    (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (hSclosed : S.IsClosed)
    (hcomplex : ∀ u : T.domain, ∃ hv : T u ∈ S.domain, S ⟨T u, hv⟩ = 0)
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ v : T.adjoint.domain, ∀ hv : (v : F) ∈ S.domain,
      c * ‖(v : F)‖ ^ 2 ≤ ‖T.adjoint v‖ ^ 2 + ‖S ⟨(v : F), hv⟩‖ ^ 2)
    (f : S.domain) (hf : S f = 0) :
    ∃ u : T.domain, T u = (f : F) ∧ ‖(u : E)‖ ≤ ‖(f : F)‖ / Real.sqrt c := by
  let K := closedKernel S
  have hKclosed : IsClosed (K : Set F) := isClosed_closedKernel S hSclosed
  let : CompleteSpace K := hKclosed.completeSpace_coe
  have hfK : (f : F) ∈ K := (mem_closedKernel_iff S _).mpr ⟨f.property, hf⟩
  have hTK (u : T.domain) : T u ∈ K := (mem_closedKernel_iff S _).mpr (hcomplex u)
  apply exists_solution_of_adjoint_estimate T hTdense hTclosed (f : F)
    (‖(f : F)‖ / Real.sqrt c) (by positivity)
  intro v
  let p := K.starProjection (v : F)
  have hpK : p ∈ K := K.starProjection_apply_mem _
  have hpair (u : T.domain) : inner ℂ (T.adjoint v) (u : E) = inner ℂ p (T u) := by
    have hzero := K.starProjection_inner_eq_zero (v : F) (T u) (hTK u)
    rw [inner_sub_left] at hzero
    exact (T.adjoint_isFormalAdjoint hTdense v u).trans (sub_eq_zero.mp hzero)
  have hpdom : p ∈ T.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists p ⟨T.adjoint v, hpair⟩
  have hpadj : T.adjoint ⟨p, hpdom⟩ = T.adjoint v :=
    LinearPMap.adjoint_apply_eq hTdense _ hpair
  obtain ⟨hpS, hpzero⟩ := (mem_closedKernel_iff S p).mp hpK
  have hbound := hcoercive ⟨p, hpdom⟩ hpS
  simp only [hpadj, hpzero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hbound
  have hsquare : (Real.sqrt c * ‖p‖) ^ 2 ≤ ‖T.adjoint v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc.le]
    exact hbound
  have hnorm : ‖p‖ ≤ ‖T.adjoint v‖ / Real.sqrt c := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hc)).mpr
    rw [mul_comm]
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsquare
  have hfpair : inner ℂ (f : F) (v : F) = inner ℂ (f : F) p := by
    change inner ℂ (f : F) (v : F) = inner ℂ (f : F) (K.starProjection (v : F))
    rw [← K.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hfK]
  rw [hfpair]
  calc
    ‖inner ℂ (f : F) p‖ ≤ ‖(f : F)‖ * ‖p‖ := norm_inner_le_norm _ _
    _ ≤ ‖(f : F)‖ * (‖T.adjoint v‖ / Real.sqrt c) :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = (‖(f : F)‖ / Real.sqrt c) * ‖T.adjoint v‖ := by ring

 

theorem exists_solution_with_all_bounds
    (T : E →ₗ.[ℂ] F) (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (f : F) (B : ℝ) (A : ℕ → E →L[ℂ] G) (C : ℕ → ℝ)
    (hC : ∀ i, 0 ≤ C i)
    (hfinite : ∀ n, ∃ u : T.domain, T u = f ∧ ‖(u : E)‖ ≤ B ∧
      ∀ i ≤ n, ‖A i (u : E)‖ ≤ C i) :
    ∃ u : T.domain, T u = f ∧ ‖(u : E)‖ ≤ B ∧ ∀ i, ‖A i (u : E)‖ ≤ C i := by
  let ball : Set (WeakDual ℂ E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ E) B
  let eqs : Set (WeakDual ℂ E) :=
    {L | ∀ v : T.adjoint.domain, L (T.adjoint v) = inner ℂ f (v : F)}
  let bounds (n : ℕ) : Set (WeakDual ℂ E) :=
    {L | ∀ i ≤ n, ∀ v : G, ‖L ((A i).adjoint v)‖ ≤ C i * ‖v‖}
  let K (n : ℕ) := ball ∩ eqs ∩ bounds n
  have heqs : IsClosed eqs := by
    simp only [eqs, Set.ofPred_forall]
    exact isClosed_iInter fun v =>
      isClosed_eq (WeakDual.eval_continuous (T.adjoint v)) continuous_const
  have hbounds (n : ℕ) : IsClosed (bounds n) := by
    simp only [bounds, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_iInter fun v =>
      isClosed_le (WeakDual.eval_continuous ((A i).adjoint v)).norm continuous_const
  have hKclosed (n : ℕ) : IsClosed (K n) :=
    ((WeakDual.isClosed_closedBall 0 B).inter heqs).inter (hbounds n)
  have hKcompact : IsCompact (K 0) :=
    (WeakDual.isCompact_closedBall (0 : StrongDual ℂ E) B).of_isClosed_subset
      (hKclosed 0) (fun _ h => h.1.1)
  have hdec (n : ℕ) : K (n + 1) ⊆ K n := by
    rintro L ⟨hL, hboundsL⟩
    exact ⟨hL, fun i hi => hboundsL i (hi.trans (Nat.le_succ n))⟩
  have hnonempty (n : ℕ) : (K n).Nonempty := by
    obtain ⟨u, hTu, hu, hAu⟩ := hfinite n
    let L := StrongDual.toWeakDual (InnerProductSpace.toDual ℂ E (u : E))
    refine ⟨L, ⟨?_, ?_⟩, ?_⟩
    · change InnerProductSpace.toDual ℂ E (u : E) ∈ Metric.closedBall 0 B
      simpa only [Metric.mem_closedBall, dist_zero_right,
        (InnerProductSpace.toDual ℂ E).norm_map] using hu
    · intro v
      change inner ℂ (u : E) (T.adjoint v) = inner ℂ f (v : F)
      rw [← hTu]
      exact ((T.adjoint_isFormalAdjoint hTdense).symm u v).symm
    · intro i hi v
      change ‖inner ℂ (u : E) ((A i).adjoint v)‖ ≤ _
      rw [(A i).adjoint_inner_right]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hAu i hi) (norm_nonneg _))
  obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hdec hnonempty hKcompact hKclosed
  have hLn (n : ℕ) : L ∈ K n := Set.mem_iInter.mp hL n
  let u : E := (InnerProductSpace.toDual ℂ E).symm (WeakDual.toStrongDual L)
  have hupair (v : T.adjoint.domain) :
      inner ℂ u (T.adjoint v) = inner ℂ f (v : F) := by
    rw [show inner ℂ u (T.adjoint v) = L (T.adjoint v) from
      InnerProductSpace.toDual_symm_apply]
    exact (hLn 0).1.2 v
  obtain ⟨x, hx, hTx⟩ := mem_graph_of_adjoint_pairing T hTdense hTclosed u f hupair
  refine ⟨x, hTx, ?_, ?_⟩
  · rw [hx]
    change ‖(InnerProductSpace.toDual ℂ E).symm (WeakDual.toStrongDual L)‖ ≤ B
    rw [(InnerProductSpace.toDual ℂ E).symm.norm_map]
    simpa only [ball, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using (hLn 0).1.1
  · intro i
    rw [hx]
    have hbound (v : G) : ‖inner ℂ (A i u) v‖ ≤ C i * ‖v‖ := by
      rw [← (A i).adjoint_inner_right]
      rw [show inner ℂ u ((A i).adjoint v) = L ((A i).adjoint v) from
        InnerProductSpace.toDual_symm_apply]
      exact (hLn i).2 i le_rfl v
    have hself := hbound (A i u)
    rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq] at hself
    nlinarith [norm_nonneg (A i u), hC i]

end NadelHilbert

open MeasureTheory

namespace SingularCutoff

theorem cutoff_energy_bound (χ : ℝ → ℝ) (hχ : ContDiff ℝ 1 χ)
    (ε : ℝ) (hε : 0 < ε) (hzero : χ 0 = 0) (hend : χ ε = 1) :
    1 / ε ≤ ∫ t in (0 : ℝ)..ε, (deriv χ t) ^ 2 := by
  have hd : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  have hdint := hd.intervalIntegrable (μ := volume) (0 : ℝ) ε
  have hd2int : IntervalIntegrable (fun t => (deriv χ t) ^ 2) volume 0 ε :=
    (hd.pow 2).intervalIntegrable (μ := volume) (0 : ℝ) ε
  have hFTC : ∫ t in (0 : ℝ)..ε, deriv χ t = 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun t _ => hχ.differentiable (by norm_num) t) hdint, hend, hzero, sub_zero]
  have hexpand :
      (∫ t in (0 : ℝ)..ε, (ε * deriv χ t - 1) ^ 2) =
      ε ^ 2 * (∫ t in (0 : ℝ)..ε, (deriv χ t) ^ 2) - ε := by
    calc
      _ = ∫ t in (0 : ℝ)..ε,
          (ε ^ 2 * (deriv χ t) ^ 2 - (2 * ε) * deriv χ t) + 1 := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hd2int.const_mul (ε ^ 2)).sub (hdint.const_mul (2 * ε)))
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 ε),
          intervalIntegral.integral_sub (hd2int.const_mul (ε ^ 2))
            (hdint.const_mul (2 * ε)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          hFTC, intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul, mul_one]
        ring
  have hpos : 0 ≤ ∫ t in (0 : ℝ)..ε, (ε * deriv χ t - 1) ^ 2 :=
    intervalIntegral.integral_nonneg hε.le
    (fun t (_ : t ∈ Set.Icc 0 ε) => sq_nonneg (ε * deriv χ t - 1))
  rw [hexpand] at hpos
  apply (div_le_iff₀ hε).2
  nlinarith

end SingularCutoff

end

end OAI
