import Mathlib
import OAI.Analysis.SymmetricDomains.Basic

namespace OAI

namespace Release061


theorem unit_disc_sum_eq_card {r : ℕ} (v : Fin r → ℂ)
    (hv : ∀ j, ‖v j‖ ≤ 1) (hs : ∑ j, v j = (r : ℂ)) : ∀ j, v j = 1 := by
  have hre : ∑ j, (v j).re = ∑ _j : Fin r, (1 : ℝ) := by
    simpa using congrArg Complex.re hs
  have hres : ∀ j, (v j).re = 1 := by
    simpa using (Finset.sum_eq_sum_iff_of_le
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
        (Complex.re_le_norm (v j)).trans (hv j))).mp hre
  intro j
  apply Complex.ext
  · simpa using hres j
  · have hsq := Complex.sq_norm_sub_sq_re (v j)
    have hnorm := hv j
    have hn := norm_nonneg (v j)
    have hi : (v j).im = 0 := by nlinarith [hres j, sq_nonneg (v j).im]
    simpa using hi

theorem locally_uniform_subsequence_of_equicontinuous
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    (F : ℕ → X → ℂ) (hF : Equicontinuous F)
    (hbound : ∀ i x, ‖F i x‖ ≤ 1) :
    ∃ f : X → ℂ, Continuous f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformly (fun i => F (φ i)) f Filter.atTop := by
  let A : Set (X → ℂ) := closure (Set.range F)
  have hRange : (Set.range F).Equicontinuous := equicontinuous_iff_range.mp hF
  have hAe : A.Equicontinuous := Set.Equicontinuous.closure hRange
  have hAb : ∀ f ∈ A, ∀ x, ‖f x‖ ≤ 1 := by
    intro f hf x
    have hsub : Set.range F ⊆ {g : X → ℂ | ‖g x‖ ≤ 1} := by
      rintro _ ⟨i, rfl⟩
      exact hbound i x
    exact (closure_minimal hsub (isClosed_le (continuous_apply x).norm continuous_const)) hf
  have hAc : IsCompact A := by
    apply (isCompact_univ_pi fun _x : X => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
      isClosed_closure
    intro f hf
    simpa [Set.mem_pi, Metric.mem_closedBall, dist_zero_right] using hAb f hf
  let S : Set C(X, ℂ) := {f | (f : X → ℂ) ∈ A}
  have himage : ContinuousMap.toFun '' S = A := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hAe.continuous_of_mem hf⟩, hf, rfl⟩
  have hSc : IsCompact S := by
    apply ArzelaAscoli.isCompact_of_equicontinuous S
    · rwa [himage]
    · exact hAe.comp (fun f : S => (⟨f.1, f.2⟩ : A))
  let G : ℕ → C(X, ℂ) := fun i => ⟨F i, hF.continuous i⟩
  have hGS : ∀ i, G i ∈ S := fun i => subset_closure (Set.mem_range_self i)
  obtain ⟨f, hf, φ, hφ, hconv⟩ := hSc.tendsto_subseq hGS
  exact ⟨f, f.continuous, hAb _ hf, φ, hφ,
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv⟩

theorem equicontinuous_of_bounded_differentiableOn
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : Set E} (hW : IsOpen W) (F : ι → E → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (F i) W)
    (hb : ∀ i x, x ∈ W → ‖F i x‖ ≤ 1) :
    Equicontinuous (fun i (x : W) => F i x) := by
  intro p
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW p p.property
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have ht : Filter.Tendsto (fun x : W => (2 / r) * dist (x : E) p)
      (nhds p) (nhds 0) := by
    simpa using ((continuous_subtype_val.dist
      (continuous_const : Continuous (fun _ : W => (p : E)))).const_mul (2 / r)).tendsto p
  have hsmall := (tendsto_order.mp ht).2 ε hε
  have hball : ∀ᶠ x : W in nhds p, (x : E) ∈ Metric.ball (p : E) r :=
    continuousAt_subtype_val.preimage_mem_nhds (Metric.ball_mem_nhds (p : E) hr)
  filter_upwards [hsmall, hball] with x hx hxr i
  have hmaps : Set.MapsTo (F i) (Metric.ball (p : E) r)
      (Metric.closedBall (F i p) 2) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm_sub]
    exact (norm_sub_le _ _).trans (by linarith [hb i z (hrW hz), hb i p p.property])
  have := (Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((hd i).mono hrW) hmaps hxr).trans_lt hx
  simpa [dist_comm] using this

theorem maximum_propagation_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {r : ℝ} (hr : 0 < r) (F : ℕ → E → ℂ) (f : E → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (F i) (Metric.ball p r))
    (hb : ∀ i x, x ∈ Metric.ball p r → ‖F i x‖ ≤ 1)
    (hc : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball p r))
    (hp : f p = 1) : Set.EqOn f (fun _ => 1) (Metric.ball p r) := by
  intro x hx
  by_cases hxp : x = p
  · simpa [hxp] using hp
  let R : ℝ := r / dist x p
  have hdpos : 0 < dist x p := dist_pos.mpr hxp
  have hR : 0 < R := div_pos hr hdpos
  let L : ℂ →ᵃ[ℂ] E := AffineMap.lineMap p x
  have hL : Set.MapsTo L (Metric.ball (0 : ℂ) R) (Metric.ball p r) := by
    intro z hz
    simpa [L, R, div_pos, lt_div_iff₀ hdpos, dist_comm p] using hz
  have hcL := hc.comp L hL L.differentiable.continuous.continuousOn
  have hdL : DifferentiableOn ℂ (f ∘ L) (Metric.ball (0 : ℂ) R) :=
    hcL.differentiableOn (Filter.Eventually.of_forall fun i =>
      (hd i).comp L.differentiable.differentiableOn hL) Metric.isOpen_ball
  have hbL : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖(f ∘ L) z‖ ≤ 1 := by
    intro z hz
    exact le_of_tendsto (hcL.tendsto_at hz).norm
      (Filter.Eventually.of_forall fun i => hb i (L z) (hL hz))
  have hL0 : (f ∘ L) 0 = 1 := by simpa [L] using hp
  have hmax : IsMaxOn (norm ∘ (f ∘ L)) (Metric.ball (0 : ℂ) R) 0 := by
    intro z hz
    change ‖(f ∘ L) z‖ ≤ ‖(f ∘ L) 0‖
    rw [hL0, norm_one]
    exact hbL z hz
  have hone : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [R, lt_div_iff₀ hdpos] using hx
  have heq := Complex.eq_const_of_exists_max hdL (Metric.mem_ball_self hR) hmax hone
  simpa [L, hp] using heq

theorem eq_one_of_local_maximum_propagation
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → ℂ) (hf : Continuous f) (p : X) (hp : f p = 1)
    (hloc : ∀ q, f q = 1 → ∀ᶠ x in nhds q, f x = 1) : ∀ x, f x = 1 := by
  have hclosed : IsClosed {x | f x = 1} := isClosed_eq hf continuous_const
  have hopen : IsOpen {x | f x = 1} := isOpen_iff_mem_nhds.mpr hloc
  have heq := (show IsClopen {x | f x = 1} from ⟨hclosed, hopen⟩).eq_univ ⟨p, hp⟩
  intro x
  have : x ∈ {x | f x = 1} := by rw [heq]; trivial
  exact this

theorem maximum_propagation_on_open_connected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : Set E} (hWo : IsOpen W) (hWc : IsPreconnected W)
    (F : ℕ → E → ℂ) (f : E → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (F i) W)
    (hb : ∀ i x, x ∈ W → ‖F i x‖ ≤ 1)
    (hc : TendstoLocallyUniformlyOn F f Filter.atTop W)
    {p : E} (hpW : p ∈ W) (hp : f p = 1) : Set.EqOn f (fun _ => 1) W := by
  let : PreconnectedSpace W := isPreconnected_iff_preconnectedSpace.mp hWc
  have hf : Continuous (fun x : W => f x) := continuousOn_iff_continuous_domRestrict.mp
    (hc.continuousOn (Filter.Eventually.of_forall (fun i => (hd i).continuousOn)).frequently)
  have heq := eq_one_of_local_maximum_propagation (fun x : W => f x) hf ⟨p, hpW⟩ hp
    (fun q hq => ?_)
  · intro x hx
    exact heq ⟨x, hx⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hWo q q.property
  have hball := maximum_propagation_on_ball hr F f
    (fun i => (hd i).mono hrW) (fun i x hx => hb i x (hrW hx)) (hc.mono hrW) hq
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds
    (Metric.ball_mem_nhds (q : E) hr)] with x hx
  exact hball hx

theorem peak_distance_lt {Y : Type*} [PseudoMetricSpace Y]
    {p q : Y} {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hb : ‖a‖ ≤ Real.exp (-(dist q p) ^ 2))
    (ha : dist (1 : ℂ) a < 1 - Real.exp (-ε ^ 2)) : dist q p < ε := by
  have htri : 1 ≤ dist (1 : ℂ) a + ‖a‖ := by
    simpa using dist_triangle (1 : ℂ) a 0
  have hexp : Real.exp (-ε ^ 2) < Real.exp (-(dist q p) ^ 2) := by linarith
  have hsq := Real.exp_lt_exp.mp hexp
  nlinarith [dist_nonneg (x := q) (y := p)]

theorem peak_localization
    {X Y ι : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (F : ι → X → Y) (h : Y → ℂ) (p : Y) {l : Filter ι}
    (hpeak : ∀ i x, ‖h (F i x)‖ ≤ Real.exp (-(dist (F i x) p) ^ 2))
    (hconv : TendstoLocallyUniformly (fun i x => h (F i x)) (fun _ => 1) l) :
    TendstoLocallyUniformly F (fun _ => p) l := by
  rw [Metric.tendstoLocallyUniformly_iff] at hconv ⊢
  intro ε hε x
  have hδ : 0 < 1 - Real.exp (-ε ^ 2) := by
    have := Real.exp_lt_one_iff.mpr (show -ε ^ 2 < 0 by nlinarith)
    linarith
  obtain ⟨t, ht, hlimit⟩ := hconv (1 - Real.exp (-ε ^ 2)) hδ x
  refine ⟨t, ht, hlimit.mono fun i hi y hy => ?_⟩
  simpa [dist_comm] using peak_distance_lt hε (hpeak i y) (hi y hy)

theorem exists_polynomial_integral_coordinates {k : Type*} [Field k]
    {n : ℕ} {V : Set (Fin n → k)} (hne : V.Nonempty) :
    ∃ d ≤ n, ∃ P : Fin d → MvPolynomial (Fin n) k,
      ∃ Q : Fin n → Polynomial (MvPolynomial (Fin d) k),
        (∀ i, (Q i).Monic) ∧
        ∀ z ∈ V, ∀ i,
          Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
            (z i) (Q i) = 0 := by
  classical
  let I := MvPolynomial.vanishingIdeal k V
  have hI : I ≠ ⊤ := by
    intro heq
    obtain ⟨z, hz⟩ := hne
    have hmem : (1 : MvPolynomial (Fin n) k) ∈ I := by simp [heq]
    have := MvPolynomial.mem_vanishingIdeal_iff.mp hmem z hz
    simp at this
  obtain ⟨d, hd, g, _hg, hgi⟩ := exists_integral_inj_algHom_of_quotient I hI
  choose P hP using fun j : Fin d =>
    Ideal.Quotient.mkₐ_surjective k I (g (MvPolynomial.X j))
  choose Q hQ hroot using fun i : Fin n => hgi ((Ideal.Quotient.mkₐ k I) (MvPolynomial.X i))
  refine ⟨d, hd, P, Q, hQ, ?_⟩
  intro z hz i
  let e : (MvPolynomial (Fin n) k ⧸ I) →ₐ[k] k :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval z) (fun p hp =>
      MvPolynomial.mem_vanishingIdeal_iff.mp hp z hz)
  have he (p : MvPolynomial (Fin n) k) : e ((Ideal.Quotient.mkₐ k I) p) =
      MvPolynomial.eval z p := rfl
  have heg : e.comp g = MvPolynomial.aeval (fun j => MvPolynomial.eval z (P j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rw [← hP j, he]
  have hx := congrArg e.toRingHom (hroot i)
  rw [map_zero, Polynomial.hom_eval₂] at hx
  have hegr : e.toRingHom.comp g.toRingHom =
      MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)) := by
    exact congrArg AlgHom.toRingHom heg
  rw [hegr] at hx
  change Polynomial.eval₂ _ (e ((Ideal.Quotient.mkₐ k I) (MvPolynomial.X i))) (Q i) = 0 at hx
  simpa only [he, MvPolynomial.eval_X] using hx

end Release061

end OAI
