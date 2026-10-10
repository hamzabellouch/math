import OAI.Analysis.ModularRecovery.ModularCovariance

namespace OAI

/-! Hilbert-space and predual ergodic averaging for the modular action. -/

universe u uE uF uι

open Filter MeasureTheory Set
open scoped Topology ComplexConjugate

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

lemma sigma_mem (S : StandardModularData H) (t : ℝ) {a : H →L[ℂ] H} (ha : a ∈ S.M) :
    S.sigma t a ∈ S.M := S.modular_covariance t a ha

@[simp] lemma sigma_apply_xi (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigma t a S.xi = S.D.unitary t (a S.xi) := by
  simp [sigma, S.fixes_xi]

@[simp] lemma sigma_one (S : StandardModularData H) (t : ℝ) :
    S.sigma t 1 = 1 := by simp [sigma]

lemma sigma_mul (S : StandardModularData H) (t : ℝ) (a b : H →L[ℂ] H) :
    S.sigma t (a * b) = S.sigma t a * S.sigma t b := by
  simp only [sigma]
  have h := S.D.unitary_neg_mul t
  calc
    _ = S.D.unitary t * a * (1 * b) * S.D.unitary (-t) := by simp [mul_assoc]
    _ = _ := by rw [← h]; simp only [mul_assoc]

lemma sigma_star (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigma t (star a) = star (S.sigma t a) := by
  simp [sigma, star_mul, mul_assoc]

lemma sigma_add (S : StandardModularData H) (t : ℝ) (a b : H →L[ℂ] H) :
    S.sigma t (a + b) = S.sigma t a + S.sigma t b := by simp [sigma, mul_add, add_mul]

lemma sigma_smul (S : StandardModularData H) (t : ℝ) (c : ℂ) (a : H →L[ℂ] H) :
    S.sigma t (c • a) = c • S.sigma t a := by simp [sigma]

lemma norm_sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    ‖S.sigma t a‖ = ‖a‖ := by
  have hle (r : ℝ) (b : H →L[ℂ] H) : ‖S.sigma r b‖ ≤ ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro v
    simp only [sigma, mul_apply_eq_comp, S.D.norm_unitary_apply]
    simpa only [S.D.norm_unitary_apply] using b.le_opNorm (S.D.unitary (-r) v)
  apply le_antisymm (hle t a)
  simpa only [← S.sigma_add_time, neg_add_cancel, S.sigma_zero] using hle (-t) (S.sigma t a)

lemma state_sigma (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.state (S.sigma t a) = S.state a := by
  simp only [state, sigma_apply_xi]
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (S.D.unitary t) S.xi) (a S.xi) = _
  rw [S.D.unitary_star, S.fixes_xi]

lemma continuous_sigma_apply (S : StandardModularData H) (a : H →L[ℂ] H) (h : H) :
    Continuous (fun t => S.sigma t a h) := by
  exact S.D.continuous_unitary_apply_varying
    (a.continuous.comp ((S.D.continuous_unitary_apply h).comp continuous_neg))

lemma fixed_of_fixed_vector (S : StandardModularData H) {a : H →L[ℂ] H}
    (ha : a ∈ S.M) (hv : ∀ t, S.D.unitary t (a S.xi) = a S.xi) :
    ∀ t, S.sigma t a = a := by
  intro t
  apply sub_eq_zero.mp
  apply S.separating _ (sub_mem (S.sigma_mem t ha) ha)
  simp [hv]

lemma norm_star_apply_xi_le (S : StandardModularData H) {a : H →L[ℂ] H}
    (ha : a ∈ S.M) {I : Set ℝ} (hband : S.D.HasSpectralSupport I (a S.xi))
    {b : ℝ} (hb : ∀ u ∈ I, u ≤ b) :
    ‖star a S.xi‖ ≤ Real.exp (b / 2) * ‖a S.xi‖ := by
  have hg : (a S.xi, star a S.xi) ∈ closure {p : H × H | ∃ c : H →L[ℂ] H,
      c ∈ S.M ∧ p = (c S.xi, star c S.xi)} := subset_closure ⟨a, ha, rfl⟩
  rw [S.tomita_graph] at hg
  obtain ⟨q, hq, heq⟩ := hg
  change star a S.xi = S.J q at heq
  rw [heq, S.J.norm_map]
  exact RealSpectralCalculus.norm_halfGraph_le hband hb hq

lemma state_star_mul (S : StandardModularData H) (a : H →L[ℂ] H) :
    S.state (star a * a) = (‖a S.xi‖ ^ 2 : ℝ) := by
  change inner ℂ S.xi (ContinuousLinearMap.adjoint a (a S.xi)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

end StandardModularData

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma convex_bounded_orbit (M : VonNeumannAlgebra H) (xi : H) (C : ℝ) :
    Convex ℝ {v : H | ∃ a : H →L[ℂ] H, a ∈ M ∧ ‖a‖ ≤ C ∧ a xi = v} := by
  rintro x ⟨a, ha, han, rfl⟩ y ⟨b, hb, hbn, rfl⟩ r q hr hq hrq
  refine ⟨(r : ℂ) • a + (q : ℂ) • b,
    add_mem (M.toStarSubalgebra.smul_mem ha _) (M.toStarSubalgebra.smul_mem hb _), ?_, ?_⟩
  · calc
      _ ≤ ‖(r : ℂ) • a‖ + ‖(q : ℂ) • b‖ := norm_add_le _ _
      _ = r * ‖a‖ + q * ‖b‖ := by simp [norm_smul, abs_of_nonneg hr, abs_of_nonneg hq]
      _ ≤ r * C + q * C := add_le_add (mul_le_mul_of_nonneg_left han hr)
        (mul_le_mul_of_nonneg_left hbn hq)
      _ = C := by rw [← add_mul, hrq, one_mul]
  · simp

lemma small_on_separating_controls_vector (M : VonNeumannAlgebra H) (xi : H)
    (hsep : ∀ a : H →L[ℂ] H, a ∈ M → a xi = 0 → a = 0)
    (h : H) {C eps : ℝ} (hC : 0 ≤ C) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ a : H →L[ℂ] H, a ∈ M → ‖a‖ ≤ C →
      ‖a xi‖ < delta → ‖a h‖ < eps := by
  have hd := commutant_cyclic M xi hsep
  obtain ⟨v,hv,hvdist⟩ := Metric.mem_closure_iff.mp (hd h)
    (eps / (2 * (C+1))) (by positivity)
  obtain ⟨b,hb,rfl⟩ := hv
  have hbcomm (a : H →L[ℂ] H) (ha : a ∈ M) : a * b = b * a :=
    (VonNeumannAlgebra.mem_commutant_iff.mp hb) a ha
  refine ⟨eps / (2 * (‖b‖+1)), by positivity, ?_⟩
  intro a ha hab haxi
  have hsmall : ‖h-b xi‖ < eps / (2*(C+1)) := by
    simpa only [dist_eq_norm] using hvdist
  have hfirst : C * ‖h-b xi‖ < eps/2 := by
    calc
      _ ≤ (C+1) * ‖h-b xi‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (C+1) * (eps/(2*(C+1))) := mul_lt_mul_of_pos_left hsmall (by positivity)
      _ = eps/2 := by field_simp
  have hsecond : ‖b‖ * ‖a xi‖ < eps/2 := by
    calc
      _ ≤ (‖b‖+1) * ‖a xi‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < (‖b‖+1) * (eps/(2*(‖b‖+1))) := mul_lt_mul_of_pos_left haxi (by positivity)
      _ = eps/2 := by field_simp
  have heq : a h = a (h-b xi) + b (a xi) := by
    have hc := congrArg (fun q : H →L[ℂ] H => q xi) (hbcomm a ha)
    change a (b xi) = b (a xi) at hc
    rw [map_sub, ← hc, sub_add_cancel]
  rw [heq]
  calc
    _ ≤ ‖a (h-b xi)‖ + ‖b (a xi)‖ := norm_add_le _ _
    _ ≤ C * ‖h-b xi‖ + ‖b‖ * ‖a xi‖ := add_le_add
      ((a.le_opNorm _).trans (mul_le_mul_of_nonneg_right hab (norm_nonneg _))) (b.le_opNorm _)
    _ < eps := by linarith

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology
namespace BoundedRecovery

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma convex_minimizer_unique {K : Set E} (hK : Convex ℝ K) {v w : E}
    (hv : v ∈ K) (hw : w ∈ K)
    (hvm : ‖(0 : E) - v‖ = ⨅ a : K, ‖(0 : E) - a‖)
    (hwm : ‖(0 : E) - w‖ = ⨅ a : K, ‖(0 : E) - a‖) : v = w := by
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero hK hv).mp hvm w hw
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero hK hw).mp hwm v hv
  have hn := norm_sub_sq_real v w
  have hi := real_inner_comm v w
  simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at h₁ h₂
  have hz : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma exists_fixed_in_closed_convex_orbit
    (U : ℝ → E →L[ℝ] E) (hadd : ∀ t r, U (t + r) = U t * U r)
    (hnorm : ∀ t v, ‖U t v‖ = ‖v‖) (x : E) :
    ∃ v ∈ closure (convexHull ℝ (Set.range (fun t => U t x))), ∀ t, U t v = v := by
  let K := closure (convexHull ℝ (Set.range (fun t => U t x)))
  have hK : Convex ℝ K := (convex_convexHull ℝ _).closure
  have hne : K.Nonempty := ⟨U 0 x, subset_closure (subset_convexHull ℝ _ ⟨0, rfl⟩)⟩
  obtain ⟨v, hv, hvm⟩ := exists_norm_eq_iInf_of_complete_convex hne isClosed_closure.isComplete hK 0
  refine ⟨v, hv, fun t => ?_⟩
  have hinv : Set.MapsTo (U t) K K := by
    apply closure_minimal ?_ (isClosed_closure.preimage (U t).continuous)
    apply convexHull_min ?_ (hK.linear_preimage (U t).toLinearMap)
    rintro y ⟨r, rfl⟩
    apply subset_closure
    apply subset_convexHull
    exact ⟨t + r, by change U (t + r) x = U t (U r x); rw [hadd]; rfl⟩
  apply convex_minimizer_unique hK (hinv hv) hv
  · simpa only [zero_sub, norm_neg, hnorm] using hvm
  · exact hvm

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma map_mem_closed_convexHull [NormedSpace ℝ E] {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {s : Set E} {x : E}
    (hx : x ∈ closure (convexHull ℝ s)) :
    L x ∈ closure (convexHull ℝ (L '' s)) := by
  apply (closure_minimal (convexHull_min ?_
    ((convex_convexHull ℝ _).closure.linear_preimage L.toLinearMap))
    (isClosed_closure.preimage L.continuous)) hx
  intro y hy
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_image_of_mem L hy))

end BoundedRecovery

noncomputable section
open Set Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardModularData

lemma inner_fixed_on_closed_convex_orbit (S : StandardModularData H) (a : H →L[ℂ] H)
    {v : H} (hv : v ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi))))) :
    inner ℂ S.xi v = S.state a := by
  have hconv : Convex ℝ {w : H | inner ℂ S.xi w = S.state a} :=
    (convex_singleton (S.state a)).linear_preimage ((innerSL ℂ S.xi).toLinearMap.restrictScalars ℝ)
  apply (closure_minimal (convexHull_min ?_ hconv)
    (isClosed_eq (by fun_prop) continuous_const)) hv
  rintro w ⟨t, rfl⟩
  change inner ℂ S.xi (S.D.unitary t (a S.xi)) = S.state a
  rw [← S.sigma_apply_xi]
  exact S.state_sigma t a

lemma fixed_eq_state_of_mem_closed_convex_orbit (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {a : H →L[ℂ] H} (ha : a ∈ S.M)
    {v : H} (hv : v ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi)))))
    (hfix : ∀ t, S.D.unitary t v = v) : v = S.state a • S.xi := by
  have hsub : closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi)))) ⊆
      {w : H | ∃ b : H →L[ℂ] H, b ∈ S.M ∧ ‖b‖ ≤ ‖a‖ ∧ b S.xi = w} := by
    apply closure_minimal ?_ (isClosed_bounded_orbit S.M S.xi S.separating (norm_nonneg _))
    apply convexHull_min ?_ (convex_bounded_orbit S.M S.xi ‖a‖)
    rintro w ⟨t, rfl⟩
    exact ⟨S.sigma t a, S.sigma_mem t ha, (S.norm_sigma t a).le, S.sigma_apply_xi t a⟩
  obtain ⟨b, hb, _, hbv⟩ := hsub hv
  obtain ⟨c, hc⟩ := hscalar b hb (S.fixed_of_fixed_vector hb (by simpa only [hbv] using hfix))
  have hvc : v = c • S.xi := by rw [hc] at hbv; simpa using hbv.symm
  have hinner := S.inner_fixed_on_closed_convex_orbit a hv
  rw [hvc, inner_smul_right, inner_self_eq_one_of_norm_eq_one S.norm_xi, mul_one] at hinner
  exact hvc.trans (congrArg (fun d : ℂ => d • S.xi) hinner)

lemma state_mem_closed_convex_orbit (S : StandardModularData H) (hscalar : S.ScalarCentralizer)
    {a : H →L[ℂ] H} (ha : a ∈ S.M) :
    S.state a • S.xi ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi)))) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_closed_convex_orbit
    (fun t => (S.D.unitary t).restrictScalars ℝ)
    (fun t r => by ext h; change S.D.unitary (t + r) h = _; rw [S.D.unitary_add]; rfl)
    (S.D.norm_unitary_apply) (a S.xi)
  have heq := S.fixed_eq_state_of_mem_closed_convex_orbit hscalar ha hv hfix
  rwa [← heq]

lemma pair_state_mem_closed_convex_orbit (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {a b : H →L[ℂ] H} (ha : a ∈ S.M) (hb : b ∈ S.M) :
    WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi) ∈ closure (convexHull ℝ
      (Set.range (fun t => WithLp.toLp 2
        (S.D.unitary t (a S.xi), S.D.unitary t (b S.xi))))) := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let L (t : ℝ) : H →ₗᵢ[ℝ] H :=
    { toLinearMap := (S.D.unitary t).toLinearMap.restrictScalars ℝ
      norm_map' := S.D.norm_unitary_apply t }
  let V (t : ℝ) : WithLp 2 (H × H) →L[ℝ] WithLp 2 (H × H) :=
    ((L t).withLpProdMap 2 (L t)).toContinuousLinearMap
  have hV (t r : ℝ) : V (t + r) = V t * V r := by
    apply ContinuousLinearMap.ext
    intro w
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · change S.D.unitary (t + r) w.fst = S.D.unitary t (S.D.unitary r w.fst)
      rw [S.D.unitary_add]
      rfl
    · change S.D.unitary (t + r) w.snd = S.D.unitary t (S.D.unitary r w.snd)
      rw [S.D.unitary_add]
      rfl
  obtain ⟨v, hv, hfix⟩ := exists_fixed_in_closed_convex_orbit V hV
    (fun t w => ((L t).withLpProdMap 2 (L t)).norm_map w) (WithLp.toLp 2 (a S.xi, b S.xi))
  have hv₁ : v.fst ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (a S.xi)))) := by
    have hh := map_mem_closed_convexHull (WithLp.fstL 2 ℝ H H) hv
    rw [← Set.range_comp'] at hh
    exact hh
  have hv₂ : v.snd ∈ closure (convexHull ℝ (Set.range (fun t => S.D.unitary t (b S.xi)))) := by
    have hh := map_mem_closed_convexHull (WithLp.sndL 2 ℝ H H) hv
    rw [← Set.range_comp'] at hh
    exact hh
  have he₁ : v.fst = S.state a • S.xi := S.fixed_eq_state_of_mem_closed_convex_orbit
    hscalar ha hv₁ (fun t => congrArg WithLp.fst (hfix t))
  have he₂ : v.snd = S.state b • S.xi := S.fixed_eq_state_of_mem_closed_convex_orbit
    hscalar hb hv₂ (fun t => congrArg WithLp.snd (hfix t))
  have he : v = WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi) :=
    WithLp.ofLp_injective 2 (Prod.ext he₁ he₂)
  rw [he] at hv
  exact hv

lemma exists_finite_average_pair (S : StandardModularData H)
    (hscalar : S.ScalarCentralizer) {a b : H →L[ℂ] H} (ha : a ∈ S.M) (hb : b ∈ S.M)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ (n : ℕ) (p t : Fin n → ℝ), (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
      ‖(∑ i, p i • S.D.unitary (t i) (a S.xi)) - S.state a • S.xi‖ < eps ∧
      ‖(∑ i, p i • S.D.unitary (t i) (b S.xi)) - S.state b • S.xi‖ < eps := by
  classical
  obtain ⟨v, hv, hvdist⟩ := Metric.mem_closure_iff.mp
    (S.pair_state_mem_closed_convex_orbit hscalar ha hb) eps heps
  obtain ⟨ι, inst, p, z, hp, hsum, hz, hveq⟩ := mem_convexHull_iff_exists_fintype.mp hv
  let := inst
  choose t ht using hz
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, p ∘ e, t ∘ e, fun i => hp _, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, Equiv.sum_comp] using hsum
  · have hh := lt_of_le_of_lt (WithLp.norm_fst_le H
      (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi)))
      (by simpa only [dist_eq_norm, norm_sub_rev] using hvdist)
    change ‖(WithLp.fstL 2 ℝ H H) (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi))‖ < eps at hh
    rw [← hveq, map_sub, map_sum] at hh
    have hzfst (i : ι) : (z i).fst = S.D.unitary (t i) (a S.xi) :=
      congrArg WithLp.fst (ht i).symm
    simp only [map_smul, WithLp.fstL_apply, WithLp.toLp_fst, hzfst] at hh
    rw [← e.sum_comp (fun i => p i • S.D.unitary (t i) (a S.xi))] at hh
    exact hh
  · have hh := lt_of_le_of_lt (WithLp.norm_snd_le H
      (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi)))
      (by simpa only [dist_eq_norm, norm_sub_rev] using hvdist)
    change ‖(WithLp.sndL 2 ℝ H H) (v - WithLp.toLp 2 (S.state a • S.xi, S.state b • S.xi))‖ < eps at hh
    rw [← hveq, map_sub, map_sum] at hh
    have hzsnd (i : ι) : (z i).snd = S.D.unitary (t i) (b S.xi) :=
      congrArg WithLp.snd (ht i).symm
    simp only [map_smul, WithLp.sndL_apply, WithLp.toLp_snd, hzsnd] at hh
    rw [← e.sum_comp (fun i => p i • S.D.unitary (t i) (b S.xi))] at hh
    exact hh

end StandardModularData
end BoundedRecovery

noncomputable section
open scoped ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma re_vectorState_star_mul_nonneg (xi : H) (a : H →L[ℂ] H) :
    0 ≤ (vectorStateLM xi (star a * a)).re := by
  rw [vectorState_star_mul]
  exact sq_nonneg _

lemma re_vectorState_sq (xi : H) {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) :
    (vectorStateLM xi (a ^ 2)).re = ‖a xi‖ ^ 2 := by
  have he : a ^ 2 = star a * a := by rw [ha.star_eq, pow_two]
  rw [he, vectorState_star_mul]
  rfl

end BoundedRecovery

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace BoundedRecovery
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace StandardModularData

def sigmaLinear (S : StandardModularData H) (t : ℝ) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun := S.sigma t
  map_add' := S.sigma_add t
  map_smul' := S.sigma_smul t

@[simp] lemma sigmaLinear_apply (S : StandardModularData H) (t : ℝ) (a : H →L[ℂ] H) :
    S.sigmaLinear t a = S.sigma t a := rfl

lemma sigma_sum {ι : Type uι} [Fintype ι] (S : StandardModularData H) (t : ℝ)
    (a : ι → H →L[ℂ] H) : S.sigma t (∑ i, a i) = ∑ i, S.sigma t (a i) :=
  map_sum (S.sigmaLinear t) a Finset.univ

lemma sigma_real_smul (S : StandardModularData H) (t c : ℝ) (a : H →L[ℂ] H) :
    S.sigma t (c • a) = c • S.sigma t a := (S.sigmaLinear t).map_smul_of_tower c a

lemma state_eq_vectorState (S : StandardModularData H) (a : H →L[ℂ] H) :
    S.state a = vectorStateLM S.xi a := rfl

lemma state_sum {ι : Type uι} [Fintype ι] (S : StandardModularData H)
    (a : ι → H →L[ℂ] H) : S.state (∑ i, a i) = ∑ i, S.state (a i) :=
  map_sum (vectorStateLM S.xi) a Finset.univ

lemma state_real_smul (S : StandardModularData H) (c : ℝ) (a : H →L[ℂ] H) :
    S.state (c • a) = c • S.state a := (vectorStateLM S.xi).map_smul_of_tower c a

lemma state_sandwich (S : StandardModularData H) (y a : H →L[ℂ] H) :
    S.state (star y * a * y) = inner ℂ (y S.xi) (a (y S.xi)) := by
  change inner ℂ S.xi (ContinuousLinearMap.adjoint y (a (y S.xi))) = _
  exact ContinuousLinearMap.adjoint_inner_right y S.xi (a (y S.xi))

lemma state_covariant_sandwich (S : StandardModularData H) (t : ℝ) (y a : H →L[ℂ] H) :
    S.state (star (S.sigma t y) * a * S.sigma t y) =
      S.state (star y * S.sigma (-t) a * y) := by
  rw [← S.state_sigma (-t) (star (S.sigma t y) * a * S.sigma t y)]
  simp only [S.sigma_mul, S.sigma_star, ← S.sigma_add_time, neg_add_cancel, S.sigma_zero]

lemma norm_state_le (S : StandardModularData H) (a : H →L[ℂ] H) : ‖S.state a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖S.xi‖ * ‖a S.xi‖ := norm_inner_le_norm _ _
    _ ≤ ‖S.xi‖ * (‖a‖ * ‖S.xi‖) := mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [S.norm_xi]; ring

lemma norm_state_real_star_mul (S : StandardModularData H) (y : H →L[ℂ] H) :
    ‖y S.xi‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have h := y.le_opNorm S.xi
  rw [S.norm_xi, mul_one] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma state_star_mul_re (S : StandardModularData H) (y : H →L[ℂ] H) :
    (S.state (star y * y)).re = ‖y S.xi‖ ^ 2 := by rw [S.state_star_mul]; rfl

lemma state_mul_star (S : StandardModularData H) (y : H →L[ℂ] H) :
    S.state (y * star y) = (‖star y S.xi‖ ^ 2 : ℝ) := by
  simpa only [star_star] using S.state_star_mul (star y)

lemma state_sq_re (S : StandardModularData H) {a : H →L[ℂ] H} (ha : IsSelfAdjoint a) :
    (S.state (a ^ 2)).re = ‖a S.xi‖ ^ 2 := re_vectorState_sq S.xi ha

end StandardModularData
end BoundedRecovery

end
end
end
end
end
end

end OAI
