import OAI.Combinatorics.MatchingEntropy.SharpRank

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter Module

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds.Refined

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

open LooplessGraph

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_lowerObjective (κ : ℝ) : Continuous (lowerObjective (E := E) κ) := by
  exact continuous_entropy.sub (continuous_const.mul (continuous_entropy.comp (by fun_prop)))

def objectiveLineD (κ : ℝ) (x v : E → ℝ) (t : ℝ) : ℝ :=
  entropyLineD x v t - κ * entropyLineD (fun e => 1-x e) (fun e => -v e) t

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem objective_line_eventually_hasDerivAt (κ : ℝ) (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t => lowerObjective κ (fun e => x e+t*v e))
        (objectiveLineD κ x v t) t := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  filter_upwards [entropy_line_eventually_hasDerivAt x v hzero,
    entropy_line_eventually_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar]
    with t ht hb
  have he : (fun t => lowerObjective κ (fun e => x e+t*v e)) =
      (fun t => entropy (fun e => x e+t*v e) -
        κ * entropy (fun e => (1-x e)+t*(-v e))) := by
    funext t
    unfold lowerObjective complementEntropy
    congr 2
    congr 1
    funext e
    ring
  rw [he]
  exact ht.sub (hb.const_mul κ)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem objectiveLineD_hasDerivAt (κ : ℝ) (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    HasDerivAt (objectiveLineD κ x v)
      (-(∑ e, (v e)^2/x e) + κ*(∑ e, (v e)^2/(1-x e))) 0 := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  have hd := (entropyLineD_hasDerivAt x v hzero).sub
    ((entropyLineD_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar).const_mul κ)
  exact hd.congr_deriv (by simp only [neg_sq]; ring)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem objective_second_variation (κ : ℝ) {A : Type uA} [Fintype A]
    (x v : E → ℝ) (hzero : ∀ e, x e=0 → v e=0) (hone : ∀ e, x e=1 → v e=0)
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (a : A → ℝ)
    (hcenter : ∑ i, p i*a i=0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => lowerObjective κ (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    -(∑ e, (v e)^2/x e) + κ*(∑ e, (v e)^2/(1-x e)) +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf := objective_line_eventually_hasDerivAt κ x v hzero hone
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (objectiveLineD_hasDerivAt κ x v hzero hone)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => lowerObjective κ (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

omit [Fintype V] [DecidableEq V] in

theorem matching_objective_second_variation (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, lowerObjective κ y-maxMatchingEntropy G y ≤
      lowerObjective κ x-maxMatchingEntropy G x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M=0) :
    -(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      κ*(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/(1-x e)) +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hzero : ∀ e, x e=0 → v e=0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  have hone : ∀ e, x e=1 → v e=0 := by
    rw [← hp.2]
    exact mean_score_one G hp.1 a hcenter
  apply objective_second_variation κ x v hzero hone hp.1 a hcenter c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r=fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M)=t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M))=c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  have hpart := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hpart,
    Real.log_one, sub_zero]
  rw [← hopt, entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

theorem objectiveDefect_attains_max (κ : ℝ) (G : LooplessGraph V E)
    (heven : Even (Fintype.card V)) (hPM : Nonempty G.Matching) :
    ∃ x ∈ G.polytope, ∀ y ∈ G.polytope,
      lowerObjective κ y-maxMatchingEntropy G y ≤ lowerObjective κ x-maxMatchingEntropy G x := by
  have hs : UpperSemicontinuousOn (fun y => lowerObjective κ y-maxMatchingEntropy G y)
      G.polytope := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using
      (continuous_lowerObjective κ).continuousOn.upperSemicontinuousOn.add
        (maxMatchingEntropy_lowerSemicontinuousOn G heven).neg
  have hn : G.polytope.Nonempty := by
    obtain ⟨M⟩ := hPM
    exact ⟨G.indicator M,subset_convexHull ℝ _ (Set.mem_range_self M)⟩
  exact UpperSemicontinuousOn.exists_isMaxOn hn G.compact_polytope hs

open Matrix
omit [Fintype V] [DecidableEq V] in

theorem matching_objective_covariance (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, lowerObjective κ y-maxMatchingEntropy G y ≤
      lowerObjective κ x-maxMatchingEntropy G x)
    (u : {e // 0 < x e} → ℝ) :
    u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) ≤
      ∑ e, (1-κ*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
  let w := matchingScoreWeights x u
  let c := ∑ e, w e*x e
  let a := linearScore G w c
  let v := G.mean (fun M => p M*a M)
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p,hp⟩
  have hcenter : ∑ M, p M*a M=0 := by
    dsimp only [a,c]
    rw [linearScore_expectation,hp.2,hp.1.2,mul_one,sub_self]
  have hh := matching_objective_second_variation κ G hp hopt hmax w c hcenter
  have hzero : ∀ e, ¬0 < x e → v e=0 := by
    intro e he
    have he0 : x e=0 := le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1
    exact mean_score_support G hp.1 a e (by rw [hp.2,he0])
  have hnorm : (∑ e, (v e)^2/x e) =
      ∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
  have hbar : (∑ e, (v e)^2/(1-x e)) =
      ∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2 := by
    rw [sum_positive_support x _ (fun e he => by rw [hzero e he]; simp)]
    apply Finset.sum_congr rfl
    intro e _
    rw [matchingNormalized_mulVec G hp,div_pow,Real.sq_sqrt e.property.le]
    change (v e.val)^2/(1-x e.val)=x e.val/(1-x e.val)*((v e.val)^2/x e.val)
    field_simp [ne_of_gt e.property]
  have hquad : (∑ M, p M*(a M)^2)=u ⬝ᵥ (covariance p (matchingNormalized G x) *ᵥ u) := by
    rw [covariance_quadratic hp.1.1]
    apply Finset.sum_congr rfl
    intro M _
    rw [← matchingNormalized_score G x u M]
  change -(∑ e, (v e)^2/x e)+κ*(∑ e, (v e)^2/(1-x e))+(∑ M,p M*(a M)^2) ≤ 0 at hh
  rw [hnorm,hbar,hquad] at hh
  have heq : (∑ e, (1-κ*x e.val/(1-x e.val))*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) =
      (∑ e, ((covariance p (matchingNormalized G x) *ᵥ u) e)^2)-
      κ*(∑ e, x e.val/(1-x e.val)*((covariance p (matchingNormalized G x) *ᵥ u) e)^2) := by
    simp_rw [sub_mul,one_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [heq]
  linarith

omit [Fintype V] in

theorem lowerObjective_forced (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x ∈ G.polytope) (e₀ : E) (he : x e₀=1) :
    lowerObjective κ (fun e : {e // G.RemainingEdge e₀ e} => x e.val)=lowerObjective κ x := by
  have hz : ∀ e, ¬G.RemainingEdge e₀ e →
      Real.negMulLog (x e)=0 ∧ Real.negMulLog (1-x e)=0 := by
    intro e h
    by_cases hneq : e=e₀
    · simp [hneq,he]
    · simp [G.forced_coordinate_zero hx e₀ he hneq h]
  unfold lowerObjective complementEntropy entropy
  rw [sum_subtype_supported _ _ (fun e h => (hz e h).1),
    sum_subtype_supported _ _ (fun e h => (hz e h).2)]

theorem objective_max_has_forced (κ : ℝ) (G : LooplessGraph V E) {x : E → ℝ}
    (heven : Even (Fintype.card V)) (hn : 0 < Fintype.card V) (hx : x ∈ G.polytope)
    (hκ : (2 - κ) * (Fintype.card V : ℝ) < 4)
    (hmax : ∀ y ∈ G.polytope, lowerObjective κ y - maxMatchingEntropy G y ≤
      lowerObjective κ x - maxMatchingEntropy G x) : ∃ e, x e = 1 := by
  by_contra hforced
  push Not at hforced
  obtain ⟨m, hm⟩ := heven
  have hV : Fintype.card V = 2 * m := by omega
  have hmpos : 0 < m := by omega
  have heven : Even (Fintype.card V) := ⟨m, hm⟩
  obtain ⟨p, hp, hopt⟩ := maxMatchingEntropy_attained G hx
  have hsecond := covariance_weighted_rank (covariance_posSemidef p (matchingNormalized G x))
    (fun e => 1 - κ * x e.val / (1 - x e.val)) (matching_objective_covariance κ G hp hopt hmax)
  have htrace : (∑ e : {e // 0 < x e}, (1 - κ * x e.val / (1 - x e.val)) *
      covariance p (matchingNormalized G x) e e) =
      Fintype.card {e // 0 < x e} - (κ + 1) * (m : ℝ) := by
    have he (e : {e // 0 < x e}) : (1 - κ * x e.val / (1 - x e.val)) *
        covariance p (matchingNormalized G x) e e = 1 - (κ + 1) * x e.val := by
      rw [matching_covariance_diagonal G hp]
      have hh : 1 - x e.val ≠ 0 := sub_ne_zero.mpr (Ne.symm (hforced e.val))
      field_simp
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hs : (∑ e : {e // 0 < x e}, x e.val) = (m : ℝ) := by
      rw [← G.marginal_sum hV hx]
      exact (sum_positive_support x x (fun e he =>
        le_antisymm (le_of_not_gt he) (G.coordinate_mem_Icc hx e).1)).symm
    rw [hs]
    simp
  rw [htrace] at hsecond
  have hrank := matching_covariance_rank_face G heven hp hopt
  have hsharp := sharp_face_rank G m hmpos hV hx
  have hrankR : (Fintype.card {e // 0 < x e} : ℝ) ≤ G.faceCodimension x +
      (covariance p (matchingNormalized G x)).rank := by exact_mod_cast hrank
  have hsharpR : (G.faceCodimension x : ℝ) + 2 ≤ 3 * (m : ℝ) := by exact_mod_cast hsharp
  rw [hV, Nat.cast_mul, Nat.cast_ofNat] at hκ
  nlinarith

theorem coefficient_down (κ : ℝ) {n k : ℕ} (hk : k ≤ n)
    (hn : (2 - κ) * (n : ℝ) < 4) : (2 - κ) * (k : ℝ) < 4 := by
  by_cases hc : 0 ≤ 2 - κ
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hc) hn
  · have hneg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    linarith

theorem strict_lower_aux (κ : ℝ) (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V = n → Even n →
      (2 - κ) * (n : ℝ) < 4 →
      ∀ x ∈ G.polytope, lowerObjective κ x ≤ maxMatchingEntropy G x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard heven hκ y hy
    by_cases hn : n = 0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      simpa [lowerObjective, complementEntropy, entropy] using maxMatchingEntropy_nonneg G hy
    · have heven' : Even (Fintype.card V) := hcard ▸ heven
      have hPM : Nonempty G.Matching := by
        obtain ⟨p,hp⟩ := (G.mem_polytope_iff y).mp hy
        by_contra h
        have : IsEmpty G.Matching := not_nonempty_iff.mp h
        simpa using hp.1.2
      obtain ⟨x, hx, hmax⟩ := objectiveDefect_attains_max κ G heven' hPM
      obtain ⟨e₀, he₀⟩ := objective_max_has_forced κ G heven' (by omega) hx (hcard ▸ hκ) hmax
      have hc := G.remaining_vertex_card e₀
      have hlt : Fintype.card {v // G.RemainingVertex e₀ v} < n := by omega
      have hev : Even (Fintype.card {v // G.RemainingVertex e₀ v}) := by
        obtain ⟨r,hr⟩ := heven
        refine ⟨r-1,?_⟩
        omega
      obtain ⟨p,hp⟩ := (G.mem_polytope_iff x).mp hx
      have hs := G.forcedLaw_feasible hp e₀ he₀
      have hxr := ((G.deleteEndpoints e₀).mem_polytope_iff _).mpr ⟨_,hs⟩
      have hsmall := ih _ hlt (G.deleteEndpoints e₀) rfl hev (coefficient_down κ hlt.le hκ) _ hxr
      rw [lowerObjective_forced κ G hx e₀ he₀] at hsmall
      have hxbound := hsmall.trans (G.maxMatchingEntropy_forced_le hx e₀ he₀)
      have hcompare := hmax y hy
      linarith

theorem refined_lower (G : LooplessGraph V E) (m : ℕ)
    (hm : 0 < m) (hV : Fintype.card V = 2 * m) (x : E → ℝ) (hx : x ∈ G.polytope) :
    lowerObjective (2 - 2 / (m : ℝ)) x ≤ maxMatchingEntropy G x := by
  let c : ℝ := 2 - 2 / (m : ℝ)
  have hcont : Continuous (fun κ : ℝ => lowerObjective κ x) := by
    unfold lowerObjective
    fun_prop
  apply le_of_tendsto (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
    Tendsto (fun κ : ℝ => lowerObjective κ x) (𝓝[>] c) (𝓝 (lowerObjective c x)))
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  have hκc : c < κ := hκ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : (2 - c) * (2 * (m : ℝ)) = 4 := by
    dsimp [c]
    field_simp
    ring
  have hstrict : (2 - κ) * (Fintype.card V : ℝ) < 4 := by
    rw [hV, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith [mul_lt_mul_of_pos_right hκc (by positivity : 0 < 2 * (m : ℝ))]
  exact strict_lower_aux κ (Fintype.card V) G rfl (by rw [hV]; exact even_two_mul m) hstrict x hx

def matchingProduct (G : LooplessGraph V E) (x : E → ℝ) (M : G.Matching) : ℝ :=
  ∏ e ∈ M.val, x e

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
theorem matchingProduct_nonneg (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, 0 ≤ x e) (M : G.Matching) : 0 ≤ matchingProduct G x M :=
  Finset.prod_nonneg (fun e _ => hx e)

omit [Fintype V] [Fintype E] in
theorem matchingProduct_addForced (G : LooplessGraph V E) (x : E → ℝ) (e₀ : E)
    (N : (G.deleteEndpoints e₀).Matching) :
    matchingProduct G x (G.addForced e₀ N) =
      x e₀ * matchingProduct (G.deleteEndpoints e₀) (fun e => x e.val) N := by
  have hnot : e₀ ∉ N.val.image Subtype.val := by
    rintro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    exact G.remainingEdge_ne e₀ e.property he
  change (∏ e ∈ insert e₀ (N.val.image Subtype.val), x e) = _
  rw [Finset.prod_insert hnot, Finset.prod_image (fun _ _ _ _ h => Subtype.ext h)]
  rfl

omit [Fintype V] in
theorem sum_matching_incident (G : LooplessGraph V E) (w : G.Matching → ℝ) (v : V) :
    (∑ M, w M) = ∑ e, if G.Incident v e then ∑ M : {M : G.Matching // e ∈ M.val}, w M.val else 0 := by
  have hone (M : G.Matching) : (∑ e, if G.Incident v e ∧ e ∈ M.val then w M else 0) = w M := by
    obtain ⟨e, ⟨he, hev⟩, huniq⟩ := M.property v
    rw [Finset.sum_eq_single e]
    · simp [he, hev]
    · intro f _ hne
      have hf : ¬ (G.Incident v f ∧ f ∈ M.val) := by
        rintro ⟨hfv, hfM⟩
        exact hne (huniq f ⟨hfM, hfv⟩)
      simp [hf]
    · simp
  calc
    _ = ∑ M, ∑ e, if G.Incident v e ∧ e ∈ M.val then w M else 0 := by simp_rw [hone]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : G.Incident v e
      · simp only [he, true_and, ite_true]
        have hh := (sum_subtype_supported (fun M : G.Matching => e ∈ M.val)
          (fun M => if e ∈ M.val then w M else 0) (by intro M h; simp [h])).symm
        apply hh.trans
        apply Finset.sum_congr rfl
        intro M _
        exact ite_eq_left M.property
      · simp [he]

omit [Fintype V] in
theorem matchingProduct_recursion (G : LooplessGraph V E) (x : E → ℝ) (v : V) :
    (∑ M, matchingProduct G x M) =
      ∑ e, if G.Incident v e then x e *
        ∑ N, matchingProduct (G.deleteEndpoints e) (fun f => x f.val) N else 0 := by
  rw [sum_matching_incident G _ v]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.Incident v e
  · simp only [he, ite_true]
    rw [← (G.forcedMatchingEquiv e).sum_comp (fun M => matchingProduct G x M.val)]
    change (∑ N, matchingProduct G x (G.addForced e N)) = _
    simp_rw [matchingProduct_addForced]
    rw [Finset.mul_sum]
  · simp [he]

omit [Fintype V] [DecidableEq E] in
theorem degree_deleteEndpoints_le (G : LooplessGraph V E) {x : E → ℝ}
    (hx : ∀ e, 0 ≤ x e) (e₀ : E) (v : {v // G.RemainingVertex e₀ v}) :
    (G.deleteEndpoints e₀).degree (fun e => x e.val) v ≤ G.degree x v.val := by
  simp only [degree, deleteEndpoints_incident]
  rw [← Finset.sum_subtype (Finset.univ.filter (G.RemainingEdge e₀)) (by simp)
    (fun e => if G.Incident v.val e then x e else 0)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro e _ _
  split
  · exact hx e
  · exact le_rfl

theorem matchingProduct_sum_le_aux (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : LooplessGraph V E), Fintype.card V = n →
      ∀ x : E → ℝ, (∀ e, 0 ≤ x e) → (∀ v, G.degree x v ≤ 1) →
      (∑ M, matchingProduct G x M) ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E _ _ _ _ G hcard x hx hd
    by_cases hn : n = 0
    · have : IsEmpty V := Fintype.card_eq_zero_iff.mp (hcard.trans hn)
      have : IsEmpty E := ⟨fun e => isEmptyElim (G.left e)⟩
      have hM : Fintype.card G.Matching ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
      have heach (M : G.Matching) : matchingProduct G x M = 1 := by
        rw [matchingProduct, Finset.eq_empty_of_isEmpty M.val, Finset.prod_empty]
      simp_rw [heach]
      simpa using (show (Fintype.card G.Matching : ℝ) ≤ 1 by exact_mod_cast hM)
    · have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨v⟩ := this
      rw [matchingProduct_recursion G x v]
      calc
        _ ≤ ∑ e, if G.Incident v e then x e else 0 := by
          apply Finset.sum_le_sum
          intro e _
          split
          · have hc := G.remaining_vertex_card e
            have hlt : Fintype.card {v // G.RemainingVertex e v} < n := by omega
            have hb := ih _ hlt (G.deleteEndpoints e) rfl (fun f => x f.val)
              (fun f => hx f.val) (fun v => (degree_deleteEndpoints_le G hx e v).trans (hd v.val))
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (hx e)
          · exact le_rfl
        _ ≤ 1 := hd v

theorem matchingProduct_sum_le (G : LooplessGraph V E) {x : E → ℝ} (hx : x ∈ G.polytope) :
    (∑ M, matchingProduct G x M) ≤ 1 := by
  have hc := G.polytope_subset_constraintPolytope hx
  exact matchingProduct_sum_le_aux (Fintype.card V) G rfl x hc.1 (fun v => (hc.2.1 v).le)

theorem matching_entropy_le_F (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x) : entropy p ≤ entropy x := by
  have hx : x ∈ G.polytope := (G.mem_polytope_iff x).mpr ⟨p, hp⟩
  have hfactor (M : G.Matching) (hM : 0 < p M) (e : E) (he : e ∈ M.val) : 0 < x e := by
    simpa [LooplessGraph.matchingBits, he] using matching_boolean_factor_pos G hp hM e
  have hprod (M : G.Matching) (hM : 0 < p M) : 0 < matchingProduct G x M :=
    Finset.prod_pos (fun e he => hfactor M hM e he)
  have hcross := entropy_le_subprob_crossEntropy
    (fun M => matchingProduct_nonneg G (fun e => (G.coordinate_mem_Icc hx e).1) M)
    (matchingProduct_sum_le G hx) hp.1
    (fun M hzero => le_antisymm (le_of_not_gt (fun hM => (ne_of_gt (hprod M hM)) hzero)) (hp.1.1 M))
  have hlog (M : G.Matching) : p M * Real.log (matchingProduct G x M) =
      ∑ e, (p M * G.indicator M e) * Real.log (x e) := by
    by_cases hzero : p M = 0
    · simp [hzero]
    · have hpos : 0 < p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hzero)
      rw [matchingProduct, Real.log_prod (fun e he => ne_of_gt (hfactor M hpos e he)), Finset.mul_sum]
      simp only [LooplessGraph.indicator, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp
  have heq : -(∑ M, p M * Real.log (matchingProduct G x M)) = entropy x := by
    simp_rw [hlog]
    rw [Finset.sum_comm, entropy_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.sum_mul]
    have he : (∑ M, p M * G.indicator M e) = x e := congrFun hp.2 e
    rw [he]
  rwa [heq] at hcross

theorem refined_upper (G : LooplessGraph V E) (x : E → ℝ) (hx : x ∈ G.polytope) :
    maxMatchingEntropy G x ≤ entropy x := by
  obtain ⟨p, hp, hopt⟩ := maxMatchingEntropy_attained G hx
  rw [← hopt]
  exact matching_entropy_le_F G hp

end MatchingEntropyBounds.Refined

end

end OAI
