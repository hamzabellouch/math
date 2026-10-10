import OAI.Combinatorics.CliqueFree.LocalWalk

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable {G : SimpleGraph V} {w : V → ℝ}

noncomputable def liftSet (u : V) (A : Finset V) : Finset (EdgeState G) :=
  univ.filter (fun e ↦ e.src = u ∧ e.dst ∈ A)

@[simp] lemma mem_liftSet (u : V) (A : Finset V) (e : EdgeState G) :
    e ∈ liftSet (G := G) u A ↔ e.src = u ∧ e.dst ∈ A := by simp [liftSet]

lemma liftSet_subset_fiber (u : V) (A : Finset V) : liftSet (G := G) u A ⊆ fiber G u := by
  intro e he
  exact (mem_fiber G e u).2 ((mem_liftSet u A e).1 he).1

lemma sum_liftSet (u : V) (A : Finset V) (f : V → ℝ) :
    (∑ e ∈ liftSet (G := G) u A, f e.dst) = ∑ v ∈ A ∩ neighbors G u, f v := by
  rw [liftSet, sum_filter]
  have he : (∑ e : EdgeState G, if e.src = u ∧ e.dst ∈ A then f e.dst else 0) =
      ∑ e : EdgeState G, if e.src = u then (if e.dst ∈ A then f e.dst else 0) else 0 := by
    apply sum_congr rfl
    intro e _
    by_cases hs : e.src = u <;> by_cases hd : e.dst ∈ A <;> simp [hs, hd]
  rw [he, EdgeState.sum_fiber u (fun v ↦ if v ∈ A then f v else 0), ← sum_filter]
  congr 1
  ext v
  simp [and_comm]

lemma lazy_neighbor_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (e f : EdgeState G) (h : e.dst ≠ f.dst) :
    lazy (transition G w) e f ≤ if G.Adj e.dst f.dst then x * w f.dst else 0 := by
  have hef : e ≠ f := fun he ↦ h (congrArg EdgeState.dst he)
  simp only [lazy, hef, ite_false, zero_add]
  have hp := transition_density hw hx hc e f
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hn := (transition_stochastic hw hc0 e).1 f
  by_cases hadj : G.Adj e.dst f.dst
  · rw [ite_eq_left hadj]
    change transition G w e f ≤ x * w f.dst at hp
    linarith
  · simp [transition, hadj]

lemma liftSet_adj_mass_le (hw : ∀ u, 0 ≤ w u) (u y : V) (A : Finset V) :
    (∑ z ∈ liftSet (G := G) u A, if G.Adj z.dst y then w z.dst else 0) ≤
      mass w (A ∩ neighbors G y) := by
  rw [sum_liftSet u A (fun z ↦ if G.Adj z y then w z else 0), ← sum_filter]
  have he : (A ∩ neighbors G u).filter (fun z ↦ G.Adj z y) =
      (A ∩ neighbors G y) ∩ neighbors G u := by
    ext z
    simp [G.adj_comm z y, and_assoc, and_comm]
  rw [he]
  exact mass_mono hw inter_subset_left

lemma incoming_good_le (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (e : EdgeState G) (A : Finset V) :
    (∑ y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ,
      ∑ z ∈ liftSet (G := G) e.src A,
        smoothed (transition G w) n e z * lazy (transition G w) z y) ≤
      x ^ 2 * t * neighborMass G w e.src := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  have hQ := stochastic_lazy hP
  have hpt := preserves_lazy (label := EdgeState.src) (transition_fixed_src (G := G) (w := w))
  have hrow (y : EdgeState G) (hy : y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ) :
      (∑ z ∈ liftSet (G := G) e.src A,
        smoothed (transition G w) n e z * lazy (transition G w) z y) ≤
        if y.src = e.src then x ^ 2 * t * w y.dst else 0 := by
    by_cases hsrc : y.src = e.src
    · rw [ite_eq_left hsrc]
      have hyout : y.dst ∉ enlarge G w t A := by
        intro h
        exact (mem_compl.1 hy) ((mem_liftSet _ _ _).2 ⟨hsrc, h⟩)
      have hymass := (not_mem_enlarge G w t A hyout).2.le
      calc
        _ ≤ ∑ z ∈ liftSet (G := G) e.src A,
            (if G.Adj z.dst y.dst then w z.dst else 0) * (x ^ 2 * w y.dst) := by
          apply sum_le_sum
          intro z hz
          have hzA := ((mem_liftSet _ _ _).1 hz).2
          have hzy : z.dst ≠ y.dst := by
            intro h
            apply hyout
            exact subset_enlarge G w t A (h ▸ hzA)
          have h1 := smoothed_density hw hx hc n e z
          have h2 := lazy_neighbor_density hw hx hc z y hzy
          change smoothed (transition G w) n e z ≤ x * w z.dst at h1
          have hm := mul_le_mul h1 h2 ((hQ z).1 y) (mul_pos hx (hw z.dst)).le
          by_cases hadj : G.Adj z.dst y.dst
          · simpa only [ite_eq_left hadj] using hm.trans_eq (by rw [ite_eq_left hadj]; ring)
          · simpa only [ite_eq_right hadj, mul_zero, zero_mul] using hm
        _ = (∑ z ∈ liftSet (G := G) e.src A,
            if G.Adj z.dst y.dst then w z.dst else 0) * (x ^ 2 * w y.dst) :=
          (sum_mul _ _ _).symm
        _ ≤ mass w (A ∩ neighbors G y.dst) * (x ^ 2 * w y.dst) :=
          mul_le_mul_of_nonneg_right (liftSet_adj_mass_le (fun u ↦ (hw u).le) _ _ _)
            (mul_nonneg (sq_nonneg x) (hw y.dst).le)
        _ ≤ t * (x ^ 2 * w y.dst) := mul_le_mul_of_nonneg_right hymass
          (mul_nonneg (sq_nonneg x) (hw y.dst).le)
        _ = _ := by ring
    · rw [ite_eq_right hsrc]
      apply le_of_eq
      apply sum_eq_zero
      intro z hz
      have hzs := ((mem_liftSet _ _ _).1 hz).1
      rw [hpt z y (fun h ↦ hsrc (h.symm.trans hzs)), mul_zero]
  calc
    _ ≤ ∑ y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ,
        if y.src = e.src then x ^ 2 * t * w y.dst else 0 := sum_le_sum hrow
    _ ≤ ∑ y : EdgeState G, if y.src = e.src then x ^ 2 * t * w y.dst else 0 := by
      apply sum_le_univ_sum_of_nonneg
      intro y
      split_ifs
      · exact mul_nonneg (mul_nonneg (sq_nonneg x) ht) (hw _).le
      · exact le_rfl
    _ = _ := by
      rw [EdgeState.sum_fiber e.src (fun y ↦ x ^ 2 * t * w y), ← mul_sum]
      rfl

lemma reach_leakage (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {L t : ℝ} (hL : ∀ u, neighborMass G w u ≤ L) (ht : 0 ≤ t)
    (n : ℕ) (e : EdgeState G) :
    rowMass (smoothed (transition G w) n) e
      (liftSet (G := G) e.src (reach G w t e.dst n))ᶜ ≤ n * (x ^ 2 * t * L) := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  induction n with
  | zero =>
    simp only [smoothed_zero, Nat.cast_zero, zero_mul, reach]
    apply le_of_eq
    apply sum_eq_zero
    intro f hf
    have hf' := mem_compl.1 hf
    by_cases hs : e.src = f.src
    · have ha : ¬G.Adj e.dst f.dst := by
        intro h
        exact hf' ((mem_liftSet _ _ _).2 ⟨hs.symm, (mem_neighbors G _ _).2 h⟩)
      simp [transition, hs, ha]
    · exact transition_fixed_src e f hs
  | succ n ih =>
    rw [smoothed_succ_right]
    have h := leakage_mul_le (stochastic_smoothed hP n) (stochastic_lazy hP) e
      (liftSet (G := G) e.src (reach G w t e.dst n))
      (liftSet (G := G) e.src (reach G w t e.dst (n+1)))
    have hinc := incoming_good_le hw hx hc ht n e (reach G w t e.dst n)
    have hmass := mul_le_mul_of_nonneg_left (hL e.src) (mul_nonneg (sq_nonneg x) ht)
    simp only [reach] at h
    simp only [Nat.cast_add, Nat.cast_one]
    change rowMass (smoothed (transition G w) n * lazy (transition G w)) e
      (liftSet (G := G) e.src (enlarge G w t (reach G w t e.dst n)))ᶜ ≤ _
    calc
      _ ≤ _ := h
      _ ≤ n * (x ^ 2 * t * L) + x ^ 2 * t * L :=
        add_le_add ih (hinc.trans hmass)
      _ = _ := by ring

lemma law_rev (e : EdgeState G) : law G w e.rev = law G w e := by
  simp only [law, EdgeState.src_rev, EdgeState.dst_rev, commonMass_comm G w e.dst e.src]
  ring

lemma law_bad_sum (B : V → Finset V) (hB : ∀ v, B v ⊆ neighbors G v) :
    (∑ e : EdgeState G, if e.src ∈ B e.dst then law G w e else 0) =
      (∑ v, w v * crossMass G w (B v) (neighbors G v)) / normalizer G w := by
  have hr := EdgeState.revEquiv (G := G) |>.sum_comp
    (fun e : EdgeState G ↦ if e.src ∈ B e.dst then law G w e else 0)
  simp only [EdgeState.revEquiv, Equiv.coe_fn_mk, EdgeState.src_rev, EdgeState.dst_rev,
    law_rev] at hr
  rw [← hr]
  unfold law
  rw [EdgeState.sum_eq (fun u v ↦ if v ∈ B u then
    w u * w v * commonMass G w u v / normalizer G w else 0)]
  simp_rw [crossMass_neighbors, mul_sum, sum_div]
  apply sum_congr rfl
  intro v _
  rw [← sum_filter]
  have he : (neighbors G v).filter (fun u ↦ u ∈ B v) = B v :=
    filter_mem_eq_inter.trans (inter_eq_right.2 (hB v))
  rw [he]
  apply sum_congr rfl
  intro u _
  rw [commonMass_comm G w v u]
  ring

lemma law_bad_le [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (B : V → Finset V) (hB : ∀ v, B v ⊆ neighbors G v) {q : ℝ}
    (hb : ∀ v, crossMass G w (B v) (neighbors G v) ≤ q * triangleAt G w v) :
    (∑ e : EdgeState G, if e.src ∈ B e.dst then law G w e else 0) ≤ q := by
  rw [law_bad_sum B hB, div_le_iff₀ (normalizer_pos hw hc)]
  calc
    _ ≤ ∑ v, w v * (q * triangleAt G w v) :=
      sum_le_sum fun v _ ↦ mul_le_mul_of_nonneg_left (hb v) (hw v).le
    _ = q * normalizer G w := by
      rw [normalizer_eq, triangleMass_eq_sum, mul_sum]
      apply sum_congr rfl
      intro v _
      ring

lemma entropy_good_row (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (e : EdgeState G) {b : ℝ} (hb : 1 ≤ b)
    (he : e.src ∉ badSet G w (fun v ↦ reach G w t v n) b e.dst) :
    entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤
      Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  have hsmall : mass w (reach G w t e.dst n ∩ neighbors G e.src) ≤ b := by
    by_contra! h
    exact he (mem_filter.2 ⟨(mem_neighbors G _ _).2 e.adj.symm, h⟩)
  have h := entropy_supported_concentration (w := vertexWeight G w)
    (fiber G e.src) (liftSet (G := G) e.src (reach G w t e.dst n))
    (liftSet_subset_fiber _ _) (fun f _ ↦ hw f.dst) (stochastic_smoothed hP n e)
    (smoothed_supported n e) hb (Real.exp_pos x)
    (by change (∑ f ∈ liftSet (G := G) e.src (reach G w t e.dst n), w f.dst) ≤ b
        rw [sum_liftSet]; exact hsmall)
    (by rw [fiber_mass]; exact hL _)
  rw [Real.log_exp] at h
  have hl := reach_leakage hw hx hc hL ht n e
  rw [rowMass_compl (stochastic_smoothed hP n)] at hl
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hl hx.le))

lemma averaged_entropy_bound [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {b q : ℝ} (hb : 1 ≤ b)
    (hbad : (∑ e : EdgeState G,
      if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then law G w e else 0) ≤ q) :
    avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) ≤
      Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x + q * x := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  let A := Real.log 2 + Real.log b + (n * (x ^ 2 * t * Real.exp x)) * x
  have hA : 0 ≤ A := by
    dsimp [A]
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
    positivity
  have hrow (e : EdgeState G) :
      entropy (vertexWeight G w) (smoothed (transition G w) n e) ≤
        A + if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then x else 0 := by
    split_ifs with he
    · exact (entropy_bounds hw hx hc hL n e).2.trans (by linarith)
    · simpa only [add_zero] using entropy_good_row hw hx hc hL ht n e hb he
  calc
    _ ≤ ∑ e, law G w e *
        (A + if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then x else 0) :=
      sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left (hrow e) (hmu.1 e)
    _ = A + (∑ e : EdgeState G,
        if e.src ∈ badSet G w (fun v ↦ reach G w t v n) b e.dst then law G w e else 0) * x := by
      simp only [mul_add, sum_add_distrib, ← sum_mul, hmu.2, one_mul, mul_ite, mul_zero]
      rw [sum_mul]
      simp only [ite_mul, zero_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hbad hx.le)

lemma avg_entropy_lower [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) (n : ℕ) :
    -Real.log x ≤ avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  calc
    _ = (∑ e, law G w e) * (-Real.log x) := by rw [hmu.2, one_mul]
    _ = ∑ e, law G w e * (-Real.log x) := sum_mul _ _ _
    _ ≤ _ := sum_le_sum fun e _ ↦ mul_le_mul_of_nonneg_left
      (entropy_bounds hw hx hc hL n e).1 (hmu.1 e)

lemma avg_entropy_upper [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 0 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x)
    (n : ℕ) (hn : (n : ℝ) ≤ 2 * x) :
    avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) n) ≤
      entropyConstant C * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  have hbad := law_bad_le hw hc0
    (badSet G w (fun u ↦ reach G w (Numerical.threshold x) u n) (x ^ 8))
    (badSet_subset G w _ _) (reach_bad_cross G (fun u ↦ (hw u).le) hC hCross hx hL hc hn)
  have hb : (1 : ℝ) ≤ x ^ 8 := one_le_pow₀ hx1
  have h := averaged_entropy_bound hw hx0 hc hL (Numerical.threshold_pos hx0).le n hb hbad
  rw [Real.log_pow] at h
  have hleak : ((n : ℝ) * (x ^ 2 * Numerical.threshold x * Real.exp x)) * x ≤ 1 := by
    rw [Numerical.leakage_factor hx0]
    calc
      _ = (n : ℝ) / x ^ 3 := by field_simp [hx0.ne']
      _ ≤ (2 * x) / x ^ 3 := div_le_div_of_nonneg_right hn (pow_pos hx0 3).le
      _ = 2 / x ^ 2 := by field_simp [hx0.ne']
      _ ≤ 1 := (div_le_iff₀ (pow_pos hx0 2)).2 (by nlinarith)
  have hE := exceptionalConstant_nonneg hC
  have hq : (exceptionalConstant C / x ^ 4) * x ≤ exceptionalConstant C * Real.log x := by
    calc
      _ = exceptionalConstant C / x ^ 3 := by field_simp [hx0.ne']
      _ ≤ exceptionalConstant C := (div_le_iff₀ (pow_pos hx0 3)).2 (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hx1 (n := 3)) hE)
      _ ≤ _ := by nlinarith [(Numerical.log_bounds hx).1]
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
  have hl1 := (Numerical.log_bounds hx).1
  unfold entropyConstant
  norm_num only [Nat.cast_ofNat] at h
  linarith

noncomputable def rowDistance (n : ℕ) : ℝ :=
  ∑ e : EdgeState G, law G w e * ∑ f, transition G w e f *
    tv (smoothed (transition G w) n e) (smoothed (transition G w) n f)

/-- The `C`-dependent entropy smoothing bound. -/
lemma exists_smooth_index [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    {C x : ℝ} (hC : 1 ≤ C) (hCross : CrossBound G w C) (hx : 32 ≤ x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (hL : ∀ u, neighborMass G w u ≤ Real.exp x) :
    ∃ j < ⌈x⌉₊,
      avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) j) ≤
        entropyConstant C * Real.log x ∧
      rowDistance (G := G) (w := w) j ≤ smoothingConstant C * Real.sqrt (Real.log x / x) := by
  have hx0 : 0 < x := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx0).trans_le (hc u v huv)
  have hmu := law_isProb hw hc0
  have hP := transition_stochastic hw hc0
  have hs := stationary_of_reversible hP (transition_reversible hw hc0)
  have hceil := Numerical.ceil_bounds hx
  have hlow := avg_entropy_lower hw hx0 hc hL 0
  have hupp := avg_entropy_upper hw hC0 hCross hx hc hL ⌈x⌉₊ hceil.2.2
  have hD : avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) ⌈x⌉₊) -
      avgEntropy (law G w) (vertexWeight G w) (smoothed (transition G w) 0) ≤
      (entropyConstant C + 1) * Real.log x := by linarith
  obtain ⟨j, hj, hdist⟩ := exists_smoothed_row_distance hmu (fun e ↦ hw e.dst) hP hs hceil.1 hD
  refine ⟨j, hj, ?_, ?_⟩
  · exact (smoothed_entropy_mono hmu (fun e ↦ hw e.dst) hP hs (Nat.le_of_lt hj)).trans hupp
  · have hA : 0 ≤ entropyConstant C + 1 := by
      have := exceptionalConstant_nonneg hC0
      unfold entropyConstant
      linarith
    have hlog : 0 ≤ Real.log x := ((Numerical.log_bounds hx).1.trans' (by norm_num))
    have href : rowDistance (G := G) (w := w) j ^ 2 ≤
        4 * ((entropyConstant C + 1) * Real.log x) / x := by
      exact hdist.trans (div_le_div_of_nonneg_left (by positivity) hx0 hceil.2.1)
    have hf : 0 ≤ Real.log x / x := div_nonneg hlog hx0.le
    have hsq : (smoothingConstant C * Real.sqrt (Real.log x / x)) ^ 2 =
        4 * ((entropyConstant C + 1) * Real.log x) / x := by
      rw [mul_pow, smoothingConstant, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hf]
      ring
    have hn : 0 ≤ smoothingConstant C * Real.sqrt (Real.log x / x) := by
      unfold smoothingConstant
      positivity
    nlinarith

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI
