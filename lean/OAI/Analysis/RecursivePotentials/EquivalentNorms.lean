import OAI.Analysis.RecursivePotentials.ZeroRootGeometry

namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

lemma weaklyNull_of_square_sum_bound {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ → E) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (S : Finset ℕ) (a : ℕ → ℝ),
      ‖∑ i ∈ S, a i • d i‖ ≤ C * Real.sqrt (∑ i ∈ S, (a i) ^ 2)) : WeaklyNull d := by
  intro f
  have hs : Summable (fun i => (f (d i)) ^ 2) := by
    apply summable_of_sum_le (fun i => sq_nonneg (f (d i)))
      (c := (‖f‖ * C) ^ 2)
    intro S
    let q := ∑ i ∈ S, (f (d i)) ^ 2
    have hq : 0 ≤ q := Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hsq := Real.sq_sqrt hq
    have hb := h S (fun i => f (d i))
    have hf := f.le_opNorm (∑ i ∈ S, f (d i) • d i)
    have he : f (∑ i ∈ S, f (d i) • d i) = q := by
      simp only [map_sum, map_smul, smul_eq_mul, q, pow_two]
    rw [he, Real.norm_eq_abs, abs_of_nonneg hq] at hf
    have hmul := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
    have hK : 0 ≤ ‖f‖ * C := mul_nonneg (norm_nonneg f) hC
    have hroot : Real.sqrt q ≤ ‖f‖ * C := by
      have hroot0 := Real.sqrt_nonneg q
      nlinarith
    change q ≤ (‖f‖ * C) ^ 2
    nlinarith [Real.sqrt_nonneg q]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simp only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs] at hsqrt
  exact (tendsto_zero_iff_norm_tendsto_zero).mpr hsqrt

lemma WeaklyNull.quotient_tendsto {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ → E} (hd : WeaklyNull d) (F : CofiniteSubspace E) :
    Tendsto (fun k => F.space.mkQL (d k)) atTop (𝓝 0) := by
  let : IsClosed (F.space : Set E) := F.closed
  let := F.finiteQuotient
  let b := Module.finBasis ℝ (E ⧸ F.space)
  let e := b.equivFunL
  have he : Tendsto (fun k => e (F.space.mkQL (d k))) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact hd (((ContinuousLinearMap.proj i).comp e.toContinuousLinearMap).comp F.space.mkQL)
  have hi := e.symm.continuous.continuousAt.tendsto.comp he
  simpa only [Function.comp_def, e.symm_apply_apply, map_zero] using hi

lemma WeaklyNull.approximate_cofinite {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ → E} (hd : WeaklyNull d) (F : CofiniteSubspace E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∃ w ∈ F.space, ‖d k - w‖ < ε := by
  have hn := (hd.quotient_tendsto F).norm
  simp only [norm_zero] at hn
  have hev : ∀ᶠ k in atTop, ‖F.space.mkQL (d k)‖ < ε / 2 :=
    hn.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hev] with k hk
  obtain ⟨v, hv, hnv⟩ := Submodule.Quotient.norm_mk_lt (F.space.mkQL (d k)) (half_pos hε)
  refine ⟨d k - v, ?_, ?_⟩
  · rw [← F.space.ker_mkQ]
    change F.space.mkQ (d k - v) = 0
    rw [map_sub]
    change F.space.mkQL (d k) - Submodule.Quotient.mk v = 0
    rw [hv, sub_self]
  · have he : d k - (d k - v) = v := by abel
    rw [he]
    linarith

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

lemma upper_pos : 0 < A.upper := A.lower_pos.trans_le A.lower_le_upper

lemma nonneg (x : E) : 0 ≤ A.N x := apply_nonneg _ _

lemma pos {x : E} (hx : x ≠ 0) : 0 < A.N x :=
  (mul_pos A.lower_pos (norm_pos_iff.mpr hx)).trans_le (A.lower_bound x)

lemma eq_zero_iff (x : E) : A.N x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (A.pos hx).ne' h
  · intro h; simp [h]

lemma sub_le (x y : E) : A.N x - A.N y ≤ A.N (x - y) := by
  have h := map_add_le_add A.N (x - y) y
  rw [sub_add_cancel] at h
  linarith

lemma lipschitz_estimate (x y : E) : |A.N x - A.N y| ≤ A.upper * ‖x - y‖ := by
  apply abs_le.mpr
  constructor
  · have h := A.sub_le y x
    have hb := A.upper_bound (y - x)
    rw [norm_sub_rev] at hb
    linarith
  · exact (A.sub_le x y).trans (A.upper_bound (x - y))

lemma exists_unit (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    ∃ y ∈ F.space, A.N y = 1 := by
  obtain ⟨x, hx, hxn⟩ := F.exists_unit hE
  have hx0 : x ≠ 0 := by intro he; simp [he] at hxn
  have hp := A.pos hx0
  refine ⟨(A.N x)⁻¹ • x, F.space.smul_mem _ hx, ?_⟩
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']

lemma inner_nonempty (x : E) (t : ℝ) (F : CofiniteSubspace E)
    (hE : ¬Module.Finite ℝ E) :
    {r : ℝ | ∃ y ∈ F.space, A.N y = 1 ∧ r = A.N (x + t • y) - 1}.Nonempty := by
  obtain ⟨y, hy, hy1⟩ := A.exists_unit F hE
  exact ⟨_, y, hy, hy1, rfl⟩

lemma inner_bddBelow (x : E) (t : ℝ) (F : CofiniteSubspace E) :
    BddBelow {r : ℝ | ∃ y ∈ F.space, A.N y = 1 ∧ r = A.N (x + t • y) - 1} := by
  refine ⟨-1, ?_⟩
  rintro r ⟨y, hy, hy1, rfl⟩
  linarith [A.nonneg (x + t • y)]

lemma inner_lower (x : E) (t : ℝ) (F : CofiniteSubspace E)
    (hE : ¬Module.Finite ℝ E) : -1 ≤ A.inner x t F := by
  apply le_csInf (A.inner_nonempty x t F hE)
  rintro r ⟨y, hy, hy1, rfl⟩
  linarith [A.nonneg (x + t • y)]

lemma inner_upper {x : E} (hx : A.N x = 1) {t : ℝ} (ht : 0 ≤ t)
    (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) : A.inner x t F ≤ t := by
  obtain ⟨y, hy, hy1⟩ := A.exists_unit F hE
  have hi : A.inner x t F ≤ A.N (x + t • y) - 1 :=
    csInf_le (A.inner_bddBelow x t F) ⟨y, hy, hy1, rfl⟩
  have h := map_add_le_add A.N x (t • y)
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht, hx, hy1, mul_one] at h
  linarith

lemma modulus_le_sup {x : E} (hx : A.N x = 1) {t : ℝ} (ht : 0 ≤ t)
    (hE : ¬Module.Finite ℝ E) : A.modulus t ≤ sSup (Set.range (A.inner x t)) := by
  have hlower : BddBelow {r : ℝ | ∃ x : E, A.N x = 1 ∧
      r = sSup (Set.range (A.inner x t))} := by
    refine ⟨-1, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hb : BddAbove (Set.range (A.inner x t)) := by
      refine ⟨t, ?_⟩
      rintro r ⟨F, rfl⟩
      exact A.inner_upper hx ht F hE
    exact (A.inner_lower x t CofiniteSubspace.top hE).trans
      (le_csSup hb (Set.mem_range_self _))
  exact csInf_le hlower ⟨x, hx, rfl⟩

lemma witness {t γ : ℝ} (ht : 0 ≤ t) (hγ : γ < A.modulus t)
    (hE : ¬Module.Finite ℝ E) (x : E) (hx : A.N x = 1) :
    ∃ F : CofiniteSubspace E, ∀ y ∈ F.space, A.N y = 1 →
      1 + γ ≤ A.N (x + t • y) := by
  have hs : γ < sSup (Set.range (A.inner x t)) :=
    hγ.trans_le (A.modulus_le_sup hx ht hE)
  obtain ⟨r, ⟨F, rfl⟩, hF⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hs
  refine ⟨F, ?_⟩
  intro y hy hy1
  have hi : A.inner x t F ≤ A.N (x + t • y) - 1 :=
    csInf_le (A.inner_bddBelow x t F) ⟨y, hy, hy1, rfl⟩
  linarith

lemma extend_radius {x y : E} (hx : A.N x = 1) (_hy : A.N y = 1)
    {t r γ : ℝ} (ht : 0 < t) (htr : t ≤ r) (hγ : 0 ≤ γ)
    (hg : 1 + γ ≤ A.N (x + t • y)) : 1 + γ ≤ A.N (x + r • y) := by
  have hr : 0 < r := ht.trans_le htr
  have hscale : x + t • y = (t / r) • (x + r • y) + (1 - t / r) • x := by
    rw [smul_add, smul_smul, div_mul_cancel₀ t hr.ne']
    module
  have hle := map_add_le_add A.N ((t / r) • (x + r • y)) ((1 - t / r) • x)
  rw [← hscale, map_smul_eq_mul, map_smul_eq_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ht.le hr.le), abs_of_nonneg (sub_nonneg.mpr
      ((div_le_one hr).mpr htr)), hx, mul_one] at hle
  have hdiv : 0 < t / r := div_pos ht hr
  have hdiv1 : t / r ≤ 1 := (div_le_one hr).mpr htr
  nlinarith

lemma long_perturbation {u w : E} (hu : u ≠ 0) {t γ : ℝ} (ht : 0 < t) (hγ : 0 ≤ γ)
    (F : CofiniteSubspace E) (hw : w ∈ F.space) (hwn : t * A.N u ≤ A.N w)
    (hF : ∀ y ∈ F.space, A.N y = 1 →
      1 + γ ≤ A.N ((A.N u)⁻¹ • u + t • y)) :
    (1 + γ) * A.N u ≤ A.N (u + w) := by
  have hu0 := A.pos hu
  have hw0 : 0 < A.N w := (mul_pos ht hu0).trans_le hwn
  have hunitu : A.N ((A.N u)⁻¹ • u) = 1 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0), inv_mul_cancel₀ hu0.ne']
  have hunitw : A.N ((A.N w)⁻¹ • w) = 1 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hw0.ne']
  have hg := A.extend_radius hunitu hunitw ht ((le_div_iff₀ hu0).mpr hwn) hγ
    (hF _ (F.space.smul_mem _ hw) hunitw)
  have he : (A.N u)⁻¹ • u + (A.N w / A.N u) • ((A.N w)⁻¹ • w) =
      (A.N u)⁻¹ • (u + w) := by
    rw [smul_smul, div_eq_mul_inv, mul_assoc, mul_comm (A.N u)⁻¹,
      ← mul_assoc, mul_inv_cancel₀ hw0.ne', one_mul, smul_add]
  rw [he, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0)] at hg
  calc
    (1 + γ) * A.N u ≤ ((A.N u)⁻¹ * A.N (u + w)) * A.N u :=
      mul_le_mul_of_nonneg_right hg hu0.le
    _ = A.N (u + w) := by field_simp

lemma bounded_tree_step (hE : ¬Module.Finite ℝ E) {u : E} (hu : u ≠ 0)
    (d : ℕ → E) (hd : WeaklyNull d) {M c γ : ℝ} (hM : 0 < M) (hc : 0 < c)
    (huM : ‖u‖ ≤ M) (hdc : ∀ k, c ≤ ‖d k‖) (hγ : 0 < γ)
    (hmod : γ < A.modulus (A.lower * c / (2 * A.upper * M))) :
    ∃ k, (1 + γ / 2) * A.N u ≤ A.N (u + d k) := by
  have hu0 := A.pos hu
  have hU0 := A.upper_pos.ne'
  let t := A.lower * c / (2 * A.upper * M)
  have ht : 0 < t := div_pos (mul_pos A.lower_pos hc) (by have := A.upper_pos; positivity)
  have hunit : A.N ((A.N u)⁻¹ • u) = 1 := by
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu0), inv_mul_cancel₀ hu0.ne']
  obtain ⟨F, hF⟩ := A.witness ht.le hmod hE _ hunit
  let ε := min (A.lower * c / (2 * A.upper)) (γ * A.N u / (2 * A.upper))
  have hε : 0 < ε := lt_min
    (div_pos (mul_pos A.lower_pos hc) (by have := A.upper_pos; positivity))
    (div_pos (mul_pos hγ hu0) (by have := A.upper_pos; positivity))
  obtain ⟨k, w, hw, hdw⟩ := (hd.approximate_cofinite F hε).exists
  have herror₁ : A.upper * ‖d k - w‖ < A.lower * c / 2 := by
    have hh := lt_of_lt_of_le hdw (min_le_left _ _)
    have he : A.upper * (A.lower * c / (2 * A.upper)) = A.lower * c / 2 := by
      field_simp [hU0, hM.ne']
    calc
      A.upper * ‖d k - w‖ < A.upper * (A.lower * c / (2 * A.upper)) :=
        mul_lt_mul_of_pos_left hh A.upper_pos
      _ = _ := he
  have herror₂ : A.upper * ‖d k - w‖ < γ * A.N u / 2 := by
    have hh := lt_of_lt_of_le hdw (min_le_right _ _)
    have he : A.upper * (γ * A.N u / (2 * A.upper)) = γ * A.N u / 2 := by
      field_simp [hU0, hM.ne']
    calc
      A.upper * ‖d k - w‖ < A.upper * (γ * A.N u / (2 * A.upper)) :=
        mul_lt_mul_of_pos_left hh A.upper_pos
      _ = _ := he
  have hwc : A.lower * c / 2 ≤ A.N w := by
    have hb := A.lower_bound (d k)
    have hc' := mul_le_mul_of_nonneg_left (hdc k) A.lower_pos.le
    have he := (A.sub_le (d k) w).trans (A.upper_bound (d k - w))
    linarith
  have hut : t * A.N u ≤ A.lower * c / 2 := by
    have hub := (A.upper_bound u).trans (mul_le_mul_of_nonneg_left huM A.upper_pos.le)
    have he : t * (A.upper * M) = A.lower * c / 2 := by
      dsimp [t]
      field_simp [hU0, hM.ne']
    exact (mul_le_mul_of_nonneg_left hub ht.le).trans_eq he
  have hwgain := A.long_perturbation hu ht hγ.le F hw (hut.trans hwc) hF
  have hdif := A.sub_le (u + w) (u + d k)
  have he : (u + w) - (u + d k) = w - d k := by abel
  rw [he] at hdif
  have hb := A.upper_bound (w - d k)
  rw [norm_sub_rev] at hb
  refine ⟨k, ?_⟩
  nlinarith

end EquivalentNorm

theorem bounded_trees_modulus_le_zero {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬Module.Finite ℝ E) (A : EquivalentNorm E) (u : ℕ → List ℕ → E)
    {m M c : ℝ} (hm : 0 < m) (hM : 0 < M) (hc : 0 < c)
    (hu : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length ≤ h → m ≤ ‖u h s‖ ∧ ‖u h s‖ ≤ M)
    (hd : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      WeaklyNull (fun k => u h (s ++ [k]) - u h s))
    (hdc : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      ∀ k, c ≤ ‖u h (s ++ [k]) - u h s‖) :
    A.modulus (A.lower * c / (2 * A.upper * M)) ≤ 0 := by
  by_contra hnon
  have hpos := lt_of_not_ge hnon
  let γ := A.modulus (A.lower * c / (2 * A.upper * M)) / 2
  have hγ : 0 < γ := half_pos hpos
  have hγmod : γ < A.modulus (A.lower * c / (2 * A.upper * M)) := half_lt_self hpos
  let δ := γ * (A.lower * m) / 2
  have hδ : 0 < δ := by dsimp [δ]; have := A.lower_pos; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (A.upper * M / δ)
  let h := n + 1
  have hh : 1 ≤ h := by omega
  have hgrow : ∀ j : ℕ, j ≤ h → ∃ s : List ℕ, s.length = j ∧
      (j : ℝ) * δ + A.lower * m ≤ A.N (u h s) := by
    intro j hj
    induction j with
    | zero =>
        refine ⟨[], rfl, ?_⟩
        have hl := A.lower_bound (u h [])
        have hm' := mul_le_mul_of_nonneg_left (hu h hh [] (by simp)).1 A.lower_pos.le
        simpa using hm'.trans hl
    | succ j ih =>
        obtain ⟨s, hs, hsn⟩ := ih (by omega)
        have hsh : s.length < h := by omega
        have hs0 : u h s ≠ 0 := by
          intro he
          have hl := (hu h hh s hsh.le).1
          rw [he, norm_zero] at hl
          linarith
        obtain ⟨k, hk⟩ := A.bounded_tree_step hE hs0 (fun k => u h (s ++ [k]) - u h s)
          (hd h hh s hsh) hM hc (hu h hh s hsh.le).2 (hdc h hh s hsh) hγ hγmod
        have hl : A.lower * m ≤ A.N (u h s) :=
          (mul_le_mul_of_nonneg_left (hu h hh s hsh.le).1 A.lower_pos.le).trans (A.lower_bound _)
        have he : u h s + (u h (s ++ [k]) - u h s) = u h (s ++ [k]) := by abel
        rw [he] at hk
        refine ⟨s ++ [k], by simp [hs], ?_⟩
        push_cast
        dsimp [δ] at hsn ⊢
        nlinarith
  obtain ⟨s, hs, hsn⟩ := hgrow h le_rfl
  have huM := (A.upper_bound (u h s)).trans
    (mul_le_mul_of_nonneg_left (hu h hh s hs.le).2 A.upper_pos.le)
  have hn' : A.upper * M < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  have hhcast : (h : ℝ) = (n : ℝ) + 1 := by simp [h]
  rw [hhcast] at hsn
  have hm' := mul_pos A.lower_pos hm
  nlinarith

theorem bounded_trees_not_AUC {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬Module.Finite ℝ E) (A : EquivalentNorm E) (u : ℕ → List ℕ → E)
    {m M c : ℝ} (hm : 0 < m) (hM : 0 < M) (hc : 0 < c)
    (hu : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length ≤ h → m ≤ ‖u h s‖ ∧ ‖u h s‖ ≤ M)
    (hd : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      WeaklyNull (fun k => u h (s ++ [k]) - u h s))
    (hdc : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      ∀ k, c ≤ ‖u h (s ++ [k]) - u h s‖) : ¬A.AUC := by
  intro ha
  have ht : 0 < A.lower * c / (2 * A.upper * M) := by have := A.lower_pos; have := A.upper_pos; positivity
  exact (not_lt_of_ge (bounded_trees_modulus_le_zero hE A u hm hM hc hu hd hdc)) (ha _ ht)

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma normSum_emb_siblings (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) (a : ℕ →₀ ℝ) :
    T.normSum (a.embDomain f) ≤ 2 * Real.sqrt (∑ k ∈ a.support, a k ^ 2) := by
  have h := T.normSum_siblings_le s (a.embDomain f) (by
    intro c hc
    rw [Finsupp.support_embDomain] at hc
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hc
    exact hf k)
  simpa only [Finsupp.support_embDomain, Finset.sum_map, Finsupp.embDomain_apply_self] using h

end FiniteRootedTree

lemma weaklyNull_of_finsupp_bound {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (ℕ →₀ ℝ) →ₗ[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ a, ‖L a‖ ≤ C * Real.sqrt (∑ k ∈ a.support, a k ^ 2)) :
    WeaklyNull (fun k => L (Finsupp.single k 1)) := by
  classical
  apply weaklyNull_of_square_sum_bound _ hC
  intro S a
  let b : ℕ →₀ ℝ := Finsupp.onFinset S (fun k => if k ∈ S then a k else 0)
    (by intro k hk; by_contra hn; simp [hn] at hk)
  have hb : b.support ⊆ S := Finsupp.support_onFinset_subset
  have he : b = ∑ k ∈ S, a k • Finsupp.single k 1 := by
    rw [← b.sum_single, b.sum_of_support_subset hb]
    · apply Finset.sum_congr rfl
      intro k hk
      simp [b, hk]
    · intro i hi; simp
  have hs : (∑ k ∈ b.support, b k ^ 2) = ∑ k ∈ S, a k ^ 2 := by
    calc
      _ = ∑ k ∈ S, b k ^ 2 := by
        apply Finset.sum_subset hb
        intro k hk hn
        rw [Finsupp.notMem_support_iff.mp hn]
        norm_num
      _ = _ := by apply Finset.sum_congr rfl; intro k hk; simp [b, hk]
  have h := hL b
  rw [hs, he, map_sum] at h
  simpa only [map_smul] using h

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

def basisVector (c : ι) : TreeSpace T := (show TreeVector T from Finsupp.single c 1)

lemma basisVector_norm (c : ι) (hc : c ≠ T.root) : ‖basisVector T c‖ = 2 := by
  change ‖(↑(show TreeVector T from Finsupp.single c 1) : TreeSpace T)‖ = 2
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_single c hc

lemma siblings_weaklyNull (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) :
    WeaklyNull (fun k => basisVector T (f k)) := by
  let L : (ℕ →₀ ℝ) →ₗ[ℝ] TreeVector T :=
    { toFun := Finsupp.embDomain f
      map_add' := Finsupp.embDomain_add f
      map_smul' := by
        intro r a
        change Finsupp.embDomain f (r • a) = r • Finsupp.embDomain f a
        ext c
        by_cases hc : c ∈ Set.range f
        · obtain ⟨k, rfl⟩ := hc
          simp only [Finsupp.embDomain_apply_self, Finsupp.smul_apply]
        · simp only [Finsupp.embDomain_of_notMem_range f _ c hc, Finsupp.smul_apply, smul_zero] }
  let D : (ℕ →₀ ℝ) →ₗ[ℝ] TreeSpace T :=
    (Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).toLinearMap.comp L
  have he : ∀ k, D (Finsupp.single k 1) = basisVector T (f k) := by
    intro k
    change (↑(show TreeVector T from Finsupp.embDomain f (Finsupp.single k 1)) : TreeSpace T) = _
    rw [Finsupp.embDomain_single]; rfl
  simp_rw [← he]
  refine weaklyNull_of_finsupp_bound D (by norm_num : (0 : ℝ) ≤ 2) ?_
  intro a
  change ‖(↑(show TreeVector T from a.embDomain f) : TreeSpace T)‖ ≤ _
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_emb_siblings s f hf a

def pathVector (s : ι) : TreeSpace T := (show TreeVector T from T.path s)

@[simp] lemma pathVector_norm (s : ι) : ‖pathVector T s‖ = 1 := by
  change ‖(↑(show TreeVector T from T.path s) : TreeSpace T)‖ = 1
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_path s

lemma pathVector_step (c : ι) (hc : c ≠ T.root) :
    pathVector T c - pathVector T (T.parent c) = basisVector T c := by
  let u : TreeVector T := T.path c
  let v : TreeVector T := T.path (T.parent c)
  let e : TreeVector T := Finsupp.single c 1
  have he : u - v = e := by
    change T.path c - T.path (T.parent c) = Finsupp.single c 1
    rw [T.path_step c hc]; abel
  change (↑u : TreeSpace T) - ↑v = ↑e
  rw [← Completion.coe_sub, he]

end

end TreeSpace

def sequenceChildren (s : List ℕ) : ℕ ↪ List ℕ where
  toFun k := s ++ [k]
  inj' := by intro k l h; simpa using h

lemma sequenceChildren_spec (s : List ℕ) (k : ℕ) :
    sequenceChildren s k ≠ sequenceTree.root ∧
      sequenceTree.parent (sequenceChildren s k) = s := by
  change s ++ [k] ≠ [] ∧ (s ++ [k]).dropLast = s
  simp

lemma XSigma_path_increments (s : List ℕ) :
    WeaklyNull (fun k => TreeSpace.pathVector sequenceTree (s ++ [k]) -
      TreeSpace.pathVector sequenceTree s) := by
  have he : ∀ k, TreeSpace.pathVector sequenceTree (s ++ [k]) -
      TreeSpace.pathVector sequenceTree s = TreeSpace.basisVector sequenceTree (sequenceChildren s k) := by
    intro k
    have h := TreeSpace.pathVector_step sequenceTree (sequenceChildren s k)
      (sequenceChildren_spec s k).1
    rw [(sequenceChildren_spec s k).2] at h
    exact h
  simp_rw [he]
  exact TreeSpace.siblings_weaklyNull sequenceTree s (sequenceChildren s) (sequenceChildren_spec s)

theorem XSigma_no_equivalent_AUC (A : EquivalentNorm XSigma) : ¬A.AUC := by
  apply bounded_trees_not_AUC (TreeSpace.not_finite_dimensional sequenceTree) A
    (fun _ s => TreeSpace.pathVector sequenceTree s)
    (m := 1) (M := 1) (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs; simp
  · intro h hh s hs; exact XSigma_path_increments s
  · intro h hh s hs k
    have ht := TreeSpace.pathVector_step sequenceTree (sequenceChildren s k)
      (sequenceChildren_spec s k).1
    rw [(sequenceChildren_spec s k).2] at ht
    change 2 ≤ ‖TreeSpace.pathVector sequenceTree (sequenceChildren s k) - TreeSpace.pathVector sequenceTree s‖
    rw [ht]
    exact (TreeSpace.basisVector_norm sequenceTree _ (sequenceChildren_spec s k).1).ge

namespace TreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

def cutPathVector (s : ι) : TreeSpace T := (show TreeVector T from T.cutPath s)

lemma cutPathVector_norm (s : ι) (hs : s ≠ T.root) : ‖cutPathVector T s‖ = 2 := by
  change ‖(↑(show TreeVector T from T.cutPath s) : TreeSpace T)‖ = 2
  rw [Completion.norm_coe, TreeVector.norm_def]
  exact T.normSum_cutPath s hs

lemma cutPathVector_step (c : ι) (hc : c ≠ T.root) :
    cutPathVector T c - cutPathVector T (T.parent c) = basisVector T c := by
  let u : TreeVector T := T.cutPath c
  let v : TreeVector T := T.cutPath (T.parent c)
  let e : TreeVector T := Finsupp.single c 1
  have he : u - v = e := T.cutPath_step c hc
  change (↑u : TreeSpace T) - ↑v = ↑e
  rw [← Completion.coe_sub, he]

end

end TreeSpace

namespace ZeroTreeSpace

noncomputable section

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

open UniformSpace

def basisVector (c : ι) (hc : c ≠ T.root) : ZeroTreeSpace T :=
  (show ZeroTreeVector T from ⟨Finsupp.single c 1, by
    change (Finsupp.single c (1 : ℝ)) T.root = 0
    simp [hc]⟩)

def pathVector (s : ι) : ZeroTreeSpace T :=
  (show ZeroTreeVector T from ⟨T.cutPath s, T.cutPath_root s⟩)

@[simp] lemma inclusion_basisVector (c : ι) (hc : c ≠ T.root) :
    inclusion T (basisVector T c hc) = TreeSpace.basisVector T c := by
  exact inclusion_coe T (show ZeroTreeVector T from ⟨Finsupp.single c 1, by
    change (Finsupp.single c (1 : ℝ)) T.root = 0
    simp [hc]⟩)

@[simp] lemma inclusion_pathVector (s : ι) :
    inclusion T (pathVector T s) = TreeSpace.cutPathVector T s := by
  exact inclusion_coe T (show ZeroTreeVector T from ⟨T.cutPath s, T.cutPath_root s⟩)

lemma basisVector_norm (c : ι) (hc : c ≠ T.root) : ‖basisVector T c hc‖ = 1 := by
  have h := norm_inclusion T (basisVector T c hc)
  rw [inclusion_basisVector, TreeSpace.basisVector_norm T c hc] at h
  linarith

lemma pathVector_norm (s : ι) (hs : s ≠ T.root) : ‖pathVector T s‖ = 1 := by
  have h := norm_inclusion T (pathVector T s)
  rw [inclusion_pathVector, TreeSpace.cutPathVector_norm T s hs] at h
  linarith

lemma pathVector_step (c : ι) (hc : c ≠ T.root) :
    pathVector T c - pathVector T (T.parent c) = basisVector T c hc := by
  apply inclusion_injective T
  rw [map_sub, inclusion_pathVector, inclusion_pathVector, inclusion_basisVector]
  exact TreeSpace.cutPathVector_step T c hc

lemma siblings_weaklyNull (s : ι) (f : ℕ ↪ ι)
    (hf : ∀ k, f k ≠ T.root ∧ T.parent (f k) = s) :
    WeaklyNull (fun k => basisVector T (f k) (hf k).1) := by
  let L : (ℕ →₀ ℝ) →ₗ[ℝ] TreeVector T :=
    { toFun := Finsupp.embDomain f
      map_add' := Finsupp.embDomain_add f
      map_smul' := by
        intro r a
        change Finsupp.embDomain f (r • a) = r • Finsupp.embDomain f a
        ext c
        by_cases hc : c ∈ Set.range f
        · obtain ⟨k, rfl⟩ := hc
          simp only [Finsupp.embDomain_apply_self, Finsupp.smul_apply]
        · simp only [Finsupp.embDomain_of_notMem_range f _ c hc, Finsupp.smul_apply, smul_zero] }
  have hr : T.root ∉ Set.range f := by
    rintro ⟨k, hk⟩
    exact (hf k).1 hk
  let L₀ : (ℕ →₀ ℝ) →ₗ[ℝ] ZeroTreeVector T :=
    L.codRestrict (TreeVector.coordinate T T.root).ker (fun a => by
      change Finsupp.embDomain f a T.root = 0
      exact Finsupp.embDomain_of_notMem_range f a T.root hr)
  let D : (ℕ →₀ ℝ) →ₗ[ℝ] ZeroTreeSpace T :=
    (Completion.toComplL : ZeroTreeVector T →L[ℝ] ZeroTreeSpace T).toLinearMap.comp L₀
  have he : ∀ k, D (Finsupp.single k 1) = basisVector T (f k) (hf k).1 := by
    intro k
    apply congrArg (Completion.toComplL : ZeroTreeVector T →L[ℝ] ZeroTreeSpace T)
    apply Subtype.ext
    exact Finsupp.embDomain_single f k 1
  simp_rw [← he]
  refine weaklyNull_of_finsupp_bound D (by norm_num : (0 : ℝ) ≤ 1) ?_
  intro a
  change ‖(↑(L₀ a) : ZeroTreeSpace T)‖ ≤ _
  rw [Completion.norm_coe, ZeroTreeVector.norm_half, one_mul]
  change T.normSum (a.embDomain f) / 2 ≤ _
  have h := T.normSum_emb_siblings s f hf a
  linarith

end

end ZeroTreeSpace

def joinedNode (h : ℕ) (s : List ℕ) : JoinedNode :=
  some ⟨⟨h + 1, by omega⟩, ⟨s.take h, by change (s.take h).length ≤ h + 1; simp only [List.length_take]; omega⟩⟩

lemma joinedNode_ne_root (h : ℕ) (s : List ℕ) : joinedNode h s ≠ joinedTree.root := by
  simp [joinedNode, joinedTree]

lemma joinedNode_parent (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    joinedTree.parent (joinedNode h (s ++ [k])) = joinedNode h s := by
  have hs' : s.length ≤ h := hs.le
  have hsk : (s ++ [k]).length ≤ h := by simp; omega
  simp only [joinedNode, List.take_of_length_le hs', List.take_of_length_le hsk]
  change (if s ++ [k] = [] then none else _) = _
  have he : s ++ [k] ≠ [] := by simp
  rw [ite_eq_right he]
  congr 3
  simp

def joinedChildren (h : ℕ) (s : List ℕ) (hs : s.length < h) : ℕ ↪ JoinedNode where
  toFun k := joinedNode h (s ++ [k])
  inj' := by
    intro k l he
    have hsk : (s ++ [k]).length ≤ h := by simp; omega
    have hsl : (s ++ [l]).length ≤ h := by simp; omega
    have hh := congrArg (fun x : JoinedNode => x.map (fun y => y.2.1)) he
    simpa [joinedNode, List.take_of_length_le hsk, List.take_of_length_le hsl] using hh

lemma joinedChildren_spec (h : ℕ) (s : List ℕ) (hs : s.length < h) (k : ℕ) :
    joinedChildren h s hs k ≠ joinedTree.root ∧
      joinedTree.parent (joinedChildren h s hs k) = joinedNode h s :=
  ⟨joinedNode_ne_root _ _, joinedNode_parent h s hs k⟩

lemma XJoined_path_increments (h : ℕ) (s : List ℕ) (hs : s.length < h) :
    WeaklyNull (fun k => TreeSpace.cutPathVector joinedTree (joinedNode h (s ++ [k])) -
      TreeSpace.cutPathVector joinedTree (joinedNode h s)) := by
  have he : ∀ k, TreeSpace.cutPathVector joinedTree (joinedNode h (s ++ [k])) -
      TreeSpace.cutPathVector joinedTree (joinedNode h s) =
      TreeSpace.basisVector joinedTree (joinedChildren h s hs k) := by
    intro k
    have H := TreeSpace.cutPathVector_step joinedTree (joinedChildren h s hs k)
      (joinedChildren_spec h s hs k).1
    have H' := H
    simp only [(joinedChildren_spec h s hs k).2] at H'
    convert H' using 1 ; rfl
  simp_rw [he]
  exact TreeSpace.siblings_weaklyNull joinedTree _ _ (joinedChildren_spec h s hs)

lemma XZero_path_increments (h : ℕ) (s : List ℕ) (hs : s.length < h) :
    WeaklyNull (fun k => ZeroTreeSpace.pathVector joinedTree (joinedNode h (s ++ [k])) -
      ZeroTreeSpace.pathVector joinedTree (joinedNode h s)) := by
  have he : ∀ k, ZeroTreeSpace.pathVector joinedTree (joinedNode h (s ++ [k])) -
      ZeroTreeSpace.pathVector joinedTree (joinedNode h s) =
      ZeroTreeSpace.basisVector joinedTree (joinedChildren h s hs k) (joinedChildren_spec h s hs k).1 := by
    intro k
    have H := ZeroTreeSpace.pathVector_step joinedTree (joinedChildren h s hs k)
      (joinedChildren_spec h s hs k).1
    have H' := H
    simp only [(joinedChildren_spec h s hs k).2] at H'
    convert H' using 1 ; rfl
  simp_rw [he]
  exact ZeroTreeSpace.siblings_weaklyNull joinedTree _ _ (joinedChildren_spec h s hs)

theorem XJoined_no_equivalent_AUC (A : EquivalentNorm XJoined) : ¬A.AUC := by
  apply bounded_trees_not_AUC (TreeSpace.not_finite_dimensional joinedTree) A
    (fun h s => TreeSpace.cutPathVector joinedTree (joinedNode h s))
    (m := 2) (M := 2) (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs
    rw [TreeSpace.cutPathVector_norm _ _ (joinedNode_ne_root h s)]; exact ⟨le_rfl, le_rfl⟩
  · intro h hh s hs; exact XJoined_path_increments h s hs
  · intro h hh s hs k
    have he := TreeSpace.cutPathVector_step joinedTree (joinedNode h (s ++ [k]))
      (joinedNode_ne_root h (s ++ [k]))
    rw [joinedNode_parent h s hs k] at he
    rw [he, TreeSpace.basisVector_norm _ _ (joinedNode_ne_root h (s ++ [k]))]

theorem XZero_no_equivalent_AUC (A : EquivalentNorm XZero) : ¬A.AUC := by
  apply bounded_trees_not_AUC (ZeroTreeSpace.not_finite_dimensional joinedTree) A
    (fun h s => ZeroTreeSpace.pathVector joinedTree (joinedNode h s))
    (m := 1) (M := 1) (c := 1) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs
    rw [ZeroTreeSpace.pathVector_norm _ _ (joinedNode_ne_root h s)]; exact ⟨le_rfl, le_rfl⟩
  · intro h hh s hs; exact XZero_path_increments h s hs
  · intro h hh s hs k
    have he := ZeroTreeSpace.pathVector_step joinedTree (joinedNode h (s ++ [k]))
      (joinedNode_ne_root h (s ++ [k]))
    rw [joinedNode_parent h s hs k] at he
    rw [he, ZeroTreeSpace.basisVector_norm]

namespace EquivalentNorm

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : EquivalentNorm E)

lemma continuous : Continuous A.N := by
  have h : LipschitzWith ⟨A.upper, A.upper_pos.le⟩ A.N := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (A.N x) (A.N y) ≤ A.upper * dist x y
    rw [Real.dist_eq, dist_eq_norm]
    exact A.lipschitz_estimate x y
  exact h.continuous

lemma norming_functional {x : E} (hx : x ≠ 0) :
    ∃ f : E →L[ℝ] ℝ, f x = A.N x ∧ ∀ y, ‖f y‖ ≤ A.N y := by
  let e := LinearEquiv.toSpanNonzeroSingleton ℝ E x hx
  let f : Module.Dual ℝ (Submodule.span ℝ {x}) := (A.N x) • e.symm.toLinearMap
  have hb : ∀ y : Submodule.span ℝ {x}, ‖f y‖ ≤ A.N y := by
    intro y
    obtain ⟨r, rfl⟩ := e.surjective y
    have he : ((e r : Submodule.span ℝ {x}) : E) = r • x := rfl
    change ‖A.N x * e.symm (e r)‖ ≤ _
    rw [e.symm_apply_apply, he, map_smul_eq_mul, norm_mul, Real.norm_of_nonneg (A.nonneg x)]
    exact le_of_eq (mul_comm _ _)
  obtain ⟨g, hg, hgb⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    (Submodule.span ℝ {x}) f A.continuous hb
  refine ⟨g, ?_, hgb⟩
  have he : ((e 1 : Submodule.span ℝ {x}) : E) = x := by
    change (1 : ℝ) • x = x
    simp
  have hg1 := hg (e 1)
  rw [he] at hg1
  simpa [f] using hg1

lemma modulus_nonneg (hE : ¬Module.Finite ℝ E) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ A.modulus t := by
  have hn : {r : ℝ | ∃ x : E, A.N x = 1 ∧ r = sSup (Set.range (A.inner x t))}.Nonempty := by
    obtain ⟨x, hx, hx1⟩ := A.exists_unit CofiniteSubspace.top hE
    exact ⟨_, x, hx1, rfl⟩
  apply le_csInf hn
  rintro r ⟨x, hx1, rfl⟩
  have hx : x ≠ 0 := by intro he; simp [he] at hx1
  obtain ⟨f, hfx, hf⟩ := A.norming_functional hx
  let F : CofiniteSubspace E := ⟨f.ker, f.isClosed_ker, Submodule.CoFG.ker f.toLinearMap⟩
  have hi : 0 ≤ A.inner x t F := by
    apply le_csInf (A.inner_nonempty x t F hE)
    rintro r ⟨y, hy, hy1, rfl⟩
    have hy0 : f y = 0 := hy
    have hb := hf (x + t • y)
    rw [map_add, map_smul, hy0, smul_zero, add_zero, hfx, hx1, norm_one] at hb
    linarith
  have hb : BddAbove (Set.range (A.inner x t)) := by
    refine ⟨t, ?_⟩
    rintro r ⟨F, rfl⟩
    exact A.inner_upper hx1 ht F hE
  exact hi.trans (le_csSup hb (Set.mem_range_self _))

end EquivalentNorm

theorem bounded_trees_modulus_eq_zero {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : ¬Module.Finite ℝ E) (A : EquivalentNorm E) (u : ℕ → List ℕ → E)
    {m M c : ℝ} (hm : 0 < m) (hM : 0 < M) (hc : 0 < c)
    (hu : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length ≤ h → m ≤ ‖u h s‖ ∧ ‖u h s‖ ≤ M)
    (hd : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      WeaklyNull (fun k => u h (s ++ [k]) - u h s))
    (hdc : ∀ h : ℕ, 1 ≤ h → ∀ s : List ℕ, s.length < h →
      ∀ k, c ≤ ‖u h (s ++ [k]) - u h s‖) :
    A.modulus (A.lower * c / (2 * A.upper * M)) = 0 := by
  apply le_antisymm (bounded_trees_modulus_le_zero hE A u hm hM hc hu hd hdc)
  apply A.modulus_nonneg hE
  have := A.lower_pos
  have := A.upper_pos
  positivity

theorem XSigma_one_sided_modulus_zero (A : EquivalentNorm XSigma) :
    A.modulus (A.lower / A.upper) = 0 := by
  have he : A.lower * 2 / (2 * A.upper * 1) = A.lower / A.upper := by field_simp [A.upper_pos.ne']
  rw [← he]
  apply bounded_trees_modulus_eq_zero (TreeSpace.not_finite_dimensional sequenceTree) A
    (fun _ s => TreeSpace.pathVector sequenceTree s)
    (m := 1) (M := 1) (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs; simp
  · intro h hh s hs; exact XSigma_path_increments s
  · intro h hh s hs k
    have ht := TreeSpace.pathVector_step sequenceTree (sequenceChildren s k)
      (sequenceChildren_spec s k).1
    rw [(sequenceChildren_spec s k).2] at ht
    change 2 ≤ ‖TreeSpace.pathVector sequenceTree (sequenceChildren s k) - TreeSpace.pathVector sequenceTree s‖
    rw [ht]
    exact (TreeSpace.basisVector_norm sequenceTree _ (sequenceChildren_spec s k).1).ge

theorem XJoined_one_sided_modulus_zero (A : EquivalentNorm XJoined) :
    A.modulus (A.lower / (2 * A.upper)) = 0 := by
  have he : A.lower * 2 / (2 * A.upper * 2) = A.lower / (2 * A.upper) := by field_simp [A.upper_pos.ne']
  rw [← he]
  apply bounded_trees_modulus_eq_zero (TreeSpace.not_finite_dimensional joinedTree) A
    (fun h s => TreeSpace.cutPathVector joinedTree (joinedNode h s))
    (m := 2) (M := 2) (c := 2) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs
    rw [TreeSpace.cutPathVector_norm _ _ (joinedNode_ne_root h s)]; exact ⟨le_rfl, le_rfl⟩
  · intro h hh s hs; exact XJoined_path_increments h s hs
  · intro h hh s hs k
    have he := TreeSpace.cutPathVector_step joinedTree (joinedNode h (s ++ [k]))
      (joinedNode_ne_root h (s ++ [k]))
    rw [joinedNode_parent h s hs k] at he
    rw [he, TreeSpace.basisVector_norm _ _ (joinedNode_ne_root h (s ++ [k]))]

theorem XZero_one_sided_modulus_zero (A : EquivalentNorm XZero) :
    A.modulus (A.lower / (2 * A.upper)) = 0 := by
  have he : A.lower * 1 / (2 * A.upper * 1) = A.lower / (2 * A.upper) := by field_simp [A.upper_pos.ne']
  rw [← he]
  apply bounded_trees_modulus_eq_zero (ZeroTreeSpace.not_finite_dimensional joinedTree) A
    (fun h s => ZeroTreeSpace.pathVector joinedTree (joinedNode h s))
    (m := 1) (M := 1) (c := 1) (by norm_num) (by norm_num) (by norm_num)
  · intro h hh s hs
    rw [ZeroTreeSpace.pathVector_norm _ _ (joinedNode_ne_root h s)]; exact ⟨le_rfl, le_rfl⟩
  · intro h hh s hs; exact XZero_path_increments h s hs
  · intro h hh s hs k
    have he := ZeroTreeSpace.pathVector_step joinedTree (joinedNode h (s ++ [k]))
      (joinedNode_ne_root h (s ++ [k]))
    rw [joinedNode_parent h s hs k] at he
    rw [he, ZeroTreeSpace.basisVector_norm]

lemma weighted_square_bound {a r k B : ℝ} (hk : 0 ≤ k) (hB : 0 ≤ B)
    (hr : r ^ 2 ≤ k * B) : (a + r) ^ 2 ≤ (k + 1) * (a ^ 2 + B) := by
  by_cases hk0 : k = 0
  · subst k
    have hr0 : r = 0 := by nlinarith [sq_nonneg r]
    simp only [hr0, add_zero, zero_add, one_mul]
    linarith
  · have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
    have hc : k * (2 * a * r - k * a ^ 2 - B) ≤ 0 := by
      nlinarith [sq_nonneg (k * a - r)]
    have hh : 2 * a * r - k * a ^ 2 - B ≤ 0 :=
      (mul_le_mul_iff_right₀ hkpos).mp (by simpa only [mul_comm, mul_zero] using hc)
    nlinarith

end RecursivePotentials

end OAI
