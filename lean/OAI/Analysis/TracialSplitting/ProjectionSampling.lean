import OAI.Analysis.TracialSplitting.ProjectionRounding

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FiniteLinearTests

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_norm_projection_mul_le (τ : TracialState D) {e : D}
    (he : IsStarProjection e) (b : D) :
    ‖τ.functional (e * b)‖ ≤ ‖b‖ * (τ.functional e).re := by
  rw [← trace_projection_corner τ he b]
  calc
    _ ≤ traceTwoNorm τ (e * b) * traceTwoNorm τ e := trace_norm_mul_le τ _ _
    _ ≤ (‖b‖ * traceTwoNorm τ e) * traceTwoNorm τ e :=
      mul_le_mul_of_nonneg_right (traceTwoNorm_mul_right τ b e) (traceTwoNorm_nonneg τ e)
    _ = ‖b‖ * (τ.functional e).re := by
      rw [← traceTwoNorm_projection_sq τ he]; ring

lemma trace_compression_error (τ : TracialState D) {e q : D}
    (he : IsStarProjection e) (hq : IsStarProjection q) (heq : e ≤ q)
    (b : D) (α : ℂ) :
    ‖τ.functional (e * b) - α * τ.functional e‖ ≤
      ‖q * b * q - α • q‖ * (τ.functional e).re := by
  have heq' := (he.le_iff_mul_eq_left hq).mp heq
  have hqe' := (he.le_iff_mul_eq_right hq).mp heq
  have htrace : τ.functional (e * (q * b * q - α • q)) =
      τ.functional (e * b) - α * τ.functional e := by
    rw [mul_sub, mul_smul_comm, heq', map_sub, map_smul]
    change τ.functional (e * (q * b * q)) - α * τ.functional e = _
    congr 1
    calc
      _ = τ.functional (e * b * q) := by rw [← mul_assoc, ← mul_assoc, heq']
      _ = τ.functional (q * (e * b)) := τ.tracial _ _
      _ = _ := by rw [← mul_assoc, hqe']
  rw [← htrace]
  exact trace_norm_projection_mul_le τ he _

lemma scalar_splitting_error (τ : TracialState D) {e q : D}
    (he : IsStarProjection e) (hq : IsStarProjection q) (heq : e ≤ q)
    {s γ : ℝ} (hs : 0 ≤ s) (b : D) (α : ℂ)
    (hγ : ‖q * b * q - α • q‖ ≤ γ) :
    ‖τ.functional (e * b) - (s : ℂ) * τ.functional (q * b)‖ ≤
      γ * ((τ.functional e).re + s * (τ.functional q).re) +
      ‖α‖ * ‖τ.functional e - (s : ℂ) * τ.functional q‖ := by
  have hbe := (trace_compression_error τ he hq heq b α).trans
    (mul_le_mul_of_nonneg_right hγ (τ.functional.map_nonneg he.nonneg).1)
  have hbq := (trace_compression_error τ hq hq le_rfl b α).trans
    (mul_le_mul_of_nonneg_right hγ (τ.functional.map_nonneg hq.nonneg).1)
  have heqv : τ.functional (e * b) - (s : ℂ) * τ.functional (q * b) =
      (τ.functional (e * b) - α * τ.functional e) +
      α * (τ.functional e - (s : ℂ) * τ.functional q) +
      (s : ℂ) * (α * τ.functional q - τ.functional (q * b)) := by ring
  rw [heqv]
  calc
    _ ≤ ‖τ.functional (e * b) - α * τ.functional e‖ +
        ‖α * (τ.functional e - (s : ℂ) * τ.functional q)‖ +
        ‖(s : ℂ) * (α * τ.functional q - τ.functional (q * b))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ = ‖τ.functional (e * b) - α * τ.functional e‖ +
        ‖α‖ * ‖τ.functional e - (s : ℂ) * τ.functional q‖ +
        s * ‖τ.functional (q * b) - α * τ.functional q‖ := by
      rw [norm_mul, norm_mul, norm_sub_rev (α * _), Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ γ * (τ.functional e).re +
        ‖α‖ * ‖τ.functional e - (s : ℂ) * τ.functional q‖ +
        s * (γ * (τ.functional q).re) := by gcongr
    _ = _ := by ring

theorem split_finite_linear_tests (hRR : RealRankZero D)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ)
    {q : D} (hq : IsStarProjection q) {s : ℝ} (hs : s ∈ Set.Icc 0 1)
    (F : Finset D) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧ e ≤ q ∧ ∀ b ∈ F, ∀ τ : TracialState D,
      ‖τ.functional (e * b) - (s : ℂ) * τ.functional (q * b)‖ < ε := by
  classical
  let γ := ε / 4
  have hγ : 0 < γ := div_pos hε (by norm_num)
  obtain ⟨P, hP⟩ := scalar_compressions hRR hq F hγ
  choose α hα using (fun i : P.Index => fun b : F => hP b.val b.property i)
  let M := ∑ i : P.Index, ∑ b : F, ‖α i b‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun b _ => norm_nonneg _
  let δ := ε / (4 * (M + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hpieces := fun i : P.Index => proportional_subprojection hRR hsmall
    (P.isProjection i) hs hδ
  choose E hE hEP hEtrace using hpieces
  have horth : Pairwise (fun i j => E i * E j = 0) := by
    intro i j hij
    exact mul_eq_zero_of_supports ((hE i).le_iff_mul_eq_left (P.isProjection i) |>.mp (hEP i))
      ((hE j).le_iff_mul_eq_right (P.isProjection j) |>.mp (hEP j)) (P.orthogonal hij)
  let e := ∑ i : P.Index, E i
  have he : IsStarProjection e := orthogonal_projection_sum Finset.univ E
    (fun i _ => hE i) (fun _ _ _ _ hij => horth hij)
  have heq : e ≤ q := by
    rw [← P.sum_eq]
    exact Finset.sum_le_sum fun i _ => hEP i
  refine ⟨e, he, heq, ?_⟩
  intro b hb τ
  let B : F := ⟨b, hb⟩
  have hscalars : (∑ i : P.Index, ‖α i B‖) ≤ M := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun x _ => norm_nonneg _) (Finset.mem_univ B)
  have hte : (∑ i : P.Index, (τ.functional (E i)).re) = (τ.functional e).re := by
    simp only [e, map_sum, Complex.re_sum]
  have htq : (∑ i : P.Index, (τ.functional (P.piece i)).re) = (τ.functional q).re := by
    have h := congrArg (fun x => (τ.functional x).re) P.sum_eq
    simpa only [map_sum, Complex.re_sum] using h
  have hmass : (τ.functional e).re + s * (τ.functional q).re ≤ 2 := by
    have hq0 := (τ.functional.map_nonneg hq.nonneg).1
    have hq1 := trace_projection_le_one τ hq
    have he1 := trace_projection_le_one τ he
    nlinarith [hs.1, hs.2]
  have hδM : δ * M ≤ ε / 4 := by
    have heqδ : δ * (4 * (M + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt (by positivity))
    nlinarith [hδ.le]
  have hsum : τ.functional (e * b) - (s : ℂ) * τ.functional (q * b) =
      ∑ i : P.Index, (τ.functional (E i * b) - (s : ℂ) * τ.functional (P.piece i * b)) := by
    calc
      _ = τ.functional ((∑ i, E i) * b) -
          (s : ℂ) * τ.functional ((∑ i, P.piece i) * b) := by rw [P.sum_eq]
      _ = _ := by simp only [Finset.sum_mul, map_sum,
        Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsum]
  calc
    _ ≤ ∑ i : P.Index, ‖τ.functional (E i * b) -
        (s : ℂ) * τ.functional (P.piece i * b)‖ := norm_sum_le _ _
    _ ≤ ∑ i : P.Index, (γ * ((τ.functional (E i)).re + s * (τ.functional (P.piece i)).re)
        + ‖α i B‖ * δ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (scalar_splitting_error τ (hE i) (P.isProjection i) (hEP i)
        hs.1 b (α i B) (hα i B).le).trans
        (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hEtrace i τ).le (norm_nonneg _)))
    _ = γ * ((τ.functional e).re + s * (τ.functional q).re) +
        δ * ∑ i : P.Index, ‖α i B‖ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib,
        ← Finset.mul_sum, hte, htq, ← Finset.sum_mul, mul_comm _ δ]
    _ ≤ γ * 2 + δ * M := add_le_add
      (mul_le_mul_of_nonneg_left hmass hγ.le) (mul_le_mul_of_nonneg_left hscalars hδ.le)
    _ ≤ γ * 2 + ε / 4 := add_le_add (le_refl _) hδM
    _ < ε := by dsimp [γ]; linarith

end FiniteLinearTests

section OrthogonalInsertion

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_mul_mono_right (τ : TracialState D) {a b c : D} (ha : 0 ≤ a) (hbc : b ≤ c) :
    (τ.functional (a * b)).re ≤ (τ.functional (a * c)).re := by
  have h := (trace_mul_nonneg τ ha (sub_nonneg.mpr hbc)).1
  simp only [mul_sub, map_sub, Complex.sub_re, Complex.zero_re] at h
  linarith

lemma trace_mul_mono_left (τ : TracialState D) {a b c : D} (hc : 0 ≤ c) (hab : a ≤ b) :
    (τ.functional (a * c)).re ≤ (τ.functional (b * c)).re := by
  rw [τ.tracial a c, τ.tracial b c]
  exact trace_mul_mono_right τ hc hab

lemma trace_projection_difference_sq (τ : TracialState D) {t y : D}
    (ht : IsStarProjection t) (hy : IsStarProjection y) :
    traceTwoNorm τ (t - y) ^ 2 =
      (τ.functional t).re + (τ.functional y).re - 2 * (τ.functional (t * y)).re := by
  rw [traceTwoNorm_sq]
  simp only [star_sub, ht.isSelfAdjoint.star_eq, hy.isSelfAdjoint.star_eq,
    sub_mul, mul_sub, ht.isIdempotentElem.eq, hy.isIdempotentElem.eq, map_sub,
    Complex.sub_re, τ.tracial y t]
  ring

lemma projection_difference_linear (τ : TracialState D) {t y : D}
    (ht : IsStarProjection t) (hy : IsStarProjection y)
    (hmass : (τ.functional t).re ≤ (τ.functional y).re) {x : D} (hx : ‖x‖ ≤ 1) :
    ‖τ.functional ((t - y) * x)‖ ≤
      2 * Real.sqrt (τ.functional y).re * traceTwoNorm τ (t - y) := by
  have hts : traceTwoNorm τ t ≤ traceTwoNorm τ y := by
    have h := Real.sqrt_le_sqrt hmass
    simpa only [traceTwoNorm, ht.isSelfAdjoint.star_eq, ht.isIdempotentElem.eq,
      hy.isSelfAdjoint.star_eq, hy.isIdempotentElem.eq] using h
  have hxy : traceTwoNorm τ ((t - y) * x) ≤ traceTwoNorm τ (t - y) :=
    (traceTwoNorm_mul_right τ x (t - y)).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (traceTwoNorm_nonneg τ _))
  have hyx : traceTwoNorm τ (y * x) ≤ traceTwoNorm τ y :=
    (traceTwoNorm_mul_right τ x y).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hx (traceTwoNorm_nonneg τ _))
  have hdecomp : (t - y) * x = t * ((t - y) * x) + (t - y) * (y * x) := by
    calc
      _ = (t * (t - y) + (t - y) * y) * x := by
        simp only [mul_sub, sub_mul, ht.isIdempotentElem.eq, hy.isIdempotentElem.eq]
        noncomm_ring
      _ = _ := by noncomm_ring
  rw [hdecomp, map_add]
  calc
    _ ≤ ‖τ.functional (t * ((t - y) * x))‖ + ‖τ.functional ((t - y) * (y * x))‖ :=
      norm_add_le _ _
    _ ≤ traceTwoNorm τ t * traceTwoNorm τ ((t - y) * x) +
        traceTwoNorm τ (t - y) * traceTwoNorm τ (y * x) :=
      add_le_add (trace_norm_mul_le τ _ _) (trace_norm_mul_le τ _ _)
    _ ≤ traceTwoNorm τ y * traceTwoNorm τ (t - y) +
        traceTwoNorm τ (t - y) * traceTwoNorm τ y :=
      add_le_add
        (mul_le_mul hts hxy (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _))
        (mul_le_mul_of_nonneg_left hyx (traceTwoNorm_nonneg τ _))
    _ = _ := by
      have hyv : traceTwoNorm τ y = Real.sqrt (τ.functional y).re := by
        simp only [traceTwoNorm, hy.isSelfAdjoint.star_eq, hy.isIdempotentElem.eq]
      rw [hyv]; ring

lemma projection_insert_normalized {f h : D} (hf : IsStarProjection f)
    (hh : IsStarProjection h) {c : ℝ} (hc : 0 < c) (hbound : c • f ≤ f * h * f) :
    ∃ t : D, IsStarProjection t ∧ t ≤ h ∧ f * t * f = f * h * f ∧
      ∀ τ : TracialState D, τ.functional t = τ.functional f := by
  obtain ⟨z, hz, hn⟩ := exists_corner_normalizer hf hh.nonneg hc hbound
  let a := f * h * f
  have hzf : (z : D) * f = z := z.property.2
  have hfz : f * (z : D) = z := z.property.1
  have haf : a * f = a := by dsimp [a]; rw [mul_assoc, hf.isIdempotentElem]
  have hfa : f * a = a := by dsimp [a]; rw [← mul_assoc, ← mul_assoc, hf.isIdempotentElem]
  have hzan : (z : D) * a * (z : D) = f := by
    calc
      _ = ((z : D) * f) * h * (f * (z : D)) := by dsimp [a]; simp only [mul_assoc]
      _ = (z : D) * h * (z : D) := by rw [hzf, hfz]
      _ = f := hn
  have haz : a * (z : D) = (z : D) * a := by
    calc
      _ = f * (a * (z : D)) := by rw [← mul_assoc, hfa]
      _ = ((z : D) * a * (z : D)) * (a * (z : D)) := by rw [hzan]
      _ = (z : D) * a * ((z : D) * a * (z : D)) := by simp only [mul_assoc]
      _ = (z : D) * a := by rw [hzan, mul_assoc, haf]
  let v := h * (z : D)
  have hv : star v * v = f := by
    dsimp [v]
    rw [star_mul, (ProjectionCorner.isSelfAdjoint_coe hf hz).star_eq,
      hh.isSelfAdjoint.star_eq]
    simpa only [mul_assoc, ← mul_assoc h h, hh.isIdempotentElem.eq] using hn
  have hhv : h * v = v := by dsimp [v]; rw [← mul_assoc, hh.isIdempotentElem]
  have ht : IsStarProjection (v * star v) :=
    ⟨isIdempotentElem_star_mul_self_iff_isIdempotentElem_self_mul_star.mp
      (hv ▸ hf.isIdempotentElem), by simp only [IsSelfAdjoint, star_mul, star_star]⟩
  have hth : v * star v ≤ h := (ht.le_iff_mul_eq_right hh).mpr (by rw [← mul_assoc, hhv])
  refine ⟨v * star v, ht, hth, ?_, fun τ => ?_⟩
  · have hfv : f * v = a * (z : D) := by
      dsimp [v, a]; simp only [mul_assoc, hfz]
    have hvf : star v * f = (z : D) * a := by
      dsimp [v, a]
      rw [star_mul, (ProjectionCorner.isSelfAdjoint_coe hf hz).star_eq, hh.isSelfAdjoint.star_eq]
      simp only [← mul_assoc, hzf]
    calc
      _ = (f * v) * (star v * f) := by simp only [mul_assoc]
      _ = (a * (z : D)) * ((z : D) * a) := by rw [hfv, hvf]
      _ = ((z : D) * a * (z : D)) * a := by rw [haz]; simp only [mul_assoc]
      _ = a := by rw [hzan, hfa]
      _ = _ := rfl
  · rw [τ.tracial v (star v), hv]

theorem orthogonal_insertion (hRR : RealRankZero D) {z y : D}
    (hz : IsStarProjection z) (hy : IsStarProjection y) :
    ∃ t : D, IsStarProjection t ∧ t ≤ 1 - z ∧ ∀ τ : TracialState D,
      ((τ.functional y).re - 3 * (τ.functional (y * z)).re ≤ (τ.functional t).re ∧
      (τ.functional t).re ≤ (τ.functional y).re) ∧
      traceTwoNorm τ (t - y) ^ 2 ≤ 5 * (τ.functional (y * z)).re ∧
      ∀ x : D, ‖x‖ ≤ 1 → ‖τ.functional ((t - y) * x)‖ ≤
        2 * Real.sqrt (τ.functional y).re * traceTwoNorm τ (t - y) := by
  obtain ⟨d, hd, hdy, hlow, hupp⟩ := exists_column_cut hRR hy hz.isSelfAdjoint
  let f := y - d
  have hf : IsStarProjection f := (hd.le_iff_sub hy).mp hdy
  have hfy : f ≤ y := by dsimp [f]; exact sub_le_self _ hd.nonneg
  have hfd : f + d = y := by dsimp [f]; abel
  have hbound : (3 / 8 : ℝ) • f ≤ f * (1 - z) * f := by
    have heq : f * (1 - z) * f = f - f * z * f := by
      rw [mul_sub f 1 z, mul_one, sub_mul, hf.isIdempotentElem]
    rw [heq]
    change f * z * f ≤ (5 / 8 : ℝ) • f at hupp
    have heqf : f - (5 / 8 : ℝ) • f = (3 / 8 : ℝ) • f := by module
    have h := sub_le_sub (le_refl f) hupp
    rwa [heqf] at h
  obtain ⟨t, ht, htz, hftf, htrace⟩ := projection_insert_normalized hf hz.one_sub
    (by norm_num : (0 : ℝ) < 3 / 8) hbound
  refine ⟨t, ht, htz, ?_⟩
  intro τ
  have htf : (τ.functional t).re = (τ.functional f).re := congrArg Complex.re (htrace τ)
  have htd : (τ.functional f).re + (τ.functional d).re = (τ.functional y).re := by
    have h := congrArg (fun x => (τ.functional x).re) hfd
    simpa only [map_add, Complex.add_re] using h
  have hyz0 : 0 ≤ (τ.functional (y * z)).re := (trace_mul_nonneg τ hy.nonneg hz.nonneg).1
  have hdz : (τ.functional (d * z)).re ≤ (τ.functional (y * z)).re :=
    trace_mul_mono_left τ hz.nonneg hdy
  have hsz : (3 / 8 : ℝ) * (τ.functional d).re ≤ (τ.functional (d * z)).re := by
    have h := (Complex.le_def.mp (τ.functional.monotone hlow)).1
    change (τ.functional ((3 / 8 : ℝ) • d)).re ≤ (τ.functional (d * z * d)).re at h
    rw [τ.functional.map_smul_of_tower, trace_projection_corner τ hd, Complex.smul_re, smul_eq_mul] at h
    exact h
  have hmasslow : (τ.functional y).re - 3 * (τ.functional (y * z)).re ≤ (τ.functional t).re := by
    linarith
  have hmassup : (τ.functional t).re ≤ (τ.functional y).re := by
    rw [htf]
    exact (Complex.le_def.mp (τ.functional.monotone hfy)).1
  have hty : (τ.functional f).re - (τ.functional (f * z)).re ≤
      (τ.functional (t * y)).re := by
    have heqt : τ.functional (t * f) = τ.functional f - τ.functional (f * z) := by
      rw [τ.tracial t f, ← trace_projection_corner τ hf t, hftf,
        trace_projection_corner τ hf (1 - z), mul_sub, mul_one, map_sub]
    rw [← Complex.sub_re, ← heqt]
    exact trace_mul_mono_right τ ht.nonneg hfy
  have hfz : (τ.functional (f * z)).re ≤ (τ.functional (y * z)).re :=
    trace_mul_mono_left τ hz.nonneg hfy
  refine ⟨⟨hmasslow, hmassup⟩, ?_, fun x hx => projection_difference_linear τ ht hy hmassup hx⟩
  rw [trace_projection_difference_sq τ ht hy]
  linarith

end OrthogonalInsertion

section MatrixRows

variable {D : Type uD} [CStarAlgebra D]

structure ProjectionRow (I : Type uI) [Fintype I] (q : D) where
  projection : IsStarProjection q
  entry : I → D
  gram_diag : ∀ i, star (entry i) * entry i = q
  gram_offdiag : ∀ i j, i ≠ j → star (entry i) * entry j = 0

namespace ProjectionRow

variable {I : Type uI} [Fintype I] {q : D} (U : ProjectionRow I q)

lemma right_support (i : I) : U.entry i * q = U.entry i :=
  partialIsometry_right_support U.projection (U.gram_diag i)

lemma left_support (i : I) : q * star (U.entry i) = star (U.entry i) := by
  simpa only [star_mul, U.projection.isSelfAdjoint.star_eq] using
    congrArg star (U.right_support i)

def coeff (a : D) (i j : I) : D := U.entry i * a * star (U.entry j)

lemma coeff_star (a : D) (i j : I) : star (U.coeff a i j) = U.coeff (star a) j i := by
  simp only [coeff, star_mul, star_star, mul_assoc]

lemma coeff_mul [DecidableEq I] (a b : D) (hb : q * b = b) (i j k l : I) :
    U.coeff a i j * U.coeff b k l =
      if j = k then U.coeff (a * b) i l else 0 := by
  classical
  rw [show U.coeff a i j * U.coeff b k l =
    (U.entry i * a) * (star (U.entry j) * U.entry k) * (b * star (U.entry l)) by
      dsimp [coeff]; noncomm_ring]
  by_cases h : j = k
  · subst k
    rw [ite_eq_left rfl, U.gram_diag]
    simp only [coeff, mul_assoc]
    rw [← mul_assoc q b, hb]
  · rw [ite_eq_right h, U.gram_offdiag j k h, mul_zero, zero_mul]

def sample (a : D) : D := ∑ i, U.coeff a i i

def matrix (a : D) (s : Matrix I I ℂ) : D := ∑ i, ∑ j, s i j • U.coeff a i j

lemma sample_star (a : D) : star (U.sample a) = U.sample (star a) := by
  simp only [sample, star_sum, U.coeff_star]

lemma sample_mul (a b : D) (hb : q * b = b) :
    U.sample a * U.sample b = U.sample (a * b) := by
  classical
  simp only [sample, Finset.sum_mul, Finset.mul_sum, U.coeff_mul a b hb]
  simp

lemma sample_projection {e : D} (he : IsStarProjection e) (hqe : q * e = e) :
    IsStarProjection (U.sample e) := by
  constructor
  · change U.sample e * U.sample e = U.sample e
    rw [U.sample_mul _ _ hqe, he.isIdempotentElem.eq]
  · change star (U.sample e) = U.sample e
    rw [U.sample_star, he.isSelfAdjoint.star_eq]

lemma range_projection : IsStarProjection (U.sample q) :=
  U.sample_projection U.projection U.projection.isIdempotentElem

lemma sample_le [PartialOrder D] [StarOrderedRing D] {e : D}
    (he : IsStarProjection e) (heq : e ≤ q) : U.sample e ≤ U.sample q := by
  have hqe := (he.le_iff_mul_eq_right U.projection).mp heq
  have heq' := (he.le_iff_mul_eq_left U.projection).mp heq
  apply ((U.sample_projection he hqe).le_iff_mul_eq_left U.range_projection).mpr
  rw [U.sample_mul _ _ U.projection.isIdempotentElem, heq']

lemma matrix_star (a : D) (s : Matrix I I ℂ) :
    star (U.matrix a s) = U.matrix (star a) (star s) := by
  simp only [matrix, star_sum, star_smul, U.coeff_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

lemma matrix_mul (a b : D) (hb : q * b = b) (s t : Matrix I I ℂ) :
    U.matrix a s * U.matrix b t = U.matrix (a * b) (s * t) := by
  classical
  calc
    _ = ∑ i, ∑ j, ∑ k, ∑ l, (s i j * t k l) •
        (if j = k then U.coeff (a * b) i l else 0) := by
      unfold matrix
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      rw [smul_mul_smul_comm, U.coeff_mul a b hb]
    _ = ∑ i, ∑ j, ∑ l, (s i j * t j l) • U.coeff (a * b) i l := by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      rw [Finset.sum_comm]
      simp
    _ = U.matrix (a * b) (s * t) := by
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]
      simp only [Matrix.mul_apply, Finset.sum_smul]

lemma matrix_one [DecidableEq I] (a : D) : U.matrix a 1 = U.sample a := by
  classical
  simp [matrix, sample, Matrix.one_apply]

lemma sample_matrix (a b : D) (hb : q * b = b) (s : Matrix I I ℂ) :
    U.sample a * U.matrix b s = U.matrix (a * b) s := by
  classical
  rw [← U.matrix_one, U.matrix_mul _ _ hb, one_mul]

lemma matrix_sample (a b : D) (hb : q * b = b) (s : Matrix I I ℂ) :
    U.matrix a s * U.sample b = U.matrix (a * b) s := by
  classical
  rw [← U.matrix_one, U.matrix_mul _ _ hb, mul_one]

lemma trace_coeff [DecidableEq I] [PartialOrder D] (τ : TracialState D) (a : D) (ha : a * q = a)
    (i j : I) : τ.functional (U.coeff a i j) = if i = j then τ.functional a else 0 := by
  classical
  rw [coeff, τ.tracial (U.entry i * a) (star (U.entry j)), ← mul_assoc]
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl, U.gram_diag, τ.tracial q a, ha]
  · rw [ite_eq_right h, U.gram_offdiag j i (Ne.symm h), zero_mul, map_zero]

lemma trace_sample [PartialOrder D] (τ : TracialState D) (a : D) (ha : a * q = a) :
    τ.functional (U.sample a) = (Fintype.card I : ℂ) * τ.functional a := by
  classical
  simp only [sample, map_sum, U.trace_coeff τ a ha, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma trace_matrix [PartialOrder D] (τ : TracialState D) (a : D) (ha : a * q = a)
    (s : Matrix I I ℂ) : τ.functional (U.matrix a s) = Matrix.trace s * τ.functional a := by
  classical
  simp [matrix, U.trace_coeff τ a ha, Matrix.trace, Finset.sum_mul]

lemma matrix_sample_commute {e : D}
    (hqe : q * e = e) (heq : e * q = e) (s : Matrix I I ℂ) :
    Commute (U.matrix q s) (U.sample e) := by
  rw [commute_iff_eq, U.matrix_sample _ _ hqe, U.sample_matrix _ _ U.projection.isIdempotentElem,
    hqe, heq]

end ProjectionRow

end MatrixRows

section SamplingEstimates

lemma proportional_complex_bound {u v : ℂ} {a b C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hu : ‖u‖ ≤ C * a) (hv : ‖v‖ ≤ C * b)
    (hcross : u * (b : ℂ) = v * (a : ℂ)) (c : ℝ) :
    ‖u - (c : ℂ) * v‖ ≤ C * |a - c * b| := by
  by_cases hb : b = 0
  · have ha0 : a = 0 := le_antisymm (hb ▸ hab) ha
    have hu0 : u = 0 := norm_le_zero_iff.mp (by simpa only [ha0, mul_zero] using hu)
    have hv0 : v = 0 := norm_le_zero_iff.mp (by simpa only [hb, mul_zero] using hv)
    simp [ha0, hb, hu0, hv0]
  · have hbpos : 0 < b := lt_of_le_of_ne (ha.trans hab) (Ne.symm hb)
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
    let α : ℂ := v / (b : ℂ)
    have hvEq : v = α * (b : ℂ) := by dsimp [α]; rw [div_mul_cancel₀ _ hbC]
    have huEq : u = α * (a : ℂ) := by
      calc
        _ = (v * (a : ℂ)) / (b : ℂ) := (eq_div_iff hbC).mpr hcross
        _ = _ := by dsimp [α]; ring
    have hα : ‖α‖ ≤ C := by
      dsimp [α]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbpos]
      exact (div_le_iff₀ hbpos).mpr hv
    have hdiff : u - (c : ℂ) * v = α * ((a - c * b : ℝ) : ℂ) := by
      rw [huEq, hvEq]
      push_cast
      ring
    rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hα (abs_nonneg _)

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
lemma norm_square_difference (a b : D) :
    ‖star a * a - star b * b‖ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  calc
    _ = ‖star a * (a - b) + star (a - b) * b‖ := by
      congr 1; rw [star_sub]; noncomm_ring
    _ ≤ ‖star a * (a - b)‖ + ‖star (a - b) * b‖ := norm_add_le _ _
    _ ≤ ‖a‖ * ‖a - b‖ + ‖a - b‖ * ‖b‖ := by
      simpa only [norm_star] using add_le_add (norm_mul_le (star a) (a - b))
        (norm_mul_le (star (a - b)) b)
    _ = _ := by ring

lemma trace_supported_norm_le (τ : TracialState D) {p a : D}
    (hp : IsStarProjection p) (hpa : p * a = a) :
    ‖τ.functional a‖ ≤ ‖a‖ * (τ.functional p).re := by
  simpa only [hpa] using trace_norm_projection_mul_le τ hp a

lemma sampling_compression_estimates (τ : TracialState D) {p y z x : D}
    (hp : IsStarProjection p) (hy : IsStarProjection y) (hyp : y ≤ p)
    (hyz : Commute y z) (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 2)
    {η : ℝ} (hclose : ‖p * x * p - z‖ ≤ η) :
    ‖τ.functional (y * x) - τ.functional (z * y)‖ ≤ η * (τ.functional y).re ∧
    |traceTwoNorm τ (y * x * y) ^ 2 - (τ.functional (star z * z * y)).re| ≤
      3 * η * (τ.functional y).re := by
  have hyp' := (hy.le_iff_mul_eq_left hp).mp hyp
  have hpy := (hy.le_iff_mul_eq_right hp).mp hyp
  have hyz' : y * z = z * y := hyz.eq
  have hym0 : 0 ≤ (τ.functional y).re := (τ.functional.map_nonneg hy.nonneg).1
  constructor
  · have ht : τ.functional (y * (p * x * p - z)) =
        τ.functional (y * x) - τ.functional (z * y) := by
      rw [mul_sub, map_sub, τ.tracial y z]
      congr 1
      calc
        _ = τ.functional (y * x * p) := by rw [← mul_assoc, ← mul_assoc, hyp']
        _ = τ.functional (p * (y * x)) := τ.tracial _ _
        _ = _ := by rw [← mul_assoc, hpy]
    rw [← ht]
    exact (trace_norm_projection_mul_le τ hy _).trans
      (mul_le_mul_of_nonneg_right hclose hym0)
  · let R := y * x * y
    let S := z * y
    have hdf : R - S = y * (p * x * p - z) * y := by
      have hpx : y * (p * x * p) * y = y * x * y := by
        calc
          _ = (y * p) * x * (p * y) := by noncomm_ring
          _ = _ := by rw [hyp', hpy]
      have hzy : y * z * y = z * y := by
        rw [hyz', mul_assoc z y y, hy.isIdempotentElem]
      dsimp [R, S]
      rw [mul_sub, sub_mul, hpx, hzy]
    have hRS : ‖R - S‖ ≤ η := by
      rw [hdf]
      exact (norm_compress_le hy _).trans hclose
    have hR : ‖R‖ ≤ 1 := (norm_compress_le hy x).trans hx
    have hS : ‖S‖ ≤ 2 := by
      calc
        _ ≤ ‖z‖ * ‖y‖ := norm_mul_le _ _
        _ ≤ 2 * 1 := mul_le_mul hz (IsStarProjection.norm_le y hy) (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hsq : ‖star R * R - star S * S‖ ≤ 3 * η := by
      exact (norm_square_difference R S).trans
        ((mul_le_mul (by linarith : ‖R‖ + ‖S‖ ≤ 3) hRS (norm_nonneg _)
         (by norm_num : (0 : ℝ) ≤ 3)))
    have hRy : R * y = R := by dsimp [R]; rw [mul_assoc, hy.isIdempotentElem]
    have hSy : S * y = S := by dsimp [S]; rw [mul_assoc, hy.isIdempotentElem]
    have hyR : y * star R = star R := by
      simpa only [star_mul, hy.isSelfAdjoint.star_eq] using congrArg star hRy
    have hyS : y * star S = star S := by
      simpa only [star_mul, hy.isSelfAdjoint.star_eq] using congrArg star hSy
    have hsup : y * (star R * R - star S * S) = star R * R - star S * S := by
      rw [mul_sub, ← mul_assoc y (star R), hyR, ← mul_assoc y (star S), hyS]
    have hnorm := (trace_supported_norm_le τ hy hsup).trans
      (mul_le_mul_of_nonneg_right hsq hym0)
    have htrS : τ.functional (star S * S) = τ.functional (star z * z * y) := by
      dsimp [S]
      rw [star_mul, hy.isSelfAdjoint.star_eq]
      calc
        _ = τ.functional (y * (star z * z) * y) := by simp only [mul_assoc]
        _ = τ.functional (y * (star z * z)) := trace_projection_corner τ hy _
        _ = _ := τ.tracial _ _
    have hreal := (Complex.abs_re_le_norm (τ.functional (star R * R - star S * S))).trans hnorm
    simpa only [map_sub, Complex.sub_re, htrS, traceTwoNorm_sq] using hreal

end SamplingEstimates

section SamplingConclusion

lemma complex_difference_transfer (a b u v : ℂ) {c : ℝ} (hc : 0 ≤ c) :
    ‖a - (c : ℂ) * b‖ ≤ ‖a - u‖ + ‖u - (c : ℂ) * v‖ + c * ‖b - v‖ := by
  calc
    _ = ‖(a - u) + (u - (c : ℂ) * v) + (c : ℂ) * (v - b)‖ := by congr 1; ring
    _ ≤ ‖a - u‖ + ‖u - (c : ℂ) * v‖ + ‖(c : ℂ) * (v - b)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, norm_sub_rev v b]

lemma real_difference_transfer (a b u v : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    |a - c * b| ≤ |a - u| + |u - c * v| + c * |b - v| := by
  calc
    _ = |(a - u) + (u - c * v) + c * (v - b)| := by congr 1; ring
    _ ≤ |a - u| + |u - c * v| + |c * (v - b)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = _ := by rw [abs_mul, abs_of_nonneg hc, abs_sub_comm v b]

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma sampling_via_scalar_reference (τ : TracialState D) {p y z : D}
    (hp : IsStarProjection p) (hy : IsStarProjection y) (hyp : y ≤ p)
    (hpz : Commute p z) (hyz : Commute y z) (x : unitary D)
    {η c : ℝ} (hη : η < 1) (hc : 0 ≤ c)
    (hclose : ‖p * (x : D) * p - z‖ < η)
    (hlin : τ.functional (z * y) * τ.functional p =
      τ.functional (z * p) * τ.functional y)
    (hsq : τ.functional (star z * z * y) * τ.functional p =
      τ.functional (star z * z * p) * τ.functional y) :
    ‖τ.functional (y * (x : D)) - (c : ℂ) * τ.functional (p * (x : D))‖ ≤
      η * ((τ.functional y).re + c * (τ.functional p).re) +
        2 * |(τ.functional y).re - c * (τ.functional p).re| ∧
    |traceTwoNorm τ ((x : D) * y - y * (x : D)) ^ 2 -
        c * traceTwoNorm τ ((x : D) * p - p * (x : D)) ^ 2| ≤
      6 * η * ((τ.functional y).re + c * (τ.functional p).re) +
        10 * |(τ.functional y).re - c * (τ.functional p).re| := by
  have hx : ‖(x : D)‖ ≤ 1 := by
    have h := CStarRing.norm_coe_unitary_mul x (1 : D)
    rw [mul_one] at h
    exact h.le.trans (IsStarProjection.norm_le (1 : D) (IsStarProjection.one D))
  have hz : ‖z‖ ≤ 2 := by
    have h1 := norm_le_norm_sub_add z (p * (x : D) * p)
    rw [norm_sub_rev z] at h1
    have h2 := (norm_compress_le hp (x : D)).trans hx
    linarith
  have hym : 0 ≤ (τ.functional y).re := (τ.functional.map_nonneg hy.nonneg).1
  have hpm : 0 ≤ (τ.functional p).re := (τ.functional.map_nonneg hp.nonneg).1
  have hymp : (τ.functional y).re ≤ (τ.functional p).re :=
    (Complex.le_def.mp (τ.functional.monotone hyp)).1
  have hnorm (r : D) (hr : IsStarProjection r) :
      ‖τ.functional (z * r)‖ ≤ 2 * (τ.functional r).re := by
    rw [τ.tracial z r]
    exact (trace_norm_projection_mul_le τ hr z).trans
      (mul_le_mul_of_nonneg_right hz (τ.functional.map_nonneg hr.nonneg).1)
  have hzsq : ‖star z * z‖ ≤ 4 := by
    have h := norm_mul_le (star z) z
    rw [norm_star] at h
    nlinarith [norm_nonneg z]
  have hnormsq (r : D) (hr : IsStarProjection r) :
      ‖τ.functional (star z * z * r)‖ ≤ 4 * (τ.functional r).re := by
    rw [τ.tracial (star z * z) r]
    exact (trace_norm_projection_mul_le τ hr _).trans
      (mul_le_mul_of_nonneg_right hzsq (τ.functional.map_nonneg hr.nonneg).1)
  rw [trace_projection_real τ hp, trace_projection_real τ hy] at hlin hsq
  have hlin' := proportional_complex_bound hym hymp (hnorm y hy) (hnorm p hp) hlin c
  have hsq' := proportional_complex_bound hym hymp (hnormsq y hy) (hnormsq p hp) hsq c
  have hsqreal : |(τ.functional (star z * z * y)).re -
      c * (τ.functional (star z * z * p)).re| ≤
        4 * |(τ.functional y).re - c * (τ.functional p).re| := by
    have h := (Complex.abs_re_le_norm (τ.functional (star z * z * y) -
      (c : ℂ) * τ.functional (star z * z * p))).trans hsq'
    simpa using h
  obtain ⟨ey, sy⟩ := sampling_compression_estimates τ hp hy hyp hyz hx hz hclose.le
  obtain ⟨ep, sp⟩ := sampling_compression_estimates τ hp hp le_rfl hpz hx hz hclose.le
  constructor
  · exact (complex_difference_transfer _ _ _ _ hc).trans
      ((add_le_add (add_le_add ey hlin') (mul_le_mul_of_nonneg_left ep hc)).trans_eq
        (by ring))
  · have henergy : |traceTwoNorm τ (y * (x : D) * y) ^ 2 -
        c * traceTwoNorm τ (p * (x : D) * p) ^ 2| ≤
        3 * η * ((τ.functional y).re + c * (τ.functional p).re) +
          4 * |(τ.functional y).re - c * (τ.functional p).re| := by
      exact (real_difference_transfer _ _ _ _ hc).trans
        ((add_le_add (add_le_add sy hsqreal) (mul_le_mul_of_nonneg_left sp hc)).trans_eq
          (by ring))
    rw [unitary_commutator_energy τ x hy, unitary_commutator_energy τ x hp]
    calc
      _ = |2 * ((τ.functional y).re - c * (τ.functional p).re) -
          2 * (traceTwoNorm τ (y * (x : D) * y) ^ 2 -
            c * traceTwoNorm τ (p * (x : D) * p) ^ 2)| := by congr 1; ring
      _ ≤ |2 * ((τ.functional y).re - c * (τ.functional p).re)| +
          |2 * (traceTwoNorm τ (y * (x : D) * y) ^ 2 -
            c * traceTwoNorm τ (p * (x : D) * p) ^ 2)| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (2 * ((τ.functional y).re - c * (τ.functional p).re)) 0 (2 * (traceTwoNorm τ (y * (x : D) * y) ^ 2 - c * traceTwoNorm τ (p * (x : D) * p) ^ 2))
      _ = 2 * |(τ.functional y).re - c * (τ.functional p).re| +
          2 * |traceTwoNorm τ (y * (x : D) * y) ^ 2 -
            c * traceTwoNorm τ (p * (x : D) * p) ^ 2| := by rw [abs_mul, abs_mul]; norm_num
      _ ≤ 2 * |(τ.functional y).re - c * (τ.functional p).re| +
          2 * (3 * η * ((τ.functional y).re + c * (τ.functional p).re) +
            4 * |(τ.functional y).re - c * (τ.functional p).re|) := by gcongr
      _ = _ := by ring

namespace ProjectionRow

variable {I : Type uI} [Fintype I] {q : D} (U : ProjectionRow I q)

omit [StarOrderedRing D] in
lemma trace_matrix_proportion (τ : TracialState D) {e : D} (heq : e * q = e)
    (s : Matrix I I ℂ) :
    τ.functional (U.matrix e s) * τ.functional (U.sample q) =
      τ.functional (U.matrix q s) * τ.functional (U.sample e) := by
  rw [U.trace_matrix τ e heq, U.trace_matrix τ q U.projection.isIdempotentElem,
    U.trace_sample τ e heq, U.trace_sample τ q U.projection.isIdempotentElem]
  ring

theorem matrix_block_sampling {e : D} (he : IsStarProjection e) (heq : e ≤ q)
    (x : unitary D) {η c : ℝ} (hη : η < 1) (hc : 0 ≤ c)
    (happrox : ∃ s : Matrix I I ℂ,
      ‖U.sample q * (x : D) * U.sample q - U.matrix q s‖ < η) (τ : TracialState D) :
    ‖τ.functional (U.sample e * (x : D)) -
        (c : ℂ) * τ.functional (U.sample q * (x : D))‖ ≤
      η * ((τ.functional (U.sample e)).re + c * (τ.functional (U.sample q)).re) +
        2 * |(τ.functional (U.sample e)).re - c * (τ.functional (U.sample q)).re| ∧
    |traceTwoNorm τ ((x : D) * U.sample e - U.sample e * (x : D)) ^ 2 -
        c * traceTwoNorm τ ((x : D) * U.sample q - U.sample q * (x : D)) ^ 2| ≤
      6 * η * ((τ.functional (U.sample e)).re + c * (τ.functional (U.sample q)).re) +
        10 * |(τ.functional (U.sample e)).re - c * (τ.functional (U.sample q)).re| := by
  obtain ⟨s, hs⟩ := happrox
  have heq' := (he.le_iff_mul_eq_left U.projection).mp heq
  have hqe := (he.le_iff_mul_eq_right U.projection).mp heq
  have hq := U.projection.isIdempotentElem
  apply sampling_via_scalar_reference τ U.range_projection (U.sample_projection he hqe)
    (U.sample_le he heq) (U.matrix_sample_commute hq hq s).symm
    (U.matrix_sample_commute hqe heq' s).symm x hη hc hs
  · rw [U.matrix_sample _ _ hqe, hqe, U.matrix_sample _ _ hq, hq]
    exact U.trace_matrix_proportion τ heq' s
  · rw [U.matrix_star, U.projection.isSelfAdjoint.star_eq, U.matrix_mul _ _ hq, hq,
      U.matrix_sample _ _ hqe, hqe, U.matrix_sample _ _ hq, hq]
    exact U.trace_matrix_proportion τ heq' (star s * s)

end ProjectionRow

end SamplingConclusion

end CurrentMain

end

end

end OAI
