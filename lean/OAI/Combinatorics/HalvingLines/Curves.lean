import OAI.Combinatorics.HalvingLines.Boundary

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

lemma path_stays_inside {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) (γ : ℝ → E) (x : E) (h r : ℝ)
    (hpos : 0 < h) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hγ₀ : γ 0 = 0) (hγ₁ : γ 1 = x)
    (hsmall : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f (γ t)‖ < r)
    (hsphere : ∀ z : E, ‖z‖ = h → r ≤ ‖f z‖) : ‖x‖ < h := by
  by_contra hn
  have hx : h ≤ ‖x‖ := not_lt.mp hn
  have hmem : h ∈ Set.Icc ‖γ 0‖ ‖γ 1‖ := by
    simp only [hγ₀, hγ₁, norm_zero, Set.mem_Icc]
    exact ⟨hpos.le, hx⟩
  obtain ⟨t, ht, hnorm⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hγ.norm hmem
  exact (not_lt_of_ge (hsphere (γ t) hnorm)) (hsmall t ht)

lemma inverse_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (hz : f 0 = 0) (R r ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hgap : R + ε < r)
    (htarget : Metric.closedBall (0 : E) R ⊆ f.target)
    (hnear : ∀ x : E, ‖x‖ = r → ‖f x - x‖ ≤ ε)
    (y : E) (hy : ‖y‖ ≤ R) : ‖f.symm y‖ < r := by
  have hinv₀ : f.symm 0 = 0 := by
    calc
      f.symm 0 = f.symm (f 0) := congrArg f.symm hz.symm
      _ = 0 := f.left_inv (by rw [hrange]; trivial)
  have hsmul (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖t • y‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg y) ht.2).trans hy
  have hpath : Set.MapsTo (fun t : ℝ => t • y) (Set.Icc 0 1) f.target := by
    intro t ht
    exact htarget (by simpa only [Metric.mem_closedBall, dist_zero_right] using hsmul t ht)
  apply path_stays_inside f (fun t : ℝ => f.symm (t • y)) (f.symm y) r (r - ε)
    (by linarith)
    (f.continuousOn_symm.comp (continuous_id.smul continuous_const).continuousOn hpath)
  · simpa only [zero_smul] using hinv₀
  · simp only [one_smul]
  · intro t ht
    rw [f.right_inv (hpath ht)]
    have hb := hsmul t ht
    linarith
  · intro x hx
    have he := hnear x hx
    have hb : ‖x‖ ≤ ‖f x - x‖ + ‖f x‖ := by
      calc
        ‖x‖ = ‖(x - f x) + f x‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - f x‖ + ‖f x‖ := norm_add_le _ _
        _ = ‖f x - x‖ + ‖f x‖ := by rw [norm_sub_rev]
    linarith

lemma inverse_near_id {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (hz : f 0 = 0) (R r ε : ℝ) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hgap : R + ε < r)
    (htarget : Metric.closedBall (0 : E) R ⊆ f.target)
    (hnear : ∀ x : E, ‖x‖ ≤ r → ‖f x - x‖ ≤ ε)
    (y : E) (hy : ‖y‖ ≤ R) : ‖f.symm y - y‖ ≤ ε := by
  have hyT : y ∈ f.target := htarget (by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
  have hb := inverse_bound f hrange hz R r ε hR hε hgap htarget
    (fun x hx => hnear x hx.le) y hy
  have he := hnear (f.symm y) hb.le
  rw [f.right_inv hyT, norm_sub_rev] at he
  exact he

lemma ray_image_leaves_ball {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (x v : E) (hv : v ≠ 0) (R : ℝ)
    (htarget : Metric.closedBall (f x) R ⊆ f.target) :
    ∃ t : ℝ, 0 ≤ t ∧ R < dist (f (x + t • v)) (f x) := by
  have hc : IsCompact (f.symm '' Metric.closedBall (f x) R) :=
    (isCompact_closedBall (f x) R).image_of_continuousOn
      (f.continuousOn_symm.mono htarget)
  obtain ⟨C, hC, hbound⟩ := hc.isBounded.exists_pos_norm_le
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let t : ℝ := (C + ‖x‖ + 1) / ‖v‖
  have ht : 0 ≤ t := div_nonneg (by positivity) hvpos.le
  refine ⟨t, ht, ?_⟩
  by_contra hn
  have hmem : f (x + t • v) ∈ Metric.closedBall (f x) R :=
    not_lt.mp hn
  have hxmem : x + t • v ∈ f.symm '' Metric.closedBall (f x) R := by
    refine ⟨f (x + t • v), hmem, ?_⟩
    apply f.left_inv
    rw [hrange]
    trivial
  have hnorm := hbound (x + t • v) hxmem
  have htri : ‖t • v‖ ≤ ‖x + t • v‖ + ‖x‖ := by
    calc
      ‖t • v‖ = ‖(x + t • v) - x‖ := by congr 1; abel
      _ ≤ ‖x + t • v‖ + ‖x‖ := norm_sub_le _ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    show t * ‖v‖ = C + ‖x‖ + 1 from div_mul_cancel₀ _ (ne_of_gt hvpos)] at htri
  linarith

lemma line_parameter_levels {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (x v : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ) (M R : ℝ)
    (hM : 0 < M)
    (hmono : StrictMono (fun t : ℝ => ℓ (f (x + t • v) - f x)))
    (hcone : ∀ t : ℝ,
      ‖f (x + t • v) - f x‖ ≤ M * |ℓ (f (x + t • v) - f x)|)
    (htarget : Metric.closedBall (f x) (M * R) ⊆ f.target)
    (s : ℝ) (hs : s ∈ Set.Icc (-R) R) :
    ∃ t : ℝ, ℓ (f (x + t • v) - f x) = s := by
  let φ : ℝ → ℝ := fun t => ℓ (f (x + t • v) - f x)
  have hφ : Continuous φ := by
    have hf : Continuous f := continuousOn_univ.mp
      (by simpa only [← hrange] using f.continuousOn)
    exact ℓ.continuous.comp
      ((hf.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
        continuous_const)
  obtain ⟨a, ha, hexit_pos⟩ := ray_image_leaves_ball f hrange x v hv (M * R) htarget
  obtain ⟨b, hb, hexit_neg⟩ := ray_image_leaves_ball f hrange x (-v) (neg_ne_zero.mpr hv)
    (M * R) htarget
  have hpos : 0 ≤ φ a := by simpa [φ] using hmono.monotone ha
  have hneg : φ (-b) ≤ 0 := by
    simpa [φ] using hmono.monotone (neg_nonpos.mpr hb)
  have haR : R < φ a := by
    rw [dist_eq_norm] at hexit_pos
    have hc := hcone a
    change ‖f (x + a • v) - f x‖ ≤ M * |φ a| at hc
    rw [abs_of_nonneg hpos] at hc
    nlinarith
  have hbR : φ (-b) < -R := by
    rw [dist_eq_norm, smul_neg, ← neg_smul] at hexit_neg
    have hc := hcone (-b)
    change ‖f (x + (-b) • v) - f x‖ ≤ M * |φ (-b)| at hc
    rw [abs_of_nonpos hneg] at hc
    nlinarith
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc
    (show -b ≤ a by linarith) hφ.continuousOn
    (show s ∈ Set.Icc (φ (-b)) (φ a) from ⟨hbR.le.trans hs.1, hs.2.trans haR.le⟩)
  exact ⟨t, ht⟩

lemma line_parameter_curve {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : OpenPartialHomeomorph E E) (hrange : f.source = Set.univ)
    (x v : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ) (M : ℝ≥0) (R : ℝ)
    (hM : 0 < M) (hR : 0 ≤ R)
    (hmono : StrictMono (fun t : ℝ => ℓ (f (x + t • v) - f x)))
    (hcone : ∀ t u : ℝ,
      ‖f (x + t • v) - f (x + u • v)‖ ≤
        M * |ℓ (f (x + t • v) - f (x + u • v))|)
    (htarget : Metric.closedBall (f x) (M * R) ⊆ f.target) :
    ∃ γ : Set.Icc (-R) R → E, LipschitzWith M γ ∧
      (∀ s, ∃ t : ℝ, γ s = f (x + t • v)) ∧
      (∀ s, ℓ (γ s - f x) = s) ∧
      γ ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = f x := by
  have hlevels (s : Set.Icc (-R) R) :
      ∃ t : ℝ, ℓ (f (x + t • v) - f x) = (s : ℝ) :=
    line_parameter_levels f hrange x v hv ℓ M R hM hmono
      (fun t => by simpa only [zero_smul, add_zero] using hcone t 0) htarget s s.property
  choose t ht using hlevels
  let γ : Set.Icc (-R) R → E := fun s => f (x + t s • v)
  have hγ : LipschitzWith M γ := by
    apply LipschitzWith.of_dist_le_mul
    intro s u
    have he : ℓ (γ s - γ u) = (s : ℝ) - u := by
      calc
        ℓ (γ s - γ u) = ℓ (γ s - f x) - ℓ (γ u - f x) := by
          simp only [map_sub]
          ring
        _ = (s : ℝ) - u := by rw [ht s, ht u]
    rw [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, ← he]
    exact hcone (t s) (t u)
  refine ⟨γ, hγ, fun s => ⟨t s, rfl⟩, ht, ?_⟩
  let z : Set.Icc (-R) R := ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩
  have hzero := hcone (t z) 0
  simp only [zero_smul, add_zero] at hzero
  rw [ht z, show (z : ℝ) = 0 from rfl, abs_zero, mul_zero] at hzero
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _)))

lemma intersects_level_graph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ ψ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun x : E => (ℓ x, ψ x)))
    (g β : ℝ → E) (a b c d : ℝ) (hcd : c ≤ d)
    (hg : ContinuousOn g (Set.Icc a b))
    (hβ : ContinuousOn β (Set.Icc c d))
    (hlevel : ∀ s ∈ Set.Icc a b, ℓ (g s) = s)
    (hinside : ∀ t ∈ Set.Icc c d, ℓ (β t) ∈ Set.Icc a b)
    (hlower : ψ (β c) ≤ ψ (g (ℓ (β c))))
    (hupper : ψ (g (ℓ (β d))) ≤ ψ (β d)) :
    ∃ t ∈ Set.Icc c d, ∃ s ∈ Set.Icc a b, β t = g s := by
  let H : ℝ → ℝ := fun t => ψ (β t) - ψ (g (ℓ (β t)))
  have hH : ContinuousOn H (Set.Icc c d) :=
    (ψ.continuous.comp_continuousOn hβ).sub
      (ψ.continuous.comp_continuousOn
        (hg.comp (ℓ.continuous.comp_continuousOn hβ) hinside))
  have hmem : (0 : ℝ) ∈ Set.Icc (H c) (H d) :=
    ⟨sub_nonpos.mpr hlower, sub_nonneg.mpr hupper⟩
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc hcd hH hmem
  refine ⟨t, ht, ℓ (β t), hinside t ht, hjoint ?_⟩
  apply Prod.ext
  · exact (hlevel _ (hinside t ht)).symm
  · exact sub_eq_zero.mp hzero

lemma bounded_parameter_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (a b : ℕ → E) (a₀ v : E) (ℓ : E →L[ℝ] ℝ) (s B : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hbound : ∀ᶠ n in atTop, ‖b n - a n‖ ≤ B)
    (hlevel : ∀ᶠ n in atTop, ℓ (b n - a n) = s) (hv : ℓ v ≠ 0)
    (hdirection : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ b₀ : E,
      Tendsto (b ∘ ρ) atTop (𝓝 b₀) → ∃ r : ℝ, b₀ - a₀ = r • v) :
    Tendsto b atTop (𝓝 (a₀ + (s / ℓ v) • v)) := by
  obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  have hb : ∀ᶠ n in atTop, b n ∈ Metric.closedBall (0 : E) (B + C) := by
    filter_upwards [hbound] with n hn
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖b n‖ = ‖(b n - a n) + a n‖ := by rw [sub_add_cancel]
      _ ≤ ‖b n - a n‖ + ‖a n‖ := norm_add_le _ _
      _ ≤ B + C := add_le_add hn (hC _ (Set.mem_range_self n))
  apply (isCompact_closedBall (0 : E) (B + C)).tendsto_nhds_of_unique_mapClusterPt hb
  intro b₀ _ hcluster
  obtain ⟨ρ, hρ, hlim⟩ := hcluster.tendsto_subseq
  obtain ⟨r, hr⟩ := hdirection ρ hρ b₀ hlim
  have he : ℓ (b₀ - a₀) = s := by
    have hh : Tendsto (fun _ : ℕ => s) atTop (𝓝 (ℓ (b₀ - a₀))) := by
      have hm := (ℓ.continuous.tendsto (b₀ - a₀)).comp
        (hlim.sub (ha.comp hρ.tendsto_atTop))
      change Tendsto (fun n => ℓ (b (ρ n) - a (ρ n))) atTop
        (𝓝 (ℓ (b₀ - a₀))) at hm
      exact hm.congr' (hρ.tendsto_atTop.eventually hlevel)
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hcoef : r = s / ℓ v := by
    apply (eq_div_iff hv).mpr
    simpa only [hr, map_smul, smul_eq_mul] using he
  rw [sub_eq_iff_eq_add] at hr
  simpa only [hcoef, add_comm] using hr

lemma parameter_curves_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (R : ℝ) (hR : 0 ≤ R) (γ : ℕ → Set.Icc (-R) R → E)
    (a : ℕ → E) (a₀ v : E) (ℓ : E →L[ℝ] ℝ) (M : ℝ≥0)
    (ha : Tendsto a atTop (𝓝 a₀)) (hγ : ∀ n, LipschitzWith M (γ n))
    (hzero : ∀ n, γ n ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = a n)
    (hlevel : ∀ᶠ n in atTop, ∀ s, ℓ (γ n s - a n) = s) (hv : ℓ v ≠ 0)
    (hdirection : ∀ s, ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ b₀ : E,
      Tendsto (fun n => γ (ρ n) s) atTop (𝓝 b₀) → ∃ r : ℝ, b₀ - a₀ = r • v) :
    TendstoUniformly γ (fun s => a₀ + ((s : ℝ) / ℓ v) • v) atTop := by
  have hp : ∀ s : Set.Icc (-R) R,
      Tendsto (fun n => γ n s) atTop (𝓝 (a₀ + ((s : ℝ) / ℓ v) • v)) := by
    intro s
    apply bounded_parameter_tendsto a (fun n => γ n s) a₀ v ℓ s (M * |(s : ℝ)|)
      ha ?_ (hlevel.mono fun _ hn => hn s) hv (hdirection s)
    apply Filter.Eventually.of_forall
    intro n
    have hb := (hγ n).dist_le_mul s ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩
    simpa only [hzero, dist_eq_norm, Subtype.dist_eq, Real.dist_eq, sub_zero,
      Real.norm_eq_abs] using hb
  have heq : Equicontinuous γ := (LipschitzWith.uniformEquicontinuous γ M hγ).equicontinuous
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((heq.tendsto_uniformFun_iff_pi atTop _).mpr (tendsto_pi_nhds.mpr hp))

noncomputable def coneLevel (Q : Point ≃L[ℝ] Point) : Point →L[ℝ] ℝ :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ) + (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp
    Q.toContinuousLinearMap

lemma coneLevel_apply (Q : Point ≃L[ℝ] Point) (x : Point) :
    coneLevel Q x = (Q x).1 + (Q x).2 := rfl

lemma norm_le_coneLevel (Q : Point ≃L[ℝ] Point) (q : Point)
    (hq₁ : 0 ≤ (Q q).1) (hq₂ : 0 ≤ (Q q).2) :
    ‖q‖ ≤ ‖Q.symm.toContinuousLinearMap‖ * coneLevel Q q := by
  have hn : ‖Q q‖ ≤ coneLevel Q q := by
    rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hq₁, abs_of_nonneg hq₂, coneLevel_apply]
    exact max_le (le_add_of_nonneg_right hq₂) (le_add_of_nonneg_left hq₁)
  calc
    ‖q‖ = ‖Q.symm (Q q)‖ := by rw [Q.symm_apply_apply]
    _ ≤ ‖Q.symm.toContinuousLinearMap‖ * ‖Q q‖ :=
      Q.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖Q.symm.toContinuousLinearMap‖ * coneLevel Q q :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)

lemma coneLevel_strictMono (Q : Point ≃L[ℝ] Point) (g : ℝ → Point)
    (hg : Function.Injective g)
    (h₁ : Monotone (fun t => (Q (g t)).1))
    (h₂ : Monotone (fun t => (Q (g t)).2)) :
    StrictMono (fun t => coneLevel Q (g t)) := by
  intro t u htu
  have ha := h₁ htu.le
  have hb := h₂ htu.le
  simp only [coneLevel_apply]
  apply lt_of_le_of_ne (add_le_add ha hb)
  intro he
  have hpair : Q (g t) = Q (g u) := Prod.ext (by linarith) (by linarith)
  exact htu.ne (hg (Q.injective hpair))

lemma coneLevel_chord (Q : Point ≃L[ℝ] Point) (g : ℝ → Point)
    (h₁ : Monotone (fun t => (Q (g t)).1))
    (h₂ : Monotone (fun t => (Q (g t)).2)) (t u : ℝ) :
    ‖g t - g u‖ ≤ ‖Q.symm.toContinuousLinearMap‖ *
      |coneLevel Q (g t - g u)| := by
  have forward (a b : ℝ) (hab : a ≤ b) :
      ‖g b - g a‖ ≤ ‖Q.symm.toContinuousLinearMap‖ *
        coneLevel Q (g b - g a) := by
    apply norm_le_coneLevel
    · rw [map_sub]
      exact sub_nonneg.mpr (h₁ hab)
    · rw [map_sub]
      exact sub_nonneg.mpr (h₂ hab)
  rcases le_total u t with hut | htu
  · exact (forward u t hut).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _))
  · rw [norm_sub_rev, ← abs_neg, ← map_neg, neg_sub]
    exact (forward t u htu).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) (norm_nonneg _))

end Zoom

end PlanarHalving

end OAI
