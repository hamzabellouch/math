import OAI.Combinatorics.HalvingLines.Curves

namespace OAI

namespace PlanarHalving

namespace Zoom

open scoped NNReal Topology
open Filter

lemma intersects_parameter_graph {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ ψ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun x : E => (ℓ x, ψ x)))
    (a : E) (R c d : ℝ) (hcd : c ≤ d)
    (γ : Set.Icc (-R) R → E) (β : Set.Icc c d → E)
    (hγ : Continuous γ) (hβ : Continuous β)
    (hlevel : ∀ s, ℓ (γ s - a) = s)
    (hinside : ∀ t, ℓ (β t - a) ∈ Set.Icc (-R) R)
    (hlower : ψ (β ⟨c, ⟨le_rfl, hcd⟩⟩) ≤
      ψ (γ ⟨ℓ (β ⟨c, ⟨le_rfl, hcd⟩⟩ - a), hinside _⟩))
    (hupper : ψ (γ ⟨ℓ (β ⟨d, ⟨hcd, le_rfl⟩⟩ - a), hinside _⟩) ≤
      ψ (β ⟨d, ⟨hcd, le_rfl⟩⟩)) :
    ∃ t s, β t = γ s := by
  let p (t : Set.Icc c d) : Set.Icc (-R) R := ⟨ℓ (β t - a), hinside t⟩
  have hp : Continuous p :=
    (ℓ.continuous.comp (hβ.sub continuous_const)).subtype_mk _
  let H (t : Set.Icc c d) : ℝ := ψ (β t) - ψ (γ (p t))
  have hH : Continuous H :=
    (ψ.continuous.comp hβ).sub (ψ.continuous.comp (hγ.comp hp))
  let c' : Set.Icc c d := ⟨c, ⟨le_rfl, hcd⟩⟩
  let d' : Set.Icc c d := ⟨d, ⟨hcd, le_rfl⟩⟩
  have hmem : (0 : ℝ) ∈ Set.Icc (H c') (H d') :=
    ⟨sub_nonpos.mpr hlower, sub_nonneg.mpr hupper⟩
  let : PreconnectedSpace (Set.Icc c d) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  obtain ⟨t, ht⟩ := intermediate_value_univ c' d' hH hmem
  refine ⟨t, p t, hjoint (Prod.ext ?_ (sub_eq_zero.mp ht))⟩
  have he := hlevel (p t)
  change ℓ (γ (p t) - a) = ℓ (β t - a) at he
  simpa only [map_sub, sub_left_inj] using he.symm

lemma eventual_arc_intersection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ ψ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun x : E => (ℓ x, ψ x)))
    (a : ℕ → E) (a₀ c v w : E) (R D r : ℝ)
    (hD : 0 < D) (hr : 0 < r)
    (γ : ℕ → Set.Icc (-R) R → E) (β : ℕ → Set.Icc (-D) D → E)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hγ : TendstoUniformly γ (fun s => a₀ + (s : ℝ) • v) atTop)
    (hβ : TendstoUniformly β (fun t => c + (t : ℝ) • w) atTop)
    (hcγ : ∀ n, Continuous (γ n)) (hcβ : ∀ n, Continuous (β n))
    (hlevel : ∀ᶠ n in atTop, ∀ s, ℓ (γ n s - a n) = s)
    (hinside : ∀ t : Set.Icc (-D) D, |ℓ (c + (t : ℝ) • w - a₀)| ≤ R - r)
    (hψv : ψ v = 0) (hψc : ψ c = ψ a₀) (hψw : 0 < ψ w) :
    ∀ᶠ n in atTop, ∃ t s, β n t = γ n s := by
  have hℓβ := ℓ.uniformContinuous.comp_tendstoUniformly hβ
  have hψβ := ψ.uniformContinuous.comp_tendstoUniformly hβ
  have hψγ := ψ.uniformContinuous.comp_tendstoUniformly hγ
  have ha' : ∀ᶠ n in atTop, |ℓ (a n) - ℓ a₀| < r / 2 := by
    have hh := ((ℓ.continuous.tendsto a₀).comp ha).eventually
      (Metric.ball_mem_nhds (ℓ a₀) (half_pos hr))
    simpa only [Metric.mem_ball, Real.dist_eq, Function.comp_apply] using hh
  have hℓβ' := Metric.tendstoUniformly_iff.mp hℓβ (r / 2) (half_pos hr)
  let e : ℝ := D * ψ w / 3
  have he : 0 < e := div_pos (mul_pos hD hψw) (by norm_num)
  have hψβ' := Metric.tendstoUniformly_iff.mp hψβ e he
  have hψγ' := Metric.tendstoUniformly_iff.mp hψγ e he
  filter_upwards [ha', hℓβ', hψβ', hψγ', hlevel] with n han hℓn hβn hγn hleveln
  have hi (t : Set.Icc (-D) D) : ℓ (β n t - a n) ∈ Set.Icc (-R) R := by
    have h₁ : -(r / 2) < ℓ (c + (t : ℝ) • w) - ℓ (β n t) ∧
        ℓ (c + (t : ℝ) • w) - ℓ (β n t) < r / 2 := abs_lt.mp (hℓn t)
    have h₂ := abs_lt.mp han
    have h₃ := abs_le.mp (hinside t)
    simp only [map_sub] at h₃ ⊢
    constructor <;> linarith
  let lo : Set.Icc (-D) D := ⟨-D, ⟨le_rfl, by linarith⟩⟩
  let up : Set.Icc (-D) D := ⟨D, ⟨by linarith, le_rfl⟩⟩
  have hl : ψ (β n lo) ≤ ψ (γ n ⟨ℓ (β n lo - a n), hi lo⟩) := by
    have hb := hβn lo
    have hg := hγn ⟨ℓ (β n lo - a n), hi lo⟩
    simp only [Function.comp_apply, Real.dist_eq, map_add, map_smul,
      hψv, hψc, smul_eq_mul, mul_zero, add_zero] at hb hg
    change |ψ a₀ + (-D) * ψ w - ψ (β n lo)| < e at hb
    have hb' := abs_lt.mp hb
    have hg' := abs_lt.mp hg
    dsimp [e] at hb' hg'
    nlinarith
  have hu : ψ (γ n ⟨ℓ (β n up - a n), hi up⟩) ≤ ψ (β n up) := by
    have hb := hβn up
    have hg := hγn ⟨ℓ (β n up - a n), hi up⟩
    simp only [Function.comp_apply, Real.dist_eq, map_add, map_smul,
      hψv, hψc, smul_eq_mul, mul_zero, add_zero] at hb hg
    change |ψ a₀ + D * ψ w - ψ (β n up)| < e at hb
    have hb' := abs_lt.mp hb
    have hg' := abs_lt.mp hg
    dsimp [e] at hb' hg'
    nlinarith
  exact intersects_parameter_graph ℓ ψ hjoint (a n) R (-D) D (by linarith)
    (γ n) (β n) (hcγ n) (hcβ n) hleveln hi hl hu

lemma level_forces_nonzero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (a b : ℕ → E) (a₀ v : E) (ℓ : E →L[ℝ] ℝ) (B : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hbound : ∀ᶠ n in atTop, ‖b n - a n‖ ≤ B)
    (hlevel : ∀ᶠ n in atTop, ℓ (b n - a n) = 1)
    (hdirection : ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ b₀ : E,
      Tendsto (b ∘ ρ) atTop (𝓝 b₀) → ∃ r : ℝ, b₀ - a₀ = r • v) :
    ℓ v ≠ 0 := by
  obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_pos_norm_le
  have hb : ∀ᶠ n in atTop, b n ∈ Metric.closedBall (0 : E) (B + C) := by
    filter_upwards [hbound] with n hn
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖b n‖ = ‖(b n - a n) + a n‖ := by rw [sub_add_cancel]
      _ ≤ ‖b n - a n‖ + ‖a n‖ := norm_add_le _ _
      _ ≤ B + C := add_le_add hn (hC _ (Set.mem_range_self n))
  obtain ⟨b₀, _, ρ, hρ, hlim⟩ :=
    (isCompact_closedBall (0 : E) (B + C)).isSeqCompact.subseq_of_frequently_in hb.frequently
  obtain ⟨r, hr⟩ := hdirection ρ hρ b₀ hlim
  have hm := (ℓ.continuous.tendsto (b₀ - a₀)).comp
    (hlim.sub (ha.comp hρ.tendsto_atTop))
  change Tendsto (fun n => ℓ (b (ρ n) - a (ρ n))) atTop
    (𝓝 (ℓ (b₀ - a₀))) at hm
  have he : ℓ (b₀ - a₀) = 1 :=
    tendsto_nhds_unique (hm.congr' (hρ.tendsto_atTop.eventually hlevel)) tendsto_const_nhds
  intro hv
  simp only [hr, map_smul, hv, smul_zero] at he
  exact zero_ne_one he

def DirectionalLimit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → E → E) (v w : E) : Prop :=
  ∀ (ρ : ℕ → ℕ), StrictMono ρ → ∀ (x y : ℕ → E),
    (∀ n, ∃ t : ℝ, y n = x n + t • v) → ∀ a b : E,
    Tendsto (fun n => f (ρ n) (x n)) atTop (𝓝 a) →
    Tendsto (fun n => f (ρ n) (y n)) atTop (𝓝 b) →
    ∃ r : ℝ, b - a = r • w

lemma controlled_line_arcs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : ℕ → OpenPartialHomeomorph E E) (hsource : ∀ n, (f n).source = Set.univ)
    (hexhaust : ∀ K : Set E, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).target)
    (x : ℕ → E) (a₀ v : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ)
    (M : ℝ≥0) (hM : 0 < M) (R : ℝ) (hR : 0 ≤ R)
    (ha : Tendsto (fun n => f n (x n)) atTop (𝓝 a₀))
    (hmono : ∀ n, StrictMono (fun t : ℝ => ℓ (f n (x n + t • v) - f n (x n))))
    (hcone : ∀ n (t u : ℝ), ‖f n (x n + t • v) - f n (x n + u • v)‖ ≤
      M * |ℓ (f n (x n + t • v) - f n (x n + u • v))|) :
    ∃ γ : ℕ → Set.Icc (-R) R → E,
      (∀ n, LipschitzWith M (γ n)) ∧
      (∀ n s, ∃ t : ℝ, γ n s = f n (x n + t • v)) ∧
      (∀ᶠ n in atTop, ∀ s, ℓ (γ n s - f n (x n)) = s) ∧
      (∀ n, γ n ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = f n (x n)) := by
  classical
  obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto _ ha).exists_pos_norm_le
  have ht : ∀ᶠ n in atTop, Metric.closedBall (f n (x n)) (M * R) ⊆ (f n).target := by
    filter_upwards [hexhaust (Metric.closedBall (0 : E) (C + M * R))
      (isCompact_closedBall _ _)] with n hn
    intro y hy
    apply hn
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖y‖ = ‖f n (x n) + (y - f n (x n))‖ := by rw [add_sub_cancel]
      _ ≤ ‖f n (x n)‖ + ‖y - f n (x n)‖ := norm_add_le _ _
      _ ≤ C + M * R := add_le_add (hC _ (Set.mem_range_self n))
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy)
  have hc (n : ℕ) : ∃ g : Set.Icc (-R) R → E,
      LipschitzWith M g ∧ (∀ s, ∃ t : ℝ, g s = f n (x n + t • v)) ∧
      (Metric.closedBall (f n (x n)) (M * R) ⊆ (f n).target →
        ∀ s, ℓ (g s - f n (x n)) = s) ∧
      g ⟨0, ⟨neg_nonpos.mpr hR, hR⟩⟩ = f n (x n) := by
    by_cases hi : Metric.closedBall (f n (x n)) (M * R) ⊆ (f n).target
    · obtain ⟨g, hg, hmem, hlevel, hz⟩ := line_parameter_curve (f n) (hsource n)
        (x n) v hv ℓ M R hM hR (hmono n) (hcone n) hi
      exact ⟨g, hg, hmem, fun _ => hlevel, hz⟩
    · refine ⟨fun _ => f n (x n), LipschitzWith.const' _, ?_,
        fun h => (hi h).elim, rfl⟩
      intro s
      exact ⟨0, by rw [zero_smul, add_zero]⟩
  choose γ hγ hmem hlevel hz using hc
  exact ⟨γ, hγ, hmem, ht.mono (fun n hn => hlevel n hn), hz⟩

lemma moving_line_arcs_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E]
    (f : ℕ → OpenPartialHomeomorph E E) (hsource : ∀ n, (f n).source = Set.univ)
    (hexhaust : ∀ K : Set E, IsCompact K → ∀ᶠ n in atTop, K ⊆ (f n).target)
    (x : ℕ → E) (a₀ v w : E) (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ)
    (M : ℝ≥0) (hM : 0 < M)
    (ha : Tendsto (fun n => f n (x n)) atTop (𝓝 a₀))
    (hmono : ∀ n, StrictMono (fun t : ℝ => ℓ (f n (x n + t • v) - f n (x n))))
    (hcone : ∀ n (t u : ℝ), ‖f n (x n + t • v) - f n (x n + u • v)‖ ≤
      M * |ℓ (f n (x n + t • v) - f n (x n + u • v))|)
    (hdir : DirectionalLimit (fun n => f n) v w) :
    ℓ w ≠ 0 ∧ ∀ R : ℝ, ∀ _hR : 0 ≤ R,
      ∃ γ : ℕ → Set.Icc (-R) R → E,
        (∀ n, LipschitzWith M (γ n)) ∧
        (∀ n s, ∃ t : ℝ, γ n s = f n (x n + t • v)) ∧
        (∀ᶠ n in atTop, ∀ s, ℓ (γ n s - f n (x n)) = s) ∧
        TendstoUniformly γ (fun s => a₀ + ((s : ℝ) / ℓ w) • w) atTop := by
  have hdirs (R : ℝ) (γ : ℕ → Set.Icc (-R) R → E)
      (hmem : ∀ n s, ∃ t : ℝ, γ n s = f n (x n + t • v))
      (s : Set.Icc (-R) R) (ρ : ℕ → ℕ) (hρ : StrictMono ρ) (b₀ : E)
      (hb : Tendsto (fun n => γ (ρ n) s) atTop (𝓝 b₀)) :
      ∃ r : ℝ, b₀ - a₀ = r • w := by
    choose t ht using fun n => hmem (ρ n) s
    apply hdir ρ hρ (fun n => x (ρ n)) (fun n => x (ρ n) + t n • v)
      (fun n => ⟨t n, rfl⟩) a₀ b₀ (ha.comp hρ.tendsto_atTop)
    simpa only [← ht] using hb
  obtain ⟨γ₁, hLip₁, hmem₁, hlevel₁, hz₁⟩ := controlled_line_arcs f hsource hexhaust
    x a₀ v hv ℓ M hM 1 (by norm_num) ha hmono hcone
  let one : Set.Icc (-1 : ℝ) 1 := ⟨1, ⟨by norm_num, le_rfl⟩⟩
  have hw : ℓ w ≠ 0 := by
    apply level_forces_nonzero (fun n => f n (x n)) (fun n => γ₁ n one)
      a₀ w ℓ M ha ?_ (hlevel₁.mono fun _ hn => hn one) (hdirs 1 γ₁ hmem₁ one)
    apply Filter.Eventually.of_forall
    intro n
    have hh := (hLip₁ n).dist_le_mul one ⟨0, by norm_num, by norm_num⟩
    simpa only [hz₁, Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs,
      one, sub_zero, abs_one, mul_one] using hh
  refine ⟨hw, ?_⟩
  intro R hR
  obtain ⟨γ, hLip, hmem, hlevel, hz⟩ := controlled_line_arcs f hsource hexhaust
    x a₀ v hv ℓ M hM R hR ha hmono hcone
  exact ⟨γ, hLip, hmem, hlevel,
    parameter_curves_tendsto R hR γ (fun n => f n (x n)) a₀ w ℓ M ha hLip hz
      hlevel hw (hdirs R γ hmem)⟩

lemma line_intersection_tendsto {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ℓ ψ : E →L[ℝ] ℝ)
    (hjoint : Function.Injective (fun x : E => (ℓ x, ψ x)))
    (A B : ℕ → Set E) (z a : ℕ → E) (a₀ b₀ c v w : E) (q : ℝ)
    (ha : Tendsto a atTop (𝓝 a₀))
    (hc : c = b₀ + q • w) (hψv : ψ v = 0) (hψc : ψ c = ψ a₀)
    (hψw : 0 < ψ w)
    (hunique : ∀ n y, y ∈ A n → y ∈ B n → y = z n)
    (hA : ∀ R : ℝ, 0 ≤ R → ∃ γ : ℕ → Set.Icc (-R) R → E,
      (∀ n, Continuous (γ n)) ∧ (∀ n s, γ n s ∈ A n) ∧
      (∀ᶠ n in atTop, ∀ s, ℓ (γ n s - a n) = s) ∧
      TendstoUniformly γ (fun s => a₀ + (s : ℝ) • v) atTop)
    (hB : ∀ R : ℝ, 0 ≤ R → ∃ δ : ℕ → Set.Icc (-R) R → E,
      (∀ n, Continuous (δ n)) ∧ (∀ n s, δ n s ∈ B n) ∧
      TendstoUniformly δ (fun s => b₀ + (s : ℝ) • w) atTop) :
    Tendsto z atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let d : ℝ := min ε 1 / (4 * (‖w‖ + |ℓ w| + 1))
  have hden : 0 < 4 * (‖w‖ + |ℓ w| + 1) := by positivity
  have hd : 0 < d := div_pos (lt_min hε zero_lt_one) hden
  have hdw : d * ‖w‖ < ε / 2 := by
    have hmul : d * (4 * (‖w‖ + |ℓ w| + 1)) = min ε 1 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hmin := min_le_left ε 1
    have ha := abs_nonneg (ℓ w)
    have hn := norm_nonneg w
    nlinarith only [hmul, hmin, ha, hn, hd]
  have hdl : d * |ℓ w| ≤ 1 / 2 := by
    have hmul : d * (4 * (‖w‖ + |ℓ w| + 1)) = min ε 1 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hmin := min_le_right ε 1
    have hn := norm_nonneg w
    have ha := abs_nonneg (ℓ w)
    nlinarith only [hmul, hmin, ha, hn, hd]
  let R : ℝ := |ℓ (c - a₀)| + 1
  obtain ⟨γ, hcγ, hmemγ, hlevel, hγ⟩ := hA R (by dsimp [R]; positivity)
  obtain ⟨δ, hcδ, hmemδ, hδ⟩ := hB (|q| + d) (by positivity)
  let p (t : Set.Icc (-d) d) : Set.Icc (-(|q| + d)) (|q| + d) :=
    ⟨q + t, by
      constructor
      · linarith only [t.property.1, neg_abs_le q]
      · linarith only [t.property.2, le_abs_self q]⟩
  have hp : Continuous p :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  let β (n : ℕ) (t : Set.Icc (-d) d) : E := δ n (p t)
  have hβ : TendstoUniformly β (fun t => c + (t : ℝ) • w) atTop := by
    have hh := hδ.comp p
    change TendstoUniformly β (fun t => b₀ + (q + (t : ℝ)) • w) atTop at hh
    simpa only [hc, add_smul, add_assoc] using hh
  have hi (t : Set.Icc (-d) d) : |ℓ (c + (t : ℝ) • w - a₀)| ≤ R - 1 / 2 := by
    have ht : |(t : ℝ)| ≤ d := abs_le.mpr t.property
    calc
      |ℓ (c + (t : ℝ) • w - a₀)| = |ℓ (c - a₀) + (t : ℝ) * ℓ w| := by
        congr 1
        rw [add_sub_right_comm, map_add, map_smul, smul_eq_mul]
      _ ≤ |ℓ (c - a₀)| + |(t : ℝ) * ℓ w| := abs_add_le _ _
      _ ≤ |ℓ (c - a₀)| + d * |ℓ w| := by
        rw [abs_mul]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ht (abs_nonneg _))
      _ ≤ R - 1 / 2 := by dsimp [R]; linarith
  have hinter := eventual_arc_intersection ℓ ψ hjoint a a₀ c v w R d (1 / 2)
    hd (by norm_num) γ β ha hγ hβ hcγ (fun n => (hcδ n).comp hp)
    hlevel hi hψv hψc hψw
  have hclose := Metric.tendstoUniformly_iff.mp hβ (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hinter.and hclose)
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨⟨t, s, hts⟩, hclose⟩ := hN n hn
  have he : β n t = z n := hunique n (β n t) (hts ▸ hmemγ n s) (hmemδ n (p t))
  calc
    dist (z n) c = dist (β n t) c := by rw [he]
    _ ≤ dist (β n t) (c + (t : ℝ) • w) + dist (c + (t : ℝ) • w) c := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      · exact (dist_comm _ _).trans_lt (hclose t)
      · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
          (abs_le.mpr t.property) (norm_nonneg w)) hdw
    _ = ε := by ring

def detPair (u v : Point) : ℝ := u.1 * v.2 - u.2 * v.1

lemma plane_span (u v : Point) (hdet : detPair u v ≠ 0) (x : Point) :
    ∃ r s : ℝ, x = r • u + s • v := by
  refine ⟨(x.1 * v.2 - x.2 * v.1) / detPair u v,
    (u.1 * x.2 - u.2 * x.1) / detPair u v, ?_⟩
  apply Prod.ext <;> dsimp
  · field_simp
    simp only [detPair]
    ring
  · field_simp
    simp only [detPair]
    ring

lemma transverse_covector (ℓ : Point →L[ℝ] ℝ) (u v : Point)
    (hℓu : ℓ u ≠ 0) (hdet : detPair u v ≠ 0) :
    ∃ ψ : Point →L[ℝ] ℝ,
      Function.Injective (fun x : Point => (ℓ x, ψ x)) ∧ ψ u = 0 ∧ ψ v = 1 := by
  let φ : Point →L[ℝ] ℝ :=
    u.1 • ContinuousLinearMap.snd ℝ ℝ ℝ - u.2 • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hφu : φ u = 0 := by change u.1 * u.2 - u.2 * u.1 = 0; ring
  have hφv : φ v = detPair u v := rfl
  let ψ : Point →L[ℝ] ℝ := (detPair u v)⁻¹ • φ
  have hψu : ψ u = 0 := by simp [ψ, hφu]
  have hψv : ψ v = 1 := by simp [ψ, hφv, hdet]
  refine ⟨ψ, ?_, hψu, hψv⟩
  intro x y hxy
  obtain ⟨r, s, hrs⟩ := plane_span u v hdet (x - y)
  have h₁ : ℓ (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Prod.fst hxy)
  have h₂ : ψ (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Prod.snd hxy)
  have hs : s = 0 := by
    simpa only [hrs, map_add, map_smul, hψu, hψv, smul_zero, zero_add,
      smul_eq_mul, mul_one, mul_zero, zero_add] using h₂
  have hr : r = 0 := by
    have hh : r * ℓ u = 0 := by simpa only [hrs, hs, zero_smul, add_zero,
      map_smul, smul_eq_mul] using h₁
    exact (mul_eq_zero.mp hh).resolve_right hℓu
  apply sub_eq_zero.mp
  simpa only [hr, hs, zero_smul, add_zero] using hrs

lemma detPair_smul_right (u v : Point) (r : ℝ) :
    detPair u (r • v) = r * detPair u v := by
  dsimp [detPair]
  ring

end Zoom

end PlanarHalving

end OAI
