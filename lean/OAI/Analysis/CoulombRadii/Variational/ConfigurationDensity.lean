import Mathlib
import OAI.Analysis.CoulombRadii.Model

namespace OAI

section
section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology ContDiff

namespace NeutralAtom

theorem largeCharge_eq_atTop (m : ℕ) : largeCharge m = atTop := by
  apply inf_eq_left.mpr
  apply Filter.le_principal_iff.mpr
  filter_upwards [eventually_ge_atTop m] with N hN
  omega

theorem bTF_pos : 0 < bTF := by
  unfold bTF
  apply Real.rpow_pos_of_pos
  positivity

theorem density_nonneg {N : ℕ} (ψ : Wavefunction (N + 1)) (x : Position) :
    0 ≤ density ψ x := by
  unfold density
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun σ _ => integral_nonneg fun y => sq_nonneg _

theorem exteriorMass_nonneg {N : ℕ} (ψ : Wavefunction (N + 1)) (r : ℝ) :
    0 ≤ exteriorMass ψ r :=
  integral_nonneg fun x => density_nonneg ψ x

theorem radius_nonneg {N : ℕ} (ψ : Wavefunction (N + 1)) (m : ℕ) :
    0 ≤ radius ψ m := by
  apply Real.sInf_nonneg
  intro r hr
  exact hr.1

theorem integrable_cons {N : ℕ} {f : Configuration (N + 1) → ℝ}
    (hf : Integrable f) :
    Integrable (fun p : Position × Configuration N => f (Fin.cons p.1 p.2)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => Position) 0).symm e
  have hh := (he.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  simpa [e, Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero] using hh

theorem integral_cons {N : ℕ} {f : Configuration (N + 1) → ℝ}
    (hf : Integrable f) :
    (∫ x : Position, ∫ y : Configuration N, f (Fin.cons x y)) = ∫ z, f z := by
  rw [← integral_prod _ (integrable_cons hf)]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => Position) 0
  have he := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (N + 1) => Position) 0).symm e
  have hh := he.integral_comp' f
  simpa [MeasureTheory.Measure.volume_eq_prod, e, MeasurableEquiv.piFinSuccAbove_symm_apply,
    Fin.insertNthEquiv, Fin.insertNth_zero] using hh

theorem integrable_density {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) : Integrable (density ψ) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro σ _
  exact (integrable_cons (hψ σ).norm.integrable_sq).integral_prod_left

theorem integral_density {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) :
    (∫ x, density ψ x) = (N + 1 : ℝ) * normSquared ψ := by
  unfold density normSquared
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro σ _
    exact integral_cons (hψ σ).norm.integrable_sq
  · intro σ _
    exact (integrable_cons (hψ σ).norm.integrable_sq).integral_prod_left

theorem groundState_integral_density {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : IsNormalizedGroundState (N + 1) ψ) :
    (∫ x, density ψ x) = N + 1 := by
  obtain ⟨g, hg, hn, _⟩ := hψ
  rw [integral_density hg.2.2.1, hn, mul_one]

theorem exteriorMass_antitone {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) : Antitone (exteriorMass ψ) := by
  intro r s hrs
  apply setIntegral_mono_set (integrable_density hψ).integrableOn
  · exact Filter.Eventually.of_forall (fun x => density_nonneg ψ x)
  · exact Filter.Eventually.of_forall (fun x hx => lt_of_le_of_lt hrs hx)

theorem exteriorMass_tendsto_zero {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) :
    Tendsto (exteriorMass ψ) atTop (𝓝 0) := by
  have hs : (⋂ r : ℝ, {x : Position | r < ‖x‖}) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    exact lt_irrefl ‖x‖ (hx ‖x‖)
  have ht := tendsto_setIntegral_of_antitone
    (f := density ψ) (s := fun r : ℝ => {x : Position | r < ‖x‖})
    (fun _ => measurableSet_lt measurable_const continuous_norm.measurable)
    (fun _ _ hrs _ hx => lt_of_le_of_lt hrs hx)
    ⟨0, (integrable_density hψ).integrableOn⟩
  change Tendsto (fun r : ℝ => ∫ x in {x : Position | r < ‖x‖}, density ψ x)
    atTop (𝓝 0)
  simpa [hs] using ht

theorem radius_set_nonempty {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {m : ℕ} (hm : 0 < m) :
    {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (m : ℝ)}.Nonempty := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he := (exteriorMass_tendsto_zero hψ).eventually (gt_mem_nhds hm')
  obtain ⟨r, hr, hmr⟩ := ((eventually_ge_atTop (0 : ℝ)).and he).exists
  exact ⟨r, hr, hmr.le⟩

theorem radius_bracket {N : ℕ} {ψ : Wavefunction (N + 1)}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) {m : ℕ} {l u : ℝ}
    (hl : (m : ℝ) < exteriorMass ψ l) (hu0 : 0 ≤ u)
    (hu : exteriorMass ψ u ≤ (m : ℝ)) :
    l ≤ radius ψ m ∧ radius ψ m ≤ u := by
  unfold radius
  constructor
  · apply le_csInf (s := {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (m : ℝ)}) ⟨u, hu0, hu⟩
    intro r hr
    by_contra! hrl
    have hh := exteriorMass_antitone hψ hrl.le
    exact (not_le_of_gt hl) (hh.trans hr.2)
  · apply csInf_le ⟨0, fun r hr => hr.1⟩
    exact ⟨hu0, hu⟩

theorem scaled_ereal_bounds {c l u : ℝ} {x : EReal} (hc : 0 < c)
    (hl : ((l / c : ℝ) : EReal) ≤ x) (hu : x ≤ ((u / c : ℝ) : EReal)) :
    (l : EReal) ≤ (c : EReal) * x ∧ (c : EReal) * x ≤ (u : EReal) := by
  have hxt : x ≠ ⊤ := ne_of_lt (hu.trans_lt (EReal.coe_lt_top _))
  have hxb : x ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe _).trans_le hl)
  lift x to ℝ using ⟨hxt, hxb⟩ with x
  rw [← EReal.coe_mul]
  norm_cast at hl hu ⊢
  constructor
  · simpa [mul_comm] using (div_le_iff₀ hc).mp hl
  · simpa [mul_comm] using (le_div_iff₀ hc).mp hu

theorem inner_limits_bracket (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    {m : ℕ} {c l u : ℝ} (hc : 0 < c)
    (h : ∀ᶠ N in atTop, l ≤ c * radius (Ψ N) m ∧ c * radius (Ψ N) m ≤ u) :
    ((l : EReal) ≤ (c : EReal) * lowerRadius Ψ m ∧
      (c : EReal) * lowerRadius Ψ m ≤ (u : EReal)) ∧
    ((l : EReal) ≤ (c : EReal) * upperRadius Ψ m ∧
      (c : EReal) * upperRadius Ψ m ≤ (u : EReal)) := by
  have hlow : ((l / c : ℝ) : EReal) ≤ lowerRadius Ψ m := by
    unfold lowerRadius
    rw [largeCharge_eq_atTop]
    refine le_liminf_of_le (h := ?_)
    filter_upwards [h] with N hN
    exact EReal.coe_le_coe_iff.mpr ((div_le_iff₀ hc).mpr (by simpa [mul_comm] using hN.1))
  have hupp : upperRadius Ψ m ≤ ((u / c : ℝ) : EReal) := by
    unfold upperRadius
    rw [largeCharge_eq_atTop]
    refine limsup_le_of_le (h := ?_)
    filter_upwards [h] with N hN
    exact EReal.coe_le_coe_iff.mpr ((le_div_iff₀ hc).mpr (by simpa [mul_comm] using hN.2))
  have hlu : lowerRadius Ψ m ≤ upperRadius Ψ m := by
    unfold lowerRadius upperRadius
    rw [largeCharge_eq_atTop]
    exact liminf_le_limsup
  exact ⟨scaled_ereal_bounds hc hlow (hlu.trans hupp),
    scaled_ereal_bounds hc (hlow.trans hlu) hupp⟩

theorem tendsto_ereal_of_eventual_brackets {α : Type*} {f : Filter α}
    {v : α → EReal} {b : ℝ} (hb : 0 < b)
    (h : ∀ l u : ℝ, 0 < l → l < b → b < u →
      ∀ᶠ a in f, (l : EReal) ≤ v a ∧ v a ≤ (u : EReal)) :
    Tendsto v f (𝓝 (b : EReal)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨l, hal, hlb⟩ := EReal.exists_between_coe_real ha
    have hmax : max l (b / 2) < b := max_lt (EReal.coe_lt_coe_iff.mp hlb) (by linarith)
    have hpos : 0 < max l (b / 2) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    filter_upwards [h (max l (b / 2)) (b + 1) hpos hmax (by linarith)] with i hi
    exact (hal.trans_le (EReal.coe_le_coe_iff.mpr (le_max_left _ _))).trans_le hi.1
  · intro a ha
    obtain ⟨u, hbu, hua⟩ := EReal.exists_between_coe_real ha
    filter_upwards [h (b / 2) u (by linarith) (by linarith)
      (EReal.coe_lt_coe_iff.mp hbu)] with i hi
    exact hi.2.trans_lt hua

theorem iterated_limits_of_radius_brackets (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (h : ∀ l u : ℝ, 0 < l → l < bTF → bTF < u →
      ∀ᶠ m : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        l ≤ (m : ℝ) ^ (1 / 3 : ℝ) * radius (Ψ N) m ∧
        (m : ℝ) ^ (1 / 3 : ℝ) * radius (Ψ N) m ≤ u) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  have hb : ∀ l u : ℝ, 0 < l → l < bTF → bTF < u →
      ∀ᶠ m : ℕ in atTop,
        (((l : EReal) ≤ ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * lowerRadius Ψ m ∧
        ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * lowerRadius Ψ m ≤ (u : EReal)) ∧
        ((l : EReal) ≤ ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * upperRadius Ψ m ∧
        ((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) * upperRadius Ψ m ≤ (u : EReal))) := by
    intro l u hl hlb hbu
    filter_upwards [h l u hl hlb hbu, eventually_gt_atTop (0 : ℕ)] with m hm hp
    apply inner_limits_bracket Ψ (Real.rpow_pos_of_pos (by exact_mod_cast hp) _) hm
  constructor
  · apply tendsto_ereal_of_eventual_brackets bTF_pos
    intro l u hl hlb hbu
    exact (hb l u hl hlb hbu).mono fun _ hi => hi.2
  · apply tendsto_ereal_of_eventual_brackets bTF_pos
    intro l u hl hlb hbu
    exact (hb l u hl hlb hbu).mono fun _ hi => hi.1

theorem inverse_comparison_inversion {t v cap low high error : ℝ}
    (ht : 0 ≤ t) (hlow : 0 < low) (hlh : low < high)
    (herror : 0 ≤ error) (hcap : v ≤ cap) (hhigh : cap + error < high)
    (hcomp : ∀ h : ℝ, low ≤ h → h ≤ high →
      (h < t → h - error ≤ v) ∧ (t < h → v ≤ h + error)) :
    t < high ∧
      (low < t → |t - max v 0| ≤ error) ∧
      (t ≤ low → max v 0 ≤ low + error) ∧
      |t - max v 0| ≤ low + error := by
  have hth : t < high := by
    by_contra! hh
    obtain ⟨h, h1, h2⟩ := exists_between (max_lt hlh hhigh)
    have hlo : low < h := (le_max_left _ _).trans_lt h1
    have hc : cap + error < h := (le_max_right _ _).trans_lt h1
    have hhcomp := (hcomp h hlo.le h2.le).1 (h2.trans_le hh)
    linarith
  have hinterior : low < t → |t - max v 0| ≤ error := by
    intro hlt
    have hvlo : t - error ≤ v := by
      by_contra! hv
      obtain ⟨h, h1, h2⟩ := exists_between
        (show max low (v + error) < t from max_lt hlt (by linarith))
      have hlo : low < h := (le_max_left _ _).trans_lt h1
      have hc : v + error < h := (le_max_right _ _).trans_lt h1
      have hhcomp := (hcomp h hlo.le (h2.trans hth).le).1 h2
      linarith
    have hvhi : v ≤ t + error := by
      by_contra! hv
      obtain ⟨h, h1, h2⟩ := exists_between
        (show t < min high (v - error) from lt_min hth (by linarith))
      have hhi : h < high := h2.trans_le (min_le_left _ _)
      have hc : h < v - error := h2.trans_le (min_le_right _ _)
      have hhcomp := (hcomp h (hlt.trans h1).le hhi.le).2 h1
      linarith
    rw [abs_le]
    have hmaxhi : max v 0 ≤ t + error := max_le hvhi (by linarith)
    have hmaxlo : t - error ≤ max v 0 := hvlo.trans (le_max_left _ _)
    constructor <;> linarith
  have hfloor : t ≤ low → max v 0 ≤ low + error := by
    intro htl
    apply max_le _ (by linarith)
    by_contra! hv
    obtain ⟨h, h1, h2⟩ := exists_between
      (show low < min high (v - error) from lt_min hlh (by linarith))
    have hhi : h < high := h2.trans_le (min_le_left _ _)
    have hc : h < v - error := h2.trans_le (min_le_right _ _)
    have hhcomp := (hcomp h h1.le hhi.le).2 (htl.trans_lt h1)
    linarith
  refine ⟨hth, hinterior, hfloor, ?_⟩
  by_cases hlt : low < t
  · exact (hinterior hlt).trans (by linarith)
  · have htl : t ≤ low := le_of_not_gt hlt
    have hv := hfloor htl
    have hp := le_max_right v (0 : ℝ)
    rw [abs_le]
    constructor <;> linarith

theorem uniform_threshold_of_sequential {X : ℕ → Type*}
    (P : ∀ N, X N → Prop) (Zmin : ℕ → ℕ) (f : ℕ → ∀ N : ℕ, X N → ℝ) (c : ℝ)
    (hseq : ∀ (m Z : ℕ → ℕ), StrictMono m → (∀ n, Zmin (m n) ≤ Z n) →
      ∀ x : ∀ n, X (Z n), (∀ n, P (Z n) (x n)) →
      Tendsto (fun n => f (m n) (Z n) (x n)) atTop (𝓝 c)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ N, Zmin m ≤ N → ∀ x : X N, P N x → |f m N x - c| < ε := by
  classical
  intro ε hε
  by_contra hnot
  have hbad := frequently_atTop.mp (not_eventually.mp hnot)
  obtain ⟨m, hm, hfail⟩ := Nat.exists_strictMono_subsequence (by
    intro M
    obtain ⟨n, hn, hbadn⟩ := hbad (M + 1)
    exact ⟨n, by omega, hbadn⟩)
  have hchoose : ∀ n, ∃ N, Zmin (m n) ≤ N ∧
      ∃ x : X N, P N x ∧ ε ≤ |f (m n) N x - c| := by
    intro n
    simpa only [not_forall, Classical.not_imp, not_lt, exists_prop] using hfail n
  choose Z hZ x hx hεx using hchoose
  have ht := hseq m Z hm hZ x hx
  obtain ⟨n, hn⟩ := ((Metric.tendsto_nhds.mp ht) ε hε).exists
  exact (not_lt_of_ge (hεx n)) (by simpa only [Real.dist_eq] using hn)

theorem cube_root_cube (m : ℕ) : ((m : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = m := by
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (x := (m : ℝ)) (n := 3) (by positivity) (by decide)

theorem bTF_cube : bTF ^ (3 : ℕ) = 81 * Real.pi ^ 2 / 2 := by
  unfold bTF
  simpa only [one_div, Nat.cast_ofNat] using
    Real.rpow_inv_natCast_pow (x := 81 * Real.pi ^ 2 / 2) (n := 3)
      (by positivity) (by decide)

theorem normalized_tail_scale (m : ℕ) (T : ℝ → ℝ) (a : ℝ) :
    ((m : ℝ) ^ (-(1 / 3 : ℝ))) ^ (3 : ℕ) * T (a * (m : ℝ) ^ (-(1 / 3 : ℝ))) =
      T (a / (m : ℝ) ^ (1 / 3 : ℝ)) / m := by
  rw [Real.rpow_neg (by positivity), inv_pow, cube_root_cube]
  simp only [div_eq_mul_inv, mul_comm]

theorem inverse_comparison_fixed_accuracy {k cap high ε : ℝ}
    (hk : 0 < k) (hhigh : 0 < high) (hcap : cap + 1 < high) (hε : 0 < ε) :
    ∃ low error : ℝ, 0 < low ∧ low < high ∧ 0 < error ∧ error < low / 16 ∧
      error < 1 ∧ ∀ t v : ℝ, 0 ≤ t → v ≤ cap →
        (∀ h : ℝ, low ≤ h → h ≤ high →
          (h < t → h - error ≤ v) ∧ (t < h → v ≤ h + error)) →
        k * |t ^ (3 / 2 : ℝ) - (max v 0) ^ (3 / 2 : ℝ)| < ε := by
  have hcont := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) high)).uniformContinuousOn_of_continuous
    (Real.continuous_rpow_const (q := (3 / 2 : ℝ)) (by norm_num)).continuousOn
  obtain ⟨δ, hδ, hδcont⟩ := Metric.uniformContinuousOn_iff.mp hcont (ε / k) (by positivity)
  let low := min (high / 2) (δ / 4)
  let error := min (low / 32) (min (1 / 2) (δ / 4))
  have hlpos : 0 < low := lt_min (by positivity) (by positivity)
  have hlhi : low < high := (min_le_left _ _).trans_lt (by linarith)
  have hld : low ≤ δ / 4 := min_le_right _ _
  have hepos : 0 < error := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hel : error < low / 16 := (min_le_left _ _).trans_lt (by linarith)
  have heone : error < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hed : error ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨low, error, hlpos, hlhi, hepos, hel, heone, ?_⟩
  intro t v ht hv hcomp
  have hinv := inverse_comparison_inversion ht hlpos hlhi hepos.le hv (by linarith) hcomp
  have htmem : t ∈ Set.Icc (0 : ℝ) high := ⟨ht, hinv.1.le⟩
  have hvmem : max v 0 ∈ Set.Icc (0 : ℝ) high :=
    ⟨le_max_right _ _, max_le (hv.trans (by linarith)) hhigh.le⟩
  have hdist : dist t (max v 0) < δ := by
    rw [Real.dist_eq]
    exact hinv.2.2.2.trans_lt (by linarith)
  have hp := hδcont t htmem (max v 0) hvmem hdist
  rw [Real.dist_eq] at hp
  have hh := (lt_div_iff₀ hk).mp hp
  simpa only [mul_comm] using hh

def configurationDensity {n : ℕ} (ψ : Wavefunction n) (x : Configuration n) : ℝ :=
  ∑ σ : Spins n, ‖ψ σ x‖ ^ 2

def rawExpectation {n : ℕ} (ψ : Wavefunction n) (F : Configuration n → ℝ) : ℝ :=
  ∫ x : Configuration n, F x * configurationDensity ψ x

def rawCount {n : ℕ} (S : Set Position) (x : Configuration n) : ℝ :=
  ∑ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (x i)

theorem configurationDensity_nonneg {n : ℕ} (ψ : Wavefunction n) (x : Configuration n) :
    0 ≤ configurationDensity ψ x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem integrable_configurationDensity {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) : Integrable (configurationDensity ψ) :=
  integrable_finsetSum _ fun σ _ => (hψ σ).norm.integrable_sq

theorem integral_configurationDensity {n : ℕ} {ψ : Wavefunction n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) :
    (∫ x, configurationDensity ψ x) = normSquared ψ := by
  exact integral_finsetSum _ fun σ _ => (hψ σ).norm.integrable_sq

theorem piCongrLeft_perm {ι α : Type*} (p : Equiv.Perm ι) (x : ι → α) :
    Equiv.piCongrLeft (fun _ : ι => α) p.symm x = x ∘ p := by
  funext i
  simp [Equiv.piCongrLeft_apply]

theorem configurationDensity_perm {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) (p : Equiv.Perm (Fin n)) :
    (fun x : Configuration n => configurationDensity ψ (x ∘ p)) =ᵐ[volume]
      configurationDensity ψ := by
  have hsign : ‖(((Equiv.Perm.sign p : ℤ) : ℂ))‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;> simp [hp]
  have ha : ∀ᵐ x : Configuration n ∂volume, ∀ σ : Spins n,
      ψ (σ ∘ p) (x ∘ p) = (((Equiv.Perm.sign p : ℤ) : ℂ)) * ψ σ x :=
    (ae_all_iff).mpr (hψ p)
  filter_upwards [ha] with x hx
  unfold configurationDensity
  have hsum := (Equiv.piCongrLeft (fun _ : Fin n => Fin 2) p.symm).sum_comp
    (fun σ : Spins n => ‖ψ σ (x ∘ p)‖ ^ 2)
  have hh : (∑ σ : Spins n, ‖ψ (σ ∘ p) (x ∘ p)‖ ^ 2) =
      ∑ σ : Spins n, ‖ψ σ (x ∘ p)‖ ^ 2 := by
    simpa only [piCongrLeft_perm] using hsum
  rw [← hh]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hx σ, norm_mul, hsign, one_mul]

end NeutralAtom
end
end
end

end OAI
