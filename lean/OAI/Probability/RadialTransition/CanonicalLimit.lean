import OAI.Probability.RadialTransition.ThermodynamicLimit

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

instance (d : ℝ) : IsCountablyGenerated (thermodynamicFilter d) := by
  unfold thermodynamicFilter
  infer_instance

def HasBoxReplication (H : ℝ → ℕ → ℝ) : Prop :=
  ∀ (s L : ℝ) (b : ℕ), 0 < s → 0 < L → (b : ℝ) * (s + 2) ≤ L →
    ∀ m : Fin (b ^ 3) → ℕ,
      H L (∑ j, m j) ≤ s ^ 3 / L ^ 3 * ∑ j, H s (m j)

theorem boxCost_adjustment {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    {s L : ℝ} (hs : 0 < s) (hL : 0 < L) (b m q N : ℕ)
    (hbL : (b : ℝ) * (s + 2) ≤ L) (hm : 0 < m) (hmq : m < q)
    (hN : N ≤ b ^ 3 * q) {c K : ℝ} (hc0 : 0 < c) (hcm : c ≤ (m : ℝ))
    (hcq : c ≤ ((q - m : ℕ) : ℝ)) (hK : 0 ≤ K)
    (hcost : ∀ j ≤ q, |H s j| ≤ K) :
    H L N ≤ s ^ 3 / L ^ 3 *
      ((b : ℝ) ^ 3 * H s m + 2 * K * (|(N : ℝ) - (b : ℝ) ^ 3 * m| / c + 1)) := by
  obtain ⟨f, hfN, hfq, hfc⟩ := exists_integer_adjustment (b ^ 3) m q N hm hmq hN hc0 hcm hcq
  have hr := hrep s L b hs hL hbL f
  rw [hfN] at hr
  have hsum := sum_changed_cost f m (H s) (hcost m hmq.le) (fun i => hcost (f i) (hfq i))
  simp only [Fintype.card_fin, Nat.cast_pow] at hsum hfc
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hsum.trans (by gcongr)

theorem boxCost_limsup_bound {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    {d s c K : ℝ} (hd : 0 < d) (hs : 0 < s) (hc : 0 < c) (hK : 0 ≤ K)
    (m q : ℕ) (hm : 0 < m) (hmq : m < q)
    (hcm : c * s ^ 3 ≤ (m : ℝ)) (hcq : c * s ^ 3 ≤ ((q - m : ℕ) : ℝ))
    (hcap : d < (q : ℝ) / (s + 2) ^ 3) (hcost : ∀ j ≤ q, |H s j| ≤ K)
    (hbelow : IsBoundedUnder (· ≥ ·) (thermodynamicFilter d) (fun z => H z.1 z.2)) :
    limsup (fun z => H z.1 z.2) (thermodynamicFilter d) ≤
      (s / (s + 2)) ^ 3 * H s m +
        2 * K / c * |d - (s / (s + 2)) ^ 3 * ((m : ℝ) / s ^ 3)| := by
  let _ := thermodynamicFilter_neBot hd.le
  let F := thermodynamicFilter d
  let b (z : ℝ × ℕ) : ℕ := ⌊z.1 / (s + 2)⌋₊
  let r (z : ℝ × ℕ) : ℝ := ((b z : ℝ) / z.1) ^ 3
  have hr : Tendsto r F (nhds ((s + 2)⁻¹ ^ 3)) := by
    have hh := ((tendsto_nat_floor_mul_div_atTop
      (show 0 ≤ (s + 2)⁻¹ by positivity)).pow 3).comp (thermodynamicFilter_side d)
    simpa only [r, b, Function.comp_def, div_eq_mul_inv, mul_comm] using hh
  have hden : Tendsto (fun z : ℝ × ℕ => (z.1 ^ 3)⁻¹) F (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : 3 ≠ 0)).comp
      (thermodynamicFilter_side d))
  let G (z : ℝ × ℕ) : ℝ := s ^ 3 * (r z * H s m +
    2 * K * (|(z.2 : ℝ) / z.1 ^ 3 - r z * m| / (c * s ^ 3) + (z.1 ^ 3)⁻¹))
  have hG : Tendsto G F (nhds (s ^ 3 * ((s + 2)⁻¹ ^ 3 * H s m +
      2 * K * (|d - (s + 2)⁻¹ ^ 3 * m| / (c * s ^ 3))))) := by
    have hh := ((hr.mul_const (H s m)).add
      (((((thermodynamicFilter_density d).sub (hr.mul_const (m : ℝ))).abs.div_const
        (c * s ^ 3)).add hden).const_mul (2 * K))).const_mul (s ^ 3)
    simpa only [add_zero] using hh
  have hcaplimit : Tendsto (fun z => r z * q) F (nhds ((q : ℝ) / (s + 2) ^ 3)) := by
    simpa only [inv_pow, div_eq_mul_inv, mul_comm] using hr.mul_const (q : ℝ)
  obtain ⟨a, hda, haq⟩ := exists_between hcap
  have hN : ∀ᶠ z in F, (z.2 : ℝ) / z.1 ^ 3 < r z * q := by
    filter_upwards [(thermodynamicFilter_density d).eventually_lt_const hda,
      hcaplimit.eventually_const_lt haq] with z hz hq
    exact hz.trans hq
  have hle : ∀ᶠ z in F, H z.1 z.2 ≤ G z := by
    filter_upwards [hN, (thermodynamicFilter_side d).eventually (eventually_gt_atTop (0 : ℝ))]
      with z hNz hL
    have hbL : (b z : ℝ) * (s + 2) ≤ z.1 :=
      (le_div_iff₀ (by positivity : 0 < s + 2)).mp (Nat.floor_le (by positivity))
    have hNe : z.2 ≤ b z ^ 3 * q := by
      have he : r z * q = ((b z : ℝ) ^ 3 * q) / z.1 ^ 3 := by dsimp [r]; ring
      rw [he] at hNz
      have hh := (div_lt_div_iff_of_pos_right (pow_pos hL 3)).mp hNz
      exact_mod_cast hh.le
    have hh := boxCost_adjustment hrep hs hL (b z) m q z.2 hbL hm hmq hNe
      (mul_pos hc (pow_pos hs 3)) hcm hcq hK hcost
    apply hh.trans_eq
    have habs : |(z.2 : ℝ) / z.1 ^ 3 - r z * m| =
        |(z.2 : ℝ) - (b z : ℝ) ^ 3 * m| / z.1 ^ 3 := by
      dsimp only [r]
      rw [div_pow, div_mul_eq_mul_div, ← sub_div, abs_div, abs_of_pos (pow_pos hL 3)]
    dsimp only [G]
    rw [habs]
    dsimp only [r]
    ring
  have hh := limsup_le_limsup hle hbelow.isCobounded_le hG.isBoundedUnder_le
  rw [hG.limsup_eq] at hh
  apply hh.trans_eq
  field_simp

theorem tendsto_side_ratio :
    Tendsto (fun s : ℝ => s / (s + 2)) atTop (nhds 1) := by
  have hh := ((tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_id)).const_mul 2).const_sub 1
  simp only [mul_zero, sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  simp only [Function.comp_def, id_eq]
  field_simp
  ring

theorem boxCost_limit {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    (hbnd : ∀ D : ℝ, 0 < D → ∃ K : ℝ, 0 ≤ K ∧
      ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ, (n : ℝ) / s ^ 3 ≤ D → |H s n| ≤ K)
    {d : ℝ} (hd : 0 < d) :
    ∃ A : ℝ, Tendsto (fun z : ℝ × ℕ => H z.1 z.2) (thermodynamicFilter d) (nhds A) := by
  let _ := thermodynamicFilter_neBot hd.le
  obtain ⟨K, hK, hbound⟩ := hbnd (2 * d) (by positivity)
  have hevent : ∀ᶠ z in thermodynamicFilter d, |H z.1 z.2| ≤ K := by
    filter_upwards [(thermodynamicFilter_side d).eventually (eventually_ge_atTop (1 : ℝ)),
      (thermodynamicFilter_density d).eventually_lt_const (show d < 2 * d by linarith)]
      with z hz hdens
    exact hbound z.1 hz z.2 hdens.le
  have hbelow : IsBoundedUnder (· ≥ ·) (thermodynamicFilter d) (fun z => H z.1 z.2) :=
    ⟨-K, hevent.mono (fun z hz => (abs_le.mp hz).1)⟩
  have habove : IsBoundedUnder (· ≤ ·) (thermodynamicFilter d) (fun z => H z.1 z.2) :=
    ⟨K, hevent.mono (fun z hz => (abs_le.mp hz).2)⟩
  let A := liminf (fun z => H z.1 z.2) (thermodynamicFilter d)
  obtain ⟨x, hxH, hx⟩ := exists_seq_tendsto_liminf habove.isCobounded_ge hbelow
  let s (j : ℕ) := (x j).1
  let m (j : ℕ) := (x j).2
  let q (j : ℕ) : ℕ := ⌊2 * d * s j ^ 3⌋₊
  have hs : Tendsto s atTop atTop := (thermodynamicFilter_side d).comp hx
  have hm : Tendsto (fun j => (m j : ℝ) / s j ^ 3) atTop (nhds d) :=
    (thermodynamicFilter_density d).comp hx
  have hq : Tendsto (fun j => (q j : ℝ) / s j ^ 3) atTop (nhds (2 * d)) :=
    (floor_density_tendsto (show 0 ≤ 2 * d by positivity)).comp hs
  have hratio := tendsto_side_ratio.comp hs
  have hcap : Tendsto (fun j => (q j : ℝ) / (s j + 2) ^ 3) atTop (nhds (2 * d)) := by
    have hh := hq.mul (hratio.pow 3)
    simp only [one_pow, mul_one] at hh
    apply hh.congr'
    filter_upwards [hs.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    simp only [Function.comp_def]
    field_simp
  have hdiff : Tendsto (fun j => ((q j : ℝ) - m j) / s j ^ 3) atTop (nhds d) := by
    have hh := hq.sub hm
    simp only [← sub_div] at hh
    convert hh using 1
    congr 1
    ring
  have href : ∀ᶠ j in atTop,
      limsup (fun z => H z.1 z.2) (thermodynamicFilter d) ≤
        (s j / (s j + 2)) ^ 3 * H (s j) (m j) +
          2 * K / (d / 2) * |d - (s j / (s j + 2)) ^ 3 * ((m j : ℝ) / s j ^ 3)| := by
    filter_upwards [hs.eventually (eventually_ge_atTop (1 : ℝ)),
      hm.eventually_const_lt (show d / 2 < d by linarith),
      hdiff.eventually_const_lt (show d / 2 < d by linarith),
      hcap.eventually_const_lt (show d < 2 * d by linarith)] with j hsj hmj hdiffj hcapj
    have hsj0 : 0 < s j := by linarith
    have hcm : d / 2 * s j ^ 3 < (m j : ℝ) :=
      (lt_div_iff₀ (pow_pos hsj0 3)).mp hmj
    have hcq : d / 2 * s j ^ 3 < (q j : ℝ) - m j :=
      (lt_div_iff₀ (pow_pos hsj0 3)).mp hdiffj
    have hm0 : 0 < m j := by
      have hh : (0 : ℝ) < m j := (by positivity : (0 : ℝ) < d / 2 * s j ^ 3).trans hcm
      exact_mod_cast hh
    have hmq : m j < q j := by
      have hh : (m j : ℝ) < q j := by linarith [show 0 < d / 2 * s j ^ 3 by positivity]
      exact_mod_cast hh
    apply boxCost_limsup_bound hrep hd hsj0 (show 0 < d / 2 by positivity) hK (m j) (q j)
      hm0 hmq hcm.le
    · rw [Nat.cast_sub hmq.le]
      exact hcq.le
    · exact hcapj
    · intro n hn
      apply hbound (s j) hsj n
      apply (div_le_iff₀ (pow_pos hsj0 3)).mpr
      exact (show (n : ℝ) ≤ q j by exact_mod_cast hn).trans (Nat.floor_le (by positivity))
    · exact hbelow
  have hlim : Tendsto (fun j => (s j / (s j + 2)) ^ 3 * H (s j) (m j) +
      2 * K / (d / 2) * |d - (s j / (s j + 2)) ^ 3 * ((m j : ℝ) / s j ^ 3)|)
      atTop (nhds A) := by
    have hh := ((hratio.pow 3).mul hxH).add
      ((((hratio.pow 3).mul hm).const_sub d).abs.const_mul (2 * K / (d / 2)))
    simpa only [one_pow, one_mul, sub_self, abs_zero, mul_zero, add_zero, Function.comp_def, s, m, A] using hh
  refine ⟨A, tendsto_of_le_liminf_of_limsup_le le_rfl ?_ habove hbelow⟩
  exact ge_of_tendsto hlim href

theorem boxCost_limit_with_bounds {H : ℝ → ℕ → ℝ} (hrep : HasBoxReplication H)
    {l u : ℝ → ℝ} (hl : Continuous l) (hu : Continuous u) (hzero : l 0 = u 0)
    (hb : ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ,
      l ((n : ℝ) / s ^ 3) ≤ H s n ∧ H s n ≤ u ((n : ℝ) / s ^ 3))
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ A : ℝ, Tendsto (fun z : ℝ × ℕ => H z.1 z.2) (thermodynamicFilter d) (nhds A) ∧
      l d ≤ A ∧ A ≤ u d := by
  let _ := thermodynamicFilter_neBot hd
  have hlo : Tendsto (fun z : ℝ × ℕ => l ((z.2 : ℝ) / z.1 ^ 3))
      (thermodynamicFilter d) (nhds (l d)) := hl.continuousAt.tendsto.comp (thermodynamicFilter_density d)
  have hup : Tendsto (fun z : ℝ × ℕ => u ((z.2 : ℝ) / z.1 ^ 3))
      (thermodynamicFilter d) (nhds (u d)) := hu.continuousAt.tendsto.comp (thermodynamicFilter_density d)
  have hevent : ∀ᶠ z in thermodynamicFilter d,
      l ((z.2 : ℝ) / z.1 ^ 3) ≤ H z.1 z.2 ∧ H z.1 z.2 ≤ u ((z.2 : ℝ) / z.1 ^ 3) := by
    filter_upwards [(thermodynamicFilter_side d).eventually (eventually_ge_atTop (1 : ℝ))] with z hz
    exact hb z.1 hz z.2
  obtain rfl | hdpos := hd.eq_or_lt
  · refine ⟨l 0, ?_, le_rfl, hzero.le⟩
    rw [← hzero] at hup
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup
      (hevent.mono (fun _ hz => hz.1)) (hevent.mono (fun _ hz => hz.2))
  · have hlocal : ∀ D : ℝ, 0 < D → ∃ K : ℝ, 0 ≤ K ∧
        ∀ s : ℝ, 1 ≤ s → ∀ n : ℕ, (n : ℝ) / s ^ 3 ≤ D → |H s n| ≤ K := by
      intro D _
      obtain ⟨Cl, hCl⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) D) hl.continuousOn
      obtain ⟨Cu, hCu⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) D) hu.continuousOn
      refine ⟨max 0 (max Cl Cu), le_max_left _ _, ?_⟩
      intro s hs n hn
      have hds : (n : ℝ) / s ^ 3 ∈ Icc (0 : ℝ) D := ⟨by positivity, hn⟩
      have hll : |l ((n : ℝ) / s ^ 3)| ≤ max 0 (max Cl Cu) := by
        have hh := hCl _ hds
        rw [Real.norm_eq_abs] at hh
        exact hh.trans ((le_max_left _ _).trans (le_max_right _ _))
      have huu : |u ((n : ℝ) / s ^ 3)| ≤ max 0 (max Cl Cu) := by
        have hh := hCu _ hds
        rw [Real.norm_eq_abs] at hh
        exact hh.trans ((le_max_right _ _).trans (le_max_right _ _))
      exact abs_le.mpr ⟨(abs_le.mp hll).1.trans (hb s hs n).1,
        (hb s hs n).2.trans (abs_le.mp huu).2⟩
    obtain ⟨A, hA⟩ := boxCost_limit hrep hlocal hdpos
    exact ⟨A, hA, le_of_tendsto_of_tendsto hlo hA (hevent.mono (fun _ hz => hz.1)),
      le_of_tendsto_of_tendsto hA hup (hevent.mono (fun _ hz => hz.2))⟩

theorem finiteCanonical_limit {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t β c B K : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlow : ∀ L : ℝ, 1 ≤ L → ∀ (N : ℕ) (x : Fin N → Position),
      x ∈ configurationCube L N → c * (N : ℝ)^2 / L^3 - B * N ≤ energy φ x)
    (hmean : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
      (∫ x : Fin N → Position, energy φ x
        ∂MeasureTheory.Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ K * (N : ℝ)^2 / L^3)
    {d : ℝ} (hd : 0 ≤ d) :
    ∃ A : ℝ, Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
        (thermodynamicFilter d) (nhds A) ∧
      β / t * (c * d ^ 2 - B * d) + (d * Real.log d - d) / t ≤ A ∧
      A ≤ β / t * K * d ^ 2 + d * Real.log d / t := by
  apply boxCost_limit_with_bounds (H := fun L N => finiteCanonical φ t L N β) (d := d)
    (fun s L b hs hL hbL m => finiteCanonical_replication hφ hb hβ ht hs hL hc b hbL m)
    (l := fun d => β / t * (c * d ^ 2 - B * d) + (d * Real.log d - d) / t)
    (u := fun d => β / t * K * d ^ 2 + d * Real.log d / t)
  · fun_prop (disch := exact Real.continuous_mul_log)
  · fun_prop (disch := exact Real.continuous_mul_log)
  · simp
  · intro L hL N
    exact finiteCanonical_bounds hφ hb (by linarith) ht hβ N (hlow L hL N) (hmean L hL N)
  · exact hd

def canonicalThermo (φ : Potential) (t β d : ℝ) : ℝ :=
  liminf (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β) (thermodynamicFilter d)

theorem canonicalThermo_spec {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t β c B K : ℝ} (ht : 0 < t) (hβ : 0 ≤ β)
    (hc : ∀ r : ℝ≥0, 2 ≤ (r : ℝ) → φ r ≤ 0)
    (hlow : ∀ L : ℝ, 1 ≤ L → ∀ (N : ℕ) (x : Fin N → Position),
      x ∈ configurationCube L N → c * (N : ℝ)^2 / L^3 - B * N ≤ energy φ x)
    (hmean : ∀ L : ℝ, 1 ≤ L → ∀ N : ℕ,
      (∫ x : Fin N → Position, energy φ x
        ∂MeasureTheory.Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ K * (N : ℝ)^2 / L^3)
    {d : ℝ} (hd : 0 ≤ d) :
    Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
        (thermodynamicFilter d) (nhds (canonicalThermo φ t β d)) ∧
      β / t * (c * d ^ 2 - B * d) + (d * Real.log d - d) / t ≤ canonicalThermo φ t β d ∧
      canonicalThermo φ t β d ≤ β / t * K * d ^ 2 + d * Real.log d / t := by
  let _ := thermodynamicFilter_neBot hd
  obtain ⟨A, hA, hlo, hhi⟩ := finiteCanonical_limit hφ hb ht hβ hc hlow hmean hd
  have he : canonicalThermo φ t β d = A := hA.liminf_eq
  rw [he]
  exact ⟨hA, hlo, hhi⟩

theorem familyCanonicalThermo_spec {t β d : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hcoerc : 2197 * t * bumpIntegral⁻¹ * (∑' n, a n) / 2 ≤ t ^ 2 / 16)
    (hβ : 0 ≤ β) (hd : 0 ≤ d) :
    Tendsto (fun z : ℝ × ℕ => finiteCanonical (familyPotential t a R) t z.1 z.2 β)
        (thermodynamicFilter d) (nhds (canonicalThermo (familyPotential t a R) t β d)) ∧
      β / t * (t ^ 2 / 3456 * d ^ 2 - t ^ 2 / 2 * d) +
        (d * Real.log d - d) / t ≤ canonicalThermo (familyPotential t a R) t β d ∧
      canonicalThermo (familyPotential t a R) t β d ≤
        β / t * coreIntegral t * d ^ 2 + d * Real.log d / t := by
  apply canonicalThermo_spec (continuous_familyPotential ha hR hs t)
    (bounded_familyPotential ha hR hs t) (by linarith) hβ
    (fun _ hr => familyPotential_nonpos_outer ha hR ht hr)
  · intro L hL N x hx
    exact family_density_stability (by linarith) hL ha hR hs hcoerc x hx
  · intro L hL N
    exact probability_energy_family_upper ht ha hR hs (by linarith) N
  · exact hd

theorem canonicalThermo_concave {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d)
    (hlim : ∀ β : ℝ, 0 < β → Tendsto (fun z : ℝ × ℕ => finiteCanonical φ t z.1 z.2 β)
      (thermodynamicFilter d) (nhds (canonicalThermo φ t β d))) :
    ConcaveOn ℝ (Ioi 0) (fun β => canonicalThermo φ t β d) := by
  let _ := thermodynamicFilter_neBot hd
  refine ⟨convex_Ioi _, ?_⟩
  intro β hβ γ hγ a b ha hb' hab
  have hmix : 0 < a * β + b * γ := by
    exact (convex_Ioi (0 : ℝ)) hβ hγ ha hb' hab
  have hl := (hlim β hβ).const_mul a |>.add ((hlim γ hγ).const_mul b)
  have hr := hlim (a * β + b * γ) hmix
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [(thermodynamicFilter_side d).eventually (eventually_gt_atTop (0 : ℝ))] with z hz
  exact (finiteCanonical_concave hφ hb ht hz z.2).2 (mem_univ β) (mem_univ γ) ha hb' hab

end RadialTransition

end

end OAI
