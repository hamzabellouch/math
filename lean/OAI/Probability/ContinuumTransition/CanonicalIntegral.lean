import OAI.Probability.ContinuumTransition.CubeCoercivity

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

@[simp] theorem radialPotential_ne_bot (φ : ℝ → ℝ) (x : Space) :
    radialPotential φ x ≠ ⊥ := by
  unfold radialPotential
  split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

theorem ereal_sum_ne_bot {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, EReal.add_ne_bot_iff]
    exact ⟨hf i (Finset.mem_insert_self i s), ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))⟩

theorem measurable_energy {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (N : ℕ) : Measurable (fun x : Fin N → Space => energy φ x) := by
  classical
  unfold energy
  fun_prop

theorem measurable_boltzmann {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    (β : ℝ) (N : ℕ) : Measurable (fun x : Fin N → Space => boltzmann φ β x) := by
  have hE := measurable_energy hφ N
  exact Measurable.ite (hE (measurableSet_singleton ⊤)) measurable_const
    ((measurable_const.mul hE.ereal_toReal).exp)

theorem boltzmann_nonneg (φ : ℝ → ℝ) (β : ℝ) {N : ℕ} (x : Fin N → Space) :
    0 ≤ boltzmann φ β x := by
  unfold boltzmann
  split_ifs
  · rfl
  · exact (Real.exp_pos _).le

theorem boltzmann_le_of_stable {φ : ℝ → ℝ} {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ≤ Real.exp (β * B * N) := by
  unfold boltzmann
  split_ifs with htop
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    have he := EReal.toReal_le_toReal (hstable N x) (EReal.coe_ne_bot _) htop
    simp only [EReal.toReal_coe] at he
    nlinarith [mul_le_mul_of_nonneg_left he hβ]

theorem isCompact_cube (L : ℝ) : IsCompact (cube L) := by
  have h := isCompact_pi_infinite (fun _ : Fin 3 => isCompact_Icc (a := -L / 2) (b := L / 2))
  exact (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).isCompact_preimage.mpr h

theorem measurableSet_cube (L : ℝ) : MeasurableSet (cube L) :=
  (isCompact_cube L).measurableSet

theorem isCompact_configurations (L : ℝ) (N : ℕ) :
    IsCompact {x : Fin N → Space | ∀ i, x i ∈ cube L} :=
  isCompact_pi_infinite (fun _ => isCompact_cube L)

theorem integrableOn_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B : ℝ} (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) :
    IntegrableOn (fun x : Fin N → Space => boltzmann φ β x)
      {x : Fin N → Space | ∀ i, x i ∈ cube L} := by
  have hK := isCompact_configurations L N
  have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  apply (integrable_const (Real.exp (β * B * N))).mono'
    (measurable_boltzmann hφ β N).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ β x)]
  exact boltzmann_le_of_stable hβ hstable x

theorem energy_eq_real_of_injective (φ : ℝ → ℝ) {N : ℕ} {x : Fin N → Space}
    (hx : Function.Injective x) :
    energy φ x = ((∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
      φ ‖x i - x j‖ : ℝ) : EReal) := by
  classical
  unfold energy
  simp only [ereal_coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  exact ite_eq_right (sub_ne_zero.mpr (hx.ne hij))

theorem boltzmann_pos_of_injective (φ : ℝ → ℝ) (β : ℝ) {N : ℕ}
    {x : Fin N → Space} (hx : Function.Injective x) : 0 < boltzmann φ β x := by
  unfold boltzmann
  rw [ite_eq_right (by rw [energy_eq_real_of_injective φ hx]; exact EReal.coe_ne_top _)]
  exact Real.exp_pos _

def openConfigurations (L : ℝ) (N : ℕ) : Set (Fin N → Space) :=
  {x | (∀ i k, x i k ∈ Ioo (-L / 2) (L / 2)) ∧ Function.Injective x}

theorem isOpen_openConfigurations (L : ℝ) (N : ℕ) :
    IsOpen (openConfigurations L N) := by
  have hbox : IsOpen {x : Fin N → Space | ∀ i k, x i k ∈ Ioo (-L / 2) (L / 2)} := by
    simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_Ioo.preimage ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp
      (continuous_apply i))
  have hinj : IsOpen {x : Fin N → Space | Function.Injective x} := by
    have heq : {x : Fin N → Space | Function.Injective x} =
        ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {x | x i ≠ x j} := by
      ext x
      simp only [mem_ofPred_eq, mem_iInter]
      exact ⟨fun h i j hij => h.ne hij, fun h i j hij => by_contra fun hij' => h i j hij' hij⟩
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply isOpen_iInter_of_finite
    intro _
    exact (isClosed_eq (continuous_apply i) (continuous_apply j)).isOpen_compl
  exact hbox.inter hinj

theorem openConfigurations_nonempty {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (openConfigurations L N).Nonempty := by
  let c : ℝ := L / (4 * ((N : ℝ) + 1))
  have hc : 0 < c := by dsimp [c]; positivity
  let x : Fin N → Space := fun i => WithLp.toLp 2 (fun _ : Fin 3 => (i : ℝ) * c)
  refine ⟨x, ?_, ?_⟩
  · intro i k
    change -L / 2 < (i : ℝ) * c ∧ (i : ℝ) * c < L / 2
    have hi : (i : ℝ) < N := by exact_mod_cast i.isLt
    have hinonneg : 0 ≤ (i : ℝ) := by positivity
    constructor
    · nlinarith [mul_nonneg hinonneg hc.le]
    · dsimp [c]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hL (by exact_mod_cast Nat.zero_lt_succ N : 0 < (N : ℝ) + 1)]
  · intro i j he
    have hij := congrArg (fun y : Space => y 0) he
    change (i : ℝ) * c = (j : ℝ) * c at hij
    have hij' := mul_right_cancel₀ hc.ne' hij
    exact Fin.ext (by exact_mod_cast hij')

theorem partition_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : 0 < partition φ β L N := by
  classical
  unfold partition
  split_ifs
  · norm_num
  · apply mul_pos (by positivity)
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
    apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
      (openConfigurations_nonempty hL N))
    apply measure_mono
    intro x hx
    exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
      fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem boltzmann_add (φ : ℝ → ℝ) (β γ : ℝ) {N : ℕ} (x : Fin N → Space) :
    boltzmann φ (β + γ) x = boltzmann φ β x * boltzmann φ γ x := by
  unfold boltzmann
  split_ifs
  · ring
  · rw [← Real.exp_add]
    congr 1
    ring

theorem boltzmann_rpow (φ : ℝ → ℝ) (β : ℝ) {p : ℝ} (hp : 0 < p)
    {N : ℕ} (x : Fin N → Space) :
    boltzmann φ β x ^ p = boltzmann φ (p * β) x := by
  unfold boltzmann
  split_ifs
  · exact Real.zero_rpow hp.ne'
  · rw [← Real.exp_mul]
    congr 1
    ring

theorem integral_boltzmann_logconvex {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B : ℝ}
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (L : ℝ) (N : ℕ) {β γ a b : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ (a * β + b * γ) x) ≤
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b := by
  let μ : Measure (Fin N → Space) :=
    volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}
  have hp (c u : ℝ) (hc : 0 < c) (x : Fin N → Space) :
      ‖boltzmann φ (c * u) x‖ ^ (1 / c) = boltzmann φ u x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (c * u) x),
      boltzmann_rpow φ (c * u) (one_div_pos.mpr hc)]
    congr 1
    field_simp
  have hLp (c u : ℝ) (hc : 0 < c) (hu : 0 < u) :
      MemLp (fun x : Fin N → Space => boltzmann φ (c * u) x) (ENNReal.ofReal (1 / c)) μ := by
    have A : ENNReal.ofReal (1 / c) ≠ 0 := by positivity
    have B' : ENNReal.ofReal (1 / c) ≠ ∞ := ENNReal.ofReal_ne_top
    rw [← memLp_norm_rpow_iff _ A B', ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / c),
      ENNReal.div_self A B', memLp_one_iff_integrable]
    · apply (integrableOn_boltzmann hφ hu.le hstable L N).congr
      exact ae_of_all _ (fun x => (hp c u hc x).symm)
    · exact (measurable_boltzmann hφ (c * u) N).aestronglyMeasurable
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (Real.holderConjugate_one_div ha hb hab)
    (ae_of_all μ (boltzmann_nonneg φ (a * β)))
    (ae_of_all μ (boltzmann_nonneg φ (b * γ)))
    (hLp a β ha hβ) (hLp b γ hb hγ)
  simp only [one_div_one_div] at hHolder
  convert hHolder using 1
  · exact integral_congr_ae (ae_of_all μ (boltzmann_add φ (a * β) (b * γ)))
  · congr 2
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (a * β) x)]
        using (hp a β ha x).symm
    · apply integral_congr_ae
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_of_nonneg (boltzmann_nonneg φ (b * γ) x)]
        using (hp b γ hb x).symm

theorem integral_boltzmann_pos {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) :
    0 < ∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (boltzmann_nonneg φ β)) (integrableOn_boltzmann hφ hβ hstable L N)]
  apply lt_of_lt_of_le ((isOpen_openConfigurations L N).measure_pos volume
    (openConfigurations_nonempty hL N))
  apply measure_mono
  intro x hx
  exact ⟨(boltzmann_pos_of_injective φ β hx.2).ne',
    fun i k => ⟨(hx.1 i k).1.le, (hx.1 i k).2.le⟩⟩

theorem convexOn_log_integral_boltzmann {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log
      (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x)) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
  intro β hβ γ hγ a b ha hb hab
  simp only [smul_eq_mul]
  have hβ' := integral_boltzmann_pos hφ hβ.le hL hstable N
  have hγ' := integral_boltzmann_pos hφ hγ.le hL hstable N
  have hac : 0 < a * β + b * γ := add_pos (mul_pos ha hβ) (mul_pos hb hγ)
  have hc := integral_boltzmann_pos hφ hac.le hL hstable N
  have hHolder := integral_boltzmann_logconvex hφ hstable L N hβ hγ ha hb hab
  calc
    _ ≤ Real.log ((∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) ^ a *
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ γ x) ^ b) :=
      Real.log_le_log hc hHolder
    _ = _ := by rw [Real.log_mul (Real.rpow_pos_of_pos hβ' a).ne' (Real.rpow_pos_of_pos hγ' b).ne',
      Real.log_rpow hβ', Real.log_rpow hγ']

theorem convexOn_log_partition {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {B L : ℝ} (hL : 0 < L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (N : ℕ) : ConvexOn ℝ (Ioi 0) (fun β => Real.log (partition φ β L N)) := by
  by_cases hN : N = 0
  · simp only [hN, partition, ↓reduceIte, Real.log_one]
    exact convexOn_const _ (convex_Ioi _)
  · have hlog (β : ℝ) (hβ : 0 < β) : Real.log (partition φ β L N) =
        Real.log (1 / (N.factorial : ℝ)) + Real.log
          (∫ x in {x : Fin N → Space | ∀ i, x i ∈ cube L}, boltzmann φ β x) := by
      unfold partition
      rw [ite_eq_right hN, Real.log_mul (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)))
        (integral_boltzmann_pos hφ hβ.le hL hstable N).ne']
    have hc := convexOn_log_integral_boltzmann hφ hL hstable N
    refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, ?_⟩
    intro β hβ γ hγ a b ha hb hab
    simp only [smul_eq_mul]
    rw [hlog _ (add_pos (mul_pos ha hβ) (mul_pos hb hγ)), hlog β hβ, hlog γ hγ]
    have hi := hc.2 hβ hγ ha.le hb.le hab
    simp only [smul_eq_mul] at hi
    have hcst : a * Real.log (1 / (N.factorial : ℝ)) +
        b * Real.log (1 / (N.factorial : ℝ)) = Real.log (1 / (N.factorial : ℝ)) := by
      rw [← add_mul, hab, one_mul]
    nlinarith only [hi, hcst]

theorem volume_cube (L : ℝ) : volume (cube L) = (ENNReal.ofReal L) ^ 3 := by
  have heq : cube L = (@WithLp.ofLp 2 (Fin 3 → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun _ : Fin 3 => Icc (-L / 2) (L / 2))) := by
    ext x
    simp only [cube, mem_preimage, mem_ofPred_eq, Set.mem_pi, mem_univ, forall_const]
  rw [heq, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet)]
  change (Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))) _ = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Icc]
  have ha : L / 2 - -L / 2 = L := by ring
  simp [ha]

theorem volume_configurations (L : ℝ) (N : ℕ) :
    volume {x : Fin N → Space | ∀ i, x i ∈ cube L} = (ENNReal.ofReal L) ^ (3 * N) := by
  have heq : {x : Fin N → Space | ∀ i, x i ∈ cube L} =
      Set.pi Set.univ (fun _ : Fin N => cube L) := by ext x; simp
  rw [heq]
  change (Measure.pi (fun _ : Fin N => (volume : Measure Space))) _ = _
  rw [Measure.pi_pi]
  simp only [volume_cube, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

theorem partition_nonneg (φ : ℝ → ℝ) (β L : ℝ) (N : ℕ) :
    0 ≤ partition φ β L N := by
  unfold partition
  split_ifs
  · norm_num
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (boltzmann_nonneg φ β)

theorem partition_le_exp_of_stable {φ : ℝ → ℝ}
    (hφ : Measurable (radialPotential φ)) {β B L : ℝ} (hβ : 0 ≤ β) (hL : 0 ≤ L)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B * (N : ℝ) : ℝ) : EReal) ≤ energy φ x) (N : ℕ) :
    partition φ β L N ≤ (L ^ 3 * Real.exp (β * B)) ^ N / (N.factorial : ℝ) := by
  by_cases hN : N = 0
  · simp [hN, partition]
  · have : IsFiniteMeasure (volume.restrict {x : Fin N → Space | ∀ i, x i ∈ cube L}) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        (isCompact_configurations L N).measure_lt_top (μ := volume)⟩
    have hi := integral_mono_ae (integrableOn_boltzmann hφ hβ hstable L N)
      (integrable_const (Real.exp (β * B * N)))
      (ae_of_all _ (boltzmann_le_of_stable hβ hstable (N := N)))
    rw [integral_const] at hi
    simp only [Measure.real, Measure.restrict_apply_univ, volume_configurations,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hL, smul_eq_mul] at hi
    unfold partition
    rw [ite_eq_right hN]
    have hfac : 0 ≤ (1 / (N.factorial : ℝ)) := by positivity
    apply (mul_le_mul_of_nonneg_left hi hfac).trans_eq
    rw [show β * B * (N : ℝ) = (N : ℝ) * (β * B) by ring, Real.exp_nat_mul,
      mul_pow, pow_mul]
    ring

end ContinuumTemperature
end

end OAI
