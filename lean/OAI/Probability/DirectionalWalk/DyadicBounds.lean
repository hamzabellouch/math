import OAI.Probability.DirectionalWalk.ContactBins

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def dyad (j : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(j+1))

lemma dyad_pos (j : ℕ) : 0 < dyad j := ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)
lemma dyad_ne_top (j : ℕ) : dyad j ≠ ∞ := ENNReal.ofReal_ne_top

lemma exists_dyad_bin {q : ℝ≥0∞} (hq : 0 < q) (h1 : q < 1) :
    ∃ j : ℕ, dyad j ≤ q ∧ q < 2*dyad j := by
  have hqf : q ≠ ∞ := ne_of_lt (h1.trans (by norm_num))
  have hqr : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt hq) hqf
  have hqr1 : q.toReal < 1 := by exact_mod_cast (ENNReal.toReal_lt_toReal hqf (by norm_num)).mpr h1
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)
  have hex : ∃ n : ℕ, (1/2 : ℝ)^n ≤ q.toReal := by
    obtain ⟨n,hn⟩ := (ht.eventually (eventually_lt_nhds hqr)).exists
    exact ⟨n,hn.le⟩
  let n := Nat.find hex
  have hn : (1/2 : ℝ)^n ≤ q.toReal := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    rw [he,pow_zero] at hn
    linarith
  refine ⟨n-1,?_,?_⟩
  · unfold dyad
    rw [Nat.sub_add_cancel hn0]
    exact (ENNReal.ofReal_le_iff_le_toReal hqf).mpr hn
  · have hp : q.toReal < (1/2 : ℝ)^(n-1) := lt_of_not_ge (Nat.find_min hex (by omega))
    have he : (2 : ℝ) * (1/2 : ℝ)^n = (1/2 : ℝ)^(n-1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn0,pow_succ]
      ring
    rw [dyad,Nat.sub_add_cancel hn0,← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by norm_num),he]
    exact (ENNReal.lt_ofReal_iff_toReal_lt hqf).mpr hp

lemma return_bins_cover {d : ℕ} (e : Step d) (k N : ℤ) (ω : Environment d)
    (hω : ∀ x f, 0 < (ω x).val f) (y : Site d)
    (hy : k ≤ axisHeight e y ∧ axisHeight e y < N) :
    ∃ j, y ∈ returnBin e k N (dyad j) ω := by
  obtain ⟨j,hj,hj'⟩ := exists_dyad_bin (quenchedReturn_pos_lt_one e k N ω hω y hy).1
    (quenchedReturn_pos_lt_one e k N ω hω y hy).2
  exact ⟨j,⟨hy.1,hy.2,hj⟩,hj'⟩

lemma tsum_subtype_cover {α : Type*} [Countable α] (A : Set α) (B : ℕ → Set α)
    (h : A ⊆ ⋃ n, B n) (f : α → ℝ≥0∞) :
    (∑' a : A, f a) ≤ ∑' n, ∑' a : B n, f a := by
  classical
  have hex (a : A) : ∃ n, a.val ∈ B n := Set.mem_iUnion.mp (h a.property)
  let g : A → (Σ n, B n) := fun a => ⟨(hex a).choose,⟨a.val,(hex a).choose_spec⟩⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hv : ((g a).2 : α) = ((g b).2 : α) := congrArg (fun i : Σ n, B n => i.2.val) hab
    exact Subtype.ext hv
  calc
    _ ≤ ∑' i : Σ n, B n, f i.2 := Summable.tsum_le_tsum_of_inj g hg (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable ENNReal.summable
    _ = _ := ENNReal.tsum_sigma (fun n (a : B n) => f a)

lemma half_geometric_sum_le (s : Finset ℕ) : (∑ j ∈ s, (1/2 : ℝ)^(j+1)) ≤ 1 := by
  have hs : HasSum (fun j : ℕ => (1/2 : ℝ)^(j+1)) 1 := by
    have hh := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_right (1/2)
    norm_num [pow_succ] at hh ⊢
    exact hh
  exact (hs.summable.sum_le_tsum s (fun j _ => by positivity)).trans_eq hs.tsum_eq

lemma half_geometric_tail_sum_le (s : Finset ℕ) (m : ℕ) :
    (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)) ≤ (1/2 : ℝ)^m := by
  classical
  let t := (s.filter (m ≤ ·)).image (fun j => j-m)
  have he : (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)) =
      (1/2 : ℝ)^m * ∑ j ∈ t, (1/2 : ℝ)^(j+1) := by
    rw [Finset.mul_sum,Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [← pow_add]
      congr 1
      have := (Finset.mem_filter.mp hj).2
      omega
    · intro a ha b hb hab
      have := (Finset.mem_filter.mp ha).2
      have := (Finset.mem_filter.mp hb).2
      change a-m=b-m at hab
      omega
  rw [he]
  exact (mul_le_mul_of_nonneg_left (half_geometric_sum_le t) (by positivity)).trans_eq (mul_one _)

lemma dyadic_weighted_mass_sum {v : ℕ → ℝ} (_hv0 : ∀ j, 0 ≤ v j) (hv1 : ∀ j, v j ≤ 1)
    (m : ℕ) (hv : ∀ j, (1/2 : ℝ)^(j+1)*v j ≤ (1/2 : ℝ)^m) (s : Finset ℕ) :
    (∑ j ∈ s, (1/2 : ℝ)^(j+1)*v j) ≤ (m+1)*(1/2 : ℝ)^m := by
  classical
  have hsmall : (∑ j ∈ s.filter (· < m), (1/2 : ℝ)^(j+1)*v j) ≤ m*(1/2 : ℝ)^m := by
    calc
      _ ≤ ∑ _ ∈ s.filter (· < m), (1/2 : ℝ)^m := Finset.sum_le_sum (fun j _ => hv j)
      _ = ((s.filter (· < m)).card : ℝ)*(1/2 : ℝ)^m := by simp
      _ ≤ m*(1/2 : ℝ)^m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh : (s.filter (· < m)).card ≤ m := by
          simpa using (Finset.card_le_card (show s.filter (· < m) ⊆ Finset.range m by
            intro j hj;exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2))
        exact_mod_cast hh
  have hlarge : (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)*v j) ≤ (1/2 : ℝ)^m := by
    apply (Finset.sum_le_sum (s := s.filter (m ≤ ·)) (fun j _ =>
      mul_le_of_le_one_right (by positivity) (hv1 j))).trans
    exact half_geometric_tail_sum_le s m
  have he : (∑ j ∈ s.filter (· < m), (1/2 : ℝ)^(j+1)*v j) +
      (∑ j ∈ s.filter (m ≤ ·), (1/2 : ℝ)^(j+1)*v j) = ∑ j ∈ s, (1/2 : ℝ)^(j+1)*v j := by
    simpa only [not_lt] using Finset.sum_filter_add_sum_filter_not s (fun j => j < m)
      (fun j => (1/2 : ℝ)^(j+1)*v j)
  linarith

lemma dyadic_event_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (S : Ω → ℝ) (hS : Integrable S ν)
    (hS0 : ∀ ξ, 0 ≤ S ξ) (c : ℝ) (hc : 0 < c)
    (hExp : Integrable (fun ξ => Real.exp (c*S ξ)) ν)
    (hExp12 : (∫ ξ, Real.exp (c*S ξ) ∂ν) ≤ 12)
    (V : ℕ → Set Ω) (m : ℕ)
    (hV : ∀ j, dyad j * ν (V j) ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑' j, 2*dyad j * ∫⁻ ξ in V j, ENNReal.ofReal (S ξ) ∂ν) ≤
      ENNReal.ofReal ((24/c)*(m+1)^2*(1/2 : ℝ)^m) := by
  classical
  let t := (1/2 : ℝ)^m
  have ht : 0 < t := pow_pos (by norm_num) _
  have ht1 : t ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hv (j : ℕ) : (1/2 : ℝ)^(j+1)*ν.real (V j) ≤ t := by
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) (hV j)
    simpa only [ENNReal.toReal_mul,dyad,ENNReal.toReal_ofReal (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) _),Measure.real,t] using hh
  have hlog : -Real.log t ≤ m := by
    dsimp [t]
    rw [Real.log_pow,Real.log_div (by norm_num) (by norm_num),Real.log_one]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg m)]
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have hI (j : ℕ) : c*(∫ ξ in V j, S ξ ∂ν) ≤ 12*t - ν.real (V j)*Real.log t := by
    have hp (ξ : Ω) : c*S ξ ≤ t*Real.exp (c*S ξ)-Real.log t := by
      have h := Real.add_one_le_exp (c*S ξ + Real.log t)
      rw [Real.exp_add,Real.exp_log ht] at h
      nlinarith
    have hi := integral_mono (hS.restrict (s := V j) |>.const_mul c)
      ((hExp.restrict.const_mul t).sub (integrable_const (Real.log t))) hp
    simp only [Pi.sub_apply] at hi
    rw [integral_const_mul,integral_sub (hExp.restrict (s := V j) |>.const_mul t) (integrable_const _),
      integral_const_mul,integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hi
    have he : (∫ ξ in V j, Real.exp (c*S ξ) ∂ν) ≤ 12 :=
      (setIntegral_le_integral hExp (Filter.Eventually.of_forall (fun ξ => Real.exp_nonneg _))).trans hExp12
    nlinarith [mul_le_mul_of_nonneg_left he ht.le]
  let B := ∑ j ∈ s, (1/2 : ℝ)^(j+1)*(∫ ξ in V j, S ξ ∂ν)
  have hB : c*B ≤ 12*t + m*((m+1)*t) := by
    have hsum := Finset.sum_le_sum (s := s) (fun j _ => mul_le_mul_of_nonneg_left (hI j)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (j+1)))
    have he1 : (∑ j ∈ s, (1/2 : ℝ)^(j+1)*(c*(∫ ξ in V j, S ξ ∂ν))) = c*B := by
      dsimp [B];rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro j _;ring
    have he2 : (∑ j ∈ s, (1/2 : ℝ)^(j+1)*(12*t-ν.real (V j)*Real.log t)) =
        12*t*(∑ j ∈ s, (1/2 : ℝ)^(j+1)) + (-Real.log t)*(∑ j ∈ s, (1/2 : ℝ)^(j+1)*ν.real (V j)) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl;intro j _;ring
    rw [he1,he2] at hsum
    have hmass := dyadic_weighted_mass_sum (fun j => measureReal_nonneg) (fun j => measureReal_le_one) m hv s
    have hh := mul_le_mul_of_nonneg_left (half_geometric_sum_le s) (show 0 ≤ 12*t by positivity)
    have hh' := mul_le_mul hlog hmass (Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) measureReal_nonneg)) (Nat.cast_nonneg m)
    dsimp [t] at *
    nlinarith
  have hbound : 2*B ≤ (24/c)*(m+1)^2*t := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hpoly : 12*t + m*((m+1)*t) ≤ 12*(m+1)^2*t := by
      nlinarith [sq_nonneg (m : ℝ)]
    have hcc : c*(2*B) ≤ c*((24/c)*(m+1)^2*t) := by
      field_simp
      nlinarith [hB.trans hpoly]
    exact (mul_le_mul_iff_right₀ hc).mp hcc
  have he (j : ℕ) : 2*dyad j * (∫⁻ ξ in V j, ENNReal.ofReal (S ξ) ∂ν) =
      ENNReal.ofReal (2*(1/2 : ℝ)^(j+1)*(∫ ξ in V j, S ξ ∂ν)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hS.restrict (Filter.Eventually.of_forall hS0),dyad]
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by norm_num)]
    norm_num
  simp_rw [he]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (by positivity)
    (integral_nonneg hS0))]
  apply ENNReal.ofReal_le_ofReal
  convert hbound using 1
  dsimp [B,t]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end DirectionalZeroOne

end OAI
