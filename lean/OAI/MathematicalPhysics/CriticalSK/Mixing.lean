import OAI.MathematicalPhysics.CriticalSK.Equilibrium

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter

section KernelContraction

variable {ι : Type*} [Fintype ι]

lemma kernel_l1_contraction {K : Matrix ι ι ℝ} {μ p : ι → ℝ} {c : ℝ}
    (hmass : ∑ x, p x = ∑ x, μ x)
    (hminor : ∀ x y, c ≤ K x y) (hrow : ∀ x, ∑ y, K x y = 1)
    (hstat : ∀ y, ∑ x, μ x*K x y = μ y) :
    (∑ y, |(∑ x, p x*K x y)-μ y|) ≤
      (1-Fintype.card ι*c)*(∑ x, |p x-μ x|) := by
  have hid (y : ι) : (∑ x, p x*K x y)-μ y = ∑ x, (p x-μ x)*(K x y-c) := by
    simp only [sub_mul,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hstat,hmass]
    ring
  simp_rw [hid]
  calc
    _ ≤ ∑ y, ∑ x, |(p x-μ x)*(K x y-c)| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ x, |p x-μ x| *(1-Fintype.card ι*c) := by
      simp_rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr (hminor _ _))]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.mul_sum,Finset.sum_sub_distrib,hrow]
      simp
    _ = _ := by rw [← Finset.sum_mul,mul_comm]

lemma kernel_row_l1_le_two {K : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hμ : ∀ y, 0 ≤ μ y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hmass : ∑ y, μ y = 1) (x : ι) :
    ∑ y, |K x y-μ y| ≤ 2 := by
  calc
    _ ≤ ∑ y, (K x y+μ y) := Finset.sum_le_sum (fun y _ => by
      simpa only [abs_of_nonneg (hK x y),abs_of_nonneg (hμ y)] using abs_sub (K x y) (μ y))
    _ = 2 := by rw [Finset.sum_add_distrib,hrow,hmass]; norm_num

variable [DecidableEq ι]

lemma strictly_positive_kernel_mixes [Nonempty ι] {K : Matrix ι ι ℝ} {μ : ι → ℝ}
    (hK : ∀ x y, 0 < K x y) (hμ : ∀ y, 0 ≤ μ y)
    (hrow : ∀ x, ∑ y, K x y = 1) (hmass : ∑ y, μ y = 1)
    (hstat : ∀ y, ∑ x, μ x*K x y = μ y) :
    ∃ k : ℕ, ∀ x, (1/2:ℝ)*(∑ y, |(K^k) x y-μ y|) ≤ 1/4 := by
  classical
  let T : Finset ℝ := Finset.univ.image (fun p : ι×ι => K p.1 p.2)
  have hT : T.Nonempty := Finset.Nonempty.image Finset.univ_nonempty _
  let c := T.min' hT/2
  have hc : 0 < c := by
    dsimp [c]
    apply half_pos
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp (Finset.min'_mem T hT)
    rw [← hp]
    exact hK _ _
  have hminor : ∀ x y, c ≤ K x y := by
    intro x y
    have hh := Finset.min'_le T (K x y) (Finset.mem_image.mpr ⟨(x,y),Finset.mem_univ _,rfl⟩)
    have hm : 0 < T.min' hT := by change 0 < T.min' hT/2 at hc; linarith
    dsimp [c]
    linarith
  have hcard : (0:ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hq0 : 0 ≤ 1-Fintype.card ι*c := by
    have hh := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hminor (Classical.arbitrary ι) y)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hrow] using sub_nonneg.mpr hh
  have hq1 : 1-Fintype.card ι*c < 1 := by nlinarith
  have hbound : ∀ k : ℕ, ∀ x, ∑ y, |(K^k) x y-μ y| ≤ 2*(1-Fintype.card ι*c)^k := by
    intro k
    induction k with
    | zero =>
      intro x
      simpa using kernel_row_l1_le_two (K := K^0) (kernel_pow_nonneg (fun x y => (hK x y).le) 0)
        hμ (kernel_pow_sum hrow 0) hmass x
    | succ k ih =>
      intro x
      simp only [pow_succ,Matrix.mul_apply]
      have hh := kernel_l1_contraction (p := fun y => (K^k) x y)
        ((kernel_pow_sum hrow k x).trans hmass.symm) hminor hrow hstat
      calc
        _ ≤ (1-Fintype.card ι*c)*(∑ y, |(K^k) x y-μ y|) := hh
        _ ≤ (1-Fintype.card ι*c)*(2*(1-Fintype.card ι*c)^k) := mul_le_mul_of_nonneg_left (ih x) hq0
        _ = _ := by ring
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).eventually
    (gt_mem_nhds (show (0:ℝ) < 1/4 by norm_num))
  obtain ⟨k,hk⟩ := hh.exists
  refine ⟨k,?_⟩
  intro x
  have hb := hbound k x
  linarith

end KernelContraction

variable {n : ℕ} (W : Disorder n)

lemma discreteKernel_pos_of_sameExcept (hn : 0 < n) {i : Fin n} {x y : Spin n}
    (hxy : sameExcept i x y) : 0 < discreteKernel W x y := by
  have hi : 0 < siteKernel W i x y := by
    change 0 < if sameExcept i x y then gibbs W y/fiberMass W i x else 0
    rw [ite_eq_left hxy]
    exact div_pos (gibbs_pos W y) (fiberMass_pos W i x)
  have hs : 0 < ∑ j : Fin n, siteKernel W j x y :=
    lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => siteKernel_nonneg W j x y) (Finset.mem_univ i))
  change 0 < (n:ℝ)⁻¹*(∑ j : Fin n, siteKernel W j) x y
  simpa only [Matrix.sum_apply] using mul_pos (inv_pos.mpr (Nat.cast_pos.mpr hn)) hs

lemma discreteKernel_power_pos (hn : 0 < n) (x y : Spin n) : 0 < (discreteKernel W^n) x y := by
  classical
  let z (k : ℕ) : Spin n := fun i => if i.val < k then y i else x i
  have hh : ∀ k, k ≤ n → 0 < (discreteKernel W^k) x (z k) := by
    intro k
    induction k with
    | zero => intro _; simp [z]
    | succ k ih =>
      intro hk
      have hik : k < n := by omega
      have hstep : sameExcept ⟨k,hik⟩ (z k) (z (k+1)) := by
        intro j hj
        have hjk : j.val ≠ k := by intro he; apply hj; exact Fin.ext he
        dsimp [z]
        split_ifs <;> simp_all <;> omega
      rw [pow_succ,Matrix.mul_apply]
      exact lt_of_lt_of_le (mul_pos (ih (by omega)) (discreteKernel_pos_of_sameExcept W hn hstep))
        (Finset.single_le_sum (fun t _ => mul_nonneg
          (kernel_pow_nonneg (discreteKernel_nonneg W) k x t) (discreteKernel_nonneg W t (z (k+1))))
          (Finset.mem_univ (z k)))
  have hz : z n = y := by funext i; simp [z,i.isLt]
  simpa only [hz] using hh n le_rfl

lemma discrete_mixing_set_nonempty (hn : 0 < n) :
    {k : ℕ | ∀ x, discreteDistance W k x ≤ 1/4}.Nonempty := by
  obtain ⟨k,hk⟩ := strictly_positive_kernel_mixes (discreteKernel_power_pos W hn)
    (gibbs_nonneg W) (kernel_pow_sum (discreteKernel_sum W hn) n) (gibbs_sum W)
    (kernel_pow_stationary (discreteKernel_stationary W hn) n)
  refine ⟨n*k,?_⟩
  intro x
  simpa only [discreteDistance,totalVariation,pow_mul] using hk x

lemma continuousKernel_add (s t : ℝ) : continuousKernel W (s+t) = continuousKernel W s*continuousKernel W t := by
  unfold continuousKernel
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (generator W)).smul_left s).smul_right t)

lemma continuousKernel_nat (k : ℕ) : continuousKernel W k = continuousKernel W 1^k := by
  induction k with
  | zero => simp [continuousKernel]
  | succ k ih => rw [Nat.cast_add,Nat.cast_one,continuousKernel_add,ih,pow_succ]

lemma continuousKernel_one_pos (hn : 0 < n) (x y : Spin n) : 0 < continuousKernel W 1 x y := by
  rw [continuousKernel_poisson W hn]
  have hs := matrix_poisson_hasSum (discreteKernel W) ((n:ℝ)*1) x y
  have hle := sum_le_hasSum ({n} : Finset ℕ) (fun k _ => mul_nonneg (poisson_coeff_nonneg _ (by positivity) k)
    (kernel_pow_nonneg (discreteKernel_nonneg W) k x y)) hs
  simp only [Finset.sum_singleton] at hle
  have hp : 0 < (Real.exp (-((n:ℝ)*1))*((n:ℝ)*1)^n/n.factorial)*(discreteKernel W^n) x y := by
    exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (pow_pos (by positivity) n))
      (Nat.cast_pos.mpr (Nat.factorial_pos n))) (discreteKernel_power_pos W hn x y)
  exact hp.trans_le hle

lemma continuous_mixing_set_nonempty (hn : 0 < n) :
    {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ 1/4}.Nonempty := by
  obtain ⟨k,hk⟩ := strictly_positive_kernel_mixes (continuousKernel_one_pos W hn)
    (gibbs_nonneg W) (continuousKernel_sum W hn 1) (gibbs_sum W)
    (continuousKernel_stationary W hn 1)
  refine ⟨k,Nat.cast_nonneg k,?_⟩
  intro x
  simpa only [continuousDistance,totalVariation,continuousKernel_nat] using hk x

end

open Set Filter MeasureTheory

section MixingLower

variable {n : ℕ} (W : Disorder n)

lemma continuousDistance_antitone (hn : 0 < n) {s t : ℝ} (_hs : 0 ≤ s) (hst : s ≤ t) (x : Spin n) :
    continuousDistance W t x ≤ continuousDistance W s x := by
  have hh := kernel_l1_contraction (p := continuousKernel W s x) (c := 0)
    ((continuousKernel_sum W hn s x).trans (gibbs_sum W).symm)
    (continuousKernel_nonneg W hn (t-s) (sub_nonneg.mpr hst))
    (continuousKernel_sum W hn (t-s)) (continuousKernel_stationary W hn (t-s))
  have he : continuousKernel W t = continuousKernel W s * continuousKernel W (t-s) := by
    rw [← continuousKernel_add]; congr 1; ring
  simp only [mul_zero,sub_zero,one_mul] at hh
  unfold continuousDistance totalVariation
  rw [he]
  simp only [Matrix.mul_apply]
  linarith

lemma discreteDistance_antitone (hn : 0 < n) {k l : ℕ} (hkl : k ≤ l) (x : Spin n) :
    discreteDistance W l x ≤ discreteDistance W k x := by
  have hh := kernel_l1_contraction (p := (discreteKernel W^k) x) (c := 0)
    ((kernel_pow_sum (discreteKernel_sum W hn) k x).trans (gibbs_sum W).symm)
    (kernel_pow_nonneg (discreteKernel_nonneg W) (l-k))
    (kernel_pow_sum (discreteKernel_sum W hn) (l-k))
    (kernel_pow_stationary (discreteKernel_stationary W hn) (l-k))
  have he : discreteKernel W^l = discreteKernel W^k*discreteKernel W^(l-k) := by
    rw [← pow_add,Nat.add_sub_of_le hkl]
  simp only [mul_zero,sub_zero,one_mul] at hh
  unfold discreteDistance totalVariation
  rw [he]
  simp only [Matrix.mul_apply]
  linarith

lemma continuousMixingTime_lower (hn : 0 < n) {t : ℝ} (h : 0 < continuousGoodMass W t) :
    t ≤ continuousMixingTime W := by
  apply le_csInf (continuous_mixing_set_nonempty W hn)
  intro s hs
  by_contra hst
  have hzero : continuousGoodMass W t = 0 := by
    unfold continuousGoodMass
    apply Finset.sum_eq_zero
    intro x _
    have hx := (continuousDistance_antitone W hn hs.1 (le_of_not_ge hst) x).trans (hs.2 x)
    rw [ite_eq_right (not_lt.mpr hx)]
  linarith

lemma discreteMixingTime_lower (hn : 0 < n) {k : ℕ} (h : 0 < discreteGoodMass W k) :
    k ≤ discreteMixingTime W := by
  have hs := Nat.sInf_mem (discrete_mixing_set_nonempty W hn)
  by_contra hk
  have hzero : discreteGoodMass W k = 0 := by
    unfold discreteGoodMass
    apply Finset.sum_eq_zero
    intro x _
    have hx := (discreteDistance_antitone W hn (le_of_not_ge hk) x).trans (hs x)
    rw [ite_eq_right (not_lt.mpr hx)]
  linarith

end MixingLower

lemma event_probability_one_of_error_zero {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : ∀ n, Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (E B : ∀ n, Set (X n)) (hcover : ∀ᶠ n : ℕ in atTop, E n ∪ B n = univ)
    (hB : Tendsto (fun n => (μ n).real (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).real (E n)) atTop (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hcover,hB.eventually (gt_mem_nhds (show 0 < 1-a by linarith))] with n hn hnb
    have hh := measureReal_union_le (μ := μ n) (E n) (B n)
    rw [hn,probReal_univ] at hh
    linarith
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

lemma continuousMixingTime_lower_limit (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hscale : Tendsto (fun n => t n/(n:ℝ)^(2/3:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (disorderLaw n).real {W | t n ≤ continuousMixingTime W}) atTop (𝓝 1) := by
  apply event_probability_one_of_error_zero (μ := disorderLaw)
    (B := fun n => {W | (1:ℝ) ≤ |continuousGoodMass W (t n)-1|})
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply Set.eq_univ_of_forall
    intro W
    by_cases hW : 0 < continuousGoodMass W (t n)
    · exact Or.inl (continuousMixingTime_lower W hn hW)
    · exact Or.inr (by change (1:ℝ) ≤ |continuousGoodMass W (t n)-1|; rw [abs_of_nonpos (by linarith [continuousGoodMass_le_one W (t n)])]; linarith)
  · exact realized_continuous_initial_states t ht hscale 1 zero_lt_one

lemma discreteMixingTime_lower_limit (k : ℕ → ℕ)
    (hscale : Tendsto (fun n => (k n:ℝ)/(n:ℝ)^(5/3:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (disorderLaw n).real {W | k n ≤ discreteMixingTime W}) atTop (𝓝 1) := by
  apply event_probability_one_of_error_zero (μ := disorderLaw)
    (B := fun n => {W | (1:ℝ) ≤ |discreteGoodMass W (k n)-1|})
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply Set.eq_univ_of_forall
    intro W
    by_cases hW : 0 < discreteGoodMass W (k n)
    · exact Or.inl (discreteMixingTime_lower W hn hW)
    · exact Or.inr (by change (1:ℝ) ≤ |discreteGoodMass W (k n)-1|; rw [abs_of_nonpos (by linarith [discreteGoodMass_le_one W (k n)])]; linarith)
  · exact realized_discrete_initial_states k hscale 1 zero_lt_one

theorem critical_mixing_lower_bounds (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (disorderLaw n).real {W | (n:ℝ)^(2/3-ε) ≤ continuousMixingTime W}) atTop (𝓝 1) ∧
    Tendsto (fun n => (disorderLaw n).real {W | (n:ℝ)^(5/3-ε) ≤ (discreteMixingTime W:ℝ)}) atTop (𝓝 1) := by
  constructor
  · exact continuousMixingTime_lower_limit (fun n => (n:ℝ)^(2/3-ε)) (fun _ => by positivity) (rpow_ratio_tendsto_zero hε)
  · have hh := discreteMixingTime_lower_limit (fun n => ⌈(n:ℝ)^(5/3-ε)⌉₊)
      (ceil_rpow_ratio_tendsto_zero (by norm_num : (0:ℝ) < 5/3) hε)
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [(tendsto_order.mp hh).1 a ha] with n hn
      refine lt_of_lt_of_le hn (measureReal_mono ?_)
      intro W hW
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hW)
    · intro a ha
      exact Filter.Eventually.of_forall (fun _ => lt_of_le_of_lt measureReal_le_one ha)

end CriticalSK

end

end OAI
