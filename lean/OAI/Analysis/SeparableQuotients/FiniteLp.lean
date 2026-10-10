import OAI.Analysis.SeparableQuotients.NormingOperations

namespace OAI

noncomputable section

namespace SeparableQuotient.LpFinite
universe u
open scoped ENNReal NNReal Classical
variable {Γ : Type u}

/-- A rational array, as an ℓᵖ vector. -/
def array (p : ℝ≥0∞) (f : Γ →₀ ℚ) : lp (fun _ : Γ => ℝ) p :=
  ⟨fun a => (f a : ℝ), by
    apply Memℓp.of_exponent_ge (q := 0) ?_ (zero_le : (0 : ℝ≥0∞) ≤ p)
    apply memℓp_zero_iff.mpr
    exact f.support.finite_toSet.subset (fun a ha => by simpa using ha)⟩

@[simp] lemma array_apply (p : ℝ≥0∞) (f : Γ →₀ ℚ) (a : Γ) : array p f a = (f a : ℝ) := rfl

@[simp] lemma array_zero (p : ℝ≥0∞) : array p (0 : Γ →₀ ℚ) = 0 := by
  apply lp.ext
  funext a
  simp

@[simp] lemma array_add (p : ℝ≥0∞) (f g : Γ →₀ ℚ) : array p (f+g) = array p f + array p g := by
  apply lp.ext
  funext a
  simp

@[simp] lemma array_smul (p : ℝ≥0∞) (c : ℚ) (f : Γ →₀ ℚ) :
    array p (c • f) = (c : ℝ) • array p f := by
  apply lp.ext
  funext a
  simp

@[simp] lemma array_sum {ι : Type*} (p : ℝ≥0∞) (s : Finset ι) (f : ι → Γ →₀ ℚ) :
    array p (∑ i ∈ s, f i) = ∑ i ∈ s, array p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, array_add, ih]

lemma norm_array_filter_le (p : ℝ≥0∞) (hp : p ≠ 0) (f : Γ →₀ ℚ) (A : Set Γ) :
    ‖array p (f.filter (· ∈ A))‖ ≤ ‖array p f‖ := by
  apply lp.norm_mono hp
  intro a
  by_cases ha : a ∈ A <;> simp [ha]

lemma norm_array_single {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (a : Γ) (c : ℚ) :
    ‖array p (Finsupp.single a c)‖ = |(c : ℝ)| := by
  have h : array p (Finsupp.single a c) = lp.single p a (c : ℝ) := by
    apply lp.ext
    funext b
    by_cases hba : b = a <;> simp [hba, lp.single_apply]
  rw [h]
  exact (lp.norm_single (E := fun _ : Γ => ℝ) (pos_iff_ne_zero.mpr hp) a (c : ℝ)).trans
    (Real.norm_eq_abs _)

end SeparableQuotient.LpFinite

namespace SeparableQuotient.LpFinite
open scoped ENNReal NNReal Classical
universe u v
variable {Γ : Type u} {ι : Type v} {p : ℝ≥0∞}

/-- Exact disjoint-support identity, including arbitrary finite index sets. -/
lemma norm_sum_rpow (hp : 0 < p.toReal) (s : Finset ι)
    (v : ι → lp (fun _ : Γ => ℝ) p)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, v i a = 0 ∨ v j a = 0) :
    ‖∑ i ∈ s, v i‖ ^ p.toReal = ∑ i ∈ s, ‖v i‖ ^ p.toReal := by
  have hpoint : ∀ a, ‖∑ i ∈ s, v i a‖ ^ p.toReal = ∑ i ∈ s, ‖v i a‖ ^ p.toReal := by
    intro a
    by_cases hex : ∃ i ∈ s, v i a ≠ 0
    · obtain ⟨i, hi, hv⟩ := hex
      have hz : ∀ j ∈ s, j ≠ i → v j a = 0 := by
        intro j hj hji
        exact (hdis j hj i hi hji a).resolve_right hv
      rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji) (fun hn => (hn hi).elim)]
      rw [Finset.sum_eq_single i (fun j hj hji => by rw [hz j hj hji]; simp [hp.ne'])
        (fun hn => (hn hi).elim)]
    · push Not at hex
      simp only [Finset.sum_eq_zero (fun i hi => hex i hi), norm_zero,
        Real.zero_rpow hp.ne']
      symm
      exact Finset.sum_eq_zero fun i hi => by rw [hex i hi]; simp [hp.ne']
  rw [lp.norm_rpow_eq_tsum hp]
  simp only [lp.coeFn_sum, Finset.sum_apply, hpoint]
  rw [Summable.tsum_finsetSum (fun i _ => (lp.memℓp (v i)).summable hp)]
  simp only [lp.norm_rpow_eq_tsum hp]

lemma norm_sum_le_card_rpow [Fact (1 ≤ p)] (hp : 0 < p.toReal) (s : Finset ι)
    (v : ι → lp (fun _ : Γ => ℝ) p)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, v i a = 0 ∨ v j a = 0)
    (hbound : ∀ i ∈ s, ‖v i‖ ≤ 1) :
    ‖∑ i ∈ s, v i‖ ≤ (s.card : ℝ) ^ (1 / p.toReal) := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hp).mp
  rw [norm_sum_rpow hp s v hdis, ← Real.rpow_mul (Nat.cast_nonneg _),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  calc
    _ ≤ ∑ i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i hi => by
      simpa using Real.rpow_le_rpow (norm_nonneg (v i)) (hbound i hi) hp.le
    _ = _ := by simp

end SeparableQuotient.LpFinite

namespace SeparableQuotient.Norming
open scoped ENNReal NNReal Classical
open LpFinite

def Family.r (f : Family) : ℝ := Parameters.r f.s
lemma Family.r_gt_one (f : Family) : 1 < f.r :=
  (Parameters.q_bounds f.s_ge_two).1.trans (Parameters.q_bounds f.s_ge_two).2.1
lemma Family.r_pos (f : Family) : 0 < f.r := zero_lt_one.trans f.r_gt_one

def Family.exponent (f : Family) : ℝ≥0∞ := ENNReal.ofReal f.r
instance Family.exponent_fact (f : Family) : Fact (1 ≤ f.exponent) :=
  ⟨by simpa [Family.exponent] using ENNReal.ofReal_le_ofReal f.r_gt_one.le⟩
@[simp] lemma Family.exponent_toReal (f : Family) : f.exponent.toReal = f.r :=
  ENNReal.toReal_ofReal f.r_pos.le
lemma Family.exponent_ne_zero (f : Family) : f.exponent ≠ 0 := by
  exact ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ f.exponent))

def Family.theta (f : Family) (j : ℕ) : ℝ := Parameters.theta f.s (j-1)
lemma Family.theta_nonneg (f : Family) (j : ℕ) : 0 ≤ f.theta j := by
  rw [Family.theta, Parameters.theta_eq f.s_ge_two]; positivity
lemma Family.theta_formula (f : Family) (j : ℕ) :
    f.theta j = (f.L j : ℝ)^(1/f.r) / (f.m j : ℝ) := rfl

lemma TypeI.lp_bound {f : Family} (e : TypeI f)
    (h : ∀ i, ‖array f.exponent (e.child i)‖ ≤ 1) :
    ‖array f.exponent e.value‖ ≤ f.theta e.weight := by
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin e.length)), ∀ j ∈ Finset.univ,
      i ≠ j → ∀ a, array f.exponent (e.child i) a = 0 ∨
        array f.exponent (e.child j) a = 0 := by
    intro i _ j _ hij a
    by_cases hi : e.child i a = 0
    · exact Or.inl (by simp [hi])
    · right
      have hz : e.child j a = 0 := by
        by_contra hj
        exact hij (successive_coefficient_unique e.child e.successive hi hj)
      simp [hz]
  have hsum : ‖∑ i, array f.exponent (e.child i)‖ ≤ (e.length : ℝ)^(1/f.r) := by
    simpa using norm_sum_le_card_rpow (by simpa using f.r_pos) Finset.univ
      (fun i => array f.exponent (e.child i)) hd (fun i _ => h i)
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos _
  rw [TypeI.value, array_smul, array_sum, norm_smul, Family.theta_formula]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hm)]
  calc
    (1/(f.m e.weight:ℝ)) * ‖∑ i, array f.exponent (e.child i)‖
      ≤ (1/(f.m e.weight:ℝ)) * (e.length:ℝ)^(1/f.r) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (1/(f.m e.weight:ℝ)) * (f.L e.weight:ℝ)^(1/f.r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le)
        (one_div_nonneg.mpr f.r_pos.le)
    _ = _ := by ring

lemma FinitePath.crop_lp_bound {f : Family} (P : FinitePath f) (A : Crop)
    (h : ∀ i j, ‖array f.exponent ((P.piece i).child j)‖ ≤ 1) :
    ‖array f.exponent (restrict (A.set f) P.value)‖ ≤ ∑ j ∈ P.active A, f.theta j := by
  let s : Finset (Fin P.length) := Finset.univ.filter
    (fun i => restrict (A.set f) (P.raw.piece i) ≠ 0)
  have heq : restrict (A.set f) P.value = ∑ i ∈ s, restrict (A.set f) (P.raw.piece i) := by
    rw [FinitePath.value, restrict, Finsupp.filter_sum]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa [s] using hi
  rw [heq, array_sum]
  calc
    ‖∑ i ∈ s, array f.exponent (restrict (A.set f) (P.raw.piece i))‖
      ≤ ∑ i ∈ s, ‖array f.exponent (restrict (A.set f) (P.raw.piece i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, f.theta (P.raw.weight i) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖array f.exponent (P.raw.piece i)‖ :=
          norm_array_filter_le f.exponent f.exponent_ne_zero _ _
        _ ≤ f.theta (P.raw.weight i) := by
          rw [← P.value_eq, ← P.weight_eq]
          exact (P.piece i).lp_bound (h i)
    _ = _ := by
      change _ = ∑ j ∈ s.image (fun i : Fin P.length => P.raw.weight i), f.theta j
      rw [Finset.sum_image]
      exact fun _ _ _ _ hij => P.valid.weight_strict.injective hij

lemma TypeII.lp_bound {f : Family} (e : TypeII f)
    (h : ∀ b i j, ‖array f.exponent (((e.path b).piece i).child j)‖ ≤ 1) :
    ‖array f.exponent e.value‖ < 1/8 := by
  let s := Finset.univ.biUnion (fun b => (e.path b).active (e.crop b))
  have hpos : ∀ j ∈ s, 1 ≤ j := by
    intro j hj
    obtain ⟨b, _, hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact (e.path b).valid.weight_pos _ i.isLt
  have hinj : Set.InjOn (fun j : ℕ => j-1) s := by
    intro j hj k hk heq
    have := hpos j hj
    have := hpos k hk
    change j-1 = k-1 at heq
    omega
  rw [TypeII.value, array_sum]
  calc
    ‖∑ b, array f.exponent (e.coefficient b • restrict ((e.crop b).set f) (e.path b).value)‖
      ≤ ∑ b, ‖array f.exponent (e.coefficient b • restrict ((e.crop b).set f) (e.path b).value)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b, ∑ j ∈ (e.path b).active (e.crop b), f.theta j := by
      apply Finset.sum_le_sum
      intro b _
      rw [array_smul, norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ 1 * ‖array f.exponent (restrict ((e.crop b).set f) (e.path b).value)‖ :=
          mul_le_mul_of_nonneg_right (e.coefficient_le_one b) (norm_nonneg _)
        _ ≤ _ := by simpa using (e.path b).crop_lp_bound (e.crop b) (h b)
    _ = ∑ j ∈ s, f.theta j := by
      symm
      apply Finset.sum_biUnion
      intro b _ c _ hbc
      exact e.disjoint_active hbc
    _ = ∑ n ∈ s.image (fun j => j-1), Parameters.theta f.s n := by
      rw [Finset.sum_image]
      · rfl
      · exact fun _ hj _ hk heq => hinj hj hk heq
    _ ≤ ∑' n, Parameters.theta f.s n :=
      (Parameters.hasSum_theta f.s_ge_two).summable.sum_le_tsum _
        (fun n _ => by rw [Parameters.theta_eq f.s_ge_two]; positivity)
    _ < 1/8 := Parameters.theta_sum_small f.s_ge_two

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped ENNReal NNReal Classical
open LpFinite

lemma Family.theta_le_one (f : Family) (j : ℕ) : f.theta j ≤ 1 := by
  rw [Family.theta, Parameters.theta_eq f.s_ge_two]
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma stage_lp_bound {base : Set Array} (f : Family)
    (hbase : ∀ x ∈ base, ‖array f.exponent x‖ ≤ 1) :
    ∀ n x, x ∈ stage base f n → ‖array f.exponent x‖ ≤ 1 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx
    · exact (e.lp_bound (fun i => ih _ (he i))).trans (f.theta_le_one _)
    · exact (e.lp_bound (fun b i j => ih _ (he b i j))).le.trans (by norm_num)

/-- The pure coefficient ℓr estimate. -/
lemma pure_lp_bound (k : ℕ) (x : Array) (hx : x ∈ Pure k) :
    ‖array (Family.pure k).exponent x‖ ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_lp_bound (.pure k) ?_ n x hn
  intro y hy
  rcases hy with rfl | ⟨a, _, rfl | rfl⟩
  · simp
  · rw [norm_array_single (Family.exponent_ne_zero _)]; norm_num
  · rw [norm_array_single (Family.exponent_ne_zero _)]; norm_num

end SeparableQuotient.Norming

end

end OAI
