import OAI.Analysis.RecursivePotentials.Model

namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

lemma leastPair_tight (x a b : ℝ) :
    (leastPair x a b).1 = a ∨ (leastPair x a b).2 = b := by
  rcases le_total (x + b) a with h | h
  · exact Or.inl (max_eq_left h)
  · exact Or.inr (max_eq_left (by linarith))

lemma energy_nonneg {p q d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    0 ≤ energy p q d := by
  unfold energy
  positivity

lemma energy_symm (p q d : ℝ) : energy p q d = energy q p d := by
  unfold energy
  congr 1
  ring

lemma energy_factor {p q d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    energy p q d =
      (d * (2 * p + d)) ^ (2 / 3 : ℝ) * ((2 * q + d) ^ 2) ^ (1 / 3 : ℝ) := by
  have hq' : 0 ≤ 2 * q + d := by positivity
  rw [energy, Real.mul_rpow (by positivity) hq']
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq']
  norm_num

lemma holder_two_thirds {ι : Type uIndex} (s : Finset ι) (u v : ι → ℝ)
    (hu : ∀ i ∈ s, 0 ≤ u i) (hv : ∀ i ∈ s, 0 ≤ v i) :
    ∑ i ∈ s, (u i) ^ (2 / 3 : ℝ) * (v i) ^ (1 / 3 : ℝ) ≤
      (∑ i ∈ s, u i) ^ (2 / 3 : ℝ) * (∑ i ∈ s, v i) ^ (1 / 3 : ℝ) := by
  have hpq : Real.HolderConjugate (3 / 2 : ℝ) 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (fun i hi => Real.rpow_nonneg (hu i hi) (2 / 3))
    (fun i hi => Real.rpow_nonneg (hv i hi) (1 / 3))
  have hleft : (∑ i ∈ s, (u i ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ)) = ∑ i ∈ s, u i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hu i hi)]
    norm_num
  have hright : (∑ i ∈ s, (v i ^ (1 / 3 : ℝ)) ^ (3 : ℝ)) = ∑ i ∈ s, v i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (hv i hi)]
    norm_num
  rw [hleft, hright] at h
  norm_num at h ⊢
  exact h

lemma energy_step_first {ι : Type uIndex} (s : Finset ι) (p q d : ι → ℝ)
    {P Q D : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (hPtight : ∑ i ∈ s, p i ^ 2 = P ^ 2)
    (hQupper : ∑ i ∈ s, q i ^ 2 ≤ Q ^ 2)
    (hPupper' : ∑ i ∈ s, (p i + d i) ^ 2 ≤ (P + D) ^ 2)
    (hQupper' : ∑ i ∈ s, (q i + d i) ^ 2 ≤ (Q + D) ^ 2) :
    ∑ i ∈ s, energy (p i) (q i) (d i) ≤ energy P Q D := by
  have hu : ∀ i ∈ s, 0 ≤ d i * (2 * p i + d i) := by
    intro i hi
    exact mul_nonneg (hd i hi) (by linarith [hp i hi, hd i hi])
  have hU : ∑ i ∈ s, d i * (2 * p i + d i) ≤ D * (2 * P + D) := by
    have heq : ∑ i ∈ s, (p i + d i) ^ 2 =
        (∑ i ∈ s, p i ^ 2) + ∑ i ∈ s, d i * (2 * p i + d i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq, hPtight] at hPupper'
    nlinarith
  have hV : ∑ i ∈ s, (2 * q i + d i) ^ 2 ≤ (2 * Q + D) ^ 2 := by
    convert sum_add_sq_le s q (fun i => q i + d i) hQ (add_nonneg hQ hD)
      hQupper hQupper' using 1 <;> congr 1
    · ext i
      ring
    · ring
  calc
    ∑ i ∈ s, energy (p i) (q i) (d i) =
        ∑ i ∈ s, (d i * (2 * p i + d i)) ^ (2 / 3 : ℝ) *
          ((2 * q i + d i) ^ 2) ^ (1 / 3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact energy_factor (hp i hi) (hq i hi) (hd i hi)
    _ ≤ (∑ i ∈ s, d i * (2 * p i + d i)) ^ (2 / 3 : ℝ) *
        (∑ i ∈ s, (2 * q i + d i) ^ 2) ^ (1 / 3 : ℝ) :=
      holder_two_thirds s _ _ hu (fun i _ => sq_nonneg _)
    _ ≤ (D * (2 * P + D)) ^ (2 / 3 : ℝ) *
        ((2 * Q + D) ^ 2) ^ (1 / 3 : ℝ) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (Finset.sum_nonneg hu) hU (by norm_num)
      · exact Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hV (by norm_num)
      · positivity
      · positivity
    _ = energy P Q D := (energy_factor hP hQ hD).symm

lemma energy_step {ι : Type uIndex} (s : Finset ι) (p q d : ι → ℝ)
    {P Q D : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hD : 0 ≤ D)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (hPupper : ∑ i ∈ s, p i ^ 2 ≤ P ^ 2)
    (hQupper : ∑ i ∈ s, q i ^ 2 ≤ Q ^ 2)
    (hPupper' : ∑ i ∈ s, (p i + d i) ^ 2 ≤ (P + D) ^ 2)
    (hQupper' : ∑ i ∈ s, (q i + d i) ^ 2 ≤ (Q + D) ^ 2)
    (htight : (∑ i ∈ s, p i ^ 2 = P ^ 2) ∨ (∑ i ∈ s, q i ^ 2 = Q ^ 2)) :
    ∑ i ∈ s, energy (p i) (q i) (d i) ≤ energy P Q D := by
  rcases htight with h | h
  · exact energy_step_first s p q d hP hQ hD hp hq hd h hQupper hPupper' hQupper'
  · simpa only [energy_symm (p := P), energy_symm (p := p _)] using
      energy_step_first s q p d hQ hP hD hq hp hd h hPupper hQupper' hPupper'

lemma energy_zero_base {d : ℝ} (hd : 0 ≤ d) : energy 0 0 d = d ^ 2 := by
  unfold energy
  rw [show d * (2 * 0 + d) * (2 * 0 + d) = d ^ 3 by ring,
    ← Real.rpow_natCast d 3, ← Real.rpow_mul hd]
  norm_num

lemma sq_rpow_three_halves {a : ℝ} (ha : 0 ≤ a) :
    (a ^ 2) ^ (3 / 2 : ℝ) = a ^ 3 := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha]
  norm_num

lemma energy_rpow_three_halves {p q d : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d) :
    (energy p q d) ^ (3 / 2 : ℝ) = d * (2 * p + d) * (2 * q + d) := by
  unfold energy
  rw [← Real.rpow_mul (by positivity)]
  norm_num

lemma cube_le_of_sq_le_energy {r k p q d : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hd : 0 ≤ d)
    (h : r ^ 2 ≤ k ^ 2 * energy p q d) :
    r ^ 3 ≤ k ^ 3 * (d * (2 * p + d) * (2 * q + d)) := by
  have hh := Real.rpow_le_rpow (sq_nonneg r) h (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rwa [sq_rpow_three_halves hr,
    Real.mul_rpow (sq_nonneg k) (energy_nonneg hp hq hd),
    sq_rpow_three_halves hk, energy_rpow_three_halves hp hq hd] at hh

namespace FiniteRootedTree

section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

def leaves : Finset ι := Finset.univ.filter fun s => T.children s = ∅

lemma sum_children (e : ι → ℝ) :
    ∑ s, ∑ c ∈ T.children s, e c = ∑ c ∈ Finset.univ.erase T.root, e c := by
  classical
  simp only [children, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    (∑ c, ∑ s, if c ≠ T.root ∧ T.parent c = s then e c else 0) =
        ∑ c, if c = T.root then 0 else e c := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases h : c = T.root
      · simp [h]
      · simp [h]
    _ = ∑ c ∈ Finset.univ.erase T.root, e c := by
      have hset : Finset.univ.erase T.root =
          Finset.univ.filter (fun c => c ≠ T.root) := by
        ext c
        simp
      rw [hset, Finset.sum_filter]
      simp only [ite_not]

lemma sum_leaves_le_root (e : ι → ℝ)
    (he : ∀ s, ∑ c ∈ T.children s, e c ≤ e s) :
    ∑ b ∈ T.leaves, e b ≤ e T.root := by
  have h := Finset.sum_le_sum (s := Finset.univ) (f := fun s =>
      (∑ c ∈ T.children s, e c) + if T.children s = ∅ then e s else 0)
    (g := e) (fun s _ => by
      by_cases hl : T.children s = ∅
      · simp [hl]
      · simpa [hl] using he s)
  rw [Finset.sum_add_distrib, T.sum_children e] at h
  have hleaves : (∑ s, if T.children s = ∅ then e s else 0) =
      ∑ s ∈ T.leaves, e s := by simp [leaves, Finset.sum_filter]
  rw [hleaves, Finset.sum_erase_eq_sub (Finset.mem_univ T.root)] at h
  linarith

theorem two_field_energy_all_leaves (p q d : ι → ℝ)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) (hd : ∀ s, 0 ≤ d s)
    (hpU : T.Upper p) (hqU : T.Upper q)
    (hp'U : T.Upper (fun s => p s + d s))
    (hq'U : T.Upper (fun s => q s + d s))
    (htight : ∀ s, (T.children s).Nonempty →
      (∑ c ∈ T.children s, p c ^ 2 = p s ^ 2) ∨
      (∑ c ∈ T.children s, q c ^ 2 = q s ^ 2)) :
    ∑ b ∈ T.leaves, d b ^ 2 ≤ energy (p T.root) (q T.root) (d T.root) := by
  have hlocal : ∀ s, ∑ c ∈ T.children s, energy (p c) (q c) (d c) ≤
      energy (p s) (q s) (d s) := by
    intro s
    by_cases h : (T.children s).Nonempty
    · exact energy_step (T.children s) p q d (hp s) (hq s) (hd s)
        (fun c _ => hp c) (fun c _ => hq c) (fun c _ => hd c)
        (hpU s) (hqU s) (hp'U s) (hq'U s) (htight s h)
    · simp only [Finset.not_nonempty_iff_eq_empty] at h
      simpa [h] using energy_nonneg (hp s) (hq s) (hd s)
  apply le_trans (Finset.sum_le_sum ?_) (T.sum_leaves_le_root _ hlocal)
  intro b hb
  have hprod : d b ^ 3 ≤ d b * (2 * p b + d b) * (2 * q b + d b) := by
    calc
      d b ^ 3 = d b * d b * d b := by ring
      _ ≤ d b * (2 * p b + d b) * (2 * q b + d b) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith [hp b]) (hd b))
          (by linarith [hq b]) (hd b)
          (mul_nonneg (hd b) (by linarith [hp b, hd b]))
  calc
    d b ^ 2 = (d b ^ 3) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast (d b) 3, ← Real.rpow_mul (hd b)]
      norm_num
    _ ≤ energy (p b) (q b) (d b) :=
      Real.rpow_le_rpow (pow_nonneg (hd b) _) hprod (by norm_num)

theorem two_field_energy (p q d : ι → ℝ) (J : Finset ι) (hJ : J ⊆ T.leaves)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) (hd : ∀ s, 0 ≤ d s)
    (hpU : T.Upper p) (hqU : T.Upper q)
    (hp'U : T.Upper (fun s => p s + d s))
    (hq'U : T.Upper (fun s => q s + d s))
    (htight : ∀ s, (T.children s).Nonempty →
      (∑ c ∈ T.children s, p c ^ 2 = p s ^ 2) ∨
      (∑ c ∈ T.children s, q c ^ 2 = q s ^ 2))
    (_hzero : ∀ b ∈ J, p b = 0 ∧ q b = 0) :
    ∑ b ∈ J, d b ^ 2 ≤ energy (p T.root) (q T.root) (d T.root) := by
  exact (Finset.sum_le_sum_of_subset_of_nonneg hJ (fun b _ _ => sq_nonneg _)).trans
    (T.two_field_energy_all_leaves p q d hp hq hd hpU hqU hp'U hq'U htight)

lemma fields_tight (v : ι → ℝ) (s : ι) :
    (∑ c ∈ T.children s, (T.fields v c).1 ^ 2 = (T.fields v s).1 ^ 2) ∨
    (∑ c ∈ T.children s, (T.fields v c).2 ^ 2 = (T.fields v s).2 ^ 2) := by
  have h := leastPair_tight (v s)
    (Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2))
    (Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2))
  rw [← T.fields_eq] at h
  rcases h with h | h
  · left
    rw [h, Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]
  · right
    rw [h, Real.sq_sqrt (Finset.sum_nonneg fun c _ => sq_nonneg _)]

lemma fields_zero (s : ι) : T.fields (fun _ => 0) s = (0, 0) := by
  have h := T.fields_minimal (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by ring)
    (fun _ => by simp) (fun _ => by simp) s
  exact Prod.ext (le_antisymm h.1 (T.fields_nonneg _ s).1)
    (le_antisymm h.2 (T.fields_nonneg _ s).2)

lemma Upper.add {p q : ι → ℝ} (hpU : T.Upper p) (hqU : T.Upper q)
    (hp : ∀ s, 0 ≤ p s) (hq : ∀ s, 0 ≤ q s) : T.Upper (fun s => p s + q s) := by
  intro s
  exact sum_add_sq_le (T.children s) p q (hp s) (hq s) (hpU s) (hqU s)

lemma Upper.smul {p : ι → ℝ} (hpU : T.Upper p) (a : ℝ) :
    T.Upper (fun s => a * p s) := by
  intro s
  simp_rw [mul_pow, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hpU s) (sq_nonneg a)

lemma fields_add_le (v w : ι → ℝ) (s : ι) :
    (T.fields (v + w) s).1 ≤ (T.fields v s).1 + (T.fields w s).1 ∧
    (T.fields (v + w) s).2 ≤ (T.fields v s).2 + (T.fields w s).2 := by
  apply T.fields_minimal
  · intro t
    exact add_nonneg (T.fields_nonneg v t).1 (T.fields_nonneg w t).1
  · intro t
    exact add_nonneg (T.fields_nonneg v t).2 (T.fields_nonneg w t).2
  · intro t
    have := T.fields_difference v t
    have := T.fields_difference w t
    simp only [Pi.add_apply]
    linarith
  · exact (T.fields_upper v).1.add T (T.fields_upper w).1
      (fun t => (T.fields_nonneg v t).1) (fun t => (T.fields_nonneg w t).1)
  · exact (T.fields_upper v).2.add T (T.fields_upper w).2
      (fun t => (T.fields_nonneg v t).2) (fun t => (T.fields_nonneg w t).2)

lemma fields_neg (v : ι → ℝ) (s : ι) :
    T.fields (-v) s = ((T.fields v s).2, (T.fields v s).1) := by
  have h₁ := T.fields_minimal (-v) (fun t => (T.fields v t).2) (fun t => (T.fields v t).1)
    (fun t => (T.fields_nonneg v t).2) (fun t => (T.fields_nonneg v t).1)
    (fun t => by simp only [Pi.neg_apply]; linarith [T.fields_difference v t])
    (T.fields_upper v).2 (T.fields_upper v).1 s
  have h₂ := T.fields_minimal v (fun t => (T.fields (-v) t).2) (fun t => (T.fields (-v) t).1)
    (fun t => (T.fields_nonneg (-v) t).2) (fun t => (T.fields_nonneg (-v) t).1)
    (fun t => by have := T.fields_difference (-v) t; simp only [Pi.neg_apply] at this; linarith)
    (T.fields_upper (-v)).2 (T.fields_upper (-v)).1 s
  exact Prod.ext (le_antisymm h₁.1 h₂.2) (le_antisymm h₁.2 h₂.1)

lemma fields_smul_le (a : ℝ) (ha : 0 ≤ a) (v : ι → ℝ) (s : ι) :
    (T.fields (a • v) s).1 ≤ a * (T.fields v s).1 ∧
    (T.fields (a • v) s).2 ≤ a * (T.fields v s).2 := by
  apply T.fields_minimal
  · intro t
    exact mul_nonneg ha (T.fields_nonneg v t).1
  · intro t
    exact mul_nonneg ha (T.fields_nonneg v t).2
  · intro t
    simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, T.fields_difference]
  · exact (T.fields_upper v).1.smul T a
  · exact (T.fields_upper v).2.smul T a

lemma fields_smul (a : ℝ) (ha : 0 ≤ a) (v : ι → ℝ) (s : ι) :
    T.fields (a • v) s = (a * (T.fields v s).1, a * (T.fields v s).2) := by
  rcases eq_or_lt_of_le ha with h | h
  · subst a
    simp only [zero_smul, zero_mul]
    exact T.fields_zero s
  · have h₁ := T.fields_smul_le a ha v s
    have h₂ := T.fields_smul_le a⁻¹ (inv_nonneg.mpr ha) (a • v) s
    simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt h), one_smul] at h₂
    have hp := mul_le_mul_of_nonneg_left h₂.1 ha
    have hq := mul_le_mul_of_nonneg_left h₂.2 ha
    simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt h), one_mul] at hp hq
    exact Prod.ext (le_antisymm h₁.1 hp) (le_antisymm h₁.2 hq)

noncomputable def rootSum (v : ι → ℝ) : ℝ :=
  (T.fields v T.root).1 + (T.fields v T.root).2

lemma rootSum_nonneg (v : ι → ℝ) : 0 ≤ T.rootSum v :=
  add_nonneg (T.fields_nonneg v T.root).1 (T.fields_nonneg v T.root).2

@[simp] lemma rootSum_zero : T.rootSum (fun _ => 0) = 0 := by
  simp [rootSum, T.fields_zero]

@[simp] lemma rootSum_neg (v : ι → ℝ) : T.rootSum (-v) = T.rootSum v := by
  simp [rootSum, T.fields_neg, add_comm]

lemma rootSum_add_le (v w : ι → ℝ) : T.rootSum (v + w) ≤ T.rootSum v + T.rootSum w := by
  have h := T.fields_add_le v w T.root
  unfold rootSum
  linarith [h.1, h.2]

lemma rootSum_smul_nonneg (a : ℝ) (ha : 0 ≤ a) (v : ι → ℝ) :
    T.rootSum (a • v) = a * T.rootSum v := by
  simp only [rootSum, T.fields_smul a ha, ← mul_add]

lemma Initial.child_not_mem {H : Finset ι} (hH : T.Initial H) {s c : ι}
    (hs : s ∉ H) (hc : c ∈ T.children s) : c ∉ H := by
  intro h
  have := hH.2 c h
  have hh := (Finset.mem_filter.mp hc).2.2
  exact hs (hh ▸ this)

theorem fields_eq_off_head {H : Finset ι} (hH : T.Initial H) (v w : ι → ℝ)
    (hvw : ∀ s ∉ H, v s = w s) (s : ι) (hs : s ∉ H) :
    T.fields v s = T.fields w s := by
  rw [T.fields_eq v s, T.fields_eq w s, hvw s hs]
  apply congrArg₂ (leastPair (w s))
  · apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro c hc
    rw [fields_eq_off_head hH v w hvw c (hH.child_not_mem T hs hc)]
  · apply congrArg Real.sqrt
    apply Finset.sum_congr rfl
    intro c hc
    rw [fields_eq_off_head hH v w hvw c (hH.child_not_mem T hs hc)]
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

lemma fields_head_zero {H : Finset ι} (hH : T.Initial H) (v : ι → ℝ)
    (hv : ∀ s ∉ H, v s = 0) (s : ι) (hs : s ∉ H) : T.fields v s = (0, 0) := by
  rw [T.fields_eq_off_head hH v (fun _ => 0) hv s hs, T.fields_zero]

noncomputable def defect (x z : ι → ℝ) (s : ι) : ℝ :=
  ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2 - (T.fields x s).1

lemma averaged_feasible (x z : ι → ℝ) :
    T.Upper (fun s => ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2) ∧
    T.Upper (fun s => ((T.fields (x + z) s).2 + (T.fields (x - z) s).2) / 2) := by
  constructor
  · convert ((T.fields_upper (x + z)).1.add T (T.fields_upper (x - z)).1
      (fun s => (T.fields_nonneg (x + z) s).1)
      (fun s => (T.fields_nonneg (x - z) s).1)).smul T (1 / 2) using 1 ;
      ext s ; ring
  · convert ((T.fields_upper (x + z)).2.add T (T.fields_upper (x - z)).2
      (fun s => (T.fields_nonneg (x + z) s).2)
      (fun s => (T.fields_nonneg (x - z) s).2)).smul T (1 / 2) using 1 ;
      ext s ; ring

lemma defect_representation (x z : ι → ℝ) (s : ι) :
    ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2 =
      (T.fields x s).1 + T.defect x z s ∧
    ((T.fields (x + z) s).2 + (T.fields (x - z) s).2) / 2 =
      (T.fields x s).2 + T.defect x z s := by
  have h₁ := T.fields_difference (x + z) s
  have h₂ := T.fields_difference (x - z) s
  have h₃ := T.fields_difference x s
  simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂
  unfold defect
  constructor <;> linarith

lemma defect_nonneg (x z : ι → ℝ) (s : ι) : 0 ≤ T.defect x z s := by
  have h := T.fields_minimal x
    (fun s => ((T.fields (x + z) s).1 + (T.fields (x - z) s).1) / 2)
    (fun s => ((T.fields (x + z) s).2 + (T.fields (x - z) s).2) / 2)
    (fun s => div_nonneg (add_nonneg (T.fields_nonneg _ s).1 (T.fields_nonneg _ s).1) (by norm_num))
    (fun s => div_nonneg (add_nonneg (T.fields_nonneg _ s).2 (T.fields_nonneg _ s).2) (by norm_num))
    (fun s => by
      have h₁ := T.fields_difference (x + z) s
      have h₂ := T.fields_difference (x - z) s
      simp only [Pi.add_apply, Pi.sub_apply] at h₁ h₂
      linarith)
    (T.averaged_feasible x z).1 (T.averaged_feasible x z).2 s
  exact sub_nonneg.mpr h.1

lemma defect_energy_step (x z : ι → ℝ) (s : ι) :
    ∑ c ∈ T.children s, energy (T.fields x c).1 (T.fields x c).2 (T.defect x z c) ≤
      energy (T.fields x s).1 (T.fields x s).2 (T.defect x z s) := by
  apply energy_step (T.children s)
    (fun c => (T.fields x c).1) (fun c => (T.fields x c).2) (T.defect x z)
    (T.fields_nonneg x s).1 (T.fields_nonneg x s).2 (T.defect_nonneg x z s)
    (fun c _ => (T.fields_nonneg x c).1) (fun c _ => (T.fields_nonneg x c).2)
    (fun c _ => T.defect_nonneg x z c) ((T.fields_upper x).1 s) ((T.fields_upper x).2 s)
  · simpa only [← (T.defect_representation x z _).1] using (T.averaged_feasible x z).1 s
  · simpa only [← (T.defect_representation x z _).2] using (T.averaged_feasible x z).2 s
  · exact T.fields_tight x s

lemma defect_off_head {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (s : ι) (hs : s ∉ H) :
    T.defect x z s = ((T.fields z s).1 + (T.fields z s).2) / 2 := by
  have h₁ := T.fields_eq_off_head hH (x + z) z
    (fun s hs => by simp [hx s hs]) s hs
  have h₂ := T.fields_eq_off_head hH (x - z) (-z)
    (fun s hs => by simp [hx s hs]) s hs
  simp only [defect, h₁, h₂, T.fields_head_zero hH x hx s hs, T.fields_neg,
    sub_zero]

lemma max_fields_sq_le_children (v : ι → ℝ) (s : ι) (hv : v s = 0) :
    (max (T.fields v s).1 (T.fields v s).2) ^ 2 ≤
      ∑ c ∈ T.children s, (max (T.fields v c).1 (T.fields v c).2) ^ 2 := by
  let R := Real.sqrt (∑ c ∈ T.children s,
    (max (T.fields v c).1 (T.fields v c).2) ^ 2)
  have hp : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).1 ^ 2) ≤ R := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro c hc
    exact pow_le_pow_left₀ (T.fields_nonneg v c).1 (le_max_left _ _) 2
  have hq : Real.sqrt (∑ c ∈ T.children s, (T.fields v c).2 ^ 2) ≤ R := by
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro c hc
    exact pow_le_pow_left₀ (T.fields_nonneg v c).2 (le_max_right _ _) 2
  have hr : max (T.fields v s).1 (T.fields v s).2 ≤ R := by
    rw [T.fields_eq]
    simp only [leastPair, hv, neg_zero, zero_add]
    exact max_le (max_le hp hq) (max_le hq hp)
  exact (Real.le_sqrt ((T.fields_nonneg v s).1.trans (le_max_left _ _))
    (Finset.sum_nonneg fun c _ => sq_nonneg _)).mp hr

theorem tail_energy {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (hz : ∀ s ∈ H, z s = 0) (s : ι) :
    (max (T.fields z s).1 (T.fields z s).2) ^ 2 ≤
      4 * energy (T.fields x s).1 (T.fields x s).2 (T.defect x z s) := by
  by_cases hs : s ∈ H
  · calc
      (max (T.fields z s).1 (T.fields z s).2) ^ 2 ≤
          ∑ c ∈ T.children s, (max (T.fields z c).1 (T.fields z c).2) ^ 2 :=
        T.max_fields_sq_le_children z s (hz s hs)
      _ ≤ ∑ c ∈ T.children s,
          4 * energy (T.fields x c).1 (T.fields x c).2 (T.defect x z c) := by
        apply Finset.sum_le_sum
        intro c hc
        exact tail_energy hH x z hx hz c
      _ = 4 * ∑ c ∈ T.children s,
          energy (T.fields x c).1 (T.fields x c).2 (T.defect x z c) := by
        rw [Finset.mul_sum]
      _ ≤ 4 * energy (T.fields x s).1 (T.fields x s).2 (T.defect x z s) :=
        mul_le_mul_of_nonneg_left (T.defect_energy_step x z s) (by norm_num)
  · rw [T.fields_head_zero hH x hx s hs]

    rw [energy_zero_base (T.defect_nonneg x z s)]
    have hp := (T.fields_nonneg z s).1
    have hq := (T.fields_nonneg z s).2
    have hm : max (T.fields z s).1 (T.fields z s).2 ≤
        (T.fields z s).1 + (T.fields z s).2 := max_le (by linarith) (by linarith)
    have hsq := pow_le_pow_left₀ (hp.trans (le_max_left _ _)) hm 2
    rw [T.defect_off_head hH x z hx s hs]
    nlinarith
termination_by T.maxDepth - T.depth s
decreasing_by all_goals exact T.child_measure hc

lemma rootSum_defect (x z : ι → ℝ) :
    (T.rootSum (x + z) + T.rootSum (x - z)) / 2 =
      T.rootSum x + 2 * T.defect x z T.root := by
  have h := T.defect_representation x z T.root
  unfold rootSum
  linarith [h.1, h.2]

lemma rootSum_eq_twice_max_of_root_zero (v : ι → ℝ) (hv : v T.root = 0) :
    T.rootSum v = 2 * max (T.fields v T.root).1 (T.fields v T.root).2 := by
  have h := T.fields_difference v T.root
  rw [hv] at h
  have heq : (T.fields v T.root).1 = (T.fields v T.root).2 := by linarith
  simp [rootSum, heq, two_mul]

theorem rootSum_cubic {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (hz : ∀ s ∈ H, z s = 0) :
    (T.rootSum z) ^ 3 ≤ 64 * T.defect x z T.root *
      (T.rootSum x + T.defect x z T.root) ^ 2 := by
  have he := T.tail_energy hH x z hx hz T.root
  have hr := (T.fields_nonneg z T.root).1.trans
    (le_max_left (T.fields z T.root).1 (T.fields z T.root).2)
  have hc := cube_le_of_sq_le_energy hr (by norm_num : (0 : ℝ) ≤ 2)
    (T.fields_nonneg x T.root).1 (T.fields_nonneg x T.root).2
    (T.defect_nonneg x z T.root) (by norm_num at he ⊢; exact he)
  have hd := T.defect_nonneg x z T.root
  have halg : (2 * (T.fields x T.root).1 + T.defect x z T.root) *
        (2 * (T.fields x T.root).2 + T.defect x z T.root) ≤
        (T.rootSum x + T.defect x z T.root) ^ 2 := by
    unfold rootSum
    nlinarith [sq_nonneg ((T.fields x T.root).1 - (T.fields x T.root).2)]
  have hm := mul_le_mul_of_nonneg_left halg hd
  rw [T.rootSum_eq_twice_max_of_root_zero z (hz T.root hH.1)]
  nlinarith

theorem rootSum_finite_midpoint_gap {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (hz : ∀ s ∈ H, z s = 0)
    (hunit : T.rootSum x = 1) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hzt : t ≤ T.rootSum z) :
    1 + t ^ 3 / 128 ≤ (T.rootSum (x + z) + T.rootSum (x - z)) / 2 := by
  have hc := T.rootSum_cubic hH x z hx hz
  have hd := T.defect_nonneg x z T.root
  have ht3 := pow_le_pow_left₀ ht.le hzt 3
  rw [hunit] at hc
  rw [T.rootSum_defect, hunit]
  by_cases hd1 : T.defect x z T.root ≤ 1
  · have hsq : (1 + T.defect x z T.root) ^ 2 ≤ 4 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 64 * T.defect x z T.root)
    nlinarith
  · have ht3' := pow_le_pow_left₀ ht.le ht1.le 3
    norm_num at ht3'
    nlinarith

lemma Upper.le_root {p : ι → ℝ} (hpU : T.Upper p) (hp : ∀ s, 0 ≤ p s) (s : ι) :
    p s ≤ p T.root := by
  by_cases hs : s = T.root
  · simp [hs]
  · have hc : s ∈ T.children (T.parent s) := by simp [children, hs]
    have hsq : p s ^ 2 ≤ p (T.parent s) ^ 2 :=
      (Finset.single_le_sum (fun c _ => sq_nonneg (p c)) hc).trans (hpU (T.parent s))
    have hle : p s ≤ p (T.parent s) := by nlinarith [hp (T.parent s)]
    exact hle.trans (Upper.le_root hpU hp (T.parent s))
termination_by T.depth s
decreasing_by exact T.parent_depth s hs

lemma abs_coordinate_le_rootSum (v : ι → ℝ) (s : ι) : |v s| ≤ T.rootSum v := by
  have hp := (T.fields_upper v).1.le_root T (fun s => (T.fields_nonneg v s).1) s
  have hq := (T.fields_upper v).2.le_root T (fun s => (T.fields_nonneg v s).2) s
  have hd := T.fields_difference v s
  have hp0 := (T.fields_nonneg v T.root).1
  have hq0 := (T.fields_nonneg v T.root).2
  have hp1 := (T.fields_nonneg v s).1
  have hq1 := (T.fields_nonneg v s).2
  unfold rootSum
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma rootSum_pos {v : ι → ℝ} (hv : v ≠ 0) : 0 < T.rootSum v := by
  apply lt_of_le_of_ne (T.rootSum_nonneg v)
  intro hzero
  apply hv
  funext s
  have := T.abs_coordinate_le_rootSum v s
  rw [← hzero] at this
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

noncomputable def rootCommon (v : ι → ℝ) : ℝ := (T.fields v T.root).1

lemma rootCommon_eq_half_sum (v : ι → ℝ) (hv : v T.root = 0) :
    T.rootCommon v = T.rootSum v / 2 := by
  have h := T.fields_difference v T.root
  unfold rootCommon rootSum
  rw [hv] at h
  linarith

theorem commonRoot_finite_cubic {H : Finset ι} (hH : T.Initial H) (x z : ι → ℝ)
    (hx : ∀ s ∉ H, x s = 0) (hz : ∀ s ∈ H, z s = 0)
    (hxroot : x T.root = 0) (hz0 : z ≠ 0) :
    T.rootCommon x + (T.rootCommon z) ^ 3 /
        (8 * (2 * T.rootCommon x + T.rootCommon z) ^ 2) ≤
      (T.rootCommon (x + z) + T.rootCommon (x - z)) / 2 := by
  have hzroot := hz T.root hH.1
  have hxzroot : (x + z) T.root = 0 := by simp [hxroot, hzroot]
  have hxmzroot : (x - z) T.root = 0 := by simp [hxroot, hzroot]
  have hzp : 0 < T.rootCommon z := by
    rw [T.rootCommon_eq_half_sum z hzroot]
    exact div_pos (T.rootSum_pos hz0) (by norm_num)
  have hxp : 0 ≤ T.rootCommon x := (T.fields_nonneg x T.root).1
  have hd := T.defect_nonneg x z T.root
  have hc := T.rootSum_cubic hH x z hx hz
  have he := T.rootSum_defect x z
  have hsum := T.rootSum_add_le x z
  have hsub := T.rootSum_add_le x (-z)
  rw [T.rootSum_neg] at hsub
  have hsub' : T.rootSum (x - z) ≤ T.rootSum x + T.rootSum z := by
    simpa [sub_eq_add_neg] using hsub
  have hxsum : T.rootSum x = 2 * T.rootCommon x := by
    linarith [T.rootCommon_eq_half_sum x hxroot]
  have hzsum : T.rootSum z = 2 * T.rootCommon z := by
    linarith [T.rootCommon_eq_half_sum z hzroot]
  have hdle : T.defect x z T.root ≤ T.rootCommon z := by
    rw [hzsum] at hsum hsub'
    linarith
  rw [hxsum, hzsum] at hc
  have hmono : (2 * T.rootCommon x + T.defect x z T.root) ^ 2 ≤
      (2 * T.rootCommon x + T.rootCommon z) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hden : 0 < 8 * (2 * T.rootCommon x + T.rootCommon z) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmono hd
  have hdiv : (T.rootCommon z) ^ 3 /
      (8 * (2 * T.rootCommon x + T.rootCommon z) ^ 2) ≤ T.defect x z T.root := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hmean : (T.rootCommon (x + z) + T.rootCommon (x - z)) / 2 =
      T.rootCommon x + T.defect x z T.root := by
    rw [T.rootCommon_eq_half_sum (x + z) hxzroot,
      T.rootCommon_eq_half_sum (x - z) hxmzroot,
      T.rootCommon_eq_half_sum x hxroot]
    linarith
  rw [hmean]
  linarith

end

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma root_mem_ancestors (s : ι) : T.root ∈ T.ancestors s := by
  rw [ancestors]
  split_ifs with hs
  · simp [hs]
  · exact Finset.mem_insert_of_mem (root_mem_ancestors (T.parent s))
termination_by T.depth s
decreasing_by exact T.parent_depth s hs

lemma ancestors_subset_of_initial {H : Finset ι} (hH : T.Initial H) (s : ι) (hs : s ∈ H) :
    T.ancestors s ⊆ H := by
  rw [ancestors]
  split_ifs with heq
  · simpa
  · exact Finset.insert_subset hs (ancestors_subset_of_initial hH (T.parent s) (hH.2 s hs))
termination_by T.depth s
decreasing_by exact T.parent_depth s heq

lemma ancestorClosure_subset_of_initial {S H : Finset ι} (hH : T.Initial H) (hS : S ⊆ H) :
    T.ancestorClosure S ⊆ H := by
  apply Finset.insert_subset hH.1
  intro s hs
  obtain ⟨c, hc, hs⟩ := Finset.mem_biUnion.mp hs
  exact T.ancestors_subset_of_initial hH c (hS hc) hs

theorem potentials_on_head (v : ι →₀ ℝ) (H : Finset ι) (hH : T.Initial H)
    (hv : v.support ⊆ H) (s : H) :
    T.P v s.1 = ((T.restrict H hH).fields (fun c => v c.1) s).1 ∧
    T.Q v s.1 = ((T.restrict H hH).fields (fun c => v c.1) s).2 := by
  let U := T.restrict H hH
  let p : ι →₀ ℝ := extend H (fun c => (U.fields (fun c => v c.1) c).1)
  let q : ι →₀ ℝ := extend H (fun c => (U.fields (fun c => v c.1) c).2)
  have hdiff : ∀ c, p c - q c = v c := by
    intro c
    by_cases hc : c ∈ H
    · simp only [p, q, extend_mem _ _ hc]
      exact U.fields_difference _ _
    · have hv0 : v c = 0 := Finsupp.notMem_support_iff.mp (fun h => hc (hv h))
      simp only [p, q, extend_not_mem _ _ hc, hv0, sub_zero]
  have h₁ := T.potentials_minimal v p q
    (extend_nonneg _ _ (fun c => (U.fields_nonneg _ c).1))
    (extend_nonneg _ _ (fun c => (U.fields_nonneg _ c).2)) hdiff
    (T.extend_upper _ _ _ (U.fields_upper _).1)
    (T.extend_upper _ _ _ (U.fields_upper _).2) s.1
  have h₂ := U.fields_minimal (fun c => v c.1) (fun c => T.P v c.1)
    (fun c => T.Q v c.1) (fun c => T.P_nonneg v c.1) (fun c => T.Q_nonneg v c.1)
    (fun c => T.P_sub_Q v c.1) ((T.P_upper v).restrict T H hH)
    ((T.Q_upper v).restrict T H hH) s
  simp only [p, q, extend_coe] at h₁
  exact ⟨le_antisymm h₁.1 h₂.1, le_antisymm h₁.2 h₂.2⟩

lemma P_eq_zero_off_head (v : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hv : v.support ⊆ H) {s : ι} (hs : s ∉ H) : T.P v s = 0 := by
  apply extend_not_mem
  exact fun hh => hs (T.ancestorClosure_subset_of_initial hH hv hh)

lemma Q_eq_zero_off_head (v : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hv : v.support ⊆ H) {s : ι} (hs : s ∉ H) : T.Q v s = 0 := by
  apply extend_not_mem
  exact fun hh => hs (T.ancestorClosure_subset_of_initial hH hv hh)

lemma normSum_on_head (v : ι →₀ ℝ) (H : Finset ι) (hH : T.Initial H)
    (hv : v.support ⊆ H) : T.normSum v = (T.restrict H hH).rootSum (fun s => v s.1) := by
  have h := T.potentials_on_head v H hH hv ⟨T.root, hH.1⟩
  exact congrArg₂ (· + ·) h.1 h.2

lemma potentials_le_normSum (v : ι →₀ ℝ) (s : ι) :
    T.P v s ≤ T.normSum v ∧ T.Q v s ≤ T.normSum v := by
  have hp := (T.P_upper v).le_root T (T.P_nonneg v) s
  have hq := (T.Q_upper v).le_root T (T.Q_nonneg v) s
  have hp0 := T.P_nonneg v T.root
  have hq0 := T.Q_nonneg v T.root
  unfold normSum
  constructor <;> linarith

lemma potentials_lipschitz (v w : ι →₀ ℝ) (s : ι) :
    |T.P v s - T.P w s| ≤ T.normSum (v - w) ∧
    |T.Q v s - T.Q w s| ≤ T.normSum (v - w) := by
  have h₁ := T.potentials_add_le (v - w) w s
  have h₂ := T.potentials_add_le (w - v) v s
  rw [sub_add_cancel] at h₁ h₂
  have hk₁ := T.potentials_le_normSum (v - w) s
  have hk₂ := T.potentials_le_normSum (w - v) s
  have hn : T.normSum (w - v) = T.normSum (v - w) := by
    rw [← neg_sub v w, T.normSum_neg]
  rw [hn] at hk₂
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2, hk₁.1, hk₁.2, hk₂.1, hk₂.2]

end FiniteRootedTree

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma norm_def (v : TreeVector T) : ‖v‖ = T.normSum v := rfl

@[simp] lemma coordinate_apply (s : ι) (v : TreeVector T) : coordinate T s v = v s := rfl

lemma lipschitz_P (s : ι) : LipschitzWith 1 (fun v : TreeVector T => T.P v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (T.potentials_lipschitz v w s).1

lemma lipschitz_Q (s : ι) : LipschitzWith 1 (fun v : TreeVector T => T.Q v s) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul, norm_def]
  exact (T.potentials_lipschitz v w s).2

@[simp] lemma projection_apply (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    projection T H hH v = T.projectHead H v := rfl

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    projection T H hH (projection T H hH v) = projection T H hH v := by
  change ι →₀ ℝ at v
  apply Finsupp.ext
  intro s
  change T.projectHead H (T.projectHead H v) s = T.projectHead H v s
  simp [FiniteRootedTree.projectHead, Finsupp.filter_apply]
  intro hs hs'
  exact (hs hs').elim

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

@[simp] lemma coordinate_coe (s : ι) (v : TreeVector T) :
    coordinate T s (v : TreeSpace T) = v s := by
  exact ContinuousLinearMap.fromCompletion_apply_coe _ v

@[simp] lemma P_coe (s : ι) (v : TreeVector T) : P T s (v : TreeSpace T) = T.P v s :=
  Completion.extension_coe (TreeVector.lipschitz_P T s).uniformContinuous v

@[simp] lemma Q_coe (s : ι) (v : TreeVector T) : Q T s (v : TreeSpace T) = T.Q v s :=
  Completion.extension_coe (TreeVector.lipschitz_Q T s).uniformContinuous v

@[continuity, fun_prop] lemma continuous_P (s : ι) : Continuous (P T s) :=
  Completion.continuous_extension

@[continuity, fun_prop] lemma continuous_Q (s : ι) : Continuous (Q T s) :=
  Completion.continuous_extension

lemma P_nonneg (s : ι) (x : TreeSpace T) : 0 ≤ P T s x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (continuous_P T s)
  | ih v => simpa using T.P_nonneg v s

lemma Q_nonneg (s : ι) (x : TreeSpace T) : 0 ≤ Q T s x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le continuous_const (continuous_Q T s)
  | ih v => simpa using T.Q_nonneg v s

lemma P_sub_Q (s : ι) (x : TreeSpace T) : P T s x - Q T s x = coordinate T s x := by
  induction x using Completion.induction_on with
  | hp =>
      exact isClosed_eq ((continuous_P T s).sub (continuous_Q T s))
        (coordinate T s).continuous
  | ih v => simpa using T.P_sub_Q v s

theorem norm_eq (x : TreeSpace T) : ‖x‖ = P T T.root x + Q T T.root x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq continuous_norm ((continuous_P T T.root).add (continuous_Q T T.root))
  | ih v => simp [TreeVector.norm_def, FiniteRootedTree.normSum]

lemma abs_coordinate_le (s : ι) (x : TreeSpace T) : |coordinate T s x| ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (continuous_abs.comp (coordinate T s).continuous) continuous_norm
  | ih v => simpa only [coordinate_coe, Completion.norm_coe, TreeVector.norm_def] using
      T.abs_coordinate_le_normSum v s

lemma fields_lipschitz (s : ι) (x y : TreeSpace T) :
    |P T s x - P T s y| ≤ ‖x - y‖ ∧ |Q T s x - Q T s y| ≤ ‖x - y‖ := by
  induction x, y using Completion.induction_on₂ with
  | hp =>
      have hp : IsClosed {p : TreeSpace T × TreeSpace T |
          |P T s p.1 - P T s p.2| ≤ ‖p.1 - p.2‖} :=
        isClosed_le (by fun_prop) (by fun_prop)
      have hq : IsClosed {p : TreeSpace T × TreeSpace T |
          |Q T s p.1 - Q T s p.2| ≤ ‖p.1 - p.2‖} :=
        isClosed_le (by fun_prop) (by fun_prop)
      exact hp.inter hq
  | ih v w =>
      simp only [P_coe, Q_coe, ← Completion.coe_sub, Completion.norm_coe,
        TreeVector.norm_def]
      exact T.potentials_lipschitz v w s

@[simp] lemma projection_coe (H : Finset ι) (hH : T.Initial H) (v : TreeVector T) :
    projection T H hH (v : TreeSpace T) = (TreeVector.projection T H hH v : TreeSpace T) :=
  ContinuousLinearMap.completion_apply_coe _ v

lemma projection_contracts (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    ‖projection T H hH x‖ ≤ ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_le (continuous_norm.comp (projection T H hH).continuous) continuous_norm
  | ih v => simpa only [projection_coe, Completion.norm_coe] using
      TreeVector.projection_contracts T H hH v

lemma projection_idem (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    projection T H hH (projection T H hH x) = projection T H hH x := by
  induction x using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v => simp only [projection_coe, TreeVector.projection_idem]

lemma coordinate_projection (H : Finset ι) (hH : T.Initial H) (s : ι) (x : TreeSpace T) :
    coordinate T s (projection T H hH x) = if s ∈ H then coordinate T s x else 0 := by
  induction x using Completion.induction_on with
  | hp =>
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
      · simp only [ite_eq_right hs]
        exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
      rw [projection_coe, coordinate_coe, coordinate_coe]
      exact T.projectHead_apply H v s

lemma tail_closed (H : Finset ι) (hH : T.Initial H) : IsClosed (tail T H hH : Set (TreeSpace T)) :=
  (projection T H hH).isClosed_ker

theorem finite_tail_dense (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T)
    (hx : x ∈ tail T H hH) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : TreeVector T, TreeVector.projection T H hH v = 0 ∧
      ‖(v : TreeSpace T) - x‖ < ε := by
  have hx0 : projection T H hH x = 0 := hx
  obtain ⟨v, hv⟩ := Completion.denseRange_coe.exists_dist_lt x (half_pos hε)
  let w : TreeVector T := v - TreeVector.projection T H hH v
  refine ⟨w, ?_, ?_⟩
  · change TreeVector.projection T H hH (v - TreeVector.projection T H hH v) = 0
    rw [map_sub, TreeVector.projection_idem, sub_self]
  · have he : (w : TreeSpace T) - x =
        ((v : TreeSpace T) - x) - projection T H hH ((v : TreeSpace T) - x) := by
      change (↑(v - TreeVector.projection T H hH v) : TreeSpace T) - x = _
      simp only [Completion.coe_sub, ← projection_coe, map_sub, hx0, sub_zero]
      abel
    rw [he]
    have hp := projection_contracts T H hH ((v : TreeSpace T) - x)
    have hv' : ‖(v : TreeSpace T) - x‖ < ε / 2 := by
      simpa only [dist_comm x, dist_eq_norm] using hv
    exact (norm_sub_le _ _).trans_lt (by linarith)

end TreeSpace

namespace FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

lemma restrict_initial (K : Finset ι) (hK : T.Initial K) (H : Finset ι)
    (hH : T.Initial H) :
    (T.restrict K hK).Initial (Finset.univ.filter (fun s : K => s.1 ∈ H)) := by
  constructor
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hH.1
  · intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hH.2 s.1 (Finset.mem_filter.mp hs).2⟩

noncomputable def meanExcess (x z : ι →₀ ℝ) : ℝ :=
  (T.normSum (x + z) + T.normSum (x - z)) / 2 - T.normSum x

theorem normSum_cubic (x z : ι →₀ ℝ) {H : Finset ι} (hH : T.Initial H)
    (hx : x.support ⊆ H) (hz : ∀ s ∈ H, z s = 0) :
    (T.normSum z) ^ 3 ≤ 8 * T.meanExcess x z *
      (2 * T.normSum x + T.meanExcess x z) ^ 2 := by
  let K := T.ancestorClosure (x.support ∪ z.support)
  have hK : T.Initial K := T.ancestorClosure_initial _
  have hxK : x.support ⊆ K := (Finset.subset_union_left).trans (T.subset_ancestorClosure _)
  have hzK : z.support ⊆ K := (Finset.subset_union_right).trans (T.subset_ancestorClosure _)
  have hpK : (x + z).support ⊆ K := Finsupp.support_add.trans (Finset.union_subset hxK hzK)
  have hmK : (x - z).support ⊆ K := Finsupp.support_sub.trans (Finset.union_subset hxK hzK)
  let U := T.restrict K hK
  let xf : K → ℝ := fun c => x c.1
  let zf : K → ℝ := fun c => z c.1
  have hxf : ∀ s ∉ Finset.univ.filter (fun s : K => s.1 ∈ H), xf s = 0 := by
    intro s hs
    have hsH : s.1 ∉ H := by simpa using hs
    exact Finsupp.notMem_support_iff.mp (fun h => hsH (hx h))
  have hzf : ∀ s ∈ Finset.univ.filter (fun s : K => s.1 ∈ H), zf s = 0 := by
    intro s hs
    exact hz s.1 (Finset.mem_filter.mp hs).2
  have he := U.rootSum_cubic (T.restrict_initial K hK H hH) xf zf hxf hzf
  have hd := U.rootSum_defect xf zf
  have hn₁ : T.normSum x = U.rootSum xf := T.normSum_on_head x K hK hxK
  have hn₂ : T.normSum z = U.rootSum zf := T.normSum_on_head z K hK hzK
  have hn₃ : T.normSum (x + z) = U.rootSum (xf + zf) := T.normSum_on_head (x + z) K hK hpK
  have hn₄ : T.normSum (x - z) = U.rootSum (xf - zf) := T.normSum_on_head (x - z) K hK hmK
  have hg : T.meanExcess x z = 2 * U.defect xf zf U.root := by
    unfold meanExcess
    rw [hn₁, hn₃, hn₄]
    linarith
  rw [hg, hn₁, hn₂]
  convert he using 1 ; ring

end FiniteRootedTree

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def meanExcess (x z : TreeSpace T) : ℝ := (‖x + z‖ + ‖x - z‖) / 2 - ‖x‖

@[simp] lemma meanExcess_coe (x z : TreeVector T) :
    meanExcess T (x : TreeSpace T) (z : TreeSpace T) = T.meanExcess x z := by
  simp only [meanExcess, ← Completion.coe_add, ← Completion.coe_sub,
    Completion.norm_coe, TreeVector.norm_def]
  rfl

@[continuity, fun_prop] lemma continuous_meanExcess :
    Continuous (fun p : TreeSpace T × TreeSpace T => meanExcess T p.1 p.2) := by
  unfold meanExcess
  fun_prop

lemma meanExcess_nonneg (x z : TreeSpace T) : 0 ≤ meanExcess T x z := by
  have he : x + z + (x - z) = (2 : ℝ) • x := by module
  have ht := norm_add_le (x + z) (x - z)
  rw [he, norm_smul, Real.norm_eq_abs] at ht
  norm_num at ht
  unfold meanExcess
  linarith

lemma meanExcess_le (x z : TreeSpace T) : meanExcess T x z ≤ ‖z‖ := by
  have h₁ := norm_add_le x z
  have h₂ := norm_sub_le x z
  unfold meanExcess
  linarith

theorem cubic_projected_tail (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : TreeSpace T) :
    ‖z - projection T H hH z‖ ^ 3 ≤
      8 * meanExcess T (x : TreeSpace T) (z - projection T H hH z) *
        (2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T)
          (z - projection T H hH z)) ^ 2 := by
  induction z using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by unfold meanExcess; fun_prop)
  | ih v =>
      rw [projection_coe, ← Completion.coe_sub, meanExcess_coe, Completion.norm_coe,
        Completion.norm_coe]
      change ι →₀ ℝ at v
      change T.normSum (v - T.projectHead H v) ^ 3 ≤ _
      apply T.normSum_cubic x _ hH hx
      intro s hs
      change v s - T.projectHead H v s = 0
      rw [T.projectHead_apply, ite_eq_left hs, sub_self]

theorem cubic_tail (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : TreeSpace T)
    (hz : z ∈ tail T H hH) :
    ‖z‖ ^ 3 ≤ 8 * meanExcess T (x : TreeSpace T) z *
      (2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T) z) ^ 2 := by
  have he := cubic_projected_tail T x hH hx z
  have hz0 : projection T H hH z = 0 := hz
  simpa only [hz0, sub_zero] using he

theorem finite_center_midpoint_gap (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (hunit : ‖x‖ = 1) (z : TreeSpace T)
    (hz : z ∈ tail T H hH) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hzt : t ≤ ‖z‖) :
    1 + t ^ 3 / 128 ≤ (‖(x : TreeSpace T) + z‖ + ‖(x : TreeSpace T) - z‖) / 2 := by
  have he := cubic_tail T x hH hx z hz
  have hd := meanExcess_nonneg T (x : TreeSpace T) z
  have hx' : ‖(x : TreeSpace T)‖ = 1 := by simpa using hunit
  rw [hx'] at he
  have ht3 := pow_le_pow_left₀ ht.le hzt 3
  have hbound : t ^ 3 / 128 ≤ meanExcess T (x : TreeSpace T) z := by
    by_cases hg : meanExcess T (x : TreeSpace T) z ≤ 2
    · have hsq : (2 * 1 + meanExcess T (x : TreeSpace T) z) ^ 2 ≤ 16 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 8 * meanExcess T (x : TreeSpace T) z)
      nlinarith
    · have ht3' := pow_le_pow_left₀ ht.le ht1.le 3
      norm_num at ht3'
      nlinarith
  unfold meanExcess at hbound
  rw [hx'] at hbound
  linarith

theorem homogeneous_cubic_tail (x : TreeVector T) {H : Finset ι} (hH : T.Initial H)
    (hx : (show ι →₀ ℝ from x).support ⊆ H) (z : TreeSpace T)
    (hz : z ∈ tail T H hH) (hz0 : z ≠ 0) :
    (‖(x : TreeSpace T) + z‖ + ‖(x : TreeSpace T) - z‖) / 2 ≥
      ‖(x : TreeSpace T)‖ + ‖z‖ ^ 3 / (8 * (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2) := by
  have he := cubic_tail T x hH hx z hz
  have hg := meanExcess_nonneg T (x : TreeSpace T) z
  have hg' := meanExcess_le T (x : TreeSpace T) z
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hmono : (2 * ‖(x : TreeSpace T)‖ + meanExcess T (x : TreeSpace T) z) ^ 2 ≤
      (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hden : 0 < 8 * (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 8 * meanExcess T (x : TreeSpace T) z)
  have hdiv : ‖z‖ ^ 3 / (8 * (2 * ‖(x : TreeSpace T)‖ + ‖z‖) ^ 2) ≤
      meanExcess T (x : TreeSpace T) z := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  unfold meanExcess at hdiv
  linarith

end TreeSpace

namespace TreeVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def ofHeadLinear (H : Finset ι) : (H → ℝ) →ₗ[ℝ] TreeVector T where
  toFun := FiniteRootedTree.extend H
  map_add' f g := by
    change FiniteRootedTree.extend H (f + g) = FiniteRootedTree.extend H f + FiniteRootedTree.extend H g
    ext s
    by_cases hs : s ∈ H
    · simp [FiniteRootedTree.extend, hs]
    · simp [FiniteRootedTree.extend, hs]
  map_smul' a f := by
    change FiniteRootedTree.extend H (a • f) = a • FiniteRootedTree.extend H f
    ext s
    by_cases hs : s ∈ H
    · simp [FiniteRootedTree.extend, hs]
    · simp [FiniteRootedTree.extend, hs]

def ofHead (H : Finset ι) : (H → ℝ) →L[ℝ] TreeVector T :=
  (ofHeadLinear T H).toContinuousLinearMap

lemma ofHead_apply (H : Finset ι) (f : H → ℝ) (s : ι) :
    ofHead T H f s = if hs : s ∈ H then f ⟨s, hs⟩ else 0 := by
  change FiniteRootedTree.extend H f s = _
  simp [FiniteRootedTree.extend]

lemma ofHead_support (H : Finset ι) (f : H → ℝ) :
    (show ι →₀ ℝ from ofHead T H f).support ⊆ H := by
  intro s hs
  by_contra hh
  have he : (ofHead T H f) s = 0 := by rw [ofHead_apply, dite_eq_right hh]
  exact (Finsupp.mem_support_iff.mp hs) he

def basisVector (s : ι) : TreeVector T := Finsupp.single s 1

lemma basisVector_apply (s c : ι) : basisVector T s c = if s = c then 1 else 0 :=
  Finsupp.single_apply

lemma not_finite_dimensional {ι : Type uIndex} [DecidableEq ι] (T : FiniteRootedTree ι) [Infinite ι] :
    ¬Module.Finite ℝ (TreeVector T) := by
  intro h
  let : Module.Finite ℝ (ι →₀ ℝ) := h
  exact Infinite.not_finite (Module.Finite.finite_basis (Finsupp.basisSingleOne : Module.Basis ι ℝ (ι →₀ ℝ)))

end TreeVector

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def headCoordinates (H : Finset ι) : TreeSpace T →L[ℝ] (H → ℝ) :=
  ContinuousLinearMap.pi (fun s : H => coordinate T s.1)

@[simp] lemma headCoordinates_apply (H : Finset ι) (x : TreeSpace T) (s : H) :
    headCoordinates T H x s = coordinate T s.1 x := rfl

theorem projection_reconstructs (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T) :
    projection T H hH x = ((TreeVector.ofHead T H (headCoordinates T H x)) : TreeSpace T) := by
  induction x using Completion.induction_on with
  | hp =>
      apply isClosed_eq
      · exact (projection T H hH).continuous
      · exact ((Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).comp
          ((TreeVector.ofHead T H).comp (headCoordinates T H))).continuous
  | ih v =>
      rw [projection_coe]
      apply congrArg ((↑) : TreeVector T → TreeSpace T)
      apply Finsupp.ext
      intro s
      change T.projectHead H v s = TreeVector.ofHead T H (headCoordinates T H (v : TreeSpace T)) s
      rw [TreeVector.ofHead_apply]
      have hp := T.projectHead_apply H (show ι →₀ ℝ from v) s
      rw [hp]
      by_cases hs : s ∈ H
      · simp only [ite_eq_left hs, dite_eq_left hs, headCoordinates_apply, coordinate_coe]
      · simp only [ite_eq_right hs, dite_eq_right hs]

lemma tail_eq_coordinate_kernel (H : Finset ι) (hH : T.Initial H) :
    tail T H hH = (headCoordinates T H).ker := by
  ext x
  constructor
  · intro hx
    change headCoordinates T H x = 0
    ext s
    have hz : projection T H hH x = 0 := hx
    have he := coordinate_projection T H hH s.1 x
    rw [hz, map_zero, ite_eq_left s.2] at he
    exact he.symm
  · intro hx
    change projection T H hH x = 0
    rw [projection_reconstructs]
    have hz : headCoordinates T H x = 0 := hx
    rw [hz, map_zero, Completion.coe_zero]

theorem tail_finite_codimension (H : Finset ι) (hH : T.Initial H) :
    Module.Finite ℝ (TreeSpace T ⧸ tail T H hH) := by
  rw [tail_eq_coordinate_kernel]
  exact Submodule.CoFG.ker (headCoordinates T H).toLinearMap

theorem supported_is_finite (H : Finset ι) (hH : T.Initial H) (x : TreeSpace T)
    (hx : projection T H hH x = x) :
    ∃ v : TreeVector T, (v : TreeSpace T) = x ∧ (show ι →₀ ℝ from v).support ⊆ H := by
  refine ⟨TreeVector.ofHead T H (headCoordinates T H x), ?_, TreeVector.ofHead_support T H _⟩
  rw [← projection_reconstructs T H hH x, hx]

theorem not_finite_dimensional [Infinite ι] : ¬Module.Finite ℝ (TreeSpace T) := by
  intro h
  let := h
  have hf := FiniteDimensional.of_injective
    (Completion.toComplL : TreeVector T →L[ℝ] TreeSpace T).toLinearMap
    (Completion.coe_injective (TreeVector T))
  exact TreeVector.not_finite_dimensional T hf

end TreeSpace

namespace CofiniteSubspace

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

def top : CofiniteSubspace E where
  space := ⊤
  closed := isClosed_univ
  finiteQuotient := inferInstance

instance : Nonempty (CofiniteSubspace E) := ⟨top⟩

lemma nontrivial_space (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    Nontrivial F.space := by
  by_contra hn
  have : Subsingleton F.space := not_nontrivial_iff_subsingleton.mp hn
  let := F.finiteQuotient
  exact hE (Module.Finite.of_submodule_quotient F.space)

lemma exists_unit (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) :
    ∃ y ∈ F.space, ‖y‖ = 1 := by
  have := F.nontrivial_space hE
  obtain ⟨y, hy⟩ := exists_norm_eq F.space (by norm_num : (0 : ℝ) ≤ 1)
  exact ⟨y, y.2, hy⟩

end CofiniteSubspace

section Moduli

variable {E : Type uSpace} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma averagedGain_lower (x : E) (t : ℝ) (y : E) : ‖x‖ - 1 ≤ averagedGain x t y := by
  have he : x + t • y + (x - t • y) = (2 : ℝ) • x := by module
  have h := norm_add_le (x + t • y) (x - t • y)
  rw [he, norm_smul, Real.norm_eq_abs] at h
  norm_num at h
  unfold averagedGain
  linarith

lemma averagedInner_bddBelow (x : E) (t : ℝ) (F : CofiniteSubspace E) :
    BddBelow {r : ℝ | ∃ y ∈ F.space, 1 ≤ ‖y‖ ∧ r = averagedGain x t y} := by
  refine ⟨‖x‖ - 1, ?_⟩
  rintro r ⟨y, hy, hy1, rfl⟩
  exact averagedGain_lower x t y

lemma averagedInner_nonempty (x : E) (t : ℝ) (F : CofiniteSubspace E)
    (hE : ¬Module.Finite ℝ E) :
    {r : ℝ | ∃ y ∈ F.space, 1 ≤ ‖y‖ ∧ r = averagedGain x t y}.Nonempty := by
  obtain ⟨y, hy, hy1⟩ := F.exists_unit hE
  exact ⟨_, y, hy, hy1.ge, rfl⟩

lemma averagedInner_le (x : E) (hx : ‖x‖ = 1) (t : ℝ) (ht : 0 ≤ t)
    (F : CofiniteSubspace E) (hE : ¬Module.Finite ℝ E) : averagedInner x t F ≤ t := by
  obtain ⟨y, hy, hy1⟩ := F.exists_unit hE
  have hle : averagedInner x t F ≤ averagedGain x t y :=
    csInf_le (averagedInner_bddBelow x t F) ⟨y, hy, hy1.ge, rfl⟩
  have h₁ := norm_add_le x (t • y)
  have h₂ := norm_sub_le x (t • y)
  have hnorm : ‖t • y‖ = t := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hy1, mul_one]
  rw [hx, hnorm] at h₁ h₂
  unfold averagedGain at hle
  linarith

theorem averagedModulus_lower_of_witness (hE : ¬Module.Finite ℝ E)
    {t c : ℝ} (ht : 0 ≤ t)
    (hw : ∀ x : E, ‖x‖ = 1 → ∀ ε : ℝ, 0 < ε →
      ∃ F : CofiniteSubspace E, ∀ y ∈ F.space, 1 ≤ ‖y‖ → c - ε ≤ averagedGain x t y) :
    c ≤ averagedModulus E t := by
  have hunit : ∃ x : E, ‖x‖ = 1 := by
    obtain ⟨x, hx, hx1⟩ := (CofiniteSubspace.top : CofiniteSubspace E).exists_unit hE
    exact ⟨x, hx1⟩
  apply le_csInf
  · obtain ⟨x, hx⟩ := hunit
    exact ⟨_, x, hx, rfl⟩
  · rintro r ⟨x, hx, rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨F, hF⟩ := hw x hx ε hε
    have hinner : c - ε ≤ averagedInner x t F := by
      apply le_csInf (averagedInner_nonempty x t F hE)
      rintro r ⟨y, hy, hy1, rfl⟩
      exact hF y hy hy1
    have hbounded : BddAbove (Set.range (averagedInner x t)) := by
      refine ⟨t, ?_⟩
      rintro r ⟨G, rfl⟩
      exact averagedInner_le x hx t ht G hE
    have hsup := le_csSup hbounded (Set.mem_range_self F)
    linarith

end Moduli

namespace TreeSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)

def cofiniteTail (H : Finset ι) (hH : T.Initial H) : CofiniteSubspace (TreeSpace T) where
  space := tail T H hH
  closed := tail_closed T H hH
  finiteQuotient := tail_finite_codimension T H hH

lemma finite_unit_dense (x : TreeSpace T) (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : TreeVector T, ‖v‖ = 1 ∧ ‖(v : TreeSpace T) - x‖ < ε := by
  obtain ⟨v, hv⟩ := Completion.denseRange_coe.exists_dist_lt x
    (lt_min (by positivity : (0 : ℝ) < ε / 4) (by norm_num : (0 : ℝ) < 1 / 2))
  have hvε : ‖(v : TreeSpace T) - x‖ < ε / 4 := by
    simpa only [dist_comm x, dist_eq_norm] using hv.trans_le (min_le_left _ _)
  have hvhalf : ‖(v : TreeSpace T) - x‖ < 1 / 2 := by
    simpa only [dist_comm x, dist_eq_norm] using hv.trans_le (min_le_right _ _)
  have hv0 : v ≠ 0 := by
    intro hv0
    have hvz := congrArg ((↑) : TreeVector T → TreeSpace T) hv0
    rw [Completion.coe_zero] at hvz
    rw [hvz, zero_sub, norm_neg, hx] at hvhalf
    norm_num at hvhalf
  let w : TreeVector T := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hv0
  have hscale : ‖v‖ • w = v := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
  have hsub : ‖w - v‖ = |1 - ‖v‖| := by
    have he : w - v = (1 - ‖v‖) • w := by rw [sub_smul, one_smul, hscale]
    rw [he, norm_smul, Real.norm_eq_abs, hw, mul_one]
  have hreverse := abs_norm_sub_norm_le (v : TreeSpace T) x
  rw [Completion.norm_coe, hx, abs_sub_comm] at hreverse
  have hdist : ‖(w : TreeSpace T) - (v : TreeSpace T)‖ ≤ ‖(v : TreeSpace T) - x‖ := by
    rw [← Completion.coe_sub, Completion.norm_coe, hsub]
    exact hreverse
  refine ⟨w, hw, ?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub (w : TreeSpace T) (v : TreeSpace T) x
  exact htri.trans_lt (by linarith)

theorem averaged_modulus_cubic [Infinite ι] {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    t ^ 3 / 128 ≤ averagedModulus (TreeSpace T) t := by
  apply averagedModulus_lower_of_witness (not_finite_dimensional T) ht.le
  intro x hx ε hε
  obtain ⟨v, hv, hvx⟩ := finite_unit_dense T x hx hε
  let H := T.head (show ι →₀ ℝ from v)
  have hH : T.Initial H := T.head_initial v
  refine ⟨cofiniteTail T H hH, ?_⟩
  intro y hy hy1
  have hty : t ≤ ‖t • y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hzy : t • y ∈ tail T H hH := (tail T H hH).smul_mem t hy
  have hfinite := finite_center_midpoint_gap T v hH (T.support_subset_head v) hv
    (t • y) hzy ht ht1 hty
  have h₁ : ‖(v : TreeSpace T) + t • y‖ ≤ ‖x + t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) + t • y‖ = ‖x + t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h₂ : ‖(v : TreeSpace T) - t • y‖ ≤ ‖x - t • y‖ + ‖(v : TreeSpace T) - x‖ := by
    calc
      ‖(v : TreeSpace T) - t • y‖ = ‖x - t • y + ((v : TreeSpace T) - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  unfold averagedGain
  linarith

end TreeSpace

end RecursivePotentials

end

end OAI
