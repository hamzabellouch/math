import OAI.Probability.FreeIsing.Estimates.RadialSummability

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem367

lemma treeShell_radial_succ (d n : ℕ) (r : ℝ) :
    (Fintype.card (TreeShell d (n + 1)) : ℝ) * r ^ (n + 1) =
      (d : ℝ) * r * (((d - 1 : ℕ) : ℝ) * r) ^ n := by
  rw [card_treeShell_succ, Nat.cast_mul, Nat.cast_pow, pow_succ, mul_pow]
  ring

theorem summable_of_tree_radial_le {d : ℕ} {f : TreeVertex d → ℝ} {C r : ℝ}
    (hf : ∀ v, 0 ≤ f v) (hbound : ∀ v, f v ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) : Summable f :=
  ((summable_geometric_radial d hr hsmall).mul_left C).of_nonneg_of_le hf hbound

theorem tsum_le_of_tree_radial_le {d : ℕ} {f : TreeVertex d → ℝ} {C r : ℝ}
    (hf : ∀ v, 0 ≤ f v) (hbound : ∀ v, f v ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∑' v, f v) ≤ C * (1 + (d : ℝ) * r / (1 - ((d - 1 : ℕ) : ℝ) * r)) := by
  have hfS := summable_of_tree_radial_le hf hbound hr hsmall
  calc
    (∑' v, f v) ≤ ∑' v : TreeVertex d, C * r ^ v.1.length :=
      hfS.tsum_le_tsum hbound ((summable_geometric_radial d hr hsmall).mul_left C)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_radial d hr hsmall]

theorem summable_of_attenuated_tree_bound {d : ℕ} {f : TreeVertex d → ℝ}
    {C θ q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hcritical : ((d - 1 : ℕ) : ℝ) * θ ^ 2 ≤ 1)
    (hf : ∀ v, 0 ≤ f v)
    (hbound : ∀ v, f v ≤ C * (θ ^ 2 * q) ^ v.1.length) : Summable f := by
  apply summable_of_tree_radial_le hf hbound (mul_nonneg (sq_nonneg _) hq)
  calc
    ((d - 1 : ℕ) : ℝ) * (θ ^ 2 * q) = (((d - 1 : ℕ) : ℝ) * θ ^ 2) * q := by ring
    _ ≤ 1 * q := mul_le_mul_of_nonneg_right hcritical hq
    _ < 1 := by simpa using hq1

theorem tsum_treeShell_radial_tail (d L : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∑' n, (Fintype.card (TreeShell d (n + L + 1)) : ℝ) * r ^ (n + L + 1)) =
      (d : ℝ) * r * (((d - 1 : ℕ) : ℝ) * r) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * r) := by
  simp_rw [treeShell_radial_succ, pow_add]
  have heq : (fun n : ℕ => (d : ℝ) * r *
      ((((d - 1 : ℕ) : ℝ) * r) ^ n * (((d - 1 : ℕ) : ℝ) * r) ^ L)) =
      (fun n => ((d : ℝ) * r * (((d - 1 : ℕ) : ℝ) * r) ^ L) *
        (((d - 1 : ℕ) : ℝ) * r) ^ n) := by
    funext n
    ring
  rw [heq, tsum_mul_left,
    tsum_geometric_of_lt_one (mul_nonneg (Nat.cast_nonneg _) hr) hsmall]
  rfl

lemma tsum_treeShell_radial_cutoff (d L : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∑' n, if L < n then (Fintype.card (TreeShell d n) : ℝ) * r ^ n else 0) =
      (d : ℝ) * r * (((d - 1 : ℕ) : ℝ) * r) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * r) := by
  let f : ℕ → ℝ := fun n =>
    if L < n then (Fintype.card (TreeShell d n) : ℝ) * r ^ n else 0
  have hf : Summable f := ((summable_radial_iff d (fun n => r ^ n) (fun n => pow_nonneg hr n)).mp
      (summable_geometric_radial d hr hsmall)).of_nonneg_of_le
    (fun n => by dsimp [f]; split_ifs <;> first | exact le_rfl | positivity)
    (fun n => by dsimp [f]; split_ifs <;> first | exact le_rfl | positivity)
  have hzero : ∑ n ∈ Finset.range (L + 1), f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hn' := Finset.mem_range.mp hn
    simp [f, show ¬ L < n by omega]
  have htail : (fun n => f (n + (L + 1))) =
      (fun n => (Fintype.card (TreeShell d (n + L + 1)) : ℝ) * r ^ (n + L + 1)) := by
    funext n
    simp only [f, show L < n + (L + 1) by omega, ite_true, Nat.add_assoc]
  have hsplit := hf.sum_add_tsum_nat_add (L + 1)
  rw [hzero, zero_add, htail] at hsplit
  change (∑' n, f n) = _
  rw [← hsplit]
  exact tsum_treeShell_radial_tail d L hr hsmall

theorem tsum_tree_radial_cutoff (d L : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∑' v : TreeVertex d, if L < v.1.length then r ^ v.1.length else 0) =
      (d : ℝ) * r * (((d - 1 : ℕ) : ℝ) * r) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * r) := by
  have hs : Summable (fun v : TreeVertex d => if L < v.1.length then r ^ v.1.length else 0) :=
    (summable_geometric_radial d hr hsmall).of_nonneg_of_le
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
  rw [tsum_radial d (fun n => if L < n then r ^ n else 0) hs]
  have heq : (fun n => (Fintype.card (TreeShell d n) : ℝ) *
      (if L < n then r ^ n else 0)) =
      (fun n => if L < n then (Fintype.card (TreeShell d n) : ℝ) * r ^ n else 0) := by
    funext n
    split_ifs <;> simp
  rw [heq]
  exact tsum_treeShell_radial_cutoff d L hr hsmall

theorem tsum_cutoff_le_of_tree_radial_le {d : ℕ} {f : TreeVertex d → ℝ} {C r : ℝ}
    (hf : ∀ v, 0 ≤ f v) (hbound : ∀ v, f v ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) (L : ℕ) :
    (∑' v : TreeVertex d, if L < v.1.length then f v else 0) ≤
      C * ((d : ℝ) * r * (((d - 1 : ℕ) : ℝ) * r) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * r)) := by
  have hs : Summable (fun v : TreeVertex d => if L < v.1.length then r ^ v.1.length else 0) :=
    (summable_geometric_radial d hr hsmall).of_nonneg_of_le
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
      (fun v => by split_ifs <;> first | exact le_rfl | positivity)
  have hle (v : TreeVertex d) : (if L < v.1.length then f v else 0) ≤
      C * (if L < v.1.length then r ^ v.1.length else 0) := by
    split_ifs
    · exact hbound v
    · simp
  have hfs : Summable (fun v : TreeVertex d => if L < v.1.length then f v else 0) :=
    (hs.mul_left C).of_nonneg_of_le (fun v => by split_ifs; exact hf v; rfl) hle
  calc
    _ ≤ ∑' v : TreeVertex d, C * (if L < v.1.length then r ^ v.1.length else 0) :=
      hfs.tsum_le_tsum hle (hs.mul_left C)
    _ = _ := by rw [tsum_mul_left, tsum_tree_radial_cutoff d L hr hsmall]

theorem ae_summable_sq_of_tree_radial_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : TreeVertex d → Ω → ℝ} {C r : ℝ}
    (hInt : ∀ v, Integrable (fun ω => A v ω ^ 2) P)
    (hbound : ∀ v, (∫ ω, A v ω ^ 2 ∂P) ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    ∀ᵐ ω ∂P, Summable (fun v => A v ω ^ 2) := by
  have hs : Summable (fun v => ∫ ω, A v ω ^ 2 ∂P) :=
    summable_of_tree_radial_le (fun v => integral_nonneg (fun ω => sq_nonneg _)) hbound hr hsmall
  have heq (v) : eLpNorm (fun ω => A v ω ^ 2) 1 P = ENNReal.ofReal (∫ ω, A v ω ^ 2 ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hInt v).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hInt v)]
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  have hfin : (∑' v, eLpNorm (fun ω => A v ω ^ 2) 1 P) ≠ ⊤ := by
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun v => integral_nonneg (fun ω => sq_nonneg _)) hs]
    exact ENNReal.ofReal_ne_top
  have ha := summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl hfin
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using ha

theorem integral_tsum_sq_eq_of_tree_radial_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : TreeVertex d → Ω → ℝ} {C r : ℝ}
    (hInt : ∀ v, Integrable (fun ω => A v ω ^ 2) P)
    (hbound : ∀ v, (∫ ω, A v ω ^ 2 ∂P) ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∫ ω, ∑' v, A v ω ^ 2 ∂P) = ∑' v, ∫ ω, A v ω ^ 2 ∂P := by
  apply (integral_tsum_of_summable_integral_norm hInt _).symm
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  exact summable_of_tree_radial_le (fun v => integral_nonneg (fun ω => sq_nonneg _))
    hbound hr hsmall

theorem integral_tsum_sq_le_of_tree_radial_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : TreeVertex d → Ω → ℝ} {C r : ℝ}
    (hInt : ∀ v, Integrable (fun ω => A v ω ^ 2) P)
    (hbound : ∀ v, (∫ ω, A v ω ^ 2 ∂P) ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) :
    (∫ ω, ∑' v, A v ω ^ 2 ∂P) ≤
      C * (1 + (d : ℝ) * r / (1 - ((d - 1 : ℕ) : ℝ) * r)) := by
  rw [integral_tsum_sq_eq_of_tree_radial_bound hInt hbound hr hsmall]
  exact tsum_le_of_tree_radial_le (fun v => integral_nonneg (fun ω => sq_nonneg _))
    hbound hr hsmall

theorem integral_tsum_sq_cutoff_le_of_tree_radial_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : TreeVertex d → Ω → ℝ} {C r : ℝ}
    (hInt : ∀ v, Integrable (fun ω => A v ω ^ 2) P)
    (hbound : ∀ v, (∫ ω, A v ω ^ 2 ∂P) ≤ C * r ^ v.1.length)
    (hr : 0 ≤ r) (hsmall : ((d - 1 : ℕ) : ℝ) * r < 1) (L : ℕ) :
    (∫ ω, ∑' v : TreeVertex d, if L < v.1.length then A v ω ^ 2 else 0 ∂P) ≤
      C * ((d : ℝ) * r * (((d - 1 : ℕ) : ℝ) * r) ^ L /
        (1 - ((d - 1 : ℕ) : ℝ) * r)) := by
  have hcutInt (v : TreeVertex d) :
      Integrable (fun ω => if L < v.1.length then A v ω ^ 2 else 0) P := by
    by_cases hv : L < v.1.length
    · simpa only [hv, ite_true] using hInt v
    · simp only [hv, ite_false]
      exact integrable_zero Ω ℝ P
  have hs : Summable (fun v => ∫ ω, A v ω ^ 2 ∂P) :=
    summable_of_tree_radial_le (fun v => integral_nonneg (fun ω => sq_nonneg _)) hbound hr hsmall
  have hcutSum : Summable (fun v => ∫ ω, ‖if L < v.1.length then A v ω ^ 2 else 0‖ ∂P) := by
    apply hs.of_nonneg_of_le (fun v => integral_nonneg (fun ω => norm_nonneg _))
    intro v
    by_cases hv : L < v.1.length
    · simp only [hv, ite_true, Real.norm_eq_abs, abs_pow, sq_abs]
      exact le_rfl
    · simp only [hv, ite_false, norm_zero, integral_zero]
      exact integral_nonneg (fun ω => sq_nonneg _)
  rw [← integral_tsum_of_summable_integral_norm hcutInt hcutSum]
  have heq : (fun v : TreeVertex d => ∫ ω, (if L < v.1.length then A v ω ^ 2 else 0) ∂P) =
      (fun v => if L < v.1.length then (∫ ω, A v ω ^ 2 ∂P) else 0) := by
    funext v
    split_ifs <;> simp
  rw [heq]
  exact tsum_cutoff_le_of_tree_radial_le (fun v => integral_nonneg (fun ω => sq_nonneg _))
    hbound hr hsmall L

end Problem367

end

end OAI
