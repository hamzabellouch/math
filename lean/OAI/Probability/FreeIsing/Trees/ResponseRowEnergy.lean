import OAI.Probability.FreeIsing.Energy.CoupledResponseRows

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.ResponseRows

theorem summable_weighted_tree_profile {d : ℕ} (theta : ℝ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n => regularPathWeight d theta n * f (n + 1))) :
    Summable (fun v : TreeVertex d => theta ^ (2 * v.1.length) * f v.1.length) := by
  have hp (n : ℕ) : 0 ≤ theta ^ (2 * n) := by
    rw [pow_mul]
    positivity
  apply (summable_radial_iff d (fun n => theta ^ (2 * n) * f n)
    (fun n => mul_nonneg (hp n) (hf n))).mpr
  apply (summable_nat_add_iff 1).mp
  simpa only [regularPathWeight, mul_assoc] using hs

theorem tsum_weighted_tree_profile {d : ℕ} (theta : ℝ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n)
    (hs : Summable (fun n => regularPathWeight d theta n * f (n + 1))) :
    (∑' v : TreeVertex d, theta ^ (2 * v.1.length) * f v.1.length) =
      f 0 + ∑' n, regularPathWeight d theta n * f (n + 1) := by
  have hrad := summable_weighted_tree_profile theta f hf hs
  rw [tsum_radial d (fun n => theta ^ (2 * n) * f n) hrad]
  have hp (n : ℕ) : 0 ≤ theta ^ (2 * n) * f n := by
    have he : 0 ≤ theta ^ (2 * n) := by rw [pow_mul]; positivity
    exact mul_nonneg he (hf n)
  have hshell := (summable_radial_iff d (fun n => theta ^ (2 * n) * f n) hp).mp hrad
  rw [hshell.tsum_eq_zero_add]
  simp only [card_treeShell_zero, Nat.cast_one, mul_zero, pow_zero, one_mul]
  congr 1
  apply tsum_congr
  intro n
  simp only [regularPathWeight, mul_assoc]

def shellProfile (root : ℝ) (tail : ℕ → ℝ) : ℕ → ℝ
  | 0 => root
  | n + 1 => tail n

@[simp] theorem shellProfile_zero (root : ℝ) (tail : ℕ → ℝ) :
    shellProfile root tail 0 = root := rfl

@[simp] theorem shellProfile_succ (root : ℝ) (tail : ℕ → ℝ) (n : ℕ) :
    shellProfile root tail (n + 1) = tail n := rfl

theorem summable_and_tsum_le_shell_budget
    {d : ℕ} (theta : ℝ) {F : TreeVertex d → ℝ} {root : ℝ} {tail : ℕ → ℝ}
    (hF : ∀ v, 0 ≤ F v) (hroot : 0 ≤ root) (htail : ∀ n, 0 ≤ tail n)
    (hs : Summable (fun n => regularPathWeight d theta n * tail n))
    (hzero : ∀ v : TreeVertex d, v.1.length = 0 → F v ≤ root)
    (hpos : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 →
      F v ≤ theta ^ (2 * (n + 1)) * tail n) :
    Summable F ∧ (∑' v, F v) ≤ root + ∑' n, regularPathWeight d theta n * tail n := by
  let f := shellProfile root tail
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    cases n with
    | zero => exact hroot
    | succ n => exact htail n
  have hsum : Summable (fun n => regularPathWeight d theta n * f (n + 1)) := hs
  have hrad := summable_weighted_tree_profile theta f hf hsum
  have hbound (v : TreeVertex d) : F v ≤ theta ^ (2 * v.1.length) * f v.1.length := by
    cases he : v.1.length with
    | zero => simpa only [f, shellProfile_zero, mul_zero, pow_zero, one_mul] using hzero v he
    | succ n => exact hpos n v he
  have hFs := Summable.of_nonneg_of_le hF hbound hrad
  refine ⟨hFs, ?_⟩
  calc
    (∑' v, F v) ≤ ∑' v : TreeVertex d, theta ^ (2 * v.1.length) * f v.1.length :=
      hFs.tsum_le_tsum hbound hrad
    _ = root + ∑' n, regularPathWeight d theta n * tail n :=
      tsum_weighted_tree_profile theta f hf hsum

theorem weighted_energy_shell_bound
    {d : ℕ} (theta : ℝ) {E : TreeVertex d → ℝ} {root : ℝ} {tail : ℕ → ℝ}
    (hE : ∀ v, 0 ≤ E v) (hroot : 0 ≤ root) (htail : ∀ n, 0 ≤ tail n)
    (hs : Summable (fun n => regularPathWeight d theta n * tail n))
    (hzero : ∀ v : TreeVertex d, v.1.length = 0 → E v ≤ root)
    (hpos : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 → E v ≤ tail n) :
    Summable (fun v : TreeVertex d => (theta ^ v.1.length) ^ 2 * E v) ∧
      (∑' v : TreeVertex d, (theta ^ v.1.length) ^ 2 * E v) ≤
        root + ∑' n, regularPathWeight d theta n * tail n := by
  apply summable_and_tsum_le_shell_budget theta
    (fun v => mul_nonneg (sq_nonneg _) (hE v)) hroot htail hs
  · intro v hv
    simpa only [hv, pow_zero, one_pow, one_mul] using hzero v hv
  · intro n v hv
    rw [hv]
    have hp : (theta ^ (n + 1)) ^ 2 = theta ^ (2 * (n + 1)) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hp]
    exact mul_le_mul_of_nonneg_left (hpos n v hv) (by rw [pow_mul]; positivity)

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

@[simp] theorem pathNoiseEnergy_empty {ι : Type*} (theta : ℝ) (X Y : ι → Ω → ℝ) :
    pathNoiseEnergy μ theta ∅ X Y = 0 := by
  simp [pathNoiseEnergy, pathProduct, pathLogDiff]

@[simp] theorem pathLinearEnergy_empty {ι : Type*} (theta : ℝ) (X : ι → Ω → ℝ)
    (U : Ω → ℝ) : pathLinearEnergy μ theta ∅ X U = ∫ ω, U ω ^ 2 ∂μ := by
  simp [pathLinearEnergy, pathProduct]

theorem pathNoiseEnergy_nonneg {ι : Type*} (theta : ℝ) (s : Finset ι)
    (X Y : ι → Ω → ℝ) : 0 ≤ pathNoiseEnergy μ theta s X Y :=
  integral_nonneg (fun _ => mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))

theorem pathLinearEnergy_nonneg {ι : Type*} (theta : ℝ) (s : Finset ι)
    (X : ι → Ω → ℝ) (U : Ω → ℝ) : 0 ≤ pathLinearEnergy μ theta s X U :=
  integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem integral_tree_density_le_shell_energies
    {d : ℕ} {ι : Type*} (s : TreeVertex d → Finset ι)
    (hcard : ∀ v, (s v).card = v.1.length)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : TreeVertex d → ι → Ω → ℝ} {H H' : Ω → ℝ}
    (hX : ∀ v i, i ∈ s v → Measurable (X v i))
    (hY : ∀ v i, i ∈ s v → Measurable (Y v i))
    (hInt : ∀ v i, i ∈ s v → Integrable (fun ω => (X v i ω - Y v i ω) ^ 2) μ)
    (hH : Measurable H) (hH' : Measurable H')
    (hU : MemLp (fun ω => H ω - H' ω) 2 μ)
    {Q L : ℕ → ℝ} (hQ0 : ∀ n, 0 ≤ Q n) (hL0 : ∀ n, 0 ≤ L n)
    (hQ : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 →
      pathNoiseEnergy μ theta (s v) (X v) (Y v) ≤ Q n)
    (hL : ∀ (n : ℕ) (v : TreeVertex d), v.1.length = n + 1 →
      pathLinearEnergy μ theta (s v) (X v) (fun ω => H ω - H' ω) ≤ L n)
    (hQs : Summable (fun n => regularPathWeight d theta n * Q n))
    (hLs : Summable (fun n => regularPathWeight d theta n * L n))
    (hRs : Summable (fun n => regularPathWeight d theta n * Real.sqrt (Q n)))
    (hrows : ∀ᵐ ω ∂μ,
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X v ω) ^ 2) ∧
      Summable (fun v => (coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y v ω) ^ 2)) :
    let c := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s X
    let c' := coefficient theta (fun v : TreeVertex d => theta ^ v.1.length) s Y
    Integrable (DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω))) μ ∧
    (∫ ω, DiscrepancyEnergy.density c c' (fun ω => H ω - H' ω)
      (fun ω => Real.tanh (H ω)) (fun ω => Real.tanh (H' ω)) ω ∂μ) ≤
      2 * (∫ ω, (H ω - H' ω) ^ 2 ∂μ) + ∑' n, regularPathWeight d theta n *
        (Q n + 2 * L n + 4 * Real.sqrt (2 * ∫ ω, (H ω - H' ω) ^ 2 ∂μ) *
          Real.sqrt (Q n)) := by
  dsimp only
  let U := fun ω => H ω - H' ω
  let V := ∫ ω, U ω ^ 2 ∂μ
  let A := fun v => pathNoiseEnergy μ theta (s v) (X v) (Y v)
  let B := fun v => pathLinearEnergy μ theta (s v) (X v) U
  let K := 4 * Real.sqrt (2 * V)
  have hV : 0 ≤ V := integral_nonneg (fun ω => sq_nonneg _)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hempty (v : TreeVertex d) (hv : v.1.length = 0) : s v = ∅ :=
    Finset.card_eq_zero.mp ((hcard v).trans hv)
  have hA0 (v : TreeVertex d) (hv : v.1.length = 0) : A v = 0 := by
    simp only [A, hempty v hv, pathNoiseEnergy_empty]
  have hB0 (v : TreeVertex d) (hv : v.1.length = 0) : B v = V := by
    simp only [B, hempty v hv, pathLinearEnergy_empty, V]
  have hAb := weighted_energy_shell_bound theta
    (fun v => pathNoiseEnergy_nonneg theta (s v) (X v) (Y v))
    (le_refl (0 : ℝ)) hQ0 hQs (fun v hv => (hA0 v hv).le) hQ
  have hBb := weighted_energy_shell_bound theta
    (fun v => pathLinearEnergy_nonneg theta (s v) (X v) U)
    hV hL0 hLs (fun v hv => (hB0 v hv).le) hL
  have hRb := weighted_energy_shell_bound theta
    (fun v => Real.sqrt_nonneg (A v)) (le_refl (0 : ℝ))
    (fun n => Real.sqrt_nonneg (Q n)) hRs
    (fun v hv => by rw [hA0 v hv, Real.sqrt_zero])
    (fun n v hv => Real.sqrt_le_sqrt (hQ n v hv))
  have hb := integral_density_le_path_energies s (fun v : TreeVertex d => theta ^ v.1.length)
    hθ hX hY hInt hH hH' hU hAb.1 hBb.1 hRb.1 hrows
  refine ⟨hb.1, hb.2.trans ?_⟩
  have hsum : (∑' n, regularPathWeight d theta n *
      (Q n + 2 * L n + K * Real.sqrt (Q n))) =
      (∑' n, regularPathWeight d theta n * Q n) +
      2 * (∑' n, regularPathWeight d theta n * L n) +
      K * (∑' n, regularPathWeight d theta n * Real.sqrt (Q n)) := by
    calc
      _ = ∑' n, ((regularPathWeight d theta n * Q n +
          2 * (regularPathWeight d theta n * L n)) +
          K * (regularPathWeight d theta n * Real.sqrt (Q n))) := by
        apply tsum_congr
        intro n
        ring
      _ = _ := by
        rw [(hQs.add (hLs.mul_left 2)).tsum_add (hRs.mul_left K),
          hQs.tsum_add (hLs.mul_left 2), tsum_mul_left, tsum_mul_left]
  change (∑' v, (theta ^ v.1.length) ^ 2 * A v) +
      2 * (∑' v, (theta ^ v.1.length) ^ 2 * B v) +
      K * (∑' v, (theta ^ v.1.length) ^ 2 * Real.sqrt (A v)) ≤ _
  calc
    _ ≤ (0 + ∑' n, regularPathWeight d theta n * Q n) +
        2 * (V + ∑' n, regularPathWeight d theta n * L n) +
        K * (0 + ∑' n, regularPathWeight d theta n * Real.sqrt (Q n)) :=
      add_le_add (add_le_add hAb.2 (mul_le_mul_of_nonneg_left hBb.2 (by norm_num)))
        (mul_le_mul_of_nonneg_left hRb.2 hK)
    _ = 2 * V + ∑' n, regularPathWeight d theta n *
        (Q n + 2 * L n + K * Real.sqrt (Q n)) := by rw [hsum]; ring

end Probability

end Problem367.ResponseRows

end

end OAI
