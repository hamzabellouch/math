import OAI.Probability.DilutedSpin.HeterogeneousMarks

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
attribute [local instance] DilutedSpinGlass.instMeasurableSpaceCarrier_challenge DilutedSpinGlass.instBorelSpaceCarrier_challenge
open Set
namespace DilutedSpinGlass.CountableReservoir
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {I : Type} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

/-- Conditional iid type/site labels, on the full fixed countable dictionary. -/
noncomputable def average (F : (n : ℕ) → (Fin n → I) → ℝ) (n : ℕ) : ℝ :=
  ∫ roots, F n roots ∂Measure.pi (fun _ : Fin n => ν)

/-- Poisson total count and iid countable labels. Marks remain in their finite,
label-dependent prior rows and are not part of this quenched root law. -/
noncomputable def poissonAverage (s : ℝ≥0) (F : (n : ℕ) → (Fin n → I) → ℝ) : ℝ :=
  ∫ n, average ν F n ∂poissonMeasure s

theorem integrable_row {n : ℕ} {f : (Fin n → I) → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) : Integrable f (Measure.pi (fun _ : Fin n => ν)) := by
  apply (integrable_const B).mono' (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hf x)

omit [Countable I] [MeasurableSingletonClass I] in
theorem abs_average_le {F : (n : ℕ) → (Fin n → I) → ℝ} {n : ℕ} {B : ℝ}
    (hB : ∀ x, |F n x| ≤ B) : |average ν F n| ≤ B := by
  simpa only [average, Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin n => ν))
      (f := F n) (C := B) (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hB x)))

omit [Countable I] [MeasurableSingletonClass I] in
theorem integrable_average (s : ℝ≥0) {F : (n : ℕ) → (Fin n → I) → ℝ} {A B : ℝ}
    (hF : ∀ n x, |F n x| ≤ A+B*n) : Integrable (average ν F) (poissonMeasure s) :=
  poisson_integrable_linear s (fun n => abs_average_le ν (hF n))

omit [Countable I] [MeasurableSingletonClass I] in
/-- The expected sum over a fixed iid list is exactly count times type mean. -/
theorem integral_sum_labels (n : ℕ) {D : I → ℝ} (hD : Integrable D ν) :
    (∫ roots : Fin n → I, ∑ q, D (roots q) ∂Measure.pi (fun _ : Fin n => ν)) =
      (n : ℝ) * ∫ i, D i ∂ν := by
  rw [integral_finsetSum _ (fun _ _ => integrable_comp_eval hD)]
  simp only [integral_comp_eval (μ := fun _ : Fin n => ν) hD.aestronglyMeasurable, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A common-law comparison is averaged without replacing the full root law
by the low types. The expected number of deleted factors is retained exactly. -/
theorem poissonAverage_sum_stability (s : ℝ≥0)
    {F G : (n : ℕ) → (Fin n → I) → ℝ} {A B : ℝ} {D : I → ℝ}
    (hF : ∀ n x, |F n x| ≤ A+B*n) (hG : ∀ n x, |G n x| ≤ A+B*n)
    (hD : Integrable D ν)
    (hdiff : ∀ n roots, |F n roots-G n roots| ≤ ∑ q, D (roots q)) :
    |poissonAverage ν s F-poissonAverage ν s G| ≤ (s : ℝ)*(∫ i, D i ∂ν) := by
  have hrow (n : ℕ) : |average ν F n-average ν G n| ≤ (n : ℝ)*(∫ i, D i ∂ν) := by
    unfold average
    rw [← integral_sub (integrable_row ν (hF n)) (integrable_row ν (hG n))]
    have hiD : Integrable (fun roots : Fin n → I => ∑ q, D (roots q))
        (Measure.pi (fun _ : Fin n => ν)) :=
      integrable_finsetSum _ (fun _ _ => integrable_comp_eval hD)
    have hb := integral_mono ((integrable_row ν (hF n)).sub (integrable_row ν (hG n))).norm
      hiD (fun roots => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hdiff n roots)
    have hn := norm_integral_le_integral_norm (μ := Measure.pi (fun _ : Fin n => ν))
      (fun roots => F n roots-G n roots)
    rw [integral_sum_labels ν n hD] at hb
    simpa only [Real.norm_eq_abs] using hn.trans hb
  unfold poissonAverage
  rw [← integral_sub (integrable_average ν s hF) (integrable_average ν s hG)]
  have hb := integral_mono ((integrable_average ν s hF).sub (integrable_average ν s hG)).norm
    ((poisson_integrable_count s).mul_const (∫ i, D i ∂ν))
    (fun n => by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hrow n)
  rw [integral_mul_const, poisson_mean] at hb
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (μ := poissonMeasure s)
      (fun n => average ν F n-average ν G n)).trans hb

end DilutedSpinGlass.CountableReservoir

namespace DilutedSpinGlass.HeterogeneousMarks
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {Ω I : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν] {L : ℕ}

/-- The literal marked-Poisson pressure, with every type in the same law. -/
noncomputable def pressure (s : ℝ≥0) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ) : ℝ :=
  CountableReservoir.poissonAverage ν s (fun _ roots => root T Q m base roots factor)

/-- A finite-type truncation is controlled uniformly in all other disorder and
parameters. The right side is the expected deleted log-factor mass. -/
theorem pressure_mask_bound (s : ℝ≥0) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (keep : I → Prop) [DecidablePred keep] {C : ℝ} (hC : 0 ≤ C)
    (hfactor : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |pressure ν s T Q m base factor -
      pressure ν s T Q m base (fun i x y => if keep i then factor i x y else 1)| ≤
        (s : ℝ) * ∫ i, (if keep i then 0 else C) ∂ν := by
  have hmasked : ∀ i x y, |Real.log (if keep i then factor i x y else 1)| ≤ C := by
    intro i x y
    by_cases hi : keep i
    · simpa only [hi, ↓reduceIte] using hfactor i x y
    · simpa only [hi, ↓reduceIte, Real.log_one, abs_zero] using hC
  apply CountableReservoir.poissonAverage_sum_stability ν s
    (fun n roots => abs_root_le T Q m hm base roots factor hfactor)
    (fun n roots => abs_root_le T Q m hm base roots _ hmasked)
  · apply (integrable_const C).mono' (measurable_of_countable _).aestronglyMeasurable
    exact ae_of_all _ (fun i => by split_ifs <;> simp_all only [norm_zero, Real.norm_eq_abs, abs_of_nonneg, le_refl])
  · intro n roots
    exact root_mask_bound T Q m hm base roots factor keep (fun _ => C) hfactor

/-- The entire countable perturbation costs at most its total expected count
 times the per-factor log bound. No finite-cutoff telescope is used. -/
theorem pressure_base_bound (s : ℝ≥0) (T : KernelTower Ω L)
    (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ) (hm : ∀ j, 0 < m j)
    (base : FinitePath Ω L → ℝ)
    (factor : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hfactor : ∀ i x y, |Real.log (factor i x y)| ≤ C) :
    |pressure ν s T Q m base factor - KernelTower.backwardLog L T m base| ≤ (s : ℝ)*C := by
  have h := pressure_mask_bound ν s T Q m hm base factor (fun _ => False) hC hfactor
  simpa only [↓reduceIte, pressure, CountableReservoir.poissonAverage,
    CountableReservoir.average, root_one, integral_const, probReal_univ,
    smul_eq_mul, one_mul] using h

end DilutedSpinGlass.HeterogeneousMarks

namespace DilutedSpinGlass.CountableReservoir
open MeasureTheory Filter
open scoped Topology

/-- The truncation error tends to zero for every fixed full type law. This
uses only total probability one, never a special fast decay of the weights. -/
theorem tail_integral_tendsto (ν : Measure ℕ) [IsProbabilityMeasure ν] {C : ℝ} (hC : 0 ≤ C) :
    Tendsto (fun K : ℕ => ∫ i : ℕ, (if i < K then 0 else C) ∂ν) atTop (𝓝 0) := by
  have hlim (i : ℕ) : Tendsto (fun K : ℕ => if i < K then (0 : ℝ) else C) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with K hK
    simp only [hK, ↓reduceIte]
  have h := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : ℕ => C)
    (F := fun K i : ℕ => if i < K then (0 : ℝ) else C) (f := fun _ => (0 : ℝ))
    (fun _ => (measurable_of_countable _).aestronglyMeasurable) (integrable_const C)
    (fun K => ae_of_all _ (fun i => by split_ifs <;> simp_all only [norm_zero, Real.norm_eq_abs, abs_of_nonneg, le_refl]))
    (ae_of_all _ hlim)
  simpa only [integral_zero] using h

end DilutedSpinGlass.CountableReservoir

namespace DilutedSpinGlass.CountableReservoir
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
variable {I : Type} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (ν : Measure I) [IsProbabilityMeasure ν]

omit [Countable I] [MeasurableSingletonClass I] in
/-- The countable root labels are genuinely iid under finite permutations. -/
theorem integral_pi_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : (Fin n → I) → ℝ) :
    (∫ roots, f (roots ∘ σ) ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ roots, f roots ∂Measure.pi (fun _ : Fin n => ν) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) σ).symm.integral_comp' f
  exact h

/-- A new label has precisely the same independent law as each old label. -/
theorem integral_pi_cons (n : ℕ) (f : (Fin (n+1) → I) → ℝ) {B : ℝ}
    (hf : ∀ roots, |f roots| ≤ B) :
    (∫ roots, f roots ∂Measure.pi (fun _ : Fin (n+1) => ν)) =
      ∫ i, ∫ roots, f (Fin.cons i roots) ∂Measure.pi (fun _ : Fin n => ν) ∂ν := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm.integral_comp' f
  have he : ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => I) 0).symm :
      I × (Fin n → I) → (Fin (n+1) → I)) =
      (fun z : I × (Fin n → I) => Fin.cons z.1 z.2) := by
    funext labels
    exact Fin.insertNth_zero' labels.1 labels.2
  rw [he] at h
  rw [← h]
  apply integral_prod
  apply (integrable_const B).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hf (Fin.cons z.1 z.2))

omit [Countable I] [MeasurableSingletonClass I] in
theorem integral_pi_equivariant {n : ℕ} (F : (Fin n → I) → Fin n → ℝ)
    (hF : ∀ (σ : Equiv.Perm (Fin n)) roots q, F (roots ∘ σ) q = F roots (σ q))
    (q q' : Fin n) :
    (∫ roots, F roots q ∂Measure.pi (fun _ : Fin n => ν)) =
      ∫ roots, F roots q' ∂Measure.pi (fun _ : Fin n => ν) := by
  classical
  rw [← integral_pi_perm ν (Equiv.swap q q') (fun roots => F roots q)]
  apply integral_congr_ae
  exact ae_of_all _ (fun roots => by
    dsimp only
    rw [hF, Equiv.swap_apply_left])

/-- Palm for the full shared countable reservoir. It does not delete the
selected type or truncate the other types in the remaining law. -/
theorem poisson_add_label (s : ℝ≥0)
    (F : (n : ℕ) → (Fin n → I) → Fin n → ℝ) {B : ℝ}
    (hB : ∀ n roots q, |F n roots q| ≤ B)
    (hF : ∀ n (σ : Equiv.Perm (Fin n)) roots q, F n (roots ∘ σ) q = F n roots (σ q)) :
    (∫ n : ℕ, ∫ roots, ∑ q, F n roots q
      ∂Measure.pi (fun _ : Fin n => ν) ∂poissonMeasure s) =
      (s : ℝ) * ∫ n : ℕ, ∫ i, ∫ roots, F (n+1) (Fin.cons i roots) 0
        ∂Measure.pi (fun _ : Fin n => ν) ∂ν ∂poissonMeasure s := by
  let a : ℕ → ℝ := fun n => if h : 0 < n then
    ∫ roots, F n roots ⟨0,h⟩ ∂Measure.pi (fun _ : Fin n => ν) else 0
  have ha (n : ℕ) : a (n+1) =
      ∫ roots, F (n+1) roots 0 ∂Measure.pi (fun _ : Fin (n+1) => ν) := by
    simp only [a, Nat.zero_lt_succ, ↓reduceDIte]
    rfl
  have hsum (n : ℕ) :
      (∫ roots, ∑ q, F n roots q ∂Measure.pi (fun _ : Fin n => ν)) = (n : ℝ)*a n := by
    rw [integral_finsetSum _ (fun q _ => integrable_row ν (fun roots => hB n roots q))]
    by_cases hn : 0 < n
    · simp only [a, dite_eq_left hn]
      rw [show (fun q : Fin n => ∫ roots, F n roots q ∂Measure.pi (fun _ : Fin n => ν)) =
        (fun _ : Fin n => ∫ roots, F n roots ⟨0,hn⟩ ∂Measure.pi (fun _ : Fin n => ν)) from
          funext (fun q => integral_pi_equivariant ν (F n) (hF n) q ⟨0,hn⟩)]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp
  have hi : Integrable (fun n => a (n+1)) (poissonMeasure s) := by
    apply poisson_integrable_linear s (A := B) (B := 0)
    intro n
    rw [ha]
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one, zero_mul, add_zero] using
      (norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin (n+1) => ν))
        (f := fun roots => F (n+1) roots 0) (C := B)
        (ae_of_all _ (fun roots => by simpa only [Real.norm_eq_abs] using hB (n+1) roots 0)))
  simp_rw [hsum]
  rw [poisson_add_one s a hi]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    rw [ha]
    exact integral_pi_cons ν n (fun roots => F (n+1) roots 0) (fun roots => hB (n+1) roots 0))

end DilutedSpinGlass.CountableReservoir

end

end OAI
