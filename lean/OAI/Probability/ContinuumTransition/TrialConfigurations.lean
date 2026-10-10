import OAI.Probability.ContinuumTransition.GeneralLabels

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

noncomputable section

noncomputable def gridPoint (q : ℝ) (i : Lattice) : Space :=
  WithLp.toLp 2 (fun k => q * (i k : ℝ))

def trialBall (q : ℝ) (i : Lattice) : Set Space := Metric.ball (gridPoint q i) (q / 8)

theorem trialBall_coord {q : ℝ} {i : Lattice} {x : Space} (hx : x ∈ trialBall q i)
    (k : Fin 3) : |x k - q * (i k : ℝ)| < q / 8 := by
  have hh := PiLp.norm_apply_le (x - gridPoint q i) k
  have hd : ‖x - gridPoint q i‖ < q / 8 := by
    simpa only [trialBall, Metric.mem_ball, dist_eq_norm] using hx
  have hc : |x k - q * (i k : ℝ)| ≤ ‖x - gridPoint q i‖ := by
    simpa [gridPoint] using hh
  exact hc.trans_lt hd

theorem trialBall_separation {q : ℝ} (hq : 0 < q) {i j : Lattice} (hij : i ≠ j)
    {x y : Space} (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) :
    3 * q / 4 < ‖x - y‖ := by
  obtain ⟨k, hk⟩ : ∃ k, i k ≠ j k := by
    by_contra! h
    exact hij (funext h)
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hc : |x k - y k| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  rw [abs_lt] at hxk hyk
  rw [abs_le] at hc
  rcases lt_or_gt_of_ne hk with h | h
  · have hh : (i k : ℝ) + 1 ≤ (j k : ℝ) := by exact_mod_cast h
    nlinarith
  · have hh : (j k : ℝ) + 1 ≤ (i k : ℝ) := by exact_mod_cast h
    nlinarith

theorem trialBall_disjoint {q : ℝ} (hq : 0 < q) :
    Pairwise (fun i j : Lattice => Disjoint (trialBall q i) (trialBall q j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hh := trialBall_separation hq hij hi hj
  simp only [sub_self, norm_zero] at hh
  linarith

noncomputable def gridRadius (q : ℝ) : ℤ := ⌈q⁻¹ + 1⌉

noncomputable def gridNeighbors (q : ℝ) (i : Lattice) : Finset Lattice :=
  Fintype.piFinset (fun k => Finset.Icc (i k - gridRadius q) (i k + gridRadius q))

theorem mem_gridNeighbors_iff {q : ℝ} {i j : Lattice} :
    j ∈ gridNeighbors q i ↔ ∀ k, |j k - i k| ≤ gridRadius q := by
  simp only [gridNeighbors, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]
  constructor <;> intro h k <;> have hh := h k <;> constructor <;> omega

theorem trialBall_close_mem {q : ℝ} (hq : 0 < q) {i j : Lattice} {x y : Space}
    (hx : x ∈ trialBall q i) (hy : y ∈ trialBall q j) (hxy : ‖x-y‖ < 1) :
    j ∈ gridNeighbors q i := by
  rw [mem_gridNeighbors_iff]
  intro k
  have hxk := trialBall_coord hx k
  have hyk := trialBall_coord hy k
  have hn : |x k - y k| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) k
  have hc : |x k - y k| < 1 := hn.trans_lt hxy
  have hceil : q⁻¹ + 1 ≤ (gridRadius q : ℝ) := Int.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil hq.le
  have hcancel : q * (q⁻¹ + 1) = 1 + q := by field_simp
  rw [hcancel] at hmul
  have hh : |((j k : ℤ) : ℝ) - (i k : ℝ)| ≤ (gridRadius q : ℝ) := by
    rw [abs_lt] at hxk hyk hc
    rw [abs_le]
    constructor <;> nlinarith
  exact_mod_cast hh

theorem gridRadius_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ gridRadius q := by
  exact Int.ceil_nonneg (by positivity)

theorem card_gridNeighbors {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (gridNeighbors q i).card = (2 * (gridRadius q).toNat + 1) ^ 3 := by
  have hr := gridRadius_nonneg hq
  simp only [gridNeighbors, Fintype.card_piFinset, Int.card_Icc]
  have hh (k : Fin 3) : (i k + gridRadius q + 1 - (i k - gridRadius q)).toNat =
      2 * (gridRadius q).toNat + 1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem grid_close_card_le {ι : Type u_1} [Fintype ι] {q : ℝ} (hq : 0 < q)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℕ) ≤
      (2 * (gridRadius q).toNat + 1)^3 := by
  classical
  rw [← card_gridNeighbors hq (f i)]
  apply Finset.card_le_card_of_injOn f
  · intro j hj
    exact trialBall_close_mem hq (hx i) (hx j) (Finset.mem_filter.mp hj).2
  · exact hf.injOn

noncomputable def trialEnergyConstant (t q : ℝ) : ℝ :=
  (2 * (gridRadius q).toNat + 1 : ℝ)^3 *
    (t^2 + (Real.exp (-t) / (3*q/4))^12)

theorem trialEnergyConstant_nonneg (t q : ℝ) : 0 ≤ trialEnergyConstant t q := by
  unfold trialEnergyConstant
  positivity

theorem trial_core_row_le {ι : Type u_1} [Fintype ι] [DecidableEq ι] {q t : ℝ} (hq : 0 < q) (ht : 1 < t)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) (i : ι) :
    ∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖) ≤ trialEnergyConstant t q := by
  classical
  let C := t^2 + (Real.exp (-t) / (3*q/4))^12
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum : (∑ j, (if i = j then 0 else coreProfile t ‖x i-x j‖)) ≤
      ∑ j, (if ‖x i-x j‖ < 1 then C else 0) := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij]
      split_ifs <;> positivity
    · rw [ite_eq_right hij]
      by_cases hdist : ‖x i-x j‖ < 1
      · rw [ite_eq_left hdist]
        exact coreProfile_le (by linarith : 0 < 3*q/4)
          (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j)).le t
      · rw [ite_eq_right hdist, coreProfile_eq_zero ht (le_of_not_gt hdist)]
  have hh := grid_close_card_le hq f hf x hx i
  have hcard : ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) ≤
      (2 * (gridRadius q).toNat + 1 : ℝ)^3 := by exact_mod_cast hh
  calc
    _ ≤ _ := hsum
    _ = ((Finset.univ.filter fun j => ‖x i - x j‖ < 1).card : ℝ) * C := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (2 * (gridRadius q).toNat + 1 : ℝ)^3 * C := mul_le_mul_of_nonneg_right hcard hC
    _ = trialEnergyConstant t q := rfl

noncomputable def interiorGrid (q L : ℝ) : Finset Lattice :=
  Fintype.piFinset (fun _ : Fin 3 =>
    Finset.Icc (-(⌊L/(2*q)-1⌋₊ : ℤ)) (⌊L/(2*q)-1⌋₊ : ℤ))

theorem interiorGrid_ball_subset {q L : ℝ} (hq : 0 < q) (hL : 2*q ≤ L)
    {i : Lattice} (hi : i ∈ interiorGrid q L) : trialBall q i ⊆ cube L := by
  intro x hx k
  have hk : -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
    have hh : ∀ k, -(⌊L/(2*q)-1⌋₊ : ℤ) ≤ i k ∧ i k ≤ (⌊L/(2*q)-1⌋₊ : ℤ) := by
      simpa only [interiorGrid, Fintype.mem_piFinset, Finset.mem_Icc] using hi
    exact hh k
  have hk1 : -(⌊L/(2*q)-1⌋₊ : ℝ) ≤ (i k : ℝ) := by exact_mod_cast hk.1
  have hk2 : (i k : ℝ) ≤ (⌊L/(2*q)-1⌋₊ : ℝ) := by exact_mod_cast hk.2
  have hnonneg : 0 ≤ L/(2*q)-1 := by
    have : 1 ≤ L/(2*q) := (le_div_iff₀ (by positivity)).2 (by nlinarith)
    linarith
  have hn := Nat.floor_le hnonneg
  have heq : (L/(2*q)-1)*(2*q) = L-2*q := by field_simp
  have hmul := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 2*q)
  rw [heq] at hmul
  have hxk := trialBall_coord hx k
  rw [abs_lt] at hxk
  constructor <;> nlinarith

theorem card_interiorGrid (q L : ℝ) :
    (interiorGrid q L).card = (2*⌊L/(2*q)-1⌋₊+1)^3 := by
  simp only [interiorGrid, Fintype.card_piFinset, Int.card_Icc]
  have hh : ((⌊L/(2*q)-1⌋₊ : ℤ) + 1 - -(⌊L/(2*q)-1⌋₊ : ℤ)).toNat =
      2*⌊L/(2*q)-1⌋₊+1 := by omega
  simp only [hh, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_interiorGrid_lower {q L : ℝ} (hq : 0 < q) (hL : 8*q ≤ L) :
    (L/(2*q))^3 ≤ ((interiorGrid q L).card : ℝ) := by
  rw [card_interiorGrid]
  push_cast
  have hh := Nat.lt_floor_add_one (L/(2*q)-1)
  have heq : (L/(2*q))*(2*q) = L := by field_simp
  have hmul := mul_lt_mul_of_pos_right hh (by positivity : 0 < 2*q)
  have hL0 : 0 ≤ L := by linarith
  have hden : 0 ≤ L/(2*q) := div_nonneg hL0 (by positivity)
  have hle : L/(2*q) ≤ 2*(⌊L/(2*q)-1⌋₊ : ℝ)+1 := by nlinarith
  exact pow_le_pow_left₀ hden hle 3

theorem exists_trial_sites {q L D : ℝ} (hq : 0 < q) (hL : 8*q ≤ L)
    (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    ∃ f : Fin N → Lattice, Function.Injective f ∧
      ∀ i, trialBall q (f i) ⊆ cube L := by
  have hL0 : 0 ≤ L := by linarith
  have hc : (N : ℝ) ≤ ((interiorGrid q L).card : ℝ) := calc
    _ ≤ D*L^3 := hN
    _ ≤ (2*q)⁻¹ ^ 3 * L^3 := mul_le_mul_of_nonneg_right hD (by positivity)
    _ = (L/(2*q))^3 := by ring
    _ ≤ _ := card_interiorGrid_lower hq hL
  have hcard : Fintype.card (Fin N) ≤ Fintype.card (interiorGrid q L) := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (show N ≤ (interiorGrid q L).card by exact_mod_cast hc)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i
  exact interiorGrid_ball_subset hq (by linarith) (e i).property

def trialVolume (q : ℝ) : ℝ := (q/8)^3 * (Real.pi*4/3)

theorem trialVolume_pos {q : ℝ} (hq : 0 < q) : 0 < trialVolume q := by
  unfold trialVolume
  positivity

theorem real_volume_trialBall {q : ℝ} (hq : 0 < q) (i : Lattice) :
    (volume (trialBall q i)).toReal = trialVolume q := by
  simp only [trialBall, EuclideanSpace.volume_ball_fin_three, trialVolume,
    ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ q/8),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]

theorem symmetricWeight_grid_lower {ι : Type u_1} [Fintype ι] {q t β : ℝ}
    (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β) {φ : ℝ → ℝ}
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (f : ι → Lattice) (hf : Function.Injective f) (x : ι → Space)
    (hx : ∀ i, x i ∈ trialBall q (f i)) :
    Real.exp (-β * (trialEnergyConstant t q * Fintype.card ι)) ≤ symmetricWeight φ β x := by
  classical
  have hdist (i j : ι) (hij : i ≠ j) : 0 < ‖x i-x j‖ :=
    lt_trans (by linarith) (trialBall_separation hq (fun h => hij (hf h)) (hx i) (hx j))
  have hinj : Function.Injective x := by
    intro i j hij
    by_contra hne
    have hh := hdist i j hne
    simp only [hij, sub_self, norm_zero, lt_self_iff_false] at hh
  have hrow (i : ι) : (∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤ trialEnergyConstant t q := by
    apply le_trans _ (trial_core_row_le hq ht f hf x hx i)
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · simp only [ite_eq_left hij, le_refl]
    · simp only [ite_eq_right hij]
      exact hcore _ (hdist i j hij)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  have hsum' : (∑ i, ∑ j, if i = j then 0 else φ ‖x i-x j‖) ≤
      trialEnergyConstant t q * (Fintype.card ι : ℝ) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hsum
  have hpos : 0 ≤ trialEnergyConstant t q * (Fintype.card ι : ℝ) :=
    mul_nonneg (trialEnergyConstant_nonneg t q) (Nat.cast_nonneg _)
  have he : realPairEnergy φ x ≤ trialEnergyConstant t q * Fintype.card ι := by
    unfold realPairEnergy
    nlinarith only [hsum', hpos]
  rw [symmetricWeight, ite_eq_left hinj]
  apply Real.exp_le_exp.mpr
  nlinarith only [he, hβ]

theorem partition_grid_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    {N : ℕ} (f : Fin N → Lattice) (hf : Function.Injective f)
    (hinc : ∀ i, trialBall q (f i) ⊆ cube L) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  classical
  let Bs := fun i : Fin N => trialBall q (f i)
  have hm : ∀ i, MeasurableSet (Bs i) := fun _ => measurableSet_ball
  have hd : Pairwise (fun i j => Disjoint (Bs i) (Bs j)) :=
    fun _ _ hij => trialBall_disjoint hq (fun h => hij (hf h))
  have hfin : ∀ i, volume (Bs i) ≠ ⊤ := fun _ => measure_ball_ne_top
  have hΩ : volume {x : Fin N → Space | ∀ i, x i ∈ cube L} ≠ ⊤ := by
    exact (isCompact_configurations L N).measure_lt_top.ne
  have hi := integral_lower_of_disjoint_assignments volume hm hd hfin
    (show IntegrableOn (fun x : Fin N → Space => symmetricWeight φ β x)
      {x | ∀ i, x i ∈ cube L} (Measure.pi fun _ => volume) by
      simpa only [← volume_pi] using integrableOn_symmetricWeight hφ hβ hstable hΩ)
    (symmetricWeight_nonneg φ β)
    (fun e x hx i => hinc (e i) (hx i))
    (fun e x hx => symmetricWeight_grid_lower hq ht hβ hcore (f ∘ e)
      (hf.comp e.injective) x hx)
  have hv : (∏ i : Fin N, (volume (Bs i)).toReal) = trialVolume q ^ N := by
    simp only [Bs, real_volume_trialBall hq, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  rw [hv, Fintype.card_fin] at hi
  have hn : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [← generalPartition_eq_partition, generalPartition, Fintype.card_fin]
  apply (le_div_iff₀ hn).2
  simpa only [mul_comm, mul_assoc, mul_left_comm, volume_pi] using hi

theorem partition_trial_lower {φ : ℝ → ℝ} (hφ : Measurable (radialPotential φ))
    {q t β B L D : ℝ} (hq : 0 < q) (ht : 1 < t) (hβ : 0 ≤ β)
    (hstable : ∀ (N : ℕ) (x : Fin N → Space),
      ((-B*(N : ℝ) : ℝ) : EReal) ≤ energy φ x)
    (hcore : ∀ r, 0 < r → φ r ≤ coreProfile t r)
    (hL : 8*q ≤ L) (hD : D ≤ (2*q)⁻¹ ^ 3) {N : ℕ} (hN : (N : ℝ) ≤ D*L^3) :
    trialVolume q ^ N * Real.exp (-β*(trialEnergyConstant t q * N)) ≤ partition φ β L N := by
  obtain ⟨f, hf, hinc⟩ := exists_trial_sites hq hL hD hN
  exact partition_grid_lower hφ hq ht hβ hstable hcore f hf hinc

end

end ContinuumTemperature
end

end OAI
