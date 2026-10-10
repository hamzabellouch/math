import OAI.Combinatorics.TreeEdit.SampledSpectrum
import OAI.Combinatorics.TreeEdit.PrimeSupply

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter FiniteProbability

def branching (k : ℕ) : ℕ := 16 * k * k ^ 2
def resolution (k : ℕ) : ℕ := k ^ (8 * k)
def cutoff (k : ℕ) : ℕ := k ^ (12 * k)
def repetitions (k : ℕ) : ℕ := k ^ (52 * k)
noncomputable def Pool (k : ℕ) := {p // p ∈ PrimeSupply.band k 2}
noncomputable instance poolFintype (k : ℕ) : Fintype (Pool k) := inferInstanceAs (Fintype {p // p ∈ PrimeSupply.band k 2})
noncomputable def poolPrime {k : ℕ} (p : Pool k) : ℕ := p.val
noncomputable def residueModulus (k : ℕ) : ℕ := ∏ p : Pool k, poolPrime p

lemma pool_properties {k : ℕ} (p : Pool k) : Nat.Prime (poolPrime p) ∧ k ^ 2 < poolPrime p ∧ poolPrime p ≤ k ^ 3 :=
  PrimeSupply.mem_band p.property

lemma residueModulus_pos (k : ℕ) : 0 < residueModulus k :=
  product_positive _ (fun p => (pool_properties p).1.pos)

noncomputable instance residueModulus_neZero (k : ℕ) : NeZero (residueModulus k) := ⟨(residueModulus_pos k).ne'⟩

lemma parameter_spacing {k : ℕ} (hk : 2 ≤ k) :
    2 * ((k ^ 3) ^ k) ^ 2 < resolution k := by
  have hp : 2 < k ^ (2 * k) := by
    calc
      2 < (2 : ℕ) ^ 4 := by norm_num
      _ ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
      _ ≤ k ^ (2 * k) := pow_le_pow_right₀ (by omega) (by omega)
  have hkpos : 0 < k ^ (6 * k) := pow_pos (by omega) _
  calc
    2 * ((k ^ 3) ^ k) ^ 2 = 2 * k ^ (6 * k) := by
      rw [← pow_mul, ← pow_mul]
      congr 2
      omega
    _ < k ^ (2 * k) * k ^ (6 * k) := Nat.mul_lt_mul_of_pos_right hp hkpos
    _ = resolution k := by rw [← pow_add]; congr 1; omega

lemma probability_error_eventually : ∀ᶠ k : ℕ in atTop,
    (16 * k : ℝ) / (k ^ 2 : ℕ) + ((k ^ 3 : ℕ) : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * k ^ 2) ≤ 1 / 10 := by
  have ht := (tendsto_pow_const_mul_const_pow_of_lt_one 48 (by norm_num : (0 : ℝ) ≤ 4 / 5) (by norm_num : (4 / 5 : ℝ) < 1)).eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 20)
  filter_upwards [ht, eventually_ge_atTop 320] with k ht hk
  have hkreal : (320 : ℝ) ≤ k := by exact_mod_cast hk
  have hka : 1 ≤ k := by omega
  have hksq : k ≤ k ^ 2 := by simpa only [pow_one] using pow_le_pow_right₀ hka (show 1 ≤ 2 by omega)
  have hb : (k : ℝ) ^ 48 * (4 / 5 : ℝ) ^ (k ^ 2) ≤ 1 / 20 := by
    calc
      _ ≤ (k : ℝ) ^ 48 * (4 / 5 : ℝ) ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hksq) (by positivity)
      _ ≤ _ := ht.le
  have hpow : ((k ^ 3 : ℕ) : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * k ^ 2) ≤ 1 / 20 := by
    calc
      _ = ((k : ℝ) ^ 48 * (4 / 5 : ℝ) ^ (k ^ 2)) ^ k := by
        push_cast
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> ring
      _ ≤ (1 / 20 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) hb _
      _ ≤ (1 / 20 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hka
      _ = _ := pow_one _
  have hfrac : (16 * k : ℝ) / (k ^ 2 : ℕ) ≤ 1 / 20 := by
    push_cast
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)).mpr
    nlinarith
  linarith

lemma torus_parameters_eventually : ∀ᶠ k : ℕ in atTop,
    2 ≤ k ∧ ∃ _ : Fin (16 * k) ↪ Pool k,
      (∀ p : Pool k, 10 ≤ poolPrime p) ∧
      (∀ p : Pool k, 2 * (resolution k : ℝ)⁻¹ * poolPrime p < 1) ∧
      2 * (resolution k : ℝ)⁻¹ * (((k ^ 3) ^ k : ℕ) : ℝ) ^ 2 < 1 ∧
      (16 * k : ℝ) / Fintype.card (Pool k) + ((k ^ 3 : ℕ) : ℝ) ^ (16 * k) * (4 / 5 : ℝ) ^ (k * k ^ 2) ≤ 1 / 10 := by
  filter_upwards [PrimeSupply.eventually_band_card 2 (by omega), probability_error_eventually,
    eventually_ge_atTop 320] with k hcard herr hk
  have hk2 : 2 ≤ k := by omega
  have hcard' : k ^ 2 ≤ Fintype.card (Pool k) := by
    rw [show Fintype.card (Pool k) = (PrimeSupply.band k 2).card from Fintype.card_coe (PrimeSupply.band k 2)]
    exact hcard
  have h16 : 16 * k ≤ Fintype.card (Pool k) := by nlinarith
  obtain ⟨j⟩ := Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin (16 * k)) ≤ Fintype.card (Pool k) by simpa using h16)
  have hR : 0 < resolution k := pow_pos (by omega) _
  have hRr : (0 : ℝ) < resolution k := by exact_mod_cast hR
  have hε : 2 * (resolution k : ℝ)⁻¹ * (((k ^ 3) ^ k : ℕ) : ℝ) ^ 2 < 1 := by
    have hh : (2 : ℝ) * ((((k ^ 3) ^ k) ^ 2 : ℕ) : ℝ) < resolution k := by exact_mod_cast parameter_spacing hk2
    push_cast at hh ⊢
    field_simp
    nlinarith
  refine ⟨hk2, j, ?_, ?_, hε, ?_⟩
  · intro p
    have hp := (pool_properties p).2.1
    nlinarith
  · intro p
    have hp := (pool_properties p).2.2
    have hu : k ^ 3 ≤ ((k ^ 3) ^ k) ^ 2 := by
      calc
        _ = (k ^ 3) ^ 1 := by simp
        _ ≤ (k ^ 3) ^ (k * 2) := pow_le_pow_right₀ (one_le_pow₀ (by omega)) (by omega)
        _ = _ := pow_mul ..
    have hh : (poolPrime p : ℝ) ≤ (((k ^ 3) ^ k : ℕ) : ℝ) ^ 2 := by exact_mod_cast hp.trans hu
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_lt hε
  · apply le_trans _ herr
    gcongr

lemma good_halfturn_eventually : ∀ᶠ k : ℕ in atTop, 2 ≤ k ∧
    ∃ (j : Fin (16 * k) ↪ Pool k) (C : Config (Pool k) (residueModulus k) (branching k) k),
      Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2) := by
  filter_upwards [torus_parameters_eventually] with k hk
  obtain ⟨hk2, j, hr10, hgrid, hε, herr⟩ := hk
  refine ⟨hk2, j, ?_⟩
  have hhalf : (resolution k : ℝ)⁻¹ ≤ ‖point 2‖ := by
    have hR : 2 ≤ resolution k := by
      calc
        2 ≤ k := hk2
        _ = k ^ 1 := by simp
        _ ≤ resolution k := pow_le_pow_right₀ (by omega) (by omega)
    have hn : ‖point 2‖ = (1 / 2 : ℝ) := by
      dsimp [point]
      simpa using AddCircle.norm_half_period_eq (1 : ℝ)
    rw [hn]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hR : (2 : ℝ) ≤ resolution k)
  have hh := good_probability (L := residueModulus k) poolPrime (fun p => (pool_properties p).1) Subtype.val_injective
    hr10 (show 1 ≤ k ^ 3 from one_le_pow₀ (by omega)) (fun p => (pool_properties p).2.2)
    (fun p => Finset.dvd_prod_of_mem _ (Finset.mem_univ p)) j hgrid hε herr k (point 2) hhalf
  have hex := probability_exists (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9 / 10) hh)
  exact hex

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical Filter

noncomputable def allPeriods {k : ℕ} (j : Fin (16*k) ↪ Pool k) : ℕ :=
  ∏ σ : Equiv.Perm (Pool k), period poolPrime j σ

lemma allPeriods_pos {k : ℕ} (j : Fin (16*k) ↪ Pool k) : 0 < allPeriods j :=
  product_positive _ (fun σ => period_pos (fun p => (pool_properties p).1.pos) j σ)

noncomputable def fineModulus {k : ℕ} (j : Fin (16*k) ↪ Pool k) : ℕ :=
  resolution k * (2 * cutoff k * ((branching k+1)*cutoff k+1) * allPeriods j)

lemma fine_parameters {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k) :
    0 < fineModulus j ∧ 2 ∣ fineModulus j ∧
    (∀ σ : Equiv.Perm (Pool k), period poolPrime j σ ∣ fineModulus j) ∧
    (branching k+1)*cutoff k < fineModulus j ∧
    ∃ D J : ℕ, 0 < D ∧ fineModulus j = resolution k*D ∧ fineModulus j = J*cutoff k := by
  have hR : 0 < resolution k := pow_pos (by omega) _
  have hQ : 0 < cutoff k := pow_pos (by omega) _
  have hP := allPeriods_pos j
  have hM : 0 < fineModulus j := by unfold fineModulus; positivity
  refine ⟨hM, ?_, ?_, ?_, ?_⟩
  · unfold fineModulus
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right 2 _) _) _) _
  · intro σ
    have hd : period poolPrime j σ ∣ allPeriods j := Finset.dvd_prod_of_mem _ (Finset.mem_univ σ)
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hd _) _
  · have he : fineModulus j = ((branching k+1)*cutoff k+1) * (resolution k*2*cutoff k*allPeriods j) := by unfold fineModulus; ring
    rw [he]
    have hh : 0 < resolution k*2*cutoff k*allPeriods j := by positivity
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_mul_of_pos_right _ hh)
  · refine ⟨2*cutoff k*((branching k+1)*cutoff k+1)*allPeriods j,
      resolution k*2*((branching k+1)*cutoff k+1)*allPeriods j, by positivity, rfl, ?_⟩
    unfold fineModulus; ring

lemma period_upper {k : ℕ} (j : Fin (16*k) ↪ Pool k) (σ : Equiv.Perm (Pool k)) :
    period poolPrime j σ ≤ k^(48*k) := by
  calc
    _ ≤ ∏ _i : Fin (16*k), k^3 := Finset.prod_le_prod (fun i _ => (pool_properties (σ (j i))).2.2)
    _ = k^(48*k) := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; congr 1; omega

lemma spectrum_error {k : ℕ} (hk : 2 ≤ k) :
    4*((k : ℝ)⁻¹^k+k*(2*(resolution k : ℝ)/cutoff k+2*(k^(48*k) : ℕ)/repetitions k)) ≤
      20*(k : ℝ)⁻¹^k := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkpos : (0 : ℝ) < k := by linarith
  have hr : (resolution k : ℝ)/cutoff k = (k : ℝ)⁻¹^(4*k) := by
    dsimp only [resolution, cutoff]
    have he : 12*k = 8*k+4*k := by omega
    rw [Nat.cast_pow, Nat.cast_pow, he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hkpos.ne'), one_div, inv_pow]
  have ht : ((k^(48*k) : ℕ) : ℝ)/repetitions k = (k : ℝ)⁻¹^(4*k) := by
    dsimp only [repetitions]
    have he : 52*k = 48*k+4*k := by omega
    rw [Nat.cast_pow, Nat.cast_pow, he, pow_add, div_mul_eq_div_div, div_self (pow_ne_zero _ hkpos.ne'), one_div, inv_pow]
  have hi : (k : ℝ)*(k : ℝ)⁻¹^(4*k) ≤ (k : ℝ)⁻¹^k := by
    have hpow : (k : ℝ)^(k+1) ≤ (k : ℝ)^(4*k) := pow_le_pow_right₀ hkr (by omega)
    have hn : (k : ℝ)^k ≠ 0 := pow_ne_zero _ hkpos.ne'
    rw [inv_pow, inv_pow]
    apply (mul_le_mul_iff_left₀ (pow_pos hkpos k)).mp
    apply (mul_le_mul_iff_left₀ (pow_pos hkpos (4*k))).mp
    simpa only [mul_assoc, inv_mul_cancel₀ hn, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hkpos.ne'), pow_succ, mul_left_comm, mul_comm] using hpow
  rw [mul_div_assoc, mul_div_assoc, hr, ht]
  nlinarith

theorem concrete_displacement {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    [NeZero (fineModulus j)] [NeZero (resolution k)]
    (F : State (ZMod (fineModulus j)) (branching k) k → RealL1) (a : ℝ) (ha : 0 ≤ a)
    (hlip : ∀ x y, dist (F x) (F y) ≤ a * ed (sampledWord poolPrime j (repetitions k) (resolution k) k C x).val
      (sampledWord poolPrime j (repetitions k) (resolution k) k C y).val) :
    FiniteFourier.average (fun x => dist (F x) (F (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ)))) ≤
      a * FiniteTree.length (branching k) (repetitions k) k * (20*(k : ℝ)⁻¹^k) := by
  obtain ⟨_, _, hPM, hM, D, J, hD, hMR, hMQ⟩ := fine_parameters hk j
  have hQ : 0 < cutoff k := pow_pos (by omega) _
  have ht : k^(48*k) ≤ repetitions k := pow_le_pow_right₀ (by omega) (by omega)
  have hpow : cutoff k ≤ (k^2)^(6*k) := by dsimp only [cutoff]; rw [← pow_mul, show 2*(6*k) = 12*k by omega]
  have hh := TorusFourier.displacement_bound poolPrime j (fun i => (pool_properties i).1) Subtype.val_injective
    hPM (period_upper j) ht hD hQ hMR hMQ (one_le_pow₀ (by omega : 1 ≤ k) : 1 ≤ k^2)
    (fun i => (pool_properties i).2.1.le) hpow (by omega : 6*k+k ≤ 16*k) (by omega : 1 ≤ k) hM C
    (fineModulus j/2 : ℕ) F a ha hlip
  exact hh.trans (mul_le_mul_of_nonneg_left (spectrum_error hk) (mul_nonneg ha (Nat.cast_nonneg _)))

lemma sampled_separation {k : ℕ} (hk : 2 ≤ k) (j : Fin (16*k) ↪ Pool k)
    (C : Config (Pool k) (residueModulus k) (branching k) k)
    [NeZero (fineModulus j)] [NeZero (resolution k)]
    (hgood : Good (resolution k : ℝ)⁻¹ poolPrime j k C (point 2))
    (x : State (ZMod (fineModulus j)) (branching k) k) :
    FiniteTree.length (branching k) (repetitions k) k ≤ 128^k * deficit
      (sampledWord poolPrime j (repetitions k) (resolution k) k C x).val
      (sampledWord poolPrime j (repetitions k) (resolution k) k C
        (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ))).val := by
  have hm : 4 ≤ branching k := by dsimp [branching]; nlinarith [sq_nonneg (k : ℤ)]
  have ht : 0 < repetitions k := pow_pos (by omega) _
  have hh := separation (fun p => (pool_properties p).1.pos) hm ht C (sample (M := fineModulus j) (m := branching k) k x) (point 2) hgood
  have hs : sample (M := fineModulus j) (m := branching k) k
      (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ)) =
      sample (M := fineModulus j) (m := branching k) k x + diagonal (A := UnitAddCircle) (m := branching k) k (point 2) := by
    dsimp only [sample]
    rw [map_add, mapState_diagonal, point_grid (M := fineModulus j) (by norm_num : 0 < 2) (fine_parameters hk j).2.1]
  have hhNat : FiniteTree.length (branching k) (repetitions k) k ≤ 128^k * deficit
      (word poolPrime j (repetitions k) (resolution k) k C (sample (M := fineModulus j) (m := branching k) k x)).val
      (word poolPrime j (repetitions k) (resolution k) k C (sample (M := fineModulus j) (m := branching k) k x + diagonal (A := UnitAddCircle) (m := branching k) k (point 2))).val := by
    exact_mod_cast hh
  have hyw : (sampledWord poolPrime j (repetitions k) (resolution k) k C
        (x + diagonal (A := ZMod (fineModulus j)) (m := branching k) k (fineModulus j/2 : ℕ))).val =
      (word poolPrime j (repetitions k) (resolution k) k C (sample (M := fineModulus j) (m := branching k) k x + diagonal (A := UnitAddCircle) (m := branching k) k (point 2))).val :=
    congrArg (fun z : State UnitAddCircle (branching k) k => (word poolPrime j (repetitions k) (resolution k) k C z).val) hs
  rw [hyw]
  exact hhNat

end TreeEdit.TorusTree

end OAI
