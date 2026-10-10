import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.HardyMollifier

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma blockRadiusSq_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    blockRadiusSq i (nuclearHardyCoordinates i R) x = ‖position x i - R‖^2 := by
  simp [blockRadiusSq, nuclearHardyCoordinates, position, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs]

lemma blockRadiusSq_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : Configuration n) :
    blockRadiusSq i (pairHardyCoordinates i j hij) x = ‖position x i - position x j‖^2 := by
  simp [blockRadiusSq, pairHardyCoordinates, position, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs]

lemma hardyCoulomb_nuclear {n : ℕ} (i : Fin n) (R : Space) (x : Configuration n) :
    hardyCoulomb i (nuclearHardyCoordinates i R) x = coulombKernel (position x i - R) := by
  rw [hardyCoulomb, blockRadiusSq_nuclear, Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma hardyCoulomb_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j) (x : Configuration n) :
    hardyCoulomb i (pairHardyCoordinates i j hij) x =
      coulombKernel (position x i - position x j) := by
  rw [hardyCoulomb, blockRadiusSq_pair, Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma H1Vector.nuclear_coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i : Fin n) (R : Space) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ∧
    (∫ x, coulombKernel (position x i - R) * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  simpa only [hardyCoulomb_nuclear] using
    ψ.coulomb_integrable_bound s i (nuclearHardyCoordinates i R) hη

lemma H1Vector.pair_coulomb_integrable_bound {n : ℕ} (ψ : H1Vector n)
    (s : Spins n) (i j : Fin n) (hij : i ≠ j) {η : ℝ} (hη : 0 < η) :
    Integrable (fun x => coulombKernel (position x i - position x j) * ‖ψ.value s x‖^2) ∧
    (∫ x, coulombKernel (position x i - position x j) * ‖ψ.value s x‖^2) ≤
      4 * η * (∑ b : Fin 3, ∫ x, ‖ψ.gradient s (i,b) x‖^2) +
      (1 / (4 * η)) * (∫ x, ‖ψ.value s x‖^2) := by
  simpa only [hardyCoulomb_pair] using
    ψ.coulomb_integrable_bound s i (pairHardyCoordinates i j hij) hη

lemma H1Vector.nuclear_integrable {M n : ℕ} (ψ : H1Vector n) (S : Nuclei M)
    (s : Spins n) :
    Integrable (fun x => (∑ i, attraction S (position x i)) * ‖ψ.value s x‖^2) := by
  simp only [attraction, Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have h := (ψ.nuclear_coulomb_integrable_bound s i (S.position j) (by norm_num : (0 : ℝ) < 1)).1
  simpa only [mul_assoc] using h.const_mul (S.charge j)

lemma H1Vector.pair_integrable {n : ℕ} (ψ : H1Vector n) (s : Spins n) :
    Integrable (fun x => (∑ i : Fin n, ∑ j : Fin n,
      if i < j then coulombKernel (position x i - position x j) else 0) *
      ‖ψ.value s x‖^2) := by
  simp only [Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    exact (ψ.pair_coulomb_integrable_bound s i j hij.ne (by norm_num : (0 : ℝ) < 1)).1
  · simp only [ite_eq_right hij, zero_mul]
    exact integrable_zero _ _ _

lemma potential_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1)
    (V : Configuration n → ℝ) (s : Spins n)
    (hI : ∀ i, Integrable (fun x => V x *
      ‖(ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).value s x‖^2)) :
    (∑ i, ∫ x, V x * ‖(ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).value s x‖^2) =
      ∫ x, V x * ‖ψ.value s x‖^2 := by
  rw [← integral_finsetSum _ (fun i _ => hI i)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change (∑ i, V x * ‖(f i x : ℂ) * ψ.value s x‖^2) = _
  simp_rw [norm_real_mul_sq]
  rw [← Finset.mul_sum, ← Finset.sum_mul, hpart, one_mul]

lemma nuclearEnergy_smooth_partition {M n : ℕ} {ι : Type*} [Fintype ι]
    (S : Nuclei M) (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, nuclearEnergy S (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) =
      nuclearEnergy S ψ := by
  unfold nuclearEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact potential_smooth_partition ψ f hf B D hB hD hpart _ s
    (fun i => (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).nuclear_integrable S s)

lemma pairEnergy_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, pairEnergy (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) = pairEnergy ψ := by
  unfold pairEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  exact potential_smooth_partition ψ f hf B D hB hD hpart _ s
    (fun i => (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)).pair_integrable s)

theorem form_smooth_partition {M n : ℕ} {ι : Type*} [Fintype ι]
    (S : Nuclei M) (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, form S (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) =
      form S ψ + (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖^2 := by
  simp only [form, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [kinetic_smooth_partition ψ f hf B D hB hD hpart,
    nuclearEnergy_smooth_partition S ψ f hf B D hB hD hpart,
    pairEnergy_smooth_partition ψ f hf B D hB hD hpart]
  ring

lemma mass_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ mass ψ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

lemma kinetic_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ kinetic ψ := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
    (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))

lemma pairEnergy_nonneg {n : ℕ} (ψ : H1Vector n) : 0 ≤ pairEnergy ψ := by
  apply Finset.sum_nonneg
  intro s _
  apply integral_nonneg
  intro x
  apply mul_nonneg _ (sq_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact inv_nonneg.mpr (norm_nonneg _)
  · exact le_rfl

lemma totalCharge_ge_card {M : ℕ} (S : Nuclei M) : (M : ℝ) ≤ totalCharge S := by
  calc
    (M : ℝ) = ∑ _j : Fin M, (1 : ℝ) := by simp
    _ ≤ totalCharge S := Finset.sum_le_sum (fun j _ => S.charge_ge_one j)

lemma totalCharge_pos {M : ℕ} (S : Nuclei M) : 0 < totalCharge S :=
  (Nat.cast_pos.mpr S.nonempty).trans_le (totalCharge_ge_card S)

lemma nuclearEnergy_eq_sum {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    nuclearEnergy S ψ = ∑ s, ∑ i, ∑ j,
      S.charge j * (∫ x, coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2) := by
  unfold nuclearEnergy
  apply Finset.sum_congr rfl
  intro s _
  have hI : ∀ i j, Integrable (fun x => S.charge j *
      (coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2)) := by
    intro i j
    exact ((ψ.nuclear_coulomb_integrable_bound s i (S.position j)
      (by norm_num : (0 : ℝ) < 1)).1).const_mul _
  simp only [attraction, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hI i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hI i j)]
  simp only [integral_const_mul]

lemma nuclearEnergy_bound {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n)
    {η : ℝ} (hη : 0 < η) :
    nuclearEnergy S ψ ≤ 8 * η * totalCharge S * kinetic ψ +
      ((n : ℝ) * totalCharge S / (4 * η)) * mass ψ := by
  let K : Spins n → Fin n → ℝ := fun s i => ∑ b : Fin 3, ∫ x,
    ‖ψ.gradient s (i,b) x‖^2
  let L : Spins n → ℝ := fun s => ∫ x, ‖ψ.value s x‖^2
  rw [nuclearEnergy_eq_sum]
  have hbound : (∑ s, ∑ i, ∑ j, S.charge j *
      (∫ x, coulombKernel (position x i - S.position j) * ‖ψ.value s x‖^2)) ≤
      ∑ s, ∑ i, ∑ j, S.charge j * (4 * η * K s i + 1 / (4 * η) * L s) := by
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (ψ.nuclear_coulomb_integrable_bound s i (S.position j) hη).2
      (le_trans (by norm_num) (S.charge_ge_one j))
  refine hbound.trans_eq ?_
  have hJ : ∀ s i, (∑ j, S.charge j * (4 * η * K s i + 1 / (4 * η) * L s)) =
      totalCharge S * (4 * η * K s i + 1 / (4 * η) * L s) := by
    intro s i
    rw [← Finset.sum_mul]
    rfl
  simp_rw [hJ]
  have hI : ∀ s, (∑ i, totalCharge S * (4 * η * K s i + 1 / (4 * η) * L s)) =
      (totalCharge S * (4 * η)) * (∑ i, K s i) +
      ((n : ℝ) * totalCharge S / (4 * η)) * L s := by
    intro s
    simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  simp_rw [hI]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hK : (∑ s, ∑ i, K s i) = 2 * kinetic ψ := by
    unfold K kinetic
    simp only [Fintype.sum_prod_type]
    ring
  rw [hK]
  change _ = 8 * η * totalCharge S * kinetic ψ +
    ((n : ℝ) * totalCharge S / (4 * η)) * (∑ s, L s)
  ring

lemma form_lower_bound {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) :
    -(2 * (n : ℝ) * (totalCharge S)^2) * mass ψ ≤ form S ψ := by
  let η : ℝ := 1 / (8 * totalCharge S)
  have hZ := totalCharge_pos S
  have hη : 0 < η := by dsimp [η]; positivity
  have hbound := nuclearEnergy_bound S ψ hη
  have hfactor₁ : 8 * η * totalCharge S = 1 := by
    dsimp [η]
    field_simp
  have hfactor₂ : (n : ℝ) * totalCharge S / (4 * η) =
      2 * (n : ℝ) * (totalCharge S)^2 := by
    dsimp [η]
    field_simp
    ring
  rw [hfactor₁, one_mul, hfactor₂] at hbound
  have hpair := pairEnergy_nonneg ψ
  unfold form
  linarith

lemma sector_forms_bddBelow {M : ℕ} (S : Nuclei M) (n : ℕ) :
    BddBelow {e : ℝ | ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧ form S ψ = e} := by
  refine ⟨-(2 * (n : ℝ) * (totalCharge S)^2), ?_⟩
  rintro e ⟨ψ, _hanti, hm, he⟩
  have h := form_lower_bound S ψ
  rw [hm, mul_one, he] at h
  exact h

lemma energy_le_form {M n : ℕ} (S : Nuclei M) (hn : n ≠ 0) (ψ : H1Vector n)
    (hanti : Antisymmetric ψ) (hm : mass ψ = 1) : energy S n ≤ form S ψ := by
  rw [energy, ite_eq_right hn]
  exact csInf_le (sector_forms_bddBelow S n) ⟨ψ, hanti, hm, rfl⟩

lemma GroundState.minimizes {M n : ℕ} {S : Nuclei M} {ψ : H1Vector n}
    (hψ : GroundState S ψ) (hn : n ≠ 0) (φ : H1Vector n)
    (hφ : Antisymmetric φ) (hm : mass φ = 1) : form S ψ ≤ form S φ := by
  rw [hψ.2.2]
  exact energy_le_form S hn φ hφ hm

lemma H1Vector.test_integrable {n : ℕ} (ψ : H1Vector n) (s : Spins n)
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    Integrable (fun x => ψ.value s x * (φ x : ℂ)) := by
  have hL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hc.comp_left (by simp))
  exact (ψ.value_L2 s).integrable_mul hL

noncomputable def H1Vector.add {n : ℕ} (ψ φ : H1Vector n) : H1Vector n where
  value s x := ψ.value s x + φ.value s x
  gradient s a x := ψ.gradient s a x + φ.gradient s a x
  value_L2 s := (ψ.value_L2 s).add (φ.value_L2 s)
  partial_L2 s a := (ψ.partial_L2 s a).add (φ.partial_L2 s a)
  weak_partial s a f hf hc := by
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (EuclideanSpace.single a 1)) :=
      (hf.fderiv_right (by simp)).clm_apply contDiff_const
    have hdc := hc.fderiv_apply ℝ (EuclideanSpace.single a 1)
    have hiψ := ψ.test_integrable s _ hd hdc
    have hiφ := φ.test_integrable s _ hd hdc
    have hL : MemLp (fun x => (f x : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp hf.continuous).memLp_of_hasCompactSupport
        (hc.comp_left (by simp))
    have hjψ := (ψ.partial_L2 s a).integrable_mul hL
    have hjφ := (φ.partial_L2 s a).integrable_mul hL
    change Integrable (fun x => ψ.gradient s a x * (f x : ℂ)) at hjψ
    change Integrable (fun x => φ.gradient s a x * (f x : ℂ)) at hjφ
    simp_rw [add_mul]
    rw [integral_add hiψ hiφ, integral_add hjψ hjφ,
      ψ.weak_partial s a f hf hc, φ.weak_partial s a f hf hc]
    ring

noncomputable def H1Vector.rsmul {n : ℕ} (t : ℝ) (ψ : H1Vector n) : H1Vector n where
  value s x := (t : ℂ) * ψ.value s x
  gradient s a x := (t : ℂ) * ψ.gradient s a x
  value_L2 s := memLp_two_real_mul (ψ.value_L2 s) continuous_const (fun _ => le_rfl)
  partial_L2 s a := memLp_two_real_mul (ψ.partial_L2 s a) continuous_const (fun _ => le_rfl)
  weak_partial s a f hf hc := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_const_mul, ψ.weak_partial s a f hf hc]
    ring

lemma Antisymmetric.add {n : ℕ} {ψ φ : H1Vector n}
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) : Antisymmetric (ψ.add φ) := by
  intro p s
  filter_upwards [hψ p s, hφ p s] with x hx hy
  change ψ.value (s ∘ p) (permute p x) + φ.value (s ∘ p) (permute p x) = _
  rw [hx, hy]
  exact (mul_add _ _ _).symm

lemma Antisymmetric.rsmul {n : ℕ} {ψ : H1Vector n}
    (hψ : Antisymmetric ψ) (t : ℝ) : Antisymmetric (ψ.rsmul t) := by
  intro p s
  filter_upwards [hψ p s] with x hx
  change (t : ℂ) * ψ.value (s ∘ p) (permute p x) = _
  rw [hx]
  change _ = ((p.sign : ℤ) : ℂ) * ((t : ℂ) * ψ.value s x)
  ring

lemma mass_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    mass (ψ.rsmul t) = t^2 * mass ψ := by
  unfold mass H1Vector.rsmul
  simp only [norm_real_mul_sq, integral_const_mul, Finset.mul_sum]

lemma kinetic_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    kinetic (ψ.rsmul t) = t^2 * kinetic ψ := by
  unfold kinetic H1Vector.rsmul
  simp only [norm_real_mul_sq, integral_const_mul, ← Finset.mul_sum]
  ring

lemma nuclearEnergy_rsmul {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) (t : ℝ) :
    nuclearEnergy S (ψ.rsmul t) = t^2 * nuclearEnergy S ψ := by
  unfold nuclearEnergy H1Vector.rsmul
  simp only [norm_real_mul_sq]
  simp_rw [mul_left_comm _ (t^2), integral_const_mul]
  rw [← Finset.mul_sum]

lemma pairEnergy_rsmul {n : ℕ} (ψ : H1Vector n) (t : ℝ) :
    pairEnergy (ψ.rsmul t) = t^2 * pairEnergy ψ := by
  unfold pairEnergy H1Vector.rsmul
  simp only [norm_real_mul_sq]
  simp_rw [mul_left_comm _ (t^2), integral_const_mul]
  rw [← Finset.mul_sum]

lemma form_rsmul {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) (t : ℝ) :
    form S (ψ.rsmul t) = t^2 * form S ψ := by
  rw [form, kinetic_rsmul, nuclearEnergy_rsmul, pairEnergy_rsmul, form]
  ring

lemma energy_mul_mass_le_form {M n : ℕ} (S : Nuclei M) (hn : n ≠ 0)
    (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : 0 < mass ψ) :
    energy S n * mass ψ ≤ form S ψ := by
  let t : ℝ := (Real.sqrt (mass ψ))⁻¹
  have ht : t^2 = (mass ψ)⁻¹ := by
    dsimp [t]
    rw [inv_pow, Real.sq_sqrt hm.le]
  have hmass : mass (ψ.rsmul t) = 1 := by
    rw [mass_rsmul, ht, inv_mul_cancel₀ (ne_of_gt hm)]
  have hbound := energy_le_form S hn (ψ.rsmul t) (hψ.rsmul t) hmass
  rw [form_rsmul, ht, ← div_eq_inv_mul] at hbound
  exact (le_div_iff₀ hm).mp hbound

lemma norm_add_rsmul_sq (u v : ℂ) (t : ℝ) :
    ‖u + (t : ℂ) * v‖^2 =
      (1-t)*‖u‖^2 + (t^2-t)*‖v‖^2 + t*‖u+v‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma mass_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ) :
    mass (ψ.add (φ.rsmul t)) =
      (1-t)*mass ψ + (t^2-t)*mass φ + t*mass (ψ.add φ) := by
  unfold mass
  have hiψ := fun s => (ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have hiφ := fun s => (φ.value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have hiadd := fun s => ((ψ.add φ).value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have heq : ∀ s, (∫ x, ‖(ψ.add (φ.rsmul t)).value s x‖^2) =
      (1-t)*(∫ x, ‖ψ.value s x‖^2) + (t^2-t)*(∫ x, ‖φ.value s x‖^2) +
      t*(∫ x, ‖(ψ.add φ).value s x‖^2) := by
    intro s
    change (∫ x, ‖ψ.value s x + (t : ℂ)*φ.value s x‖^2) = _
    simp_rw [norm_add_rsmul_sq]
    have hsum : Integrable (fun x => (1-t)*‖ψ.value s x‖^2 +
        (t^2-t)*‖φ.value s x‖^2) := ((hiψ s).const_mul _).add ((hiφ s).const_mul _)
    have hadd : Integrable (fun x => t*‖ψ.value s x + φ.value s x‖^2) :=
      (hiadd s).const_mul t
    rw [integral_add hsum hadd,
      integral_add ((hiψ s).const_mul (1-t)) ((hiφ s).const_mul (t^2-t))]
    simp only [integral_const_mul]
    rfl
  simp_rw [heq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma kinetic_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ) :
    kinetic (ψ.add (φ.rsmul t)) =
      (1-t)*kinetic ψ + (t^2-t)*kinetic φ + t*kinetic (ψ.add φ) := by
  unfold kinetic
  have heq : ∀ s a, (∫ x, ‖(ψ.add (φ.rsmul t)).gradient s a x‖^2) =
      (1-t)*(∫ x, ‖ψ.gradient s a x‖^2) +
      (t^2-t)*(∫ x, ‖φ.gradient s a x‖^2) +
      t*(∫ x, ‖(ψ.add φ).gradient s a x‖^2) := by
    intro s a
    have hiψ := (ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)
    have hiφ := (φ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)
    have hiadd := ((ψ.add φ).partial_L2 s a).integrable_norm_pow (p := 2) (by decide)
    change (∫ x, ‖ψ.gradient s a x + (t : ℂ)*φ.gradient s a x‖^2) = _
    simp_rw [norm_add_rsmul_sq]
    have hsum : Integrable (fun x => (1-t)*‖ψ.gradient s a x‖^2 +
        (t^2-t)*‖φ.gradient s a x‖^2) := (hiψ.const_mul _).add (hiφ.const_mul _)
    have hadd : Integrable (fun x => t*‖ψ.gradient s a x + φ.gradient s a x‖^2) :=
      hiadd.const_mul t
    rw [integral_add hsum hadd, integral_add (hiψ.const_mul (1-t)) (hiφ.const_mul (t^2-t))]
    simp only [integral_const_mul]
    rfl
  simp_rw [heq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Coulomb
end
end

end OAI
