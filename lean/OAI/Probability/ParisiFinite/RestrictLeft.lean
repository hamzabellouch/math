import Mathlib
import OAI.Probability.ParisiFinite.IntegrablePdfMul
import OAI.Probability.ParisiFinite.TendstoDyadicRound

namespace OAI

/-! Restrict Left. -/

noncomputable section

open scoped BigOperators Matrix Topology
open MeasureTheory ProbabilityTheory Filter
namespace SKQAOA

open SKGaussian

def restrictLeft {n m : ℕ} (σ : Configuration (n + m)) : Configuration n :=
  fun i => σ (Fin.castAdd m i)

def restrictRight {n m : ℕ} (σ : Configuration (n + m)) : Configuration m :=
  fun i => σ (Fin.natAdd n i)

@[simp] theorem restrictLeft_append {n m : ℕ} (σ : Configuration n) (τ : Configuration m) :
    restrictLeft (Fin.append σ τ) = σ := by
  funext i
  simp [restrictLeft]

@[simp] theorem restrictRight_append {n m : ℕ} (σ : Configuration n) (τ : Configuration m) :
    restrictRight (Fin.append σ τ) = τ := by
  funext i
  simp [restrictRight]

theorem overlapSum_split {n m : ℕ} (σ τ : Configuration (n + m)) :
    overlapSum σ τ = overlapSum (restrictLeft σ) (restrictLeft τ) +
      overlapSum (restrictRight σ) (restrictRight τ) := by
  exact Fin.sum_univ_add (fun i => spin σ i * spin τ i)

 
def blockCoeff (n m : ℕ) (σ : Configuration (n + m)) : Edge n ⊕ Edge m → ℝ :=
  Sum.elim (skCoeff n (restrictLeft σ)) (skCoeff m (restrictRight σ))

theorem blockCoeff_increment {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (σ τ : Configuration (n + m)) :
    (∑ e, (blockCoeff n m σ e - blockCoeff n m τ e) ^ 2) ≤
      ∑ e, (skCoeff (n + m) σ e - skCoeff (n + m) τ e) ^ 2 := by
  simp only [blockCoeff, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [coeff_increment hn, coeff_increment hm, coeff_increment (by omega), overlapSum_split]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let a := overlapSum (restrictLeft σ) (restrictLeft τ)
  let b := overlapSum (restrictRight σ) (restrictRight τ)
  change (n : ℝ) - a^2 / n + ((m : ℝ) - b^2 / m) ≤
    (↑(n + m) : ℝ) - (a + b)^2 / ↑(n + m)
  push_cast
  field_simp
  nlinarith [sq_nonneg ((m : ℝ) * a - (n : ℝ) * b)]

theorem groundMaximum_eq_finiteMax (n : ℕ) (J : Disorder n) :
    groundMaximum n J = finiteMax (field (skCoeff n) J) := by
  have he : field (skCoeff n) J = hamiltonian n J :=
    funext fun σ => (hamiltonian_eq_coeff n J σ).symm
  rw [he]
  simp [groundMaximum, finiteMax, Finset.sup'_eq_csSup_image]

 
theorem block_finiteMax {n m : ℕ} (J : (Edge n ⊕ Edge m) → ℝ) :
    finiteMax (field (blockCoeff n m) J) =
      groundMaximum n (fun e => J (Sum.inl e)) +
        groundMaximum m (fun e => J (Sum.inr e)) := by
  have he (σ : Configuration (n + m)) : field (blockCoeff n m) J σ =
      field (skCoeff n) (fun e => J (Sum.inl e)) (restrictLeft σ) +
        field (skCoeff m) (fun e => J (Sum.inr e)) (restrictRight σ) := by
    simp only [field, blockCoeff, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [groundMaximum_eq_finiteMax, groundMaximum_eq_finiteMax]
  apply le_antisymm
  · exact Finset.sup'_le Finset.univ_nonempty _ fun σ _ => by
      rw [he]
      exact add_le_add (le_finiteMax _ _) (le_finiteMax _ _)
  · obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Configuration n)).Nonempty)
      (field (skCoeff n) (fun e => J (Sum.inl e)))
    obtain ⟨τ, _, hτ⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Configuration m)).Nonempty)
      (field (skCoeff m) (fun e => J (Sum.inr e)))
    have hp := le_finiteMax (field (blockCoeff n m) J) (Fin.append σ τ)
    rw [he, restrictLeft_append, restrictRight_append] at hp
    simpa only [finiteMax, hσ, hτ] using hp

 
def expectedMaximum (n : ℕ) : ℝ := ∫ J, groundMaximum n J ∂disorderLaw n

theorem ground_integrable (n : ℕ) : Integrable (groundMaximum n) (disorderLaw n) := by
  simp_rw [show groundMaximum n = fun J => finiteMax (field (skCoeff n) J) from
    funext (groundMaximum_eq_finiteMax n)]
  exact integrable_finiteMax (integrable_field (skCoeff n))

theorem expected_block_maximum (n m : ℕ) :
    (∫ J, finiteMax (field (blockCoeff n m) J) ∂gaussianLaw (Edge n ⊕ Edge m)) =
      expectedMaximum n + expectedMaximum m := by
  let T : ((Disorder n) × (Disorder m)) ≃ᵐ ((Edge n ⊕ Edge m) → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Edge n ⊕ Edge m => ℝ)).symm
  have hp : MeasurePreserving T ((disorderLaw n).prod (disorderLaw m))
      (gaussianLaw (Edge n ⊕ Edge m)) :=
    measurePreserving_sumPiEquivProdPi_symm (fun _ => gaussianReal 0 1)
  rw [← hp.integral_comp' (fun J => finiteMax (field (blockCoeff n m) J))]
  simp_rw [block_finiteMax]
  change (∫ J, groundMaximum n J.1 + groundMaximum m J.2
    ∂(disorderLaw n).prod (disorderLaw m)) = _
  have : IsProbabilityMeasure (disorderLaw n) := by unfold disorderLaw; infer_instance
  have : IsProbabilityMeasure (disorderLaw m) := by unfold disorderLaw; infer_instance
  rw [integral_add ((ground_integrable n).comp_fst _) ((ground_integrable m).comp_snd _)]
  simp [integral_fun_fst, integral_fun_snd, expectedMaximum]

 

theorem expectedMaximum_superadditive_pos {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    expectedMaximum n + expectedMaximum m ≤ expectedMaximum (n + m) := by
  have h := expected_field_max_le (blockCoeff n m) (skCoeff (n + m))
    (blockCoeff_increment hn hm)
  rw [expected_block_maximum] at h
  simpa only [← groundMaximum_eq_finiteMax, gaussianLaw, disorderLaw, expectedMaximum] using h

@[simp] theorem groundMaximum_zero (J : Disorder 0) : groundMaximum 0 J = 0 := by
  have he : hamiltonian 0 J = fun _ => 0 := by
    funext σ
    simp [hamiltonian]
  rw [groundMaximum, he]
  simp

@[simp] theorem expectedMaximum_zero : expectedMaximum 0 = 0 := by
  simp [expectedMaximum]

theorem expectedMaximum_superadditive (n m : ℕ) :
    expectedMaximum n + expectedMaximum m ≤ expectedMaximum (n + m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  exact expectedMaximum_superadditive_pos hn hm

 
def siteCoeff (n : ℕ) (σ : Configuration n) (i : Fin n) : ℝ := spin σ i

theorem site_increment (n : ℕ) (σ τ : Configuration n) :
    (∑ i, (siteCoeff n σ i - siteCoeff n τ i) ^ 2) =
      2 * (n : ℝ) - 2 * overlapSum σ τ := by
  have he (i : Fin n) : (siteCoeff n σ i - siteCoeff n τ i) ^ 2 =
      2 - 2 * (spin σ i * spin τ i) := by
    dsimp [siteCoeff]
    nlinarith [spin_sq σ i, spin_sq τ i]
  simp_rw [he]
  simp [Finset.sum_sub_distrib, Finset.mul_sum, overlapSum]
  ring

theorem sk_to_site_increment {n : ℕ} (hn : 0 < n) (σ τ : Configuration n) :
    (∑ e, (skCoeff n σ e - skCoeff n τ e) ^ 2) ≤
      ∑ i, (siteCoeff n σ i - siteCoeff n τ i) ^ 2 := by
  rw [coeff_increment hn, site_increment]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  field_simp
  nlinarith [sq_nonneg (overlapSum σ τ - (n : ℝ))]

def gaussianAbsoluteMean : ℝ := ∫ x : ℝ, |x| ∂gaussianReal 0 1

theorem integrable_abs_standard : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
  (MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := 0) (v := 1) 1)).abs

theorem site_maximum_le (n : ℕ) (J : Fin n → ℝ) :
    finiteMax (field (siteCoeff n) J) ≤ ∑ i, |J i| := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro σ _
  apply Finset.sum_le_sum
  intro i _
  change spin σ i * J i ≤ |J i|
  unfold spin
  split
  · simpa using neg_le_abs (J i)
  · simpa using le_abs_self (J i)

 

theorem expectedMaximum_le (n : ℕ) : expectedMaximum n ≤ (n : ℝ) * gaussianAbsoluteMean := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hcomp := expected_field_max_le (skCoeff n) (siteCoeff n) (sk_to_site_increment hn)
  have hi : ∀ i : Fin n, Integrable (fun J : Fin n → ℝ => |J i|) (gaussianLaw (Fin n)) :=
    fun i => integrable_comp_eval (i := i) integrable_abs_standard
  calc
    _ ≤ ∫ J, finiteMax (field (siteCoeff n) J) ∂gaussianLaw (Fin n) := by
      simpa only [← groundMaximum_eq_finiteMax, gaussianLaw, disorderLaw, expectedMaximum] using hcomp
    _ ≤ ∫ J : Fin n → ℝ, ∑ i, |J i| ∂gaussianLaw (Fin n) :=
      integral_mono (integrable_finiteMax (integrable_field (siteCoeff n)))
        (integrable_finsetSum _ fun i _ => hi i) (site_maximum_le n)
    _ = _ := by
      rw [integral_finsetSum _ fun i _ => hi i]
      have he (i : Fin n) : (∫ J : Fin n → ℝ, |J i| ∂gaussianLaw (Fin n)) = gaussianAbsoluteMean :=
        integral_comp_eval integrable_abs_standard.aestronglyMeasurable
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

 

theorem tendsto_expectedGround : Tendsto expectedGround atTop (𝓝 Pstar) := by
  have hs : Subadditive (fun n => -expectedMaximum n) := by
    intro n m
    linarith [expectedMaximum_superadditive n m]
  have hb : BddBelow (Set.range fun n => -expectedMaximum n / (n : ℝ)) := by
    refine ⟨-gaussianAbsoluteMean, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [expectedMaximum_zero, neg_zero, Nat.cast_zero, div_zero]
      exact neg_nonpos.mpr (integral_nonneg fun x => abs_nonneg x)
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      apply (le_div_iff₀ hn').mpr
      linarith [expectedMaximum_le n]
  have ht := (hs.tendsto_lim hb).neg
  have he : (fun n => -(-expectedMaximum n / (n : ℝ))) = expectedGround := by
    funext n
    simp [expectedGround, expectedMaximum, neg_div]
  rw [he] at ht
  have hp : Pstar = -hs.lim := ht.limUnder_eq
  rwa [hp]

end SKQAOA

namespace TensorMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

 
def lift (A : ι → Matrix κ κ ℂ) : Matrix (ι → κ) (ι → κ) ℂ :=
  fun σ τ => ∏ i, A i (σ i) (τ i)

omit [DecidableEq ι] [Fintype κ] in
@[simp] theorem lift_one : lift (fun _ : ι => (1 : Matrix κ κ ℂ)) = 1 := by
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp [lift]
  · have he : ∃ i, σ i ≠ τ i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := he
    simp only [lift, Matrix.one_apply, ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq κ] in
@[simp] theorem lift_mul (A B : ι → Matrix κ κ ℂ) :
    lift (fun i => A i * B i) = lift A * lift B := by
  ext σ τ
  simp only [lift, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact Fintype.prod_sum _

 
def atSite (i : ι) (A : Matrix κ κ ℂ) : Matrix (ι → κ) (ι → κ) ℂ :=
  lift (Function.update (fun _ => 1) i A)

omit [Fintype κ] in
@[simp] theorem local_one (i : ι) : atSite i (1 : Matrix κ κ ℂ) = 1 := by
  simp [atSite, Function.update_eq_self]

@[simp] theorem local_mul (i : ι) (A B : Matrix κ κ ℂ) :
    atSite i (A * B) = atSite i A * atSite i B := by
  rw [atSite, atSite, atSite, ← lift_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [Function.update, h]

omit [Fintype κ] in
theorem atSite_apply (i : ι) (A : Matrix κ κ ℂ) (σ τ : ι → κ) :
    atSite i A σ τ = A (σ i) (τ i) *
      ∏ j ∈ Finset.univ.erase i, (1 : Matrix κ κ ℂ) (σ j) (τ j) := by
  unfold atSite lift
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

omit [Fintype κ] in
@[simp] theorem local_add (i : ι) (A B : Matrix κ κ ℂ) :
    atSite i (A + B) = atSite i A + atSite i B := by
  ext σ τ
  simp only [Matrix.add_apply, atSite_apply]
  exact add_mul _ _ _

omit [Fintype κ] in
@[simp] theorem local_zero (i : ι) : atSite i (0 : Matrix κ κ ℂ) = 0 := by
  ext σ τ
  simp [atSite_apply]

omit [Fintype κ] in
@[simp] theorem local_smul (i : ι) (c : ℂ) (A : Matrix κ κ ℂ) :
    atSite i (c • A) = c • atSite i A := by
  ext σ τ
  simp only [Matrix.smul_apply, atSite_apply, smul_eq_mul]
  exact mul_assoc _ _ _

 
def localAlgHom (i : ι) : Matrix κ κ ℂ →ₐ[ℂ] Matrix (ι → κ) (ι → κ) ℂ where
  toFun := atSite i
  map_one' := local_one i
  map_mul' := local_mul i
  map_zero' := local_zero i
  map_add' := local_add i
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, local_smul, local_one]

open scoped Matrix.Norms.Operator in
@[simp] theorem local_exp (i : ι) (A : Matrix κ κ ℂ) :
    atSite i (NormedSpace.exp A) = NormedSpace.exp (atSite i A) := by
  exact NormedSpace.map_exp (localAlgHom i)
    (localAlgHom (κ := κ) i).toLinearMap.continuous_of_finiteDimensional A

theorem atSite_commute {i j : ι} (hij : i ≠ j) (A B : Matrix κ κ ℂ) :
    Commute (atSite i A) (atSite j B) := by
  show atSite i A * atSite j B = atSite j B * atSite i A
  simp only [atSite, ← lift_mul]
  congr 1
  funext k
  by_cases hi : k = i
  · subst k
    simp [Function.update, hij]
  · by_cases hj : k = j
    · subst k
      simp [Function.update, Ne.symm hij]
    · simp [Function.update, hi, hj]

theorem exp_sum_atSite (s : Finset ι) (A : ι → Matrix κ κ ℂ) :
    NormedSpace.exp (∑ i ∈ s, atSite i (A i)) =
      lift (fun i => if i ∈ s then NormedSpace.exp (A i) else 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hc : Commute (atSite a (A a)) (∑ i ∈ s, atSite i (A i)) := by
      apply Commute.sum_right
      intro i hi
      exact atSite_commute (i := a) (j := i) (fun e => ha (e.symm ▸ hi)) _ _
    rw [Finset.sum_insert ha, Matrix.exp_add_of_commute _ _ hc, ih, ← local_exp,
      atSite, ← lift_mul]
    congr 1
    funext i
    by_cases hi : i = a
    · subst i
      simp [ha]
    · simp [hi]

theorem exp_sum_atSite_univ (A : ι → Matrix κ κ ℂ) :
    NormedSpace.exp (∑ i, atSite i (A i)) = lift (fun i => NormedSpace.exp (A i)) := by
  simpa using exp_sum_atSite Finset.univ A

end TensorMatrix

namespace TwoState

def swap : Matrix Bool Bool ℂ := fun a b => if a = !b then 1 else 0

def hadamard : Matrix Bool Bool ℂ := fun a b => if a && b then -1 else 1

def hadamardUnit : (Matrix Bool Bool ℂ)ˣ where
  val := hadamard
  inv := (1/2 : ℂ) • hadamard
  val_inv := by
    ext a b
    cases a <;> cases b <;> norm_num [hadamard, Matrix.mul_apply, Fintype.sum_bool]
  inv_val := by
    ext a b
    cases a <;> cases b <;> norm_num [hadamard, Matrix.mul_apply, Fintype.sum_bool]

theorem conj_diagonal (z : ℂ) :
    ((hadamardUnit : (Matrix Bool Bool ℂ)ˣ) : Matrix Bool Bool ℂ) *
        Matrix.diagonal (fun b : Bool => if b then -z else z) * ((hadamardUnit⁻¹ : (Matrix Bool Bool ℂ)ˣ) : Matrix Bool Bool ℂ) = z • swap := by
  ext a b
  cases a <;> cases b <;>
    simp [hadamardUnit, hadamard, swap, Matrix.mul_apply] <;> ring

 
theorem exp_swap (z : ℂ) :
    NormedSpace.exp (z • swap) =
      ((Complex.exp z + Complex.exp (-z))/2) • (1 : Matrix Bool Bool ℂ) +
      ((Complex.exp z - Complex.exp (-z))/2) • swap := by
  rw [← conj_diagonal z, Matrix.exp_units_conj, Matrix.exp_diagonal]
  ext a b
  cases a <;> cases b <;>
    simp [hadamardUnit, hadamard, swap, Matrix.mul_apply,
      ← Complex.exp_eq_exp_ℂ] <;> ring

def rotation (t : ℝ) : Matrix Bool Bool ℂ :=
  (Real.cos t : ℂ) • (1 : Matrix Bool Bool ℂ) +
    (-(Real.sin t : ℂ) * Complex.I) • swap

theorem rotation_eq_exp (t : ℝ) :
    rotation t = NormedSpace.exp ((-(t : ℂ) * Complex.I) • swap) := by
  rw [exp_swap]
  have hp : Complex.exp (-(t : ℂ) * Complex.I) =
      (Real.cos t : ℂ) - (Real.sin t : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, sub_eq_add_neg]
  have hm : Complex.exp (-(-(t : ℂ) * Complex.I)) =
      (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
    rw [neg_mul, neg_neg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [hp, hm]
  unfold rotation
  congr 1 <;> congr 1 <;> ring

@[simp] theorem rotation_apply (t : ℝ) (a b : Bool) :
    rotation t a b = if a = b then (Real.cos t : ℂ) else -(Real.sin t : ℂ) * Complex.I := by
  cases a <;> cases b <;> simp [rotation, swap]

end TwoState

namespace SKQAOA

theorem pauliX_eq_atSite {n : ℕ} (i : Fin n) :
    pauliX i = TensorMatrix.atSite i TwoState.swap := by
  ext σ τ
  have he : TensorMatrix.atSite i TwoState.swap σ τ =
      ∏ j, if σ j = Function.update τ i (!(τ i)) j then (1 : ℂ) else 0 := by
    unfold TensorMatrix.atSite TensorMatrix.lift
    apply Finset.prod_congr rfl
    intro j _
    by_cases h : j = i
    · subst j
      simp [TwoState.swap]
    · simp [Function.update_of_ne h, Matrix.one_apply]
  rw [he, Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one, ← funext_iff, pauliX]

 
theorem cost_evolution_eq_diagonal (n : ℕ) (J : Disorder n) (t : ℝ) :
    evolution t (cost n J) = Matrix.diagonal
      (fun σ => Complex.exp (-(t : ℂ) * Complex.I * (hamiltonian n J σ : ℂ))) := by
  simp only [evolution, cost_eq_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext σ
  simp [← Complex.exp_eq_exp_ℂ]

 
theorem mixer_evolution_eq_tensor (n : ℕ) (t : ℝ) :
    evolution t (mixer n) = TensorMatrix.lift (fun _ : Fin n => TwoState.rotation t) := by
  unfold evolution mixer
  simp_rw [Finset.smul_sum, pauliX_eq_atSite, ← TensorMatrix.local_smul]
  rw [TensorMatrix.exp_sum_atSite_univ]
  simp only [← TwoState.rotation_eq_exp]

 
theorem mixer_evolution_apply (n : ℕ) (t : ℝ) (σ τ : Configuration n) :
    evolution t (mixer n) σ τ =
      ∏ i, if σ i = τ i then (Real.cos t : ℂ) else -(Real.sin t : ℂ) * Complex.I := by
  rw [mixer_evolution_eq_tensor]
  simp [TensorMatrix.lift]

end SKQAOA

open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory

namespace GaussianFourier
open scoped _root_.GaussianFourier

def law (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (κ : Type*) [Fintype κ] : IsProbabilityMeasure (law κ) := by
  unfold law
  infer_instance

 
theorem integral_exp (z : ℂ) :
    (∫ x : ℝ, Complex.exp (z * x) ∂gaussianReal 0 1) = Complex.exp (z ^ 2 / 2) := by
  simpa [complexMGF] using complexMGF_id_gaussianReal (μ := 0) (v := 1) z

theorem integral_mul_exp (z : ℂ) :
    (∫ x : ℝ, (x : ℂ) * Complex.exp (z * x) ∂gaussianReal 0 1) =
      z * Complex.exp (z ^ 2 / 2) := by
  have h := hasDerivAt_complexMGF (X := id) (μ := gaussianReal 0 1) (z := z) (by simp)
  have he : complexMGF id (gaussianReal 0 1) = fun z : ℂ => Complex.exp (z ^ 2 / 2) := by
    funext w
    simpa using complexMGF_id_gaussianReal (μ := 0) (v := 1) w
  rw [he] at h
  have hd := (Complex.hasDerivAt_exp (z ^ 2 / 2)).comp z (((hasDerivAt_id z).pow 2).div_const 2)
  have hg := h.unique hd
  simpa [mul_comm] using hg

theorem integrable_exp (z : ℂ) :
    Integrable (fun x : ℝ => Complex.exp (z * x)) (gaussianReal 0 1) := by
  simpa using integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 1) (z := z) (by simp) 0

theorem integrable_mul_exp (z : ℂ) :
    Integrable (fun x : ℝ => (x : ℂ) * Complex.exp (z * x)) (gaussianReal 0 1) := by
  simpa using integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet
    (X := id) (μ := gaussianReal 0 1) (z := z) (by simp) 1

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
 
theorem integral_exp_sum (z : κ → ℂ) :
    (∫ x : κ → ℝ, Complex.exp (∑ k, z k * x k) ∂law κ) =
      Complex.exp (∑ k, z k ^ 2 / 2) := by
  simp_rw [Complex.exp_sum]
  rw [law, integral_fintype_prod_eq_prod (fun k (x : ℝ) => Complex.exp (z k * x))]
  simp only [integral_exp]

omit [DecidableEq κ] in
theorem integrable_exp_sum (z : κ → ℂ) :
    Integrable (fun x : κ → ℝ => Complex.exp (∑ k, z k * x k)) (law κ) := by
  simp_rw [Complex.exp_sum]
  exact Integrable.fintype_prod (fun k => integrable_exp (z k))

theorem coord_mul_exp_sum (z : κ → ℂ) (i : κ) (x : κ → ℝ) :
    (x i : ℂ) * Complex.exp (∑ k, z k * x k) =
      ∏ k, if k = i then (x k : ℂ) * Complex.exp (z k * x k)
        else Complex.exp (z k * x k) := by
  rw [Complex.exp_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  rw [mul_assoc]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [ite_eq_right (Finset.ne_of_mem_erase hk)]

theorem integrable_coord_exp_sum (z : κ → ℂ) (i : κ) :
    Integrable (fun x : κ → ℝ => (x i : ℂ) * Complex.exp (∑ k, z k * x k)) (law κ) := by
  simp_rw [coord_mul_exp_sum]
  apply Integrable.fintype_prod (f := fun k (x : ℝ) =>
    if k = i then (x : ℂ) * Complex.exp (z k * x) else Complex.exp (z k * x))
  intro k
  by_cases h : k = i
  · simp only [h, ite_true]
    exact integrable_mul_exp (z i)
  · simp only [h, ite_false]
    exact integrable_exp (z k)

theorem integral_coord_exp_sum (z : κ → ℂ) (i : κ) :
    (∫ x : κ → ℝ, (x i : ℂ) * Complex.exp (∑ k, z k * x k) ∂law κ) =
      z i * Complex.exp (∑ k, z k ^ 2 / 2) := by
  simp_rw [coord_mul_exp_sum]
  rw [law, integral_fintype_prod_eq_prod (fun k (x : ℝ) =>
    if k = i then (x : ℂ) * Complex.exp (z k * x) else Complex.exp (z k * x))]
  have hi (k : κ) : (∫ x : ℝ,
      (if k = i then (x : ℂ) * Complex.exp (z k * x) else Complex.exp (z k * x))
        ∂gaussianReal 0 1) =
      if k = i then z k * Complex.exp (z k ^ 2 / 2) else Complex.exp (z k ^ 2 / 2) := by
    split_ifs <;> simp only [integral_mul_exp, integral_exp]
  simp_rw [hi]
  rw [Complex.exp_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  rw [mul_assoc]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [ite_eq_right (Finset.ne_of_mem_erase hk)]

end GaussianFourier

namespace TensorMatrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] theorem lift_conjTranspose (A : ι → Matrix κ κ ℂ) :
    (lift A)ᴴ = lift (fun i => (A i)ᴴ) := by
  ext σ τ
  simp [lift, Matrix.conjTranspose_apply]

omit [DecidableEq ι] [Fintype κ] in
@[simp] theorem lift_diagonal (a : ι → κ → ℂ) :
    lift (fun i => Matrix.diagonal (a i)) = Matrix.diagonal (fun σ => ∏ i, a i (σ i)) := by
  ext σ τ
  by_cases h : σ = τ
  · subst τ
    simp [lift]
  · have he : ∃ i, σ i ≠ τ i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := he
    simp only [lift, Matrix.diagonal_apply_ne _ h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

omit [Fintype κ] in
@[simp] theorem local_diagonal (i : ι) (a : κ → ℂ) :
    atSite i (Matrix.diagonal a) = Matrix.diagonal (fun σ => a (σ i)) := by
  have he : (Function.update (fun _ : ι => (1 : Matrix κ κ ℂ)) i (Matrix.diagonal a)) =
      fun j => Matrix.diagonal (Function.update (fun _ : ι => fun _ : κ => (1 : ℂ)) i a j) := by
    funext j
    by_cases h : j = i <;> simp [Function.update, h]
  rw [atSite, he, lift_diagonal]
  congr 1
  funext σ
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have hp : (∏ j ∈ Finset.univ.erase i,
      Function.update (fun _ : ι => fun _ : κ => (1 : ℂ)) i a j (σ j)) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hp, mul_one]

theorem conjugate_local (i : ι) (A : Matrix κ κ ℂ) (U : ι → Matrix κ κ ℂ)
    (hU : ∀ j, (U j)ᴴ * U j = 1) :
    (lift U)ᴴ * atSite i A * lift U = atSite i ((U i)ᴴ * A * U i) := by
  simp only [lift_conjTranspose, atSite, ← lift_mul]
  congr 1
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h, hU]

end TensorMatrix

namespace TwoState

def sign (b : Bool) : ℂ := if b then -1 else 1

def z : Matrix Bool Bool ℂ := Matrix.diagonal sign

def y : Matrix Bool Bool ℂ := Complex.I • (swap * z)

@[simp] theorem z_apply (a b : Bool) : z a b = if a = b then sign a else 0 := by
  simp [z, Matrix.diagonal_apply]

@[simp] theorem y_apply (a b : Bool) : y a b = if a = !b then -Complex.I * sign a else 0 := by
  cases a <;> cases b <;> simp [y, swap, z, sign]

theorem rotation_star_mul (t : ℝ) : (rotation t)ᴴ * rotation t = 1 := by
  ext a b
  cases a <;> cases b <;> apply Complex.ext <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rotation_apply, -Complex.ofReal_sin, -Complex.ofReal_cos, Complex.mul_re,
      Complex.mul_im] <;> nlinarith [Real.sin_sq_add_cos_sq t]

theorem rotation_conjugate_z (t : ℝ) :
    (rotation t)ᴴ * z * rotation t =
      (Real.cos (2*t) : ℂ) • z + (Real.sin (2*t) : ℂ) • y := by
  ext a b
  cases a <;> cases b <;> apply Complex.ext <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rotation_apply, z, y, swap, sign,
      Real.cos_two_mul, Real.sin_two_mul, -Complex.ofReal_sin, -Complex.ofReal_cos,
      Complex.mul_re, Complex.mul_im, -Complex.ofReal_pow] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

end TwoState

namespace SKQAOA

 
def pauliY {n : ℕ} (i : Fin n) : Operator n := TensorMatrix.atSite i TwoState.y

theorem pauliZ_eq_atSite {n : ℕ} (i : Fin n) :
    pauliZ i = TensorMatrix.atSite i TwoState.z := by
  simp only [TwoState.z, TensorMatrix.local_diagonal, pauliZ]
  congr 1
  funext σ
  cases h : σ i <;> simp [spin, TwoState.sign, h]

theorem mixer_conjugate_pauliZ {n : ℕ} (i : Fin n) (t : ℝ) :
    (evolution t (mixer n))ᴴ * pauliZ i * evolution t (mixer n) =
      (Real.cos (2*t) : ℂ) • pauliZ i + (Real.sin (2*t) : ℂ) • pauliY i := by
  rw [mixer_evolution_eq_tensor, pauliZ_eq_atSite,
    TensorMatrix.conjugate_local _ _ _ (fun _ => TwoState.rotation_star_mul t),
    TwoState.rotation_conjugate_z, TensorMatrix.local_add,
    TensorMatrix.local_smul, TensorMatrix.local_smul]
  rfl

def quad {n : ℕ} (ψ : State n) (A : Operator n) : ℂ := star ψ ⬝ᵥ A.mulVec ψ

theorem quad_mulVec {n : ℕ} (ψ : State n) (A U : Operator n) :
    quad (U.mulVec ψ) A = quad ψ (Uᴴ * A * U) := by
  simp only [quad, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

@[simp] theorem quad_add {n : ℕ} (ψ : State n) (A B : Operator n) :
    quad ψ (A+B) = quad ψ A + quad ψ B := by
  simp [quad, Matrix.add_mulVec, dotProduct_add]

@[simp] theorem quad_smul {n : ℕ} (ψ : State n) (a : ℂ) (A : Operator n) :
    quad ψ (a • A) = a * quad ψ A := by
  simp [quad, Matrix.smul_mulVec, dotProduct_smul]

end SKQAOA

end

end OAI
