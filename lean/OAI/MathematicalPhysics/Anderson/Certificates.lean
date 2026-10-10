import Mathlib

namespace OAI

/-! Uniform-site Anderson operators and measurable finite-volume certificate events. -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal lp ComplexConjugate

namespace Anderson

abbrev Site (d : ℕ) := Fin d → ℤ

abbrev SingleSite := Set.Icc (-1 : ℝ) 1

instance singleSiteMeasureSpace : MeasureSpace SingleSite := Measure.Subtype.measureSpace

def uniformSite : Measure SingleSite := (2 : ℝ≥0∞)⁻¹ • volume

instance uniformSite_isProbabilityMeasure : IsProbabilityMeasure uniformSite where
  measure_univ := by
    rw [uniformSite, Measure.smul_apply, smul_eq_mul,
      Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc]
    norm_num only [sub_neg_eq_add, one_add_one_eq_two, ENNReal.ofReal_ofNat]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma uniformSite_map_val :
    uniformSite.map (fun v : SingleSite => (v : ℝ)) =
      (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  rw [uniformSite, Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  congr 1
  exact (measurePreserving_subtype_coe measurableSet_Icc).map_eq

abbrev Configuration (d : ℕ) := Site d → SingleSite

def disorderLaw (d : ℕ) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Site d => uniformSite)

instance disorderLaw_isProbabilityMeasure (d : ℕ) :
    IsProbabilityMeasure (disorderLaw d) := by
  unfold disorderLaw
  infer_instance

def potential {d : ℕ} (ω : Configuration d) (x : Site d) : ℝ := ω x

lemma potential_mem_Icc {d : ℕ} (ω : Configuration d) (x : Site d) :
    potential ω x ∈ Set.Icc (-1 : ℝ) 1 := (ω x).property

lemma abs_potential_le_one {d : ℕ} (ω : Configuration d) (x : Site d) :
    |potential ω x| ≤ 1 := abs_le.mpr (potential_mem_Icc ω x)

lemma site_marginal {d : ℕ} (x : Site d) :
    (disorderLaw d).map (fun ω => ω x) = uniformSite :=
  Measure.infinitePi_map_eval _ x

lemma potential_measurable {d : ℕ} (x : Site d) :
    Measurable (fun ω : Configuration d => potential ω x) :=
  measurable_subtype_coe.comp (measurable_pi_apply x)

lemma potential_distribution {d : ℕ} (x : Site d) :
    (disorderLaw d).map (fun ω => potential ω x) =
      (2 : ℝ≥0∞)⁻¹ • volume.restrict (Set.Icc (-1 : ℝ) 1) := by
  change (disorderLaw d).map ((fun v : SingleSite => (v : ℝ)) ∘ (fun ω => ω x)) = _
  rw [← Measure.map_map measurable_subtype_coe (measurable_pi_apply x), site_marginal,
    uniformSite_map_val]

lemma cylinder_probability {d : ℕ} (s : Finset (Site d))
    (B : Site d → Set SingleSite) (hB : ∀ x ∈ s, MeasurableSet (B x)) :
    disorderLaw d ((↑s : Set (Site d)).pi B) = ∏ x ∈ s, uniformSite (B x) :=
  Measure.infinitePi_pi _ hB

abbrev StateSpace (d : ℕ) := ℓ²(Site d, ℂ)

def reindexL2 {ι : Type*} (e : ι ≃ ι) : ℓ²(ι, ℂ) ≃ₗᵢ[ℂ] ℓ²(ι, ℂ) where
  toFun f := ⟨fun i => f (e i), memℓp_gen (e.summable_iff.mpr
    ((lp.memℓp f).summable (by norm_num)))⟩
  invFun f := ⟨fun i => f (e.symm i), memℓp_gen (e.symm.summable_iff.mpr
    ((lp.memℓp f).summable (by norm_num)))⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_add' f g := by ext i; rfl
  map_smul' a f := by ext i; rfl
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change (∑' i, ‖f (e i)‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) =
      (∑' i, ‖f i‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.tsum_eq (fun i => ‖f i‖ ^ (2 : ℝ≥0∞).toReal))

def shift {d : ℕ} (a : Site d) : StateSpace d →L[ℂ] StateSpace d :=
  (reindexL2 (Equiv.addRight a)).toLinearIsometry.toContinuousLinearMap

@[simp] lemma shift_apply {d : ℕ} (a : Site d) (f : StateSpace d) (x : Site d) :
    shift a f x = f (x + a) := rfl

lemma shift_norm {d : ℕ} (a : Site d) (f : StateSpace d) :
    ‖shift a f‖ = ‖f‖ := (reindexL2 (Equiv.addRight a)).norm_map f

lemma norm_shift_le_one {d : ℕ} (a : Site d) : ‖shift a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simp [shift_norm]

lemma inner_shift {d : ℕ} (a : Site d) (f g : StateSpace d) :
    inner ℂ (shift a f) g = inner ℂ f (shift (-a) g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simpa only [shift_apply, Equiv.coe_addRight, add_neg_cancel_right] using
    (Equiv.addRight a).tsum_eq (fun x => inner ℂ (f x) (g (x + -a)))

def basisVector {d : ℕ} (j : Fin d) : Site d := Pi.single j 1

def hopping (d : ℕ) : StateSpace d →L[ℂ] StateSpace d :=
  -∑ j : Fin d, (shift (basisVector j) + shift (-basisVector j))

lemma shift_pair_isSelfAdjoint {d : ℕ} (a : Site d) :
    IsSelfAdjoint (shift a + shift (-a)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (shift a f + shift (-a) f) g =
    inner ℂ f (shift a g + shift (-a) g)
  rw [inner_add_left, inner_add_right, inner_shift, inner_shift, neg_neg]
  exact add_comm _ _

lemma hopping_isSelfAdjoint (d : ℕ) : IsSelfAdjoint (hopping d) := by
  unfold hopping
  apply IsSelfAdjoint.neg (R := StateSpace d →L[ℂ] StateSpace d)
  exact isSelfAdjoint_sum _ (fun j _ => shift_pair_isSelfAdjoint (basisVector j))

def potentialLinear {d : ℕ} (ω : Configuration d) : StateSpace d →ₗ[ℂ] StateSpace d where
  toFun f := ⟨fun x => (potential ω x : ℂ) * f x,
    (lp.memℓp f).mono' (fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_potential_le_one ω x))⟩
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' a f := by
    ext x
    change (potential ω x : ℂ) * (a * f x) = a * ((potential ω x : ℂ) * f x)
    ring

lemma potentialLinear_norm_le {d : ℕ} (ω : Configuration d) (f : StateSpace d) :
    ‖potentialLinear ω f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro x
  change ‖(potential ω x : ℂ) * f x‖ ≤ ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (abs_potential_le_one ω x)

def potentialOperator {d : ℕ} (ω : Configuration d) :
    StateSpace d →L[ℂ] StateSpace d :=
  (potentialLinear ω).mkContinuous 1 (fun f => by
    simpa only [one_mul] using potentialLinear_norm_le ω f)

@[simp] lemma potentialOperator_apply {d : ℕ} (ω : Configuration d)
    (f : StateSpace d) (x : Site d) :
    potentialOperator ω f x = (potential ω x : ℂ) * f x := rfl

lemma norm_potentialOperator_le_one {d : ℕ} (ω : Configuration d) :
    ‖potentialOperator ω‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖potentialLinear ω f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using potentialLinear_norm_le ω f

lemma potentialOperator_isSelfAdjoint {d : ℕ} (ω : Configuration d) :
    IsSelfAdjoint (potentialOperator ω) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  change inner ℂ ((potential ω x : ℂ) • f x) (g x) =
    inner ℂ (f x) ((potential ω x : ℂ) • g x)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

def hamiltonian {d : ℕ} (coupling : ℝ) (ω : Configuration d) :
    StateSpace d →L[ℂ] StateSpace d :=
  hopping d + (coupling : ℂ) • potentialOperator ω

lemma hamiltonian_isSelfAdjoint {d : ℕ} (coupling : ℝ) (ω : Configuration d) :
    IsSelfAdjoint (hamiltonian coupling ω) := by
  exact (hopping_isSelfAdjoint d).add (R := StateSpace d →L[ℂ] StateSpace d)
    ((show IsSelfAdjoint (coupling : ℂ) from Complex.conj_ofReal coupling).smul
      (A := StateSpace d →L[ℂ] StateSpace d)
      (potentialOperator_isSelfAdjoint ω))

@[simp] lemma hamiltonian_apply {d : ℕ} (coupling : ℝ) (ω : Configuration d)
    (f : StateSpace d) (x : Site d) :
    hamiltonian coupling ω f x =
      -(∑ j : Fin d, (f (x + basisVector j) + f (x - basisVector j))) +
        (coupling * potential ω x : ℂ) * f x := by
  simp only [hamiltonian, hopping, add_apply, neg_apply, sum_apply, smul_apply,
    lp.coeFn_add, lp.coeFn_neg, lp.coeFn_sum, lp.coeFn_smul, Pi.add_apply,
    Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, shift_apply,
    potentialOperator_apply, smul_eq_mul, sub_eq_add_neg, mul_assoc]

lemma norm_hopping_le (d : ℕ) : ‖hopping d‖ ≤ 2 * (d : ℝ) := by
  calc
    ‖hopping d‖ = ‖∑ j : Fin d, (shift (basisVector j) + shift (-basisVector j))‖ :=
      norm_neg _
    _ ≤ ∑ j : Fin d, ‖shift (basisVector j) + shift (-basisVector j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact (norm_add_le _ _).trans (by
        have h₁ := norm_shift_le_one (basisVector j)
        have h₂ := norm_shift_le_one (-basisVector j)
        linarith)
    _ = 2 * (d : ℝ) := by simp [mul_comm]

lemma norm_hamiltonian_le {d : ℕ} (coupling : ℝ) (ω : Configuration d) :
    ‖hamiltonian coupling ω‖ ≤ 2 * (d : ℝ) + |coupling| := by
  calc
    ‖hamiltonian coupling ω‖ ≤ ‖hopping d‖ + ‖(coupling : ℂ) • potentialOperator ω‖ := norm_add_le _ _
    _ = ‖hopping d‖ + |coupling| * ‖potentialOperator ω‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * (d : ℝ) + |coupling| := by
      have hV := mul_le_of_le_one_right (abs_nonneg coupling) (norm_potentialOperator_le_one ω)
      exact add_le_add (norm_hopping_le d) hV

def higherDimWindow (d : ℕ) : Set ℝ :=
  Set.Ioo (-2 * (d : ℝ) + 1 / 200) (-2 * (d : ℝ) + 1 / 100)

def energyWindow (d : ℕ) (e₂ : ℝ) : Set ℝ :=
  if d = 3 then Set.Ioo (-6 + e₂ / 2) (-6 + e₂) else higherDimWindow d

@[simp] lemma energyWindow_three (e₂ : ℝ) :
    energyWindow 3 e₂ = Set.Ioo (-6 + e₂ / 2) (-6 + e₂) := by
  simp [energyWindow]

lemma energyWindow_of_four_le {d : ℕ} (hd : 4 ≤ d) (e₂ : ℝ) :
    energyWindow d e₂ = higherDimWindow d := by
  rw [energyWindow, ite_eq_right (by omega)]

lemma energyWindow_open (d : ℕ) (e₂ : ℝ) : IsOpen (energyWindow d e₂) := by
  unfold energyWindow higherDimWindow
  split_ifs <;> exact isOpen_Ioo

lemma energyWindow_nonempty {d : ℕ} {e₂ : ℝ} (he : 0 < e₂) :
    (energyWindow d e₂).Nonempty := by
  unfold energyWindow higherDimWindow
  split_ifs
  · exact Set.nonempty_Ioo.mpr (by linarith)
  · exact Set.nonempty_Ioo.mpr (by linarith)

lemma energyWindow_subset_freeBand {d : ℕ} (hd : 3 ≤ d) {e₂ : ℝ}
    (he : e₂ ∈ Set.Ioo (0 : ℝ) (1 / 100)) :
    energyWindow d e₂ ⊆ Set.Ioo (-2 * (d : ℝ)) (2 * (d : ℝ)) := by
  intro E hE
  by_cases h3 : d = 3
  · subst d
    rw [energyWindow_three] at hE
    constructor <;> norm_num at * <;> linarith [hE.1, hE.2, he.1, he.2]
  · change E ∈ (if d = 3 then _ else _) at hE
    rw [ite_eq_right h3] at hE
    change -2 * (d : ℝ) + 1 / 200 < E ∧ E < -2 * (d : ℝ) + 1 / 100 at hE
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    constructor <;> linarith [hE.1, hE.2]

def sideLength (m : ℕ) : ℕ := 4 ^ (20 * m)

instance sideLength_neZero (m : ℕ) : NeZero (sideLength m) :=
  ⟨pow_ne_zero _ (by norm_num)⟩

abbrev Torus (d m : ℕ) := Fin d → ZMod (sideLength m)

abbrev TorusConfiguration (d m : ℕ) := Torus d m → SingleSite

def torusLaw (d m : ℕ) : Measure (TorusConfiguration d m) :=
  Measure.pi (fun _ : Torus d m => uniformSite)

instance torusLaw_isProbabilityMeasure (d m : ℕ) : IsProbabilityMeasure (torusLaw d m) := by
  unfold torusLaw
  infer_instance

lemma torus_card (d m : ℕ) : Fintype.card (Torus d m) = (sideLength m) ^ d := by
  simp [Torus, ZMod.card]

def torusBasisVector {d m : ℕ} (j : Fin d) : Torus d m := Pi.single j 1

def periodicHamiltonian {d m : ℕ} (coupling : ℝ) (ω : TorusConfiguration d m) :
    Matrix (Torus d m) (Torus d m) ℂ := fun x y =>
  -(∑ j : Fin d,
    ((if y = x + torusBasisVector j then (1 : ℂ) else 0) +
     (if y = x - torusBasisVector j then (1 : ℂ) else 0))) +
    (if x = y then (coupling * (ω x : ℝ) : ℂ) else 0)

def diagonalOn {d m : ℕ} (A : Finset (Torus d m)) (r : Torus d m → ℂ) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  Matrix.diagonal (fun i => if i ∈ A then r i else 0)

def scaleCoupling (n₀ : ℕ) (u : ℝ) : ℝ := Real.sqrt (3 * u) / (2 : ℝ) ^ n₀

def scaleHeight (m : ℕ) (u : ℝ) : ℝ := u / (4 : ℝ) ^ m

def certificateMatrix {d : ℕ} (n₀ m : ℕ) (u E : ℝ)
    (ω : TorusConfiguration d m) (A : Finset (Torus d m)) (r : Torus d m → ℂ) :
    Matrix (Torus d m) (Torus d m) ℂ :=
  periodicHamiltonian (scaleCoupling n₀ u) ω - (E : ℂ) • 1 -
    (scaleHeight m u : ℂ) • diagonalOn A r

def certificateEvent (d k n₀ m : ℕ) (u E : ℝ) : Set (TorusConfiguration d m) :=
  {ω | ∃ (A : Finset (Torus d m)) (r : Torus d m → ℂ)
      (G : Matrix (Torus d m) (Torus d m) ℂ),
    Fintype.card (Torus d m) ≤ 2 * A.card ∧
    (∀ i ∈ A, ‖r i‖ ≤ (k : ℝ) ∧ 1 / (k : ℝ) ≤ (r i).im) ∧
    certificateMatrix n₀ m u E ω A r * G = 1 ∧
    G * certificateMatrix n₀ m u E ω A r = 1 ∧
    (∀ i ∈ A, 1 / (k : ℝ) ≤ (G i i).im)}

lemma continuous_periodicHamiltonian (d n : ℕ) (coupling : ℝ) :
    Continuous (periodicHamiltonian coupling : TorusConfiguration d n →
      Matrix (Torus d n) (Torus d n) ℂ) := by
  apply continuous_matrix
  intro x y
  unfold periodicHamiltonian
  split_ifs <;> fun_prop

lemma continuous_diagonalOn {d m : ℕ} (A : Finset (Torus d m)) :
    Continuous (diagonalOn A) := by
  apply continuous_matrix
  intro x y
  change Continuous (fun a : Torus d m → ℂ =>
    if x = y then (if x ∈ A then a x else 0) else 0)
  split_ifs <;> fun_prop

lemma certificateEvent_measurableSet (d k n₀ m : ℕ) (u E : ℝ) :
    MeasurableSet (certificateEvent d k n₀ m u E) := by
  classical
  let X := TorusConfiguration d m ×
    (Torus d m → ℂ) × Matrix (Torus d m) (Torus d m) ℂ
  have : CompactSpace SingleSite := isCompact_iff_compactSpace.mp isCompact_Icc
  have : SigmaCompactSpace X := by
    change SigmaCompactSpace (TorusConfiguration d m ×
      (Torus d m → ℂ) × (Torus d m → Torus d m → ℂ))
    infer_instance
  let C (A : Finset (Torus d m)) : Set X := {p |
    (∀ i ∈ A, ‖p.2.1 i‖ ≤ (k : ℝ) ∧ 1 / (k : ℝ) ≤ (p.2.1 i).im) ∧
    certificateMatrix n₀ m u E p.1 A p.2.1 * p.2.2 = 1 ∧
    p.2.2 * certificateMatrix n₀ m u E p.1 A p.2.1 = 1 ∧
    (∀ i ∈ A, 1 / (k : ℝ) ≤ (p.2.2 i i).im)}
  have hc (A : Finset (Torus d m)) : IsClosed (C A) := by
    have hB : Continuous (fun p : X => certificateMatrix n₀ m u E p.1 A p.2.1) := by
      unfold certificateMatrix
      exact ((continuous_periodicHamiltonian d m _).comp continuous_fst).sub
        continuous_const |>.sub
        (((continuous_diagonalOn A).comp (continuous_fst.comp continuous_snd)).const_smul (scaleHeight m u : ℂ))
    have hr : IsClosed {p : X | ∀ i ∈ A,
        ‖p.2.1 i‖ ≤ (k : ℝ) ∧ 1 / (k : ℝ) ≤ (p.2.1 i).im} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      have h₁ : IsClosed {p : X | ‖p.2.1 i‖ ≤ (k : ℝ)} :=
        isClosed_le (by fun_prop) continuous_const
      have h₂ : IsClosed {p : X | 1 / (k : ℝ) ≤ (p.2.1 i).im} :=
        isClosed_le continuous_const (by fun_prop)
      exact h₁.inter h₂
    have hG : IsClosed {p : X | ∀ i ∈ A, 1 / (k : ℝ) ≤ (p.2.2 i i).im} := by
      simp only [Set.ofPred_forall]
      apply isClosed_iInter
      intro i
      apply isClosed_iInter
      intro _
      exact isClosed_le continuous_const (by fun_prop)
    have hGcont : Continuous (fun p : X => p.2.2) := continuous_snd.comp continuous_snd
    exact hr.inter ((isClosed_eq (hB.mul hGcont) continuous_const).inter
      ((isClosed_eq (hGcont.mul hB) continuous_const).inter hG))
  have hm (A : Finset (Torus d m)) : MeasurableSet (Prod.fst '' C A) := by
    have hs : IsSigmaCompact (C A) :=
      isSigmaCompact_univ.of_isClosed_subset (hc A) (Set.subset_univ _)
    obtain ⟨K, hK, hEq⟩ := hs.image continuous_fst
    rw [← hEq]
    exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)
  have heq : certificateEvent d k n₀ m u E =
      ⋃ A : Finset (Torus d m), ⋃ (_ : Fintype.card (Torus d m) ≤ 2 * A.card),
        Prod.fst '' C A := by
    ext ω
    simp only [certificateEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_image, Prod.exists, C]
    constructor
    · rintro ⟨A, r, G, hA, hr, hBG, hGB, hG⟩
      exact ⟨A, hA, ω, r, G, ⟨hr, hBG, hGB, hG⟩, rfl⟩
    · rintro ⟨A, hA, ω', r, G, ⟨hr, hBG, hGB, hG⟩, rfl⟩
      exact ⟨A, r, G, hA, hr, hBG, hGB, hG⟩
  rw [heq]
  exact MeasurableSet.iUnion fun A => MeasurableSet.iUnion fun _ => hm A

def thresholdCriterion (d k : ℕ) : Prop :=
  10 ≤ k ∧
  ∀ n₀ : ℕ, k ≤ n₀ → ∀ m : ℕ, 4 * n₀ ≤ m →
    ∀ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 → ∀ E : ℝ, E ∈ higherDimWindow d →
      (1 / 2 : ℝ≥0∞) ≤ torusLaw d m (certificateEvent d k n₀ m u E)

lemma certificateEvent_mono {d j k n₀ m : ℕ} {u E : ℝ}
    (hj : 0 < j) (hjk : j ≤ k) :
    certificateEvent d j n₀ m u E ⊆ certificateEvent d k n₀ m u E := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have hrecip : 1 / (k : ℝ) ≤ 1 / (j : ℝ) := one_div_le_one_div_of_le hjR hjkR
  rintro ω ⟨A, r, G, hA, hr, hBG, hGB, hG⟩
  exact ⟨A, r, G, hA,
    fun i hi => ⟨(hr i hi).1.trans hjkR, hrecip.trans (hr i hi).2⟩,
    hBG, hGB, fun i hi => hrecip.trans (hG i hi)⟩

lemma thresholdCriterion_mono {d j k : ℕ} (hj : thresholdCriterion d j) (hjk : j ≤ k) :
    thresholdCriterion d k := by
  have hjpos : 0 < j := lt_of_lt_of_le (by decide : 0 < 10) hj.1
  refine ⟨hj.1.trans hjk, ?_⟩
  intro n₀ hn m hm u hu E hE
  exact (hj.2 n₀ (hjk.trans hn) m hm u hu E hE).trans
    (measure_mono (certificateEvent_mono hjpos hjk))

def finiteBoxThreshold (d : ℕ) (bound : ℝ) : Prop :=
  ∃ k : ℕ, IsLeast {n : ℕ | thresholdCriterion d n} k ∧
    bound = Real.sqrt 3 / (2 : ℝ) ^ k

lemma finiteBoxThreshold_exists_iff (d : ℕ) :
    (∃ a : ℝ, finiteBoxThreshold d a) ↔ ∃ k : ℕ, thresholdCriterion d k := by
  classical
  constructor
  · rintro ⟨a, k, hk, _⟩
    exact ⟨k, hk.1⟩
  · intro h
    refine ⟨Real.sqrt 3 / (2 : ℝ) ^ Nat.find h, Nat.find h, ?_, rfl⟩
    exact ⟨Nat.find_spec h, fun _ hn => Nat.find_min' h hn⟩

lemma thresholdIndex_unique {d j k : ℕ}
    (hj : IsLeast {n : ℕ | thresholdCriterion d n} j)
    (hk : IsLeast {n : ℕ | thresholdCriterion d n} k) : j = k :=
  le_antisymm (hj.2 hk.1) (hk.2 hj.1)

lemma finiteBoxThreshold_unique {d : ℕ} {a b : ℝ}
    (ha : finiteBoxThreshold d a) (hb : finiteBoxThreshold d b) : a = b := by
  obtain ⟨j, hj, rfl⟩ := ha
  obtain ⟨k, hk, rfl⟩ := hb
  rw [thresholdIndex_unique hj hk]

lemma finiteBoxThreshold_pos {d : ℕ} {a : ℝ} (ha : finiteBoxThreshold d a) : 0 < a := by
  obtain ⟨k, _, rfl⟩ := ha
  positivity

lemma coupling_parametrization {k : ℕ} {coupling : ℝ} (hc : 0 < coupling)
    (hk : coupling < Real.sqrt 3 / (2 : ℝ) ^ k) :
    ∃ n₀ : ℕ, k ≤ n₀ ∧ ∃ u : ℝ, u ∈ Set.Ioc (1 / 4 : ℝ) 1 ∧
      scaleCoupling n₀ u = coupling := by
  have hpow (n : ℕ) : (4 : ℝ) ^ n = ((2 : ℝ) ^ n) ^ 2 := by
    calc
      (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
      _ = ((2 : ℝ) ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hc2 : 0 < coupling ^ 2 := sq_pos_of_pos hc
  have hk' : coupling * (2 : ℝ) ^ k < Real.sqrt 3 :=
    (lt_div_iff₀ (by positivity)).mp hk
  have hsq : (coupling * (2 : ℝ) ^ k) ^ 2 < 3 := by
    have h := (sq_lt_sq₀ (by positivity : 0 ≤ coupling * (2 : ℝ) ^ k)
      (Real.sqrt_nonneg 3)).mpr hk'
    simpa only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] using h
  have hbase : (4 : ℝ) ^ k < 3 / coupling ^ 2 := by
    apply (lt_div_iff₀ hc2).mpr
    rw [hpow]
    nlinarith [hsq]
  have hx : 1 ≤ 3 / coupling ^ 2 :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)).trans hbase.le
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 4)
  have hkn : k ≤ n := by
    by_contra h
    have hn : n + 1 ≤ k := by omega
    have hp : (4 : ℝ) ^ (n + 1) ≤ 4 ^ k := by gcongr; norm_num
    linarith
  let u : ℝ := coupling ^ 2 / 3 * (4 : ℝ) ^ n
  have hulo : 1 / 4 < u := by
    have h := (div_lt_iff₀ hc2).mp hnhi
    rw [pow_succ] at h
    dsimp [u]
    nlinarith
  have huhi : u ≤ 1 := by
    have h := (le_div_iff₀ hc2).mp hnlo
    dsimp [u]
    nlinarith
  refine ⟨n, hkn, u, ⟨hulo, huhi⟩, ?_⟩
  have hrel : 3 * u = (coupling * (2 : ℝ) ^ n) ^ 2 := by
    dsimp [u]
    rw [hpow]
    ring
  rw [scaleCoupling, hrel, Real.sqrt_sq (by positivity)]
  exact mul_div_cancel_right₀ coupling (by positivity)

structure SpectralResolution {d : ℕ} (T : StateSpace d →L[ℂ] StateSpace d) where
  projection : Set ℝ → StateSpace d →L[ℂ] StateSpace d
  projection_empty : projection ∅ = 0
  projection_univ : projection Set.univ = 1
  projection_selfAdjoint : ∀ B : Set ℝ, MeasurableSet B → IsSelfAdjoint (projection B)
  projection_inter : ∀ B C : Set ℝ, MeasurableSet B → MeasurableSet C →
    projection (B ∩ C) = projection B * projection C
  projection_iUnion : ∀ B : ℕ → Set ℝ, (∀ n, MeasurableSet (B n)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) → ∀ v : StateSpace d,
      HasSum (fun n => projection (B n) v) (projection (⋃ n, B n) v)
  vectorMeasure : StateSpace d → Measure ℝ
  finite_vectorMeasure : ∀ v, IsFiniteMeasure (vectorMeasure v)
  vectorMeasure_apply : ∀ (v : StateSpace d) (B : Set ℝ), MeasurableSet B →
    vectorMeasure v B = ENNReal.ofReal (‖projection B v‖ ^ 2)
  vectorMeasure_supported : ∀ v,
    vectorMeasure v (Set.Icc (-‖T‖) ‖T‖)ᶜ = 0
  vectorMeasure_moments : ∀ (v : StateSpace d) (n : ℕ),
    ∫ t : ℝ, t ^ n ∂vectorMeasure v = (inner ℂ v ((T ^ n) v)).re

namespace SpectralResolution

variable {d : ℕ} {T : StateSpace d →L[ℂ] StateSpace d} (S : SpectralResolution T)

def acVectors : Set (StateSpace d) := {v | S.vectorMeasure v ≪ volume}

lemma mem_acVectors_iff (v : StateSpace d) :
    v ∈ S.acVectors ↔ ∀ B : Set ℝ, MeasurableSet B → volume B = 0 → S.projection B v = 0 := by
  constructor
  · intro hv B hB hnull
    have h := hv hnull
    rw [S.vectorMeasure_apply v B hB, ENNReal.ofReal_eq_zero] at h
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (S.projection B v)]
  · intro hv
    apply Measure.AbsolutelyContinuous.mk
    intro B hB hnull
    rw [S.vectorMeasure_apply v B hB, hv B hB hnull]
    simp

def acSubspace : Submodule ℂ (StateSpace d) where
  carrier := S.acVectors
  zero_mem' := (S.mem_acVectors_iff 0).mpr (by intros; simp)
  add_mem' := by
    intro x y hx hy
    apply (S.mem_acVectors_iff (x + y)).mpr
    intro B hB hnull
    rw [map_add, (S.mem_acVectors_iff x).mp hx B hB hnull,
      (S.mem_acVectors_iff y).mp hy B hB hnull, add_zero]
  smul_mem' := by
    intro c x hx
    apply (S.mem_acVectors_iff (c • x)).mpr
    intro B hB hnull
    rw [map_smul, (S.mem_acVectors_iff x).mp hx B hB hnull, smul_zero]

@[simp] lemma mem_acSubspace (v : StateSpace d) :
    v ∈ S.acSubspace ↔ S.vectorMeasure v ≪ volume := Iff.rfl

lemma isClosed_acVectors : IsClosed S.acVectors := by
  have heq : S.acVectors = {v | ∀ B : Set ℝ,
      MeasurableSet B → volume B = 0 → S.projection B v = 0} :=
    Set.ext S.mem_acVectors_iff
  rw [heq]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro B
  apply isClosed_iInter
  intro _
  apply isClosed_iInter
  intro _
  exact isClosed_eq (S.projection B).continuous continuous_const

def purelyACOn (I : Set ℝ) : Prop :=
  ∀ v : StateSpace d, (S.vectorMeasure v).restrict I ≪ volume

lemma projection_idempotent {B : Set ℝ} (hB : MeasurableSet B) :
    S.projection B * S.projection B = S.projection B := by
  rw [← S.projection_inter B B hB hB, Set.inter_self]

lemma vectorMeasure_univ (v : StateSpace d) :
    S.vectorMeasure v Set.univ = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [S.vectorMeasure_apply v Set.univ MeasurableSet.univ, S.projection_univ]
  rfl

lemma vectorMeasure_projection {I : Set ℝ} (hI : MeasurableSet I) (v : StateSpace d) :
    S.vectorMeasure (S.projection I v) = (S.vectorMeasure v).restrict I := by
  ext B hB
  rw [S.vectorMeasure_apply _ B hB, Measure.restrict_apply hB,
    S.vectorMeasure_apply v (B ∩ I) (hB.inter hI), S.projection_inter B I hB hI]
  rfl

lemma range_subset_acVectors_iff {I : Set ℝ} (hI : MeasurableSet I) :
    Set.range (S.projection I) ⊆ S.acVectors ↔ S.purelyACOn I := by
  constructor
  · intro h v
    rw [← S.vectorMeasure_projection hI v]
    exact h ⟨v, rfl⟩
  · rintro h _ ⟨v, rfl⟩
    change S.vectorMeasure (S.projection I v) ≪ volume
    rw [S.vectorMeasure_projection hI v]
    exact h v

end SpectralResolution

end Anderson

end

end OAI
