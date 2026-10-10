import OAI.InformationTheory.PhotonNumber.Generator
import OAI.InformationTheory.PhotonNumber.SpectralLog
import OAI.InformationTheory.PhotonNumber.Continuity

namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace Annihilation
open EntropyPhotonNumber QuantumTrace WeightedShift
open scoped ComplexConjugate
variable {n : ℕ}

def diagonal (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ k, |f k| ≤ C) :
    Fock n →L[ℂ] Fock n :=
  pullCLM id Function.injective_id (fun k => (f k:ℂ)) C hC
    (fun k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hf k)

@[simp] theorem diagonal_apply (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) (x : Fock n) (k : NumberIndex n) :
    diagonal f C hC hf x k=(f k:ℂ)*x k := rfl

theorem diagonal_quadratic (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) (x : Fock n) :
    HasSum (fun k => f k*‖x k‖^2) (inner ℂ x (diagonal f C hC hf x)).re := by
  have hh := (lp.hasSum_inner (𝕜 := ℂ) x (diagonal f C hC hf x)).mapL Complex.reCLM
  convert! hh using 1
  ext k
  simp only [RCLike.inner_apply, diagonal_apply, Complex.reCLM_apply]
  rw [mul_assoc, Complex.mul_conj, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]

theorem gain_lower_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖gain j false x k‖^2 = numberWeight k^4*((k j:ℝ)+1)/numberWeight (up j k)^6 * ‖x (up j k)‖^2 := by
  simp only [gain, Bool.false_eq_true, ↓reduceIte, sandwich_apply, coefficient, norm_mul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (show 0≤(k j:ℝ)+1 by positivity)]
  ring

theorem gain_raise_sq (j : Fin n) (x : Fock n) (k : NumberIndex n) :
    ‖gain j true x (up j k)‖^2 = numberWeight (up j k)^4*((k j:ℝ)+1)/numberWeight k^6 * ‖x k‖^2 := by
  simp only [gain, ↓reduceIte, creationSandwich_up, creationCoefficient, norm_mul,
    mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (show 0≤(k j:ℝ)+1 by positivity)]
  ring

theorem gain_raise_zero (j : Fin n) (x : Fock n) (k : NumberIndex n) (hk : k j=0) :
    gain j true x k=0 := creationSandwich_zero 2 3 (by omega) j x k hk

theorem gain_lower_diagonal (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k /numberWeight k^4| ≤ C) (j : Fin n) (x : Fock n) :
    HasSum (fun k => (k j:ℝ)*f (down j k)/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (gain j false x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (gain j false x))).re := by
  have hh := diagonal_quadratic (fun k => f k/numberWeight k^4) C hC hf (gain j false x)
  have he (k : NumberIndex n) : f k/numberWeight k^4 *‖gain j false x k‖^2 =
      (((up j k) j:ℝ)*f (down j (up j k))/numberWeight (up j k)^6 *‖x (up j k)‖^2) := by
    rw [gain_lower_sq, up_same, down_up, Nat.cast_add, Nat.cast_one]
    have hw : numberWeight k ≠ 0 := by linarith [numberWeight_one_le k]
    field_simp
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      (k j:ℝ)*f (down j k)/numberWeight k^6 *‖x k‖^2=0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [he]
    · exact (hk ⟨l,rfl⟩).elim
  apply (up_injective j).hasSum_iff hz |>.mp
  convert! hh using 1
  ext k
  exact (he k).symm

theorem gain_raise_diagonal (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (j : Fin n) (x : Fock n) :
    HasSum (fun k => ((k j:ℝ)+1)*f (up j k)/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (gain j true x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (gain j true x))).re := by
  have hz (k : NumberIndex n) (hk : k ∉ Set.range (up j)) :
      f k/numberWeight k^4 *‖gain j true x k‖^2=0 := by
    rcases index_cases j k with he | ⟨l,rfl⟩
    · simp [gain_raise_zero _ _ _ he]
    · exact (hk ⟨l,rfl⟩).elim
  have hh := (up_injective j).hasSum_iff hz |>.mpr
    (diagonal_quadratic (fun k => f k/numberWeight k^4) C hC hf (gain j true x))
  convert! hh using 1
  ext k
  simp only [Function.comp_def, gain_raise_sq]
  have hw : numberWeight (up j k) ≠ 0 := by linarith [numberWeight_one_le (up j k)]
  field_simp

theorem diagonal_mode_left (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (j : Fin n) (u : Bool) (x : Fock n) :
    HasSum (fun k => ((k j:ℝ)+(if u then 1 else 0))*f k/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (inverseWeight 1 x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (modeBound j u x))).re := by
  have hh := (lp.hasSum_inner (𝕜 := ℂ) (inverseWeight 1 x)
    (diagonal (fun k => f k/numberWeight k^4) C hC hf (modeBound j u x))).mapL Complex.reCLM
  convert! hh using 1
  ext k
  simp only [RCLike.inner_apply, diagonal_apply, inverseWeight_apply, modeBound_apply,
    map_mul, map_inv₀, map_pow, Complex.conj_ofReal, Complex.reCLM_apply]
  have he : ((f k/numberWeight k^4:ℝ):ℂ) *
      (((((k j:ℝ)+(if u then 1 else 0))/numberWeight k:ℝ):ℂ)*x k) *
      (((numberWeight k:ℂ)^1)⁻¹*conj (x k)) =
      (((((k j:ℝ)+(if u then 1 else 0))*f k/numberWeight k^6):ℝ):ℂ)*(x k*conj (x k)) := by
    push_cast
    ring
  rw [he, Complex.mul_conj, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]

theorem diagonal_selfAdjoint (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k| ≤ C) : IsSelfAdjoint (diagonal f C hC hf) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  apply HasSum.unique (lp.hasSum_inner (𝕜 := ℂ) (diagonal f C hC hf x) y)
  convert! lp.hasSum_inner (𝕜 := ℂ) x (diagonal f C hC hf y) using 1
  ext k
  simp only [diagonal_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem diagonal_mode_right (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (j : Fin n) (u : Bool) (x : Fock n) :
    HasSum (fun k => ((k j:ℝ)+(if u then 1 else 0))*f k/numberWeight k^6 *‖x k‖^2)
      (inner ℂ (modeBound j u x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (inverseWeight 1 x))).re := by
  have he := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (diagonal_selfAdjoint _ C hC hf)
    (modeBound j u x) (inverseWeight 1 x)
  have ht := congrArg Complex.re he
  have hi : (inner ℂ (diagonal (fun k => f k/numberWeight k^4) C hC hf (modeBound j u x)) (inverseWeight 1 x)).re =
      (inner ℂ (inverseWeight 1 x) (diagonal (fun k => f k/numberWeight k^4) C hC hf (modeBound j u x))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  exact (hi.symm.trans ht) ▸ diagonal_mode_left f C hC hf j u x
end Annihilation

namespace WeightedGenerator
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped BigOperators
variable {n : ℕ} {I : Type*}

def columnPairing (r : ℝ) (x : Fock n) (Z : Fock n →L[ℂ] Fock n) : ℝ :=
  ∑ j, ((r+1)*((inner ℂ (gain j false x) (Z (gain j false x))).re-
      ((inner ℂ (inverseWeight 1 x) (Z (modeBound j false x))).re+
       (inner ℂ (modeBound j false x) (Z (inverseWeight 1 x))).re)/2)+
    r*((inner ℂ (gain j true x) (Z (gain j true x))).re-
      ((inner ℂ (inverseWeight 1 x) (Z (modeBound j true x))).re+
       (inner ℂ (modeBound j true x) (Z (inverseWeight 1 x))).re)/2))

theorem columnPairing_hasSum (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun i => columnPairing r (x i) Z) (pairing r x Z).re := by
  have ha (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (gain j u)
  have hb (j : Fin n) (u : Bool) := CrossEnsemble.applied_summable hx (modeBound j u)
  have hc := CrossEnsemble.applied_summable hx (inverseWeight 1)
  have h (j : Fin n) (u : Bool) :=
    ((CrossEnsemble.pairing_summable (ha j u) (ha j u) Z).hasSum.sub
      ((((CrossEnsemble.pairing_summable (hb j u) hc Z).hasSum).add
        ((CrossEnsemble.pairing_summable hc (hb j u) Z).hasSum)).mul_left (2:ℂ)⁻¹))
  have hh := (hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    ((h j false).mul_left ((r+1:ℝ):ℂ)).add ((h j true).mul_left (r:ℂ))).mapL Complex.reCLM
  convert! hh using 1
  · ext i
    simp only [columnPairing, Complex.reCLM_apply, Complex.re_sum, Complex.add_re,
      Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    ext j
    norm_num
    ring

def drift (r : ℝ) (f : NumberIndex n → ℝ) (k : NumberIndex n) : ℝ :=
  ∑ j, ((r+1)*(k j:ℝ)*(f (down j k)-f k)+r*((k j:ℝ)+1)*(f (up j k)-f k))

theorem mode_pairing_hasSum (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (x : Fock n) (j : Fin n) (u : Bool) :
    let Z := diagonal (fun k => f k/numberWeight k^4) C hC hf
    HasSum (fun k => ((k j:ℝ)+(if u then 1 else 0))*f k/numberWeight k^6*‖x k‖^2)
      (((inner ℂ (inverseWeight 1 x) (Z (modeBound j u x))).re+
        (inner ℂ (modeBound j u x) (Z (inverseWeight 1 x))).re)/2) := by
  have h₁ := diagonal_mode_left f C hC hf j u x
  have h₂ := diagonal_mode_right f C hC hf j u x
  have hh := (h₁.add h₂).div_const 2
  convert! hh using 1
  ext k
  ring

def componentPairing (r : ℝ) (x : Fock n) (Z : Fock n →L[ℂ] Fock n) (j : Fin n) : ℝ :=
  (r+1)*((inner ℂ (gain j false x) (Z (gain j false x))).re-
    ((inner ℂ (inverseWeight 1 x) (Z (modeBound j false x))).re+
     (inner ℂ (modeBound j false x) (Z (inverseWeight 1 x))).re)/2)+
  r*((inner ℂ (gain j true x) (Z (gain j true x))).re-
    ((inner ℂ (inverseWeight 1 x) (Z (modeBound j true x))).re+
     (inner ℂ (modeBound j true x) (Z (inverseWeight 1 x))).re)/2)

theorem component_pairing_hasSum (r : ℝ) (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (x : Fock n) (j : Fin n) :
    HasSum
      (fun k => ((r+1)*(k j:ℝ)*(f (down j k)-f k)+r*((k j:ℝ)+1)*(f (up j k)-f k))/numberWeight k^6*‖x k‖^2)
      (componentPairing r x (diagonal (fun k => f k/numberWeight k^4) C hC hf) j) := by
  have h₁ := (gain_lower_diagonal f C hC hf j x).sub (mode_pairing_hasSum f C hC hf x j false)
  have h₂ := (gain_raise_diagonal f C hC hf j x).sub (mode_pairing_hasSum f C hC hf x j true)
  have hh := (h₁.mul_left (r+1)).add (h₂.mul_left r)
  convert! hh using 1
  ext k
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

theorem drift_column (r : ℝ) (f : NumberIndex n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C) (x : Fock n) :
    HasSum (fun k => drift r f k/numberWeight k^6*‖x k‖^2)
      (columnPairing r x (diagonal (fun k => f k/numberWeight k^4) C hC hf)) := by
  have hh := hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    component_pairing_hasSum r f C hC hf x j
  convert! hh using 1
  · ext k
    simp only [drift, Finset.sum_div, Finset.sum_mul]
end WeightedGenerator

namespace WeightedShift
variable {I K : Type*}
theorem family_coordinates_summable (x : I → H K) (hx : Summable (fun i => ‖x i‖^2)) :
    Summable (fun ik : I × K => ‖x ik.1 ik.2‖^2) := by
  exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    ⟨fun i => (hasSum_square (x i)).summable,
      by simpa only [(hasSum_square _).tsum_eq] using hx⟩
end WeightedShift

namespace EntropyPhotonNumber
open QuantumTrace WeightedShift Annihilation
variable {n : ℕ}

theorem weightedRoot_row (m : ℕ) (ρ : State n) (hm : FiniteMoment (2*m) ρ)
    (k : NumberIndex n) :
    HasSum (fun i => ‖weightedRoot m ρ hm i k‖^2)
      (numberWeight k^(2*m)*(entry ρ.op k k).re) := by
  have hh := (TraceEnsemble.hasSum_quadratic (rootColumn_norm ρ).summable (numberKet k)).mul_left (numberWeight k^(2*m))
  rw [rootColumn_operator] at hh
  convert! hh using 1
  ext i
  simp only [weightedRoot_apply, numberKet, lp.inner_single_left, RCLike.inner_apply,
    map_one, mul_one, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← pow_mul, mul_comm m 2]

theorem thermalGenerator_drift (r : ℝ) (ρ : State n) (hm : FiniteMoment 6 ρ)
    (f : NumberIndex n → ℝ) (C D : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, |f k/numberWeight k^4| ≤ C)
    (hd : ∀ k, |WeightedGenerator.drift r f k/numberWeight k^6| ≤ D) :
    HasSum (fun k => WeightedGenerator.drift r f k*(entry ρ.op k k).re)
      (WeightedGenerator.pairing r (weightedRoot 3 ρ hm)
        (diagonal (fun k => f k/numberWeight k^4) C hC hf)).re := by
  let x := weightedRoot 3 ρ hm
  let a := fun (i k : NumberIndex n) => WeightedGenerator.drift r f k/numberWeight k^6*‖x i k‖^2
  have hx := weightedRoot_summable 3 ρ hm
  have hp : Summable (Function.uncurry a) := by
    apply ((family_coordinates_summable x hx).mul_left D).of_norm_bounded
    intro ik
    change ‖WeightedGenerator.drift r f ik.2/numberWeight ik.2^6*‖x ik.1 ik.2‖^2‖ ≤ D*‖x ik.1 ik.2‖^2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖x ik.1 ik.2‖)]
    exact mul_le_mul_of_nonneg_right (hd _) (sq_nonneg _)
  have hc (i : NumberIndex n) := WeightedGenerator.drift_column r f C hC hf (x i)
  have hr (k : NumberIndex n) : HasSum (fun i => a i k)
      (WeightedGenerator.drift r f k*(entry ρ.op k k).re) := by
    have he := (weightedRoot_row 3 ρ hm k).mul_left (WeightedGenerator.drift r f k/numberWeight k^6)
    convert! he using 1
    have hne : numberWeight k ≠ 0 := by linarith [numberWeight_one_le k]
    field_simp
  have he : (∑' k, ∑' i, a i k)=(WeightedGenerator.pairing r x
      (diagonal (fun k => f k/numberWeight k^4) C hC hf)).re := by
    rw [hp.tsum_comm]
    simp only [a, (hc _).tsum_eq]
    exact (WeightedGenerator.columnPairing_hasSum r x hx _).tsum_eq
  have hs := hp.prod_symm.prod.hasSum
  change HasSum (fun k => ∑' i, a i k) (∑' k, ∑' i, a i k) at hs
  rw [he] at hs
  simpa only [(hr _).tsum_eq] using hs
end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section
open Filter Topology

def numberBox (n K : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset (fun _ => Finset.range (K + 1))

theorem numberBox_compl_weight {n K : ℕ} {k : Fin n → ℕ}
    (hk : k ∉ numberBox n K) : (K + 1 : ℝ) ≤ ∑ j, (k j : ℝ) := by
  classical
  simp only [numberBox, Fintype.mem_piFinset, Finset.mem_range, not_forall] at hk
  obtain ⟨j, hj⟩ := hk
  have hh : K + 1 ≤ k j := Nat.le_of_not_gt hj
  have hs := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => Nat.zero_le (k i))
    (Finset.mem_univ j)
  exact_mod_cast hh.trans hs

theorem number_tail_mass_le {n K : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : Summable p)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k)) :
    (∑' k : {k // k ∉ numberBox n K}, p k) ≤
      (∑' k, (∑ j, (k j : ℝ)) * p k) / (K + 1) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < K + 1)]
  rw [← tsum_mul_right]
  calc
    _ ≤ ∑' k : {k // k ∉ numberBox n K}, (∑ j, ((k : Fin n → ℕ) j : ℝ)) * p k := by
      apply ((hs.subtype _).mul_right _).tsum_le_tsum _ (hE.subtype _)
      intro k
      change p k * (K + 1) ≤ (∑ j, ((k : Fin n → ℕ) j : ℝ)) * p k
      nlinarith [numberBox_compl_weight k.property, hp k]
    _ ≤ _ := Summable.tsum_subtype_le _ _ (fun k => mul_nonneg
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k)) hE

theorem entropy_tail_le_modulus {n : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hpu : ∀ k, p k ≤ 1) (hs : Summable p)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k))
    (s : Finset (Fin n → ℕ)) {E : ℝ}
    (hEb : (∑' k, (∑ j, (k j : ℝ)) * p k) ≤ E) :
    let q := ∑' k : {k // k ∉ s}, p k
    (∑' k : {k // k ∉ s}, Real.negMulLog (p k)) ≤
      (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 + E * q := by
  classical
  let a : (Fin n → ℕ) → ℝ := fun k => if k ∈ s then 0 else p k
  have ha : ∀ k, 0 ≤ a k := fun k => by dsimp [a]; split_ifs <;> first | exact le_refl _ | exact hp k
  have hau : ∀ k, a k ≤ 1 := fun k => by dsimp [a]; split_ifs <;> first | linarith | exact hpu k
  have has : Summable a := hs.of_nonneg_of_le ha (fun k => by dsimp [a]; split_ifs <;> simp_all)
  have hae : Summable (fun k => (∑ j, (k j : ℝ)) * a k) := by
    apply hE.of_nonneg_of_le (fun k => mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (ha k))
    intro k
    dsimp [a]; split_ifs
    · simp only [mul_zero]
      exact mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k)
    · exact le_refl _
  have haq : (∑' k, a k) = ∑' k : {k // k ∉ s}, p k := by
    convert (tsum_subtype {k | k ∉ s} p).symm using 1
    · congr 1; ext k; simp [a, Set.indicator_apply]
    · rfl
  have haentropy : (∑' k, Real.negMulLog (a k)) =
      ∑' k : {k // k ∉ s}, Real.negMulLog (p k) := by
    convert (tsum_subtype {k | k ∉ s} (fun k => Real.negMulLog (p k))).symm using 1
    · congr 1; ext k; by_cases hk : k ∈ s <;> simp [a, hk]
    · rfl
  have hh := (entropy_small_mass_bound a ha hau has.hasSum hae).2
  rw [haq, haentropy] at hh
  apply hh.trans
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (tsum_nonneg (fun k : {k // k ∉ s} => hp k))
  apply le_trans _ hEb
  apply hae.tsum_le_tsum _ hE
  intro k
  dsimp [a]; split_ifs
  · simp only [mul_zero]
    exact mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k)
  · exact le_refl _

theorem entropy_uniform_tail {n : ℕ} {E ε : ℝ} (_hE0 : 0 ≤ E) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ (p : (Fin n → ℕ) → ℝ), (∀ k, 0 ≤ p k) →
      (∀ k, p k ≤ 1) → Summable p →
      Summable (fun k => (∑ j, (k j : ℝ)) * p k) →
      (∑' k, (∑ j, (k j : ℝ)) * p k) ≤ E →
      (∑' k : {k // k ∉ numberBox n K}, Real.negMulLog (p k)) < ε := by
  let M : ℝ → ℝ := fun q => (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 + E * q
  have hm : ContinuousAt M 0 := by fun_prop
  have hm0 : M 0 = 0 := by simp [M]
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hm ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (E / δ)
  refine ⟨K, ?_⟩
  intro p hp hpu hs hEs hEb
  let q := ∑' k : {k // k ∉ numberBox n K}, p k
  have hq0 : 0 ≤ q := tsum_nonneg (fun k => hp k)
  have hqle : q ≤ E / (K + 1) :=
    (number_tail_mass_le p hp hs hEs).trans (div_le_div_of_nonneg_right hEb (by positivity))
  have hqδ : q < δ := by
    have hkδ : E < K * δ := (div_lt_iff₀ hδ).mp hK
    apply hqle.trans_lt
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
    nlinarith
  have hh := hd (show dist q 0 < δ by simpa [Real.dist_eq, abs_of_nonneg hq0] using hqδ)
  rw [hm0, dist_zero_right, Real.norm_eq_abs] at hh
  exact (entropy_tail_le_modulus p hp hpu hs hEs _ hEb).trans_lt ((le_abs_self _).trans_lt hh)

theorem tendsto_tsum_of_uniform_tail {α ι : Type*} {l : Filter α}
    {f : α → ι → ℝ} {g : ι → ℝ}
    (hf : ∀ a, Summable (f a)) (hg : Summable g)
    (hfp : ∀ a i, 0 ≤ f a i) (hgp : ∀ i, 0 ≤ g i)
    (hlim : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i)))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      (∀ a, (∑' i : {i // i ∉ s}, f a i) < ε) ∧
      (∑' i : {i // i ∉ s}, g i) < ε) :
    Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs, hsg⟩ := htail (ε / 3) (by positivity)
  have hh := Metric.tendsto_nhds.mp (tendsto_finsetSum s (fun i _ => hlim i)) (ε / 3) (by positivity)
  filter_upwards [hh] with a ha
  rw [dist_eq_norm, ← (hf a).sum_add_tsum_compl (s := s), ← hg.sum_add_tsum_compl (s := s)]
  have hsub :
      (∑ i ∈ s, f a i) + (∑' i : {i // i ∉ s}, f a i) -
      ((∑ i ∈ s, g i) + (∑' i : {i // i ∉ s}, g i)) =
      ((∑ i ∈ s, f a i) - (∑ i ∈ s, g i)) +
      ((∑' i : {i // i ∉ s}, f a i) - (∑' i : {i // i ∉ s}, g i)) := by ring
  change ‖(∑ i ∈ s, f a i) + (∑' i : {i // i ∉ s}, f a i) -
    ((∑ i ∈ s, g i) + (∑' i : {i // i ∉ s}, g i))‖ < ε
  rw [hsub]
  apply (norm_add_le _ _).trans_lt
  have hnorm := norm_sub_le (∑' i : {i // i ∉ s}, f a i) (∑' i : {i // i ∉ s}, g i)
  simp only [Real.norm_eq_abs] at hnorm
  rw [abs_of_nonneg (tsum_nonneg (fun i : {i // i ∉ s} => hfp a i)),
    abs_of_nonneg (tsum_nonneg (fun i : {i // i ∉ s} => hgp i))] at hnorm
  simp only [Real.norm_eq_abs]
  rw [dist_eq_norm, Real.norm_eq_abs] at ha
  linarith [hs a]

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

omit [CompleteSpace H] in
theorem diagonal_le_one (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hp : T.IsPositive) (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) 1)
    (i : ι) : (inner ℂ (b i) (T (b i))).re ≤ 1 := by
  simpa only [ht.tsum_eq] using ht.summable.le_tsum i (fun j _ => hp.re_inner_nonneg_right (b j))

theorem entropyOperator_tendsto {α : Type*} {l : Filter α}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hp : ∀ a, (T a).IsPositive) (hA : A.IsPositive)
    (hn : ∀ a, ‖T a‖ ≤ 1) (hnA : ‖A‖ ≤ 1)
    (ht : Tendsto T l (𝓝 A)) :
    Tendsto (fun a => entropyOperator (T a)) l (𝓝 (entropyOperator A)) := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · have : Subsingleton H := hH
    have he : (fun a => entropyOperator (T a)) = fun _ => entropyOperator A :=
      funext (fun a => Subsingleton.elim _ _)
    rw [he]
    exact tendsto_const_nhds
  have : Nontrivial H := hH
  have hspec (B : H →L[ℂ] H) (hB : B.IsPositive) (hBn : ‖B‖ ≤ 1) :
      spectrum ℝ B ⊆ Set.Icc 0 1 := by
    intro x hx
    exact ⟨spectrum_nonneg_of_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hB) hx,
      (Real.le_norm_self _).trans ((spectrum.norm_le_norm_of_mem hx).trans hBn)⟩
  exact Tendsto.cfc isCompact_Icc Real.negMulLog ht
    (Eventually.of_forall (fun a => hspec _ (hp a) (hn a)))
    (Eventually.of_forall (fun a => (hp a).isSymmetric.isSelfAdjoint))
    (hspec _ hA hnA) hA.isSymmetric.isSelfAdjoint Real.continuous_negMulLog.continuousOn

theorem entropy_tendsto_finite_energy {α : Type*} {l : Filter α} {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hp : ∀ a, (T a).IsPositive) (hA : A.IsPositive)
    (ht : ∀ a, HasSum (fun k => (inner ℂ (b k) (T a (b k))).re) 1)
    (htA : HasSum (fun k => (inner ℂ (b k) (A (b k))).re) 1)
    (hEs : ∀ a, Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T a (b k))).re))
    (hEsA : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (A (b k))).re))
    {E : ℝ} (hEb : ∀ a, (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T a (b k))).re) ≤ E)
    (hEbA : (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (A (b k))).re) ≤ E)
    (hlim : Tendsto T l (𝓝 A)) :
    Tendsto (fun a => ∑' k, (inner ℂ (b k) (entropyOperator (T a) (b k))).re) l
      (𝓝 (∑' k, (inner ℂ (b k) (entropyOperator A (b k))).re)) := by
  have hn (a : α) := norm_le_trace b (hp a) (ht a)
  have hnA := norm_le_trace b hA htA
  have hepos (a : α) := entropyOperator_positive (hp a) (hn a)
  have heA := entropyOperator_positive hA hnA
  apply tendsto_tsum_of_uniform_tail
    (fun a => entropy_summable_finite_energy b (hp a) (ht a) (hEs a))
    (entropy_summable_finite_energy b hA htA hEsA)
    (fun a k => (hepos a).re_inner_nonneg_right (b k))
    (fun k => heA.re_inner_nonneg_right (b k))
  · intro k
    have hh := entropyOperator_tendsto hp hA hn hnA hlim
    have heval : Continuous (fun B : H →L[ℂ] H => B (b k)) :=
      continuous_id.clm_apply continuous_const
    have hx := heval.continuousAt.tendsto.comp hh
    exact Complex.continuous_re.continuousAt.tendsto.comp (tendsto_const_nhds.inner hx)
  · intro ε hε
    have hE0 : 0 ≤ E := (tsum_nonneg (fun k => mul_nonneg
      (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hA.re_inner_nonneg_right (b k)))).trans hEbA
    obtain ⟨K, hK⟩ := entropy_uniform_tail (n := n) hE0 hε
    refine ⟨numberBox n K, ?_, ?_⟩
    · intro a
      have hpd (k : Fin n → ℕ) := (hp a).re_inner_nonneg_right (b k)
      have hpu (k : Fin n → ℕ) := diagonal_le_one b (hp a) (ht a) k
      have hes := (entropy_small_mass_bound _ hpd hpu (ht a) (hEs a)).1
      apply lt_of_le_of_lt _ (hK _ hpd hpu (ht a).summable (hEs a) (hEb a))
      apply ((entropy_summable_finite_energy b (hp a) (ht a) (hEs a)).subtype _).tsum_le_tsum _ (hes.subtype _)
      intro k
      exact entropyOperator_quadratic_le b (hp a) (ht a) (b k) (b.orthonormal.norm_eq_one k)
    · have hpd (k : Fin n → ℕ) := hA.re_inner_nonneg_right (b k)
      have hpu (k : Fin n → ℕ) := diagonal_le_one b hA htA k
      have hes := (entropy_small_mass_bound _ hpd hpu htA hEsA).1
      apply lt_of_le_of_lt _ (hK _ hpd hpu htA.summable hEsA hEbA)
      apply ((entropy_summable_finite_energy b hA htA hEsA).subtype _).tsum_le_tsum _ (hes.subtype _)
      intro k
      exact entropyOperator_quadratic_le b hA htA (b k) (b.orthonormal.norm_eq_one k)

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

def basisProjection (b : HilbertBasis ι ℂ H) (s : Finset ι) : H →L[ℂ] H :=
  basisApprox b (ContinuousLinearMap.id ℂ H) s

omit [CompleteSpace H] in
theorem basisProjection_apply_basis (b : HilbertBasis ι ℂ H) (s : Finset ι) (j : ι)
    [Decidable (j ∈ s)] : basisProjection b s (b j) = if j ∈ s then b j else 0 := by
  simpa [basisProjection] using basisApprox_apply_basis b (ContinuousLinearMap.id ℂ H) s j

theorem basisProjection_adjoint (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    adjoint (basisProjection b s) = basisProjection b s := by
  simp [basisProjection, basisApprox]

omit [CompleteSpace H] in
theorem basisProjection_idempotent (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    basisProjection b s ∘L basisProjection b s = basisProjection b s := by
  classical
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨j, rfl⟩
  simp only [comp_apply, basisProjection_apply_basis]
  by_cases hj : j ∈ s <;> simp [hj, basisProjection_apply_basis]

theorem basisProjection_norm_le (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    ‖basisProjection b s‖ ≤ 1 := by
  apply IsStarProjection.norm_le
  exact ⟨basisProjection_idempotent b s, basisProjection_adjoint b s⟩

omit [CompleteSpace H] in
theorem basisApprox_eq_comp (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) (s : Finset ι) :
    basisApprox b T s = T ∘L basisProjection b s := by
  classical
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨j, rfl⟩
  simp only [basisApprox_apply_basis, comp_apply, basisProjection_apply_basis]
  split_ifs <;> simp

theorem double_compression_norm_le (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H}
    (hp : T.IsPositive) (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) 1)
    (s : Finset ι) :
    ‖T - basisProjection b s ∘L T ∘L basisProjection b s‖ ≤
      2 * Real.sqrt (1 - ∑ i ∈ s, (inner ℂ (b i) (T (b i))).re) := by
  let P := basisProjection b s
  let S := CFC.sqrt T
  have hS : S ∘L S = T := by
    simpa only [S, pow_two, ContinuousLinearMap.mul_def] using
      CFC.sq_sqrt T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hp)
  have hSn : ‖S‖ ≤ 1 := by
    dsimp [S]
    rw [CFC.norm_sqrt T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hp)]
    exact (Real.sqrt_le_sqrt (norm_le_trace b hp ht)).trans_eq Real.sqrt_one
  have hsp : ‖S - S ∘L P‖ ≤
      Real.sqrt (1 - ∑ i ∈ s, (inner ℂ (b i) (T (b i))).re) := by
    have hs : HasSum (fun i => ‖S (b i)‖ ^ 2) 1 := by
      simpa only [sqrt_inner_eq hp] using ht
    simpa only [basisApprox_eq_comp, S, P, ← sqrt_inner_eq hp] using basisApprox_norm_sub_le b S hs s
  have hright : ‖T - T ∘L P‖ ≤
      Real.sqrt (1 - ∑ i ∈ s, (inner ℂ (b i) (T (b i))).re) := by
    have he : T - T ∘L P = S ∘L (S - S ∘L P) := by
      rw [comp_sub, ← comp_assoc, hS]
    rw [he]
    exact (opNorm_comp_le _ _).trans ((mul_le_mul_of_nonneg_right hSn (norm_nonneg _)).trans
      (by simpa using hsp))
  have hleft : ‖T - P ∘L T‖ = ‖T - T ∘L P‖ := by
    rw [← (adjoint : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H)).norm_map (T - P ∘L T)]
    simp [adjoint_comp, hp.isSymmetric.isSelfAdjoint.adjoint_eq, P, basisProjection_adjoint]
  have he : T - P ∘L T ∘L P = (T - P ∘L T) + P ∘L (T - T ∘L P) := by
    rw [comp_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖T - P ∘L T‖ + ‖P ∘L (T - T ∘L P)‖ := norm_add_le _ _
    _ ≤ ‖T - T ∘L P‖ + ‖P‖ * ‖T - T ∘L P‖ := by
      rw [hleft]; exact add_le_add_right (opNorm_comp_le _ _) _
    _ ≤ 2 * ‖T - T ∘L P‖ := by
      have hn := mul_le_mul_of_nonneg_right (basisProjection_norm_le b s) (norm_nonneg (T - T ∘L P))
      dsimp [P] at *
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hright (by norm_num)

end

section
open Filter Topology

theorem tsum_bound_of_tendsto {α ι : Type*} {l : Filter α} [NeBot l]
    {f : α → ι → ℝ} {g : ι → ℝ} {C : ℝ}
    (hfp : ∀ a i, 0 ≤ f a i) (hfs : ∀ a, Summable (f a))
    (hfb : ∀ a, (∑' i, f a i) ≤ C)
    (hlim : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i))) :
    Summable g ∧ (∑' i, g i) ≤ C := by
  have hg : ∀ i, 0 ≤ g i := fun i => ge_of_tendsto (hlim i) (Eventually.of_forall (fun a => hfp a i))
  have hs : ∀ s : Finset ι, (∑ i ∈ s, g i) ≤ C := by
    intro s
    apply le_of_tendsto (tendsto_finsetSum s (fun i _ => hlim i))
    exact Eventually.of_forall (fun a => ((hfs a).sum_le_tsum s (fun i _ => hfp a i)).trans (hfb a))
  exact ⟨summable_of_sum_le hg hs, Real.tsum_le_of_sum_le hg hs⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def energySet {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) : Set (H →L[ℂ] H) :=
  {T | T.IsPositive ∧
    HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1 ∧
    Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) ∧
    (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) ≤ E}

theorem energySet_limit {α : Type*} {l : Filter α} [NeBot l] {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {E : ℝ}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hT : ∀ a, T a ∈ energySet b E) (hlim : Tendsto T l (𝓝 A)) : A ∈ energySet b E := by
  have hA : A.IsPositive := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    exact isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall (fun a =>
      ContinuousLinearMap.nonneg_iff_isPositive.mpr (hT a).1))
  have hdiag (k : Fin n → ℕ) :
      Tendsto (fun a => (inner ℂ (b k) (T a (b k))).re) l
        (𝓝 (inner ℂ (b k) (A (b k))).re) := by
    have heval : Continuous (fun B : H →L[ℂ] H => B (b k)) :=
      continuous_id.clm_apply continuous_const
    exact Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_const_nhds.inner (heval.continuousAt.tendsto.comp hlim))
  have hds := tsum_bound_of_tendsto
    (fun a k => (hT a).1.re_inner_nonneg_right (b k))
    (fun a => (hT a).2.1.summable) (fun a => (hT a).2.1.tsum_eq.le) hdiag
  have hes := tsum_bound_of_tendsto
    (fun a k => mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
      ((hT a).1.re_inner_nonneg_right (b k)))
    (fun a => (hT a).2.2.1) (fun a => (hT a).2.2.2)
    (fun k => tendsto_const_nhds.mul (hdiag k))
  have hsum : Tendsto (fun a => ∑' k, (inner ℂ (b k) (T a (b k))).re) l
      (𝓝 (∑' k, (inner ℂ (b k) (A (b k))).re)) := by
    apply tendsto_tsum_of_uniform_tail
      (fun a => (hT a).2.1.summable) hds.1
      (fun a k => (hT a).1.re_inner_nonneg_right (b k))
      (fun k => hA.re_inner_nonneg_right (b k)) hdiag
    intro ε hε
    obtain ⟨K, hK⟩ := exists_nat_gt (E / ε)
    have hb : E / (K + 1) < ε := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
      have hh := (div_lt_iff₀ hε).mp hK
      nlinarith
    refine ⟨numberBox n K, ?_, ?_⟩
    · intro a
      apply lt_of_le_of_lt _ hb
      exact (number_tail_mass_le _ (fun k => (hT a).1.re_inner_nonneg_right (b k))
        (hT a).2.1.summable (hT a).2.2.1).trans
        (div_le_div_of_nonneg_right (hT a).2.2.2 (by positivity))
    · apply lt_of_le_of_lt _ hb
      exact (number_tail_mass_le _ (fun k => hA.re_inner_nonneg_right (b k))
        hds.1 hes.1).trans (div_le_div_of_nonneg_right hes.2 (by positivity))
  have heq : (∑' k, (inner ℂ (b k) (A (b k))).re) = 1 := by
    apply tendsto_nhds_unique hsum
    convert! (tendsto_const_nhds : Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)) using 1
    funext a
    exact (hT a).2.1.tsum_eq
  exact ⟨hA, heq ▸ hds.1.hasSum, hes⟩

end

section
open ContinuousLinearMap InnerProductSpace Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*}

def matrixEmbed (b : HilbertBasis ι ℂ H) (s : Finset ι) (c : s → s → ℂ) : H →L[ℂ] H :=
  ∑ i, ∑ j, c i j • rankOne ℂ (b i) (b j)

omit [CompleteSpace H] in
theorem matrixEmbed_continuous (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    Continuous (matrixEmbed b s) := by
  unfold matrixEmbed
  fun_prop

omit [CompleteSpace H] in
theorem matrixEmbed_entries (b : HilbertBasis ι ℂ H) (s : Finset ι) (T : H →L[ℂ] H) :
    matrixEmbed b s (fun i j => inner ℂ (b i) (T (b j))) =
      basisProjection b s ∘L T ∘L basisProjection b s := by
  classical
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨k, rfl⟩
  simp only [comp_apply, basisProjection_apply_basis]
  by_cases hk : k ∈ s
  · simp only [ite_eq_left hk, matrixEmbed, sum_apply, smul_apply, rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal]
    simp only [smul_ite, smul_zero, one_smul, ite_smul, zero_smul]
    have hj (j : s) : ((j : ι) = k) = (j = ⟨k, hk⟩) := by
      apply propext
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    simp_rw [hj]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    calc
      _ = ∑ i ∈ s, inner ℂ (b i) (T (b k)) • b i :=
        Finset.sum_coe_sort s (fun i : ι => inner ℂ (b i) (T (b k)) • b i)
      _ = _ := by simp [basisProjection, basisApprox, sum_apply, rankOne_apply]
  · simp only [ite_eq_right hk, map_zero, matrixEmbed, sum_apply, smul_apply, rankOne_apply,
      orthonormal_iff_ite.mp b.orthonormal]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hj : (j : ι) ≠ k := fun hh => hk (hh ▸ j.property)
    simp [hj]

omit [CompleteSpace H] in
theorem entry_norm_le_one (b : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} (hT : ‖T‖ ≤ 1)
    (i j : ι) : ‖inner ℂ (b i) (T (b j))‖ ≤ 1 := by
  calc
    _ ≤ ‖b i‖ * ‖T (b j)‖ := norm_inner_le_norm _ _
    _ = ‖T (b j)‖ := by rw [b.orthonormal.norm_eq_one, one_mul]
    _ ≤ ‖T‖ * ‖b j‖ := T.le_opNorm _
    _ ≤ 1 := by simpa only [b.orthonormal.norm_eq_one, mul_one] using hT

omit [CompleteSpace H] in

theorem double_compressions_compact (b : HilbertBasis ι ℂ H) (s : Finset ι) :
    ∃ C : Set (H →L[ℂ] H), IsCompact C ∧
      ∀ T : H →L[ℂ] H, ‖T‖ ≤ 1 → basisProjection b s ∘L T ∘L basisProjection b s ∈ C := by
  let C := matrixEmbed b s '' Metric.closedBall (0 : s → s → ℂ) 1
  refine ⟨C, (isCompact_closedBall _ _).image (matrixEmbed_continuous b s), ?_⟩
  intro T hT
  refine ⟨(fun i j => inner ℂ (b i) (T (b j))), ?_, matrixEmbed_entries b s T⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  exact entry_norm_le_one b hT i j

theorem energySet_isClosed {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    IsClosed (energySet b E) := by
  apply IsSeqClosed.isClosed
  intro T A hT hlim
  exact energySet_limit b hT hlim

end

section
open ContinuousLinearMap Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem energySet_totallyBounded {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    TotallyBounded (energySet b E) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (E / (ε / 4) ^ 2)
  have hcut : E / (K + 1) < (ε / 4) ^ 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < K + 1)]
    have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < (ε / 4) ^ 2)).mp hK
    nlinarith
  let s := numberBox n K
  let P := basisProjection b s
  obtain ⟨C, hC, hPC⟩ := double_compressions_compact b s
  obtain ⟨t, htfin, hcover⟩ := Metric.totallyBounded_iff.mp hC.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, htfin, ?_⟩
  intro T hT
  have hp := hT.1
  have htr := hT.2.1
  have hmass : (1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re) =
      ∑' k : {k // k ∉ s}, (inner ℂ (b k) (T (b k))).re := by
    have hh := htr.summable.sum_add_tsum_compl (s := s)
    rw [htr.tsum_eq] at hh
    change (∑ k ∈ s, (inner ℂ (b k) (T (b k))).re) +
      (∑' k : {k // k ∉ s}, (inner ℂ (b k) (T (b k))).re) = 1 at hh
    linarith
  have hq0 : 0 ≤ 1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re := by
    rw [hmass]
    exact tsum_nonneg (fun k => hp.re_inner_nonneg_right (b k))
  have hqb : 1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re < (ε / 4) ^ 2 := by
    rw [hmass]
    apply lt_of_le_of_lt _ hcut
    exact (number_tail_mass_le _ (fun k => hp.re_inner_nonneg_right (b k)) htr.summable hT.2.2.1).trans
      (div_le_div_of_nonneg_right hT.2.2.2 (by positivity))
  have happ : dist T (P ∘L T ∘L P) < ε / 2 := by
    rw [dist_eq_norm]
    apply (double_compression_norm_le b hp htr s).trans_lt
    have hs := Real.sq_sqrt hq0
    have hn := Real.sqrt_nonneg (1 - ∑ k ∈ s, (inner ℂ (b k) (T (b k))).re)
    nlinarith
  have hc : P ∘L T ∘L P ∈ C := hPC T (norm_le_trace b hp htr)
  obtain ⟨y, hy, hdist⟩ : ∃ y ∈ t, dist (P ∘L T ∘L P) y < ε / 2 := by
    rcases Set.mem_iUnion.mp (hcover hc) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hy⟩
    exact ⟨y, hyt, hy⟩
  simp only [Set.mem_iUnion, Metric.mem_ball]
  refine ⟨y, hy, ?_⟩
  exact (dist_triangle T (P ∘L T ∘L P) y).trans_lt (by linarith)

theorem energySet_isCompact {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    IsCompact (energySet b E) :=
  (energySet_totallyBounded b E).isCompact_of_isClosed (energySet_isClosed b E)

end

open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def momentSet {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (w : (Fin n → ℕ) → ℝ) (E M : ℝ) : Set (H →L[ℂ] H) :=
  {T | T ∈ energySet b E ∧
    Summable (fun k => w k * (inner ℂ (b k) (T (b k))).re) ∧
    (∑' k, w k * (inner ℂ (b k) (T (b k))).re) ≤ M}

theorem momentSet_limit {α : Type*} {l : Filter α} [NeBot l] {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {w : (Fin n → ℕ) → ℝ}
    (hw : ∀ k, 0 ≤ w k) {E M : ℝ}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hT : ∀ a, T a ∈ momentSet b w E M) (hlim : Tendsto T l (𝓝 A)) :
    A ∈ momentSet b w E M := by
  refine ⟨energySet_limit b (fun a => (hT a).1) hlim, ?_⟩
  apply tsum_bound_of_tendsto (l := l)
    (fun a k => mul_nonneg (hw k) ((hT a).1.1.re_inner_nonneg_right (b k)))
    (fun a => (hT a).2.1) (fun a => (hT a).2.2)
  intro k
  have heval : Continuous (fun B : H →L[ℂ] H => B (b k)) :=
    continuous_id.clm_apply continuous_const
  exact tendsto_const_nhds.mul (Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_const_nhds.inner (heval.continuousAt.tendsto.comp hlim)))

theorem momentSet_isCompact {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (w : (Fin n → ℕ) → ℝ) (hw : ∀ k, 0 ≤ w k) (E M : ℝ) :
    IsCompact (momentSet b w E M) := by
  have hc : IsClosed (momentSet b w E M) := by
    apply IsSeqClosed.isClosed
    intro T A hT hlim
    exact momentSet_limit b hw hT hlim
  exact (energySet_isCompact b E).of_isClosed_subset hc (fun _ h => h.1)

theorem lowerSemicontinuous_tsum_nonneg {A I : Type*} [TopologicalSpace A]
    (f : A → I → ℝ) (hp : ∀ a i, 0 ≤ f a i) (hs : ∀ a, Summable (f a))
    (hc : ∀ i, Continuous (fun a => f a i)) :
    LowerSemicontinuous (fun a => ∑' i, f a i) := by
  intro a y hy
  obtain ⟨F, hF⟩ := ((hs a).hasSum.eventually (eventually_gt_nhds hy)).exists
  have ch : Continuous (fun x => ∑ i ∈ F, f x i) :=
    continuous_finsetSum F (fun i _ => hc i)
  filter_upwards [ch.continuousAt.eventually (eventually_gt_nhds hF)] with x hx
  exact hx.trans_le ((hs x).sum_le_tsum F (fun i _ => hp x i))

omit [CompleteSpace H] in
theorem moment_lowerSemicontinuous {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H)
    (w : (Fin n → ℕ) → ℝ) (hw : ∀ k, 0 ≤ w k) (E M : ℝ) :
    LowerSemicontinuous (fun T : momentSet b w E M =>
      ∑' k, w k * (inner ℂ (b k) (T.val (b k))).re) := by
  apply lowerSemicontinuous_tsum_nonneg
  · exact fun T k => mul_nonneg (hw k) (T.property.1.1.re_inner_nonneg_right _)
  · exact fun T => T.property.2.1
  · intro k
    exact continuous_const.mul (Complex.continuous_re.comp
      (continuous_const.inner (continuous_subtype_val.clm_apply continuous_const)))

omit [CompleteSpace H] in
theorem energy_lowerSemicontinuous {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    LowerSemicontinuous (fun T : energySet b E =>
      ∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T.val (b k))).re) := by
  apply lowerSemicontinuous_tsum_nonneg
  · exact fun T k => mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
      (T.property.1.re_inner_nonneg_right _)
  · exact fun T => T.property.2.2.1
  · intro k
    exact continuous_const.mul (Complex.continuous_re.comp
      (continuous_const.inner (continuous_subtype_val.clm_apply continuous_const)))

theorem entropy_continuous_energySet {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ H) (E : ℝ) :
    Continuous (fun T : energySet b E =>
      ∑' k, (inner ℂ (b k) (entropyOperator T.val (b k))).re) := by
  rw [continuous_iff_continuousAt]
  intro A
  apply entropy_tendsto_finite_energy b
    (fun T => T.property.1) A.property.1
    (fun T => T.property.2.1) A.property.2.1
    (fun T => T.property.2.2.1) A.property.2.2.1
    (fun T => T.property.2.2.2) A.property.2.2.2
  exact continuous_subtype_val.continuousAt

end QuantumTrace

end

namespace EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

def energy {n : ℕ} (ρ : State n) : ℝ :=
  ∑' k, (totalNumber k : ℝ) * (entry ρ.op k k).re

theorem energy_nonneg {n : ℕ} (ρ : State n) : 0 ≤ energy ρ := by
  exact tsum_nonneg (fun k => mul_nonneg (Nat.cast_nonneg _)
    (ρ.positive.re_inner_nonneg_right _))

theorem entropy_eq_quantumTrace {n : ℕ} (ρ : State n) :
    entropy ρ = ∑' k, (inner ℂ (numberBasis n k)
      (QuantumTrace.entropyOperator ρ.op (numberBasis n k))).re := by
  rw [QuantumTrace.entropyOperator_eq_complex ρ.positive.isSymmetric]
  simp only [entropy, entry, numberBasis_apply]

theorem entropy_summable {n : ℕ} (ρ : State n) (hρ : FiniteEnergy ρ) :
    Summable (fun k => (entry (cfc (fun z : ℂ => (-(z.re * Real.log z.re) : ℂ)) ρ.op) k k).re) := by
  have hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (numberBasis n k) (ρ.op (numberBasis n k))).re) := by
    simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, numberBasis_apply, entry] using hρ
  have hh := QuantumTrace.entropy_summable_finite_energy (numberBasis n) ρ.positive (trace_one_numberBasis ρ) hE
  simpa only [QuantumTrace.entropyOperator_eq_complex ρ.positive.isSymmetric, numberBasis_apply, entry] using hh

theorem entropy_nonneg {n : ℕ} (ρ : State n) : 0 ≤ entropy ρ := by
  rw [entropy_eq_quantumTrace]
  exact QuantumTrace.entropy_nonneg (numberBasis n) ρ.positive (trace_one_numberBasis ρ)

theorem entropy_energy_bound {n : ℕ} (hn : 1 ≤ n) (ρ : State n) (hρ : FiniteEnergy ρ) :
    0 ≤ entropy ρ ∧ entropy ρ ≤ n * g (energy ρ / n) := by
  refine ⟨entropy_nonneg ρ, ?_⟩
  rw [entropy_eq_quantumTrace]
  have hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (numberBasis n k) (ρ.op (numberBasis n k))).re) := by
    simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, numberBasis_apply, entry] using hρ
  simpa only [g, energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using
    QuantumTrace.entropy_energy_bound hn (numberBasis n) ρ.positive (trace_one_numberBasis ρ) hE

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal

namespace TraceEnsemble
open Filter Topology
open scoped BigOperators
variable {I A E G : Type*}
variable [NormedAddCommGroup G] [CompleteSpace G]

theorem norm_tail_le {f : I → G} {s : ℝ} (hf : HasSum (fun i => ‖f i‖) s)
    (F : Finset I) : ‖(∑' i, f i) - ∑ i ∈ F, f i‖ ≤ s - ∑ i ∈ F, ‖f i‖ := by
  classical
  have h₁ := hf.summable.of_norm.sum_add_tsum_compl (s := F)
  have h₂ := hf.summable.sum_add_tsum_compl (s := F)
  rw [hf.tsum_eq] at h₂
  have e₁ : (∑' i, f i) - ∑ i ∈ F, f i = ∑' i : ↥((↑F : Set I)ᶜ), f i := by
    rw [← h₁]; abel
  have e₂ : s - ∑ i ∈ F, ‖f i‖ = ∑' i : ↥((↑F : Set I)ᶜ), ‖f i‖ := by
    rw [← h₂]; ring
  rw [e₁,e₂]
  exact norm_tsum_le_tsum_norm (hf.summable.subtype _)

theorem tendsto_tsum_fixed_norm {l : Filter A} {f : A → I → G} {g : I → G} {s : ℝ}
    (hf : ∀ a, HasSum (fun i => ‖f a i‖) s) (hg : HasSum (fun i => ‖g i‖) s)
    (hfg : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i))) :
    Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i)) := by
  classical
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨F, hF⟩ : ∃ F : Finset I, dist (∑ i ∈ F, ‖g i‖) s < ε/4 :=
    ((Metric.tendsto_nhds.mp hg) (ε/4) (by positivity)).exists
  have hsF : s - ∑ i ∈ F, ‖g i‖ < ε/4 := by
    exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq, abs_sub_comm] using hF)
  have hhead := tendsto_finsetSum F (fun i _ => hfg i)
  have hmass := tendsto_finsetSum F (fun i _ => (hfg i).norm)
  filter_upwards [(Metric.tendsto_nhds.mp hhead) (ε/4) (by positivity),
    (Metric.tendsto_nhds.mp hmass) (ε/4) (by positivity)] with a ha hm
  have hmass' : (∑ i ∈ F, ‖g i‖) - ∑ i ∈ F, ‖f a i‖ < ε/4 :=
    (le_abs_self _).trans_lt (by simpa [Real.dist_eq, abs_sub_comm] using hm)
  rw [dist_eq_norm]
  calc
    _ ≤ ‖(∑' i, f a i) - ∑ i ∈ F, f a i‖ +
        ‖(∑ i ∈ F, f a i) - ∑ i ∈ F, g i‖ +
        ‖(∑' i, g i) - ∑ i ∈ F, g i‖ := by
      simpa [norm_sub_rev, add_assoc] using
        (norm_sub_le_norm_sub_add_norm_sub (∑' i, f a i)
          (∑ i ∈ F, f a i) (∑' i, g i)).trans
          (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub
            (∑ i ∈ F, f a i) (∑ i ∈ F, g i) (∑' i, g i)))
    _ ≤ (s - ∑ i ∈ F, ‖f a i‖) + ‖(∑ i ∈ F, f a i) - ∑ i ∈ F, g i‖ +
        (s - ∑ i ∈ F, ‖g i‖) :=
      add_le_add (add_le_add (norm_tail_le (hf a) F) le_rfl) (norm_tail_le hg F)
    _ < ε := by rw [dist_eq_norm] at ha; linarith

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem tendsto_operator {l : Filter A} {v : A → I → E} {w : I → E} {s : ℝ}
    (hv : ∀ a, HasSum (fun i => ‖v a i‖^2) s) (hw : HasSum (fun i => ‖w i‖^2) s)
    (hvw : ∀ i, Tendsto (fun a => v a i) l (𝓝 (w i))) :
    Tendsto (fun a => operator (v a)) l (𝓝 (operator w)) := by
  apply tendsto_tsum_fixed_norm (s := s)
  · intro a
    simpa only [InnerProductSpace.norm_rankOne, pow_two] using hv a
  · simpa only [InnerProductSpace.norm_rankOne, pow_two] using hw
  · intro i
    have hc : Continuous (fun x : E => InnerProductSpace.rankOne ℂ x x) := by
      simp only [InnerProductSpace.rankOne_def]
      exact ((ContinuousLinearMap.smulRightL ℂ E E).continuous.comp
        (innerSL ℂ).continuous).clm_apply continuous_id
    exact (hc.tendsto _).comp (hvw i)

theorem tendsto_positiveRoot {l : Filter A} {T : A → E →L[ℂ] E} {R : E →L[ℂ] E}
    (hT : ∀ a, (T a).IsPositive) (hR : R.IsPositive)
    (h : Tendsto T l (𝓝 R)) : Tendsto (fun a => positiveRoot (T a)) l (𝓝 (positiveRoot R)) := by
  apply (CFC.continuousOn_sqrt.continuousWithinAt
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hR)).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨h, Filter.Eventually.of_forall (fun a =>
    ContinuousLinearMap.nonneg_iff_isPositive.mpr (hT a))⟩

end TraceEnsemble

namespace TensorLp
variable {A B : Type*}

def tensorBilinear : H A →L[ℂ] H B →L[ℂ] H (A × B) :=
  LinearMap.mkContinuous
    { toFun := tensorLeft
      map_add' := fun x y => by
        apply ContinuousLinearMap.ext
        intro z
        apply lp.ext
        funext ab
        change (x ab.1+y ab.1)*z ab.2 = x ab.1*z ab.2 + y ab.1*z ab.2
        ring
      map_smul' := fun c x => by
        apply ContinuousLinearMap.ext
        intro z
        apply lp.ext
        funext ab
        change (c*x ab.1)*z ab.2 = c*(x ab.1*z ab.2)
        ring }
    1 (fun x => by
      apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      intro y
      change ‖tensor x y‖ ≤ (1*‖x‖)*‖y‖
      rw [tensor_norm, one_mul])

@[simp] theorem tensorBilinear_apply (x : H A) (y : H B) : tensorBilinear x y = tensor x y := rfl

theorem tendsto_tensor {C : Type*} {l : Filter C} {x : C → H A} {y : C → H B}
    {a : H A} {b : H B} (hx : Filter.Tendsto x l (nhds a)) (hy : Filter.Tendsto y l (nhds b)) :
    Filter.Tendsto (fun c => tensor (x c) (y c)) l (nhds (tensor a b)) :=
  (tensorBilinear.continuous₂.tendsto (a,b)).comp (hx.prodMk_nhds hy)

end TensorLp

namespace EntropyPhotonNumber

section
open Filter Topology TensorLp

theorem tendsto_rootColumn {n : ℕ} {A : Type*} {l : Filter A}
    {ρ : A → State n} {σ : State n}
    (h : Tendsto (fun a => (ρ a).op) l (𝓝 σ.op)) (k : NumberIndex n) :
    Tendsto (fun a => rootColumn (ρ a) k) l (𝓝 (rootColumn σ k)) :=
  (ContinuousLinearMap.apply ℂ (Fock n) (numberKet k)).continuous.tendsto _ |>.comp
    (TraceEnsemble.tendsto_positiveRoot (fun a => (ρ a).positive) σ.positive h)

theorem tendsto_beamOutput {n : ℕ} {A : Type*} {l : Filter A}
    (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {ρ σ : A → State n} {ρ₀ σ₀ : State n}
    (hρ : Tendsto (fun a => (ρ a).op) l (𝓝 ρ₀.op))
    (hσ : Tendsto (fun a => (σ a).op) l (𝓝 σ₀.op)) :
    Tendsto (fun a => (beamOutput η hη (ρ a) (σ a)).op) l (𝓝 (beamOutput η hη ρ₀ σ₀).op) := by
  apply TraceEnsemble.tendsto_operator
    (fun a => hasSum_slice_family (mixedVector_norm η hη (ρ a) (σ a)))
    (hasSum_slice_family (mixedVector_norm η hη ρ₀ σ₀))
  intro bi
  apply (sliceCLM bi.1).continuous.tendsto _ |>.comp
  apply (beamUnitary η hη).continuous.tendsto _ |>.comp
  exact tendsto_tensor (tendsto_rootColumn hρ bi.2.1) (tendsto_rootColumn hσ bi.2.2)

end

open QuantumTrace TraceEnsemble
theorem diagonalState_entropy {n : ℕ} (p : NumberIndex n → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : HasSum p 1) :
    entropy (diagonalState p hp hs) = ∑' k, Real.negMulLog (p k) := by
  rw [entropy_eq_quantumTrace]
  congr 1
  funext k
  rw [QuantumTrace.entropyOperator_apply_eigenvector (diagonalState p hp hs).positive.isSymmetric
    (diagonalState_eigen p hp hs k), inner_smul_right,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal k k, ite_eq_left rfl, mul_one, Complex.ofReal_re]
@[simp] theorem mixture_entry {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) (ρ σ : State n)
    (k l : NumberIndex n) :
    entry (mixture t ht ρ σ).op k l = (t : ℂ)*entry ρ.op k l + ((1-t : ℝ) : ℂ)*entry σ.op k l := by
  simp only [mixture, entry, add_apply, smul_apply,
    inner_add_right, inner_smul_right]

theorem mixture_finiteEnergy {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) {ρ σ : State n}
    (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) : FiniteEnergy (mixture t ht ρ σ) := by
  unfold FiniteEnergy
  convert! (hρ.mul_left t).add (hσ.mul_left (1-t)) using 1
  funext k
  simp only [mixture_entry, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem mixture_energy {n : ℕ} (t : ℝ) (ht : t ∈ Set.Icc 0 1) {ρ σ : State n}
    (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (mixture t ht ρ σ) = t*energy ρ+(1-t)*energy σ := by
  unfold energy
  have he (k : NumberIndex n) :
      (totalNumber k : ℝ)*(entry (mixture t ht ρ σ).op k k).re =
      t*((totalNumber k : ℝ)*(entry ρ.op k k).re)+
        (1-t)*((totalNumber k : ℝ)*(entry σ.op k k).re) := by
    simp only [mixture_entry, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  simp only [he]
  rw [(hρ.mul_left t).tsum_add (hσ.mul_left (1-t)), tsum_mul_left, tsum_mul_left]

end EntropyPhotonNumber

namespace QuantumTrace
open scoped ENNReal

theorem summable_finite_product (n : ℕ) (w : ℕ → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : Summable w) :
    Summable (fun k : Fin n → ℕ => ∏ j, w (k j)) := by
  have hh : (∑' k : Fin n → ℕ, ENNReal.ofReal (∏ j, w (k j))) < ⊤ := by
    simp only [ENNReal.ofReal_prod_of_nonneg (fun _ _ => hw _)]
    rw [tsum_finite_product n (fun k => ENNReal.ofReal (w k))]
    exact ENNReal.pow_lt_top hs.tsum_ofReal_lt_top
  have he := ENNReal.summable_toReal hh.ne
  simpa only [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun _ _ => hw _))] using he

theorem one_add_sum_le_product {I : Type*} (s : Finset I) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 1+∑ i ∈ s, a i ≤ ∏ i ∈ s, (1+a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hp : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg (fun j _ => ha j)
    have hm := mul_le_mul_of_nonneg_left ih (by linarith [ha i] : 0 ≤ 1+a i)
    nlinarith [mul_nonneg (ha i) hp]

theorem summable_shift_pow_geometric {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (m : ℕ) :
    Summable (fun k : ℕ => (1+(k : ℝ))^m*q^k) := by
  have hs := (summable_pow_mul_geometric_of_norm_lt_one m
    (show ‖q‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hq])).comp_injective Nat.succ_injective
  convert! hs.mul_left q⁻¹ using 1
  funext k
  change (1+(k : ℝ))^m*q^k = q⁻¹*((k+1 : ℕ)^m*q^(k+1))
  simp only [Nat.cast_succ, pow_succ]
  rw [add_comm (k : ℝ) 1]
  field_simp

theorem thermalWeight_moment_summable (n m : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun k : Fin n → ℕ => (1+∑ j, (k j : ℝ))^m * thermalWeight n r k) := by
  let q := r/(r+1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := (div_lt_one (by linarith : 0 < r+1)).mpr (by linarith)
  have hs := summable_finite_product n
    (fun k => (1+(k : ℝ))^m*((r+1)⁻¹*q^k))
    (fun _ => by positivity)
    (by simpa only [mul_left_comm _ (r+1)⁻¹] using
      (summable_shift_pow_geometric hq hq1 m).mul_left (r+1)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by apply mul_nonneg _ (thermalWeight_pos n hr _).le; positivity) _ hs
  intro k
  have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1+∑ j, (k j : ℝ))
    (one_add_sum_le_product Finset.univ (fun j => (k j : ℝ)) (fun _ => Nat.cast_nonneg _)) m
  have hh := mul_le_mul_of_nonneg_right h (thermalWeight_pos n hr k).le
  simpa only [← Finset.prod_pow, thermalWeight, ← Finset.prod_mul_distrib, q] using hh

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace
theorem numberMoment_nonneg {n : ℕ} (m : ℕ) (ρ : State n) : 0 ≤ numberMoment m ρ :=
  tsum_nonneg (fun k => mul_nonneg (by positivity) (ρ.positive.re_inner_nonneg_right _))

theorem thermalState_finiteMoment (n m : ℕ) (r : ℝ) (hr : 0 < r) :
    FiniteMoment m (thermalState n r hr) := by
  simpa only [FiniteMoment, thermalState_diagonal, totalNumber, Nat.cast_sum] using
    thermalWeight_moment_summable n m hr

theorem finiteMoment_finiteEnergy {n m : ℕ} (hm : 1 ≤ m) {ρ : State n} (hρ : FiniteMoment m ρ) :
    FiniteEnergy ρ := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)) _ hρ
  intro k
  have h : (1+(totalNumber k : ℝ))^1 ≤ (1+(totalNumber k : ℝ))^m :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (totalNumber k)]) hm
  exact mul_le_mul_of_nonneg_right (by simpa only [pow_one] using (by linarith :
    (totalNumber k : ℝ) ≤ (1+(totalNumber k : ℝ))^m)) (ρ.positive.re_inner_nonneg_right _)

theorem thermalState_finiteEnergy (n : ℕ) (r : ℝ) (hr : 0 < r) :
    FiniteEnergy (thermalState n r hr) :=
  finiteMoment_finiteEnergy le_rfl (thermalState_finiteMoment n 1 r hr)

theorem mixture_finiteMoment {n : ℕ} (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) {ρ σ : State n}
    (hρ : FiniteMoment m ρ) (hσ : FiniteMoment m σ) : FiniteMoment m (mixture t ht ρ σ) := by
  unfold FiniteMoment
  convert! (hρ.mul_left t).add (hσ.mul_left (1-t)) using 1
  funext k
  simp only [mixture_entry, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

end

open QuantumTrace Filter Topology

theorem energyMoment_ofReal {n : ℕ} {ρ : State n} (hρ : FiniteEnergy ρ) :
    energyMoment ρ = ENNReal.ofReal (energy ρ) := by
  rw [energyMoment_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun k => mul_nonneg (Nat.cast_nonneg _) (ρ.positive.re_inner_nonneg_right _)) hρ).symm

theorem beamOutput_energy_bound {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    {ρ σ : State n} (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (beamOutput η hη ρ σ) ≤ energy ρ + energy σ := by
  have h := beamOutput_energy_le η hη ρ σ
  rw [energyMoment_ofReal (beamOutput_finiteEnergy η hη hρ hσ),
    energyMoment_ofReal hρ, energyMoment_ofReal hσ,
    ← ENNReal.ofReal_add (energy_nonneg ρ) (energy_nonneg σ)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (energy_nonneg ρ) (energy_nonneg σ))).mp h

def regularizedOutput {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) (τD τ0 ρ σ : State n) : State n :=
  mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
    (beamOutput (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩
      (beamOutput η hη ρ σ) τD) τ0

theorem regularizedOutput_finiteEnergy {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) {τD τ0 ρ σ : State n}
    (hD : FiniteEnergy τD) (h0 : FiniteEnergy τ0) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    FiniteEnergy (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ σ) :=
  mixture_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ (beamOutput_finiteEnergy _ _ hρ hσ) hD) h0

theorem regularizedOutput_energy_bound {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) {τD τ0 ρ σ : State n}
    (hD : FiniteEnergy τD) (h0 : FiniteEnergy τ0) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ σ) ≤
      energy ρ+energy σ+energy τD+energy τ0 := by
  let γ := beamOutput (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩ (beamOutput η hη ρ σ) τD
  have hg := beamOutput_finiteEnergy (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩ (beamOutput_finiteEnergy η hη hρ hσ) hD
  have hb := beamOutput_energy_bound (1-δ) ⟨sub_nonneg.mpr hδ.2, sub_le_self _ hδ.1⟩
    (beamOutput_finiteEnergy η hη hρ hσ) hD
  have ha := beamOutput_energy_bound η hη hρ hσ
  change energy (mixture _ _ γ τ0) ≤ _
  apply (mixture_energy (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
    (ρ := γ) (σ := τ0) hg h0).le.trans
  have hp := energy_nonneg γ
  have hq := energy_nonneg τ0
  have hb' : energy γ ≤ energy ρ+energy σ+energy τD := by dsimp [γ]; linarith
  nlinarith [mul_nonneg hκ.1 hp, mul_nonneg (sub_nonneg.mpr hκ.2) hq]

theorem tendsto_regularizedOutput {n : ℕ} {A : Type*} {l : Filter A}
    (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1) (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1)
    (τD τ0 : State n) {ρ σ : A → State n} {ρ₀ σ₀ : State n}
    (hρ : Tendsto (fun a => (ρ a).op) l (𝓝 ρ₀.op))
    (hσ : Tendsto (fun a => (σ a).op) l (𝓝 σ₀.op)) :
    Tendsto (fun a => (regularizedOutput η δ κ hη hδ hκ τD τ0 (ρ a) (σ a)).op) l
      (𝓝 (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ₀ σ₀).op) := by
  exact ((tendsto_const_nhds.smul (tendsto_beamOutput _ _
    (tendsto_beamOutput _ _ hρ hσ) tendsto_const_nhds)).add tendsto_const_nhds)

theorem tendsto_entropy {n : ℕ} {A : Type*} {l : Filter A} {ρ : A → State n} {σ : State n}
    {E : ℝ} (hρ : ∀ a, FiniteEnergy (ρ a)) (hσ : FiniteEnergy σ)
    (hb : ∀ a, energy (ρ a) ≤ E) (hc : energy σ ≤ E)
    (h : Tendsto (fun a => (ρ a).op) l (𝓝 σ.op)) :
    Tendsto (fun a => entropy (ρ a)) l (𝓝 (entropy σ)) := by
  simp only [entropy_eq_quantumTrace]
  apply entropy_tendsto_finite_energy (E := E) (numberBasis n) (fun a => (ρ a).positive) σ.positive
    (fun a => trace_one_numberBasis (ρ a)) (trace_one_numberBasis σ) _ _ _ _ h
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hρ
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hσ
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hb
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hc

theorem entropy_linear_bound {n : ℕ} (ρ : State n) (hρ : FiniteEnergy ρ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a*entropy ρ ≤ a*n*Real.log (2*a/b+1)+(b/2)*energy ρ := by
  have hr : 0 < 2*a/b := by positivity
  have hh := entropy_le_thermal_crossEntropy (numberBasis n) ρ.positive
    (trace_one_numberBasis ρ)
    (by simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hρ) hr
  have hlog : Real.log ((2*a/b+1)/(2*a/b)) ≤ b/(2*a) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < (2*a/b+1)/(2*a/b))
    convert h using 1
    field_simp
    ring
  rw [← entropy_eq_quantumTrace] at hh
  have hh' : entropy ρ ≤ n*Real.log (2*a/b+1)+energy ρ*Real.log ((2*a/b+1)/(2*a/b)) := by
    simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hh
  have hm := mul_le_mul_of_nonneg_left hh' ha.le
  have hl := mul_le_mul_of_nonneg_left hlog (mul_nonneg ha.le (energy_nonneg ρ))
  have he : a*energy ρ*(b/(2*a)) = b/2*energy ρ := by field_simp
  rw [he] at hl
  nlinarith

instance stateTopology (n : ℕ) : TopologicalSpace (State n) :=
  TopologicalSpace.induced State.op inferInstance

theorem continuous_state_op (n : ℕ) : Continuous (State.op : State n → Fock n →L[ℂ] Fock n) :=
  continuous_induced_dom

theorem State.ext_op {n : ℕ} {ρ σ : State n} (h : ρ.op = σ.op) : ρ = σ := by
  cases ρ
  cases σ
  cases h
  rfl

def boundedStates (n : ℕ) (E M : ℝ) : Set (State n) :=
  {ρ | FiniteEnergy ρ ∧ energy ρ ≤ E ∧ FiniteMoment 4 ρ ∧ numberMoment 4 ρ ≤ M}

def stateOfMomentSet {n : ℕ} {E M : ℝ}
    (T : momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M) : State n where
  op := T.val
  positive := T.property.1.1
  trace_one := by simpa only [numberBasis_apply, entry] using T.property.1.2.1

theorem stateOfMomentSet_mem {n : ℕ} {E M : ℝ}
    (T : momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M) :
    stateOfMomentSet T ∈ boundedStates n E M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply,
      stateOfMomentSet] using T.property.1.2.2.1
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply,
      stateOfMomentSet] using T.property.1.2.2.2
  · simpa only [FiniteMoment, entry, numberBasis_apply, stateOfMomentSet] using T.property.2.1
  · simpa only [numberMoment, entry, numberBasis_apply, stateOfMomentSet] using T.property.2.2

theorem op_mem_momentSet {n : ℕ} {E M : ℝ} {ρ : State n} (hρ : ρ ∈ boundedStates n E M) :
    ρ.op ∈ momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M := by
  refine ⟨⟨ρ.positive, trace_one_numberBasis ρ, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [FiniteEnergy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hρ.1
  · simpa only [energy, totalNumber, Nat.cast_sum, entry, numberBasis_apply] using hρ.2.1
  · simpa only [FiniteMoment, entry, numberBasis_apply] using hρ.2.2.1
  · simpa only [numberMoment, entry, numberBasis_apply] using hρ.2.2.2

theorem boundedStates_isCompact (n : ℕ) (E M : ℝ) : IsCompact (boundedStates n E M) := by
  let S := momentSet (numberBasis n) (fun k => (1+(totalNumber k : ℝ))^4) E M
  have hc : IsCompact S := momentSet_isCompact _ _ (fun _ => by positivity) E M
  let : CompactSpace S := isCompact_iff_compactSpace.mp hc
  have hf : Continuous (stateOfMomentSet : S → State n) :=
    continuous_induced_rng.mpr continuous_subtype_val
  have hi : Set.range (stateOfMomentSet : S → State n) = boundedStates n E M := by
    ext ρ
    constructor
    · rintro ⟨T, rfl⟩
      exact stateOfMomentSet_mem T
    · intro hρ
      exact ⟨⟨ρ.op, op_mem_momentSet hρ⟩, State.ext_op rfl⟩
  rw [← hi]
  exact isCompact_range hf

theorem continuous_entropy_boundedStates (n : ℕ) (E M : ℝ) :
    Continuous (fun ρ : boundedStates n E M => entropy ρ.val) := by
  rw [continuous_iff_continuousAt]
  intro ρ
  exact tendsto_entropy (fun σ => σ.property.1) ρ.property.1
    (fun σ => σ.property.2.1) ρ.property.2.1
    ((continuous_state_op n).comp continuous_subtype_val).continuousAt

theorem penalty_lowerSemicontinuous (n : ℕ) (E M : ℝ) {b ζ : ℝ} (hb : 0 ≤ b) (hζ : 0 ≤ ζ) :
    LowerSemicontinuous (fun ρ : boundedStates n E M => b*energy ρ.val+ζ*numberMoment 4 ρ.val) := by
  have he (ρ : boundedStates n E M) : b*energy ρ.val+ζ*numberMoment 4 ρ.val =
      ∑' k, (b*(totalNumber k : ℝ)+ζ*(1+(totalNumber k : ℝ))^4)*(entry ρ.val.op k k).re := by
    rw [energy, numberMoment, ← tsum_mul_left, ← tsum_mul_left,
      ← (ρ.property.1.mul_left b).tsum_add (ρ.property.2.2.1.mul_left ζ)]
    congr 1
    funext k
    ring
  simp only [he]
  apply lowerSemicontinuous_tsum_nonneg
  · intro ρ k
    apply mul_nonneg _ (ρ.val.positive.re_inner_nonneg_right _)
    positivity
  · intro ρ
    convert! (ρ.property.1.mul_left b).add (ρ.property.2.2.1.mul_left ζ) using 1
    funext k
    ring
  · intro k
    exact continuous_const.mul (Complex.continuous_re.comp (continuous_const.inner
      (((continuous_state_op n).comp continuous_subtype_val).clm_apply continuous_const)))

structure Regularization (n : ℕ) where
  η : ℝ
  δ : ℝ
  κ : ℝ
  hη : η ∈ Set.Icc 0 1
  hδ : δ ∈ Set.Icc 0 1
  hκ : κ ∈ Set.Icc 0 1
  τD : State n
  τ0 : State n
  finiteD : FiniteEnergy τD
  finite0 : FiniteEnergy τ0
  c : ℝ
  a1 : ℝ
  a2 : ℝ
  b1 : ℝ
  b2 : ℝ
  ζ : ℝ
  hc : 0 < c
  ha1 : 0 < a1
  ha2 : 0 < a2
  hb1 : 0 < b1
  hb2 : 0 < b2
  hζ : 0 < ζ

namespace Regularization
variable {n : ℕ} (R : Regularization n)

def output (ρ σ : State n) : State n :=
  regularizedOutput R.η R.δ R.κ R.hη R.hδ R.hκ R.τD R.τ0 ρ σ

def objective (ρ σ : State n) : ℝ :=
  R.c*entropy (R.output ρ σ)-R.a1*entropy ρ-R.a2*entropy σ+
    (R.b1*energy ρ+R.ζ*numberMoment 4 ρ)+(R.b2*energy σ+R.ζ*numberMoment 4 σ)

def entropyConstant : ℝ :=
  R.a1*n*Real.log (2*R.a1/R.b1+1)+R.a2*n*Real.log (2*R.a2/R.b2+1)

theorem coercive (ρ σ : State n) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    R.b1/2*energy ρ+R.b2/2*energy σ+R.ζ*numberMoment 4 ρ+R.ζ*numberMoment 4 σ ≤
      R.objective ρ σ+R.entropyConstant := by
  have h1 := entropy_linear_bound ρ hρ R.ha1 R.hb1
  have h2 := entropy_linear_bound σ hσ R.ha2 R.hb2
  have h0 := mul_nonneg R.hc.le (entropy_nonneg (R.output ρ σ))
  dsimp [objective, entropyConstant]
  linarith

theorem continuous_output_entropy (E M : ℝ) :
    Continuous (fun p : boundedStates n E M × boundedStates n E M =>
      entropy (R.output p.1.val p.2.val)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_entropy (E := E+E+energy R.τD+energy R.τ0)
    (fun q => regularizedOutput_finiteEnergy _ _ _ _ _ _ R.finiteD R.finite0
      q.1.property.1 q.2.property.1)
    (regularizedOutput_finiteEnergy _ _ _ _ _ _ R.finiteD R.finite0 p.1.property.1 p.2.property.1)
  · intro q
    exact (regularizedOutput_energy_bound _ _ _ _ _ _ R.finiteD R.finite0
      q.1.property.1 q.2.property.1).trans (by linarith [q.1.property.2.1, q.2.property.2.1])
  · exact (regularizedOutput_energy_bound _ _ _ _ _ _ R.finiteD R.finite0
      p.1.property.1 p.2.property.1).trans (by linarith [p.1.property.2.1, p.2.property.2.1])
  · exact tendsto_regularizedOutput _ _ _ _ _ _ _ _
      ((continuous_state_op n).comp (continuous_subtype_val.comp continuous_fst)).continuousAt
      ((continuous_state_op n).comp (continuous_subtype_val.comp continuous_snd)).continuousAt

theorem objective_lowerSemicontinuous (E M : ℝ) :
    LowerSemicontinuous (fun p : boundedStates n E M × boundedStates n E M =>
      R.objective p.1.val p.2.val) := by
  have hc : Continuous (fun p : boundedStates n E M × boundedStates n E M =>
      R.c*entropy (R.output p.1.val p.2.val)-R.a1*entropy p.1.val-R.a2*entropy p.2.val) :=
    ((continuous_const.mul (R.continuous_output_entropy E M)).sub
      (continuous_const.mul ((continuous_entropy_boundedStates n E M).comp continuous_fst))).sub
      (continuous_const.mul ((continuous_entropy_boundedStates n E M).comp continuous_snd))
  exact (hc.lowerSemicontinuous.add
    ((penalty_lowerSemicontinuous n E M R.hb1.le R.hζ.le).comp continuous_fst)).add
    ((penalty_lowerSemicontinuous n E M R.hb2.le R.hζ.le).comp continuous_snd)

theorem sublevel_bounds (C : ℝ) (ρ σ : State n) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ)
    (h : R.objective ρ σ ≤ C) :
    0 ≤ C+R.entropyConstant ∧
    energy ρ ≤ 2*(C+R.entropyConstant)/R.b1 ∧
    energy σ ≤ 2*(C+R.entropyConstant)/R.b2 ∧
    numberMoment 4 ρ ≤ (C+R.entropyConstant)/R.ζ ∧
    numberMoment 4 σ ≤ (C+R.entropyConstant)/R.ζ := by
  have hc := R.coercive ρ σ hρ hσ
  have he1 := energy_nonneg ρ
  have he2 := energy_nonneg σ
  have hm1 := numberMoment_nonneg 4 ρ
  have hm2 := numberMoment_nonneg 4 σ
  have hp1 := mul_nonneg R.hb1.le he1
  have hp2 := mul_nonneg R.hb2.le he2
  have hq1 := mul_nonneg R.hζ.le hm1
  have hq2 := mul_nonneg R.hζ.le hm2
  refine ⟨by linarith, (le_div_iff₀ R.hb1).mpr ?_, (le_div_iff₀ R.hb2).mpr ?_,
    (le_div_iff₀ R.hζ).mpr ?_, (le_div_iff₀ R.hζ).mpr ?_⟩ <;> nlinarith

theorem sublevel_mem_bounded (C : ℝ) (ρ σ : State n)
    (h1 : FiniteMoment 4 ρ) (h2 : FiniteMoment 4 σ) (h : R.objective ρ σ ≤ C) :
    ρ ∈ boundedStates n (2*(C+R.entropyConstant)/R.b1+2*(C+R.entropyConstant)/R.b2)
      ((C+R.entropyConstant)/R.ζ) ∧
    σ ∈ boundedStates n (2*(C+R.entropyConstant)/R.b1+2*(C+R.entropyConstant)/R.b2)
      ((C+R.entropyConstant)/R.ζ) := by
  have hE1 := finiteMoment_finiteEnergy (by decide : 1 ≤ 4) h1
  have hE2 := finiteMoment_finiteEnergy (by decide : 1 ≤ 4) h2
  have hb := R.sublevel_bounds C ρ σ hE1 hE2 h
  have hp : 0 ≤ 2*(C+R.entropyConstant)/R.b1 := div_nonneg (by linarith [hb.1]) R.hb1.le
  have hq : 0 ≤ 2*(C+R.entropyConstant)/R.b2 := div_nonneg (by linarith [hb.1]) R.hb2.le
  exact ⟨⟨hE1, by linarith [hb.2.1], h1, hb.2.2.2.1⟩,
    ⟨hE2, by linarith [hb.2.2.1], h2, hb.2.2.2.2⟩⟩

theorem exists_constrained_minimum (E M : ℝ) (pw : boundedStates n E M × boundedStates n E M) :
    ∃ p : boundedStates n E M × boundedStates n E M,
      ∀ q : boundedStates n E M × boundedStates n E M,
        R.objective p.1.val p.2.val ≤ R.objective q.1.val q.2.val := by
  let : CompactSpace (boundedStates n E M) :=
    isCompact_iff_compactSpace.mp (boundedStates_isCompact n E M)
  obtain ⟨p, _, hp⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨pw, Set.mem_univ _⟩ isCompact_univ
    ((R.objective_lowerSemicontinuous E M).lowerSemicontinuousOn Set.univ)
  exact ⟨p, fun q => hp (Set.mem_univ q)⟩

theorem exists_minimum (ρw σw : State n) (hw1 : FiniteMoment 4 ρw) (hw2 : FiniteMoment 4 σw) :
    ∃ ρ σ : State n, FiniteMoment 4 ρ ∧ FiniteMoment 4 σ ∧
      R.objective ρ σ ≤ R.objective ρw σw ∧
      ∀ ρ' σ' : State n, FiniteMoment 4 ρ' → FiniteMoment 4 σ' →
        R.objective ρ σ ≤ R.objective ρ' σ' := by
  let C := R.objective ρw σw
  let E := 2*(C+R.entropyConstant)/R.b1+2*(C+R.entropyConstant)/R.b2
  let M := (C+R.entropyConstant)/R.ζ
  have hwm := R.sublevel_mem_bounded C ρw σw hw1 hw2 le_rfl
  let pw : boundedStates n E M × boundedStates n E M := (⟨ρw, hwm.1⟩, ⟨σw, hwm.2⟩)
  obtain ⟨p, hp⟩ := R.exists_constrained_minimum E M pw
  have hpw : R.objective p.1.val p.2.val ≤ C := hp pw
  refine ⟨p.1.val, p.2.val, p.1.property.2.2.1, p.2.property.2.2.1, hpw, ?_⟩
  intro ρ σ h1 h2
  by_cases h : R.objective ρ σ ≤ C
  · have hh := R.sublevel_mem_bounded C ρ σ h1 h2 h
    exact hp (⟨ρ, hh.1⟩, ⟨σ, hh.2⟩)
  · exact hpw.trans (le_of_lt (lt_of_not_ge h))

end Regularization
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

def basisMoment (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ∑' i, w i*ENNReal.ofReal (‖inner ℂ (b i) x‖^2)

def basisExpectation (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' i, w i*ENNReal.ofReal (inner ℂ (b i) (T (b i))).re

theorem basisMoment_one (b : HilbertBasis I ℂ E) (x : E) :
    basisMoment b (fun _ => 1) x = ENNReal.ofReal (‖x‖^2) := by
  simp only [basisMoment, one_mul]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (basis_hasSum_norm_sq b x).summable,
    (basis_hasSum_norm_sq b x).tsum_eq]

theorem basisMoment_ofReal (b : HilbertBasis I ℂ E) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : E) (hs : Summable (fun i => w i*‖inner ℂ (b i) x‖^2)) :
    basisMoment b (fun i => ENNReal.ofReal (w i)) x =
      ENNReal.ofReal (∑' i, w i*‖inner ℂ (b i) x‖^2) := by
  simp only [basisMoment, ← ENNReal.ofReal_mul (hw _)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hw i) (sq_nonneg _)) hs).symm

variable [CompleteSpace E]

theorem basisExpectation_ensemble (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞)
    {v : J → E} (hv : Summable (fun j => ‖v j‖^2)) :
    basisExpectation b w (TraceEnsemble.operator v) = ∑' j, basisMoment b w (v j) := by
  have he (i : I) : ENNReal.ofReal (inner ℂ (b i) (TraceEnsemble.operator v (b i))).re =
      ∑' j, ENNReal.ofReal (‖inner ℂ (b i) (v j)‖^2) := by
    have hs := TraceEnsemble.hasSum_quadratic hv (b i)
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable]
  simp only [basisExpectation, he, ← ENNReal.tsum_mul_left, basisMoment]
  exact ENNReal.tsum_comm

theorem basisExpectation_le_of_form_le (a : HilbertBasis J ℂ E) (b : HilbertBasis I ℂ E)
    (w : I → ℝ≥0∞) (v : J → ℝ≥0∞) {A B : ℝ≥0∞}
    (h : ∀ x, basisMoment b w x ≤ A*ENNReal.ofReal (‖x‖^2)+B*basisMoment a v x)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun j => (inner ℂ (a j) (T (a j))).re) 1) :
    basisExpectation b w T ≤ A+B*basisExpectation a v T := by
  let u : J → E := fun j => TraceEnsemble.positiveRoot T (a j)
  have hu : HasSum (fun j => ‖u j‖^2) 1 := by
    simpa only [TraceEnsemble.sqrt_quadratic hp] using ht
  have he : TraceEnsemble.operator u = T := TraceEnsemble.sqrt_ensemble a hp ht.summable
  have hn : (∑' j, ENNReal.ofReal (‖u j‖^2)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hu.summable,
      hu.tsum_eq, ENNReal.ofReal_one]
  rw [← he, basisExpectation_ensemble b w hu.summable, basisExpectation_ensemble a v hu.summable]
  calc
    _ ≤ ∑' j, (A*ENNReal.ofReal (‖u j‖^2)+B*basisMoment a v (u j)) :=
      ENNReal.tsum_le_tsum (fun j => h (u j))
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hn, mul_one]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace

def numberVectorMoment {n : ℕ} (x : Fock n) : ℝ≥0∞ :=
  basisMoment (numberBasis n) (fun k => (totalNumber k : ℝ≥0∞)) x

theorem numberVectorMoment_eq {n : ℕ} (x : Fock n) :
    numberVectorMoment x = ∑' k, ENNReal.ofReal ((totalNumber k : ℝ)*‖inner ℂ (numberBasis n k) x‖^2) := by
  simp only [numberVectorMoment, basisMoment, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

theorem finiteVectorEnergy_iff {n : ℕ} (x : Fock n) :
    FiniteVectorEnergy x ↔ numberVectorMoment x < ⊤ := by
  rw [numberVectorMoment_eq]
  constructor
  · intro hx
    exact hx.tsum_ofReal_lt_top
  · intro hx
    have hs := ENNReal.summable_toReal hx.ne
    simpa only [FiniteVectorEnergy, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))] using hs

theorem numberVectorMoment_ofReal {n : ℕ} (x : Fock n) (hx : FiniteVectorEnergy x) :
    numberVectorMoment x = ENNReal.ofReal (vectorEnergy x) := by
  rw [numberVectorMoment_eq]
  exact (ENNReal.ofReal_tsum_of_nonneg
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hx).symm

theorem thermal_log_constants {n : ℕ} {r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    0 ≤ -Real.log κ+n*Real.log (r+1) ∧ 0 < Real.log ((r+1)/r) := by
  have hr1 : 1 ≤ r+1 := by linarith
  have hlogκ := Real.log_nonpos hκ.le hκ1
  have hlogr := Real.log_nonneg hr1
  constructor
  · exact add_nonneg (neg_nonneg.mpr hlogκ) (mul_nonneg (Nat.cast_nonneg _) hlogr)
  · apply Real.log_pos
    exact (lt_div_iff₀ hr).mpr (by linarith)

theorem negativeLog_extended_le_thermal {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (x : Fock n) :
    basisMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) x ≤
      ENNReal.ofReal (-Real.log κ+n*Real.log (r+1))*ENNReal.ofReal (‖x‖^2)+
      ENNReal.ofReal (Real.log ((r+1)/r))*numberVectorMoment x := by
  have hc := thermal_log_constants (n := n) hr hκ hκ1
  have hp1 (j : J) : p j ≤ 1 := hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)
  have hlog (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le (hp1 j))
  by_cases hx : FiniteVectorEnergy x
  · have h := negativeLog_le_thermal ρ hr hκ hκ1 hle b p hp hs he x hx
    have hE : 0 ≤ vectorEnergy x := tsum_nonneg (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    rw [basisMoment_ofReal b _ hlog x h.1, numberVectorMoment_ofReal x hx,
      ← ENNReal.ofReal_mul hc.1, ← ENNReal.ofReal_mul hc.2.le, ← ENNReal.ofReal_add (mul_nonneg hc.1 (sq_nonneg _)) (mul_nonneg hc.2.le hE)]
    exact ENNReal.ofReal_le_ofReal h.2
  · have he : numberVectorMoment x = ⊤ := not_lt_top_iff.mp (fun h => hx ((finiteVectorEnergy_iff x).mpr h))
    rw [he, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc.2).ne', add_top]
    exact le_top

theorem negativeLog_expectation_le_thermal {n : ℕ} (ρ σ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    basisExpectation b (fun j => ENNReal.ofReal (-Real.log (p j))) σ.op ≤
      ENNReal.ofReal (-Real.log κ+n*Real.log (r+1))+
      ENNReal.ofReal (Real.log ((r+1)/r))*
        basisExpectation (numberBasis n) (fun k => (totalNumber k : ℝ≥0∞)) σ.op :=
  basisExpectation_le_of_form_le (numberBasis n) b _ _
    (negativeLog_extended_le_thermal ρ hr hκ hκ1 hle b p hp hs he) σ.positive (trace_one_numberBasis σ)

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

def sliceMoment (b : HilbertBasis J ℂ E) (w : J → ℝ≥0∞)
    (V : I → E →L[ℂ] E) (x : E) : ℝ≥0∞ := ∑' i, basisMoment b w (V i x)

omit [CompleteSpace E] in
theorem sliceMoment_bound (a : HilbertBasis K ℂ E) (b : HilbertBasis J ℂ E)
    (v : K → ℝ≥0∞) (w : J → ℝ≥0∞) (V : I → E →L[ℂ] E) {A B F : ℝ≥0∞}
    (hform : ∀ x, basisMoment b w x ≤ A*ENNReal.ofReal (‖x‖^2)+B*basisMoment a v x)
    (hn : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (he : ∀ x, (∑' i, basisMoment a v (V i x)) ≤
      basisMoment a v x+F*ENNReal.ofReal (‖x‖^2)) (x : E) :
    sliceMoment b w V x ≤ (A+B*F)*ENNReal.ofReal (‖x‖^2)+B*basisMoment a v x := by
  have hN : (∑' i, ENNReal.ofReal (‖V i x‖^2)) = ENNReal.ofReal (‖x‖^2) := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hn x).summable, (hn x).tsum_eq]
  calc
    _ ≤ ∑' i, (A*ENNReal.ofReal (‖V i x‖^2)+B*basisMoment a v (V i x)) :=
      ENNReal.tsum_le_tsum (fun i => hform (V i x))
    _ = A*ENNReal.ofReal (‖x‖^2)+B*(∑' i, basisMoment a v (V i x)) := by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hN]
    _ ≤ A*ENNReal.ofReal (‖x‖^2)+B*(basisMoment a v x+F*ENNReal.ofReal (‖x‖^2)) := by
      exact add_le_add le_rfl (mul_le_mul' le_rfl (he x))
    _ = _ := by ring

def sliceCoordinates (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) (ij : I × J) : E →ₗ[ℂ] ℂ :=
  (Real.sqrt (w ij.2) : ℂ) • ((innerSL ℂ (b ij.2)).toLinearMap.comp
    ((V ij.1).toLinearMap.comp S.toLinearMap))

omit [CompleteSpace E] in
theorem sliceCoordinates_square (b : HilbertBasis J ℂ E) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) (ij : I × J) (x : E) :
    ‖sliceCoordinates b w V S ij x‖^2 = w ij.2*‖inner ℂ (b ij.2) (V ij.1 (S x))‖^2 := by
  change ‖(Real.sqrt (w ij.2) : ℂ)*inner ℂ (b ij.2) (V ij.1 (S x))‖^2 = _
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hw _)]

omit [CompleteSpace E] in
theorem sliceCoordinates_sum (b : HilbertBasis J ℂ E) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) (x : E) :
    (∑' ij, ENNReal.ofReal (‖sliceCoordinates b w V S ij x‖^2)) =
      sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) := by
  simp only [sliceCoordinates_square b w hw, ENNReal.ofReal_mul (hw _),
    ENNReal.tsum_prod', sliceMoment, basisMoment]

theorem sliceMoment_bounded_representation (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (V : I → E →L[ℂ] E) (S : E →L[ℂ] E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) ≤
      ENNReal.ofReal (C*‖x‖^2)) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (w j)) V (S x) := by
  let f := sliceCoordinates b w V S
  have hs (x : E) : Summable (fun ij => ‖f ij x‖^2) := by
    have hfinite : (∑' ij, ENNReal.ofReal (‖f ij x‖^2)) ≠ ⊤ := by
      rw [sliceCoordinates_sum b w hw]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb x)
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hfinite
  have hbound (x : E) : (∑' ij, ‖f ij x‖^2) ≤ C*‖x‖^2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (sq_nonneg _))).mp
    rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs x), sliceCoordinates_sum b w hw]
    exact hb x
  obtain ⟨B,hB,he⟩ := SquareAnalysis.exists_positive_representation f hs hC hbound
  refine ⟨B,hB,fun x => ?_⟩
  rw [he, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (hs x)]
  exact sliceCoordinates_sum b w hw V S x

end QuantumTrace

namespace EntropyPhotonNumber

section
open QuantumTrace TensorLp

theorem numberVectorMoment_eq_tensor {n : ℕ} (x : Fock n) :
    numberVectorMoment x = vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x := by
  simp only [numberVectorMoment, basisMoment, vectorMoment, numberBasis_apply, numberKet,
    lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

theorem numberWeight_eq {n : ℕ} (i : NumberIndex n) :
    numberWeight i = 1+(totalNumber i : ℝ) := by
  simp only [numberWeight, totalNumber, Nat.cast_sum]

def energyInverse (n : ℕ) : Fock n →L[ℂ] Fock n :=
  inversePower rootNumberWeight rootNumberWeight_one_le 1

theorem energyInverse_quadratic {n : ℕ} (x : Fock n) (i : NumberIndex n) :
    numberWeight i*‖energyInverse n x i‖^2 = ‖x i‖^2 := by
  have hW : 0 < numberWeight i := lt_of_lt_of_le (by norm_num) (numberWeight_one_le i)
  change numberWeight i*‖(((rootNumberWeight i^1)⁻¹ : ℝ) : ℂ)*x i‖^2 = _
  rw [pow_one, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    inv_pow, rootNumberWeight, Real.sq_sqrt hW.le]
  rw [← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul]

theorem energyInverse_norm {n : ℕ} (x : Fock n) : ‖energyInverse n x‖ ≤ ‖x‖ := by
  calc
    _ ≤ ‖energyInverse n‖*‖x‖ := (energyInverse n).le_opNorm x
    _ ≤ 1*‖x‖ := mul_le_mul_of_nonneg_right (inversePower_norm_le _ _ _) (norm_nonneg _)
    _ = _ := one_mul _

theorem energyInverse_finiteEnergy {n : ℕ} (x : Fock n) : FiniteVectorEnergy (energyInverse n x) := by
  change Summable _
  simp only [numberBasis_apply, numberKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  apply Summable.of_nonneg_of_le (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) _
    (SquareAnalysis.hasSum_square x).summable
  intro i
  calc
    _ ≤ numberWeight i*‖energyInverse n x i‖^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [numberWeight_eq]
      linarith
    _ = _ := energyInverse_quadratic x i

theorem energyInverse_energy {n : ℕ} (x : Fock n) :
    vectorEnergy (energyInverse n x) ≤ ‖x‖^2 := by
  rw [vectorEnergy, ← (SquareAnalysis.hasSum_square x).tsum_eq]
  apply (energyInverse_finiteEnergy x).tsum_le_tsum _ (SquareAnalysis.hasSum_square x).summable
  intro i
  simp only [numberBasis_apply, numberKet, lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]
  calc
    _ ≤ numberWeight i*‖energyInverse n x i‖^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      rw [numberWeight_eq]
      linarith
    _ = _ := energyInverse_quadratic x i

theorem logarithmic_slice_representation {n : ℕ} (ρ : State n) {r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ.op)
    {J I : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (V : I → Fock n →L[ℂ] Fock n) (F : ℝ) (hF : 0 ≤ F)
    (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (hE : ∀ x, (∑' i, vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) (V i x)) ≤
      vectorMoment (fun k => (totalNumber k : ℝ≥0∞)) x+ENNReal.ofReal F*ENNReal.ofReal (‖x‖^2)) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) V (energyInverse n x) := by
  let A := -Real.log κ+n*Real.log (r+1)
  let D := Real.log ((r+1)/r)
  have hc := thermal_log_constants (n := n) hr hκ hκ1
  have hA : 0 ≤ A := hc.1
  have hD : 0 ≤ D := hc.2.le
  have hp1 (j : J) : p j ≤ 1 := hs.tsum_eq ▸ hs.summable.le_tsum j (fun i _ => (hp i).le)
  have hlog (j : J) : 0 ≤ -Real.log (p j) := neg_nonneg.mpr (Real.log_nonpos (hp j).le (hp1 j))
  apply sliceMoment_bounded_representation b (fun j => -Real.log (p j)) hlog V (energyInverse n)
    (C := A+D*F+D) (by positivity)
  intro x
  have h := sliceMoment_bound (numberBasis n) b (fun k => (totalNumber k : ℝ≥0∞))
    (fun j => ENNReal.ofReal (-Real.log (p j))) V
    (negativeLog_extended_le_thermal ρ hr hκ hκ1 hle b p hp hs he) hV
    (by intro y; simpa only [← numberVectorMoment_eq_tensor, numberVectorMoment] using hE y) (energyInverse n x)
  have hN : ‖energyInverse n x‖^2 ≤ ‖x‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (energyInverse_norm x) 2
  have hE0 : 0 ≤ vectorEnergy (energyInverse n x) :=
    tsum_nonneg (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  change _ ≤ (ENNReal.ofReal A+ENNReal.ofReal D*ENNReal.ofReal F)*
    ENNReal.ofReal (‖energyInverse n x‖^2)+ENNReal.ofReal D*numberVectorMoment (energyInverse n x) at h
  rw [numberVectorMoment_ofReal _ (energyInverse_finiteEnergy x), ← ENNReal.ofReal_mul hD,
    ← ENNReal.ofReal_add hA (mul_nonneg hD hF),
    ← ENNReal.ofReal_mul (add_nonneg hA (mul_nonneg hD hF)),
    ← ENNReal.ofReal_mul hD, ← ENNReal.ofReal_add
      (mul_nonneg (add_nonneg hA (mul_nonneg hD hF)) (sq_nonneg _)) (mul_nonneg hD hE0)] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hn := mul_le_mul_of_nonneg_left hN (add_nonneg hA (mul_nonneg hD hF))
  have he' := mul_le_mul_of_nonneg_left (energyInverse_energy x) hD
  nlinarith

end

open QuantumTrace

theorem number_form_representation (n : ℕ) :
    ∃ B : Fock n →L[ℂ] Fock n, B.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (B x)).re = numberVectorMoment (energyInverse n x) := by
  have hb (x : Fock n) : sliceMoment (numberBasis n) (fun k => ENNReal.ofReal (totalNumber k))
      (fun _ : Unit => (1 : Fock n →L[ℂ] Fock n)) (energyInverse n x) ≤
      ENNReal.ofReal (1*‖x‖^2) := by
    simp only [sliceMoment, one_apply_eq_self, tsum_fintype,
      Fintype.sum_unique, ENNReal.ofReal_natCast]
    change numberVectorMoment (energyInverse n x) ≤ _
    rw [numberVectorMoment_ofReal _ (energyInverse_finiteEnergy x), one_mul]
    exact ENNReal.ofReal_le_ofReal (energyInverse_energy x)
  obtain ⟨B,hB,h⟩ := sliceMoment_bounded_representation (numberBasis n)
    (fun k => (totalNumber k : ℝ)) (fun _ => Nat.cast_nonneg _)
    (fun _ : Unit => (1 : Fock n →L[ℂ] Fock n)) (energyInverse n) (by norm_num : (0:ℝ) ≤ 1) hb
  refine ⟨B,hB,fun x => ?_⟩
  simpa only [sliceMoment, one_apply_eq_self, tsum_fintype,
    Fintype.sum_unique, ENNReal.ofReal_natCast, numberVectorMoment] using h x

theorem combined_form_representation {n : ℕ} {J I : Type*}
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞) (V : I → Fock n →L[ℂ] Fock n)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive)
    (he : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re = sliceMoment b w V (energyInverse n x))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    ∃ C : Fock n →L[ℂ] Fock n, C.IsPositive ∧ ∀ x,
      ENNReal.ofReal (inner ℂ x (C x)).re =
        ENNReal.ofReal α*sliceMoment b w V (energyInverse n x)+
        ENNReal.ofReal β*numberVectorMoment (energyInverse n x) := by
  obtain ⟨D,hD,hDe⟩ := number_form_representation n
  let C := (α : ℂ) • B+(β : ℂ) • D
  have hC : C.IsPositive := (hB.smul_of_nonneg (by exact_mod_cast hα)).add
    (hD.smul_of_nonneg (by exact_mod_cast hβ))
  refine ⟨C,hC,fun x => ?_⟩
  have hx : (inner ℂ x (C x)).re = α*(inner ℂ x (B x)).re+β*(inner ℂ x (D x)).re := by
    change (inner ℂ x ((α : ℂ) • B x+(β : ℂ) • D x)).re = _
    simp
  have hBx : 0 ≤ (inner ℂ x (B x)).re := hB.re_inner_nonneg_right x
  have hDx : 0 ≤ (inner ℂ x (D x)).re := hD.re_inner_nonneg_right x
  rw [hx, ENNReal.ofReal_add (mul_nonneg hα hBx) (mul_nonneg hβ hDx), ENNReal.ofReal_mul hα,
    ENNReal.ofReal_mul hβ, he, hDe]

theorem gibbsFactor_quadratic {ι : Type*} (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    (k : ℝ) (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (x : SequenceHilbert ι) :
    (inner ℂ x (gibbsFactor s hs k B x)).re = k*‖x‖^2+
      (inner ℂ (inversePower s hs 3 x) (B (inversePower s hs 3 x))).re := by
  have hh : inner ℂ (inversePower s hs 3 x) (B (inversePower s hs 3 x)) =
      inner ℂ x (inversePower s hs 3 (B (inversePower s hs 3 x))) :=
    (inversePower_positive s hs 3).isSymmetric x (B (inversePower s hs 3 x))
  change (inner ℂ x (k • x+inversePower s hs 3 (B (inversePower s hs 3 x)))).re = _
  rw [inner_add_right, Complex.add_re, ← hh]
  rw [inner_smul_right_eq_smul, Complex.smul_re]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem energyInverse_mul_three {n : ℕ} (x : Fock n) :
    energyInverse n (inversePower rootNumberWeight rootNumberWeight_one_le 3 x) =
      inversePower rootNumberWeight rootNumberWeight_one_le 4 x := by
  exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x)
    (inversePower_mul rootNumberWeight rootNumberWeight_one_le 1 3)

theorem gibbsFactor_slice_form {n : ℕ} {J I : Type*}
    (b : HilbertBasis J ℂ (Fock n)) (w : J → ℝ≥0∞) (V : I → Fock n →L[ℂ] Fock n)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ}
    (he : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment b w V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 ≤ k) (x : Fock n) :
    ENNReal.ofReal (inner ℂ x (gibbsFactor rootNumberWeight rootNumberWeight_one_le k B x)).re =
      ENNReal.ofReal k*ENNReal.ofReal (‖x‖^2)+
      (ENNReal.ofReal α*sliceMoment b w V (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)+
      ENNReal.ofReal β*numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) := by
  have hBx : 0 ≤ (inner ℂ (inversePower rootNumberWeight rootNumberWeight_one_le 3 x)
      (B (inversePower rootNumberWeight rootNumberWeight_one_le 3 x))).re :=
    hB.re_inner_nonneg_right _
  rw [gibbsFactor_quadratic, ENNReal.ofReal_add (mul_nonneg hk (sq_nonneg _))
    hBx, ENNReal.ofReal_mul hk, he, energyInverse_mul_three]

end EntropyPhotonNumber

namespace QuantumTrace

section
variable {ι J L : Type*}

theorem gibbs_form_energy_identity (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    (A : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (hA : IsStrictlyPositive A)
    (c : HilbertBasis L ℂ (SequenceHilbert ι)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (heU : ∀ l, (inversePower s hs 4*Ring.inverse A*inversePower s hs 4) (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l)
    (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (heT : ∀ j, T (b j) = (p j : ℂ) • b j)
    (hm : Summable (fun i => s i^8*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re)) :
    ∃ y : J → SequenceHilbert ι,
      (∀ j i, y j i = (s i^4 : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) ∧
      (∀ j, inversePower s hs 4 (y j) = (Real.sqrt (p j) : ℂ) • b j) ∧
      Summable (fun j => ‖y j‖^2) ∧
      (∑' j, ‖y j‖^2) = ∑' i, s i^8*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re ∧
      Summable (fun j => (inner ℂ (y j) (A (y j))).re) ∧
      HasSum (fun l => u l*(inner ℂ (c l) (T (c l))).re)
        (∑' j, (inner ℂ (y j) (A (y j))).re) := by
  have hm' : Summable (fun i => (s i^4)^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
    simpa only [← pow_mul] using hm
  obtain ⟨y, hy, hyS, hyE⟩ := weighted_spectral_vectors b T p hp heT (fun i => s i^4) hm'
  have hxy (j : J) : inversePower s hs 4 (y j) = (Real.sqrt (p j) : ℂ) • b j := by
    ext i
    rw [inversePower_apply, hy]
    change (((s i^4)⁻¹ : ℝ) : ℂ)*(((s i^4 : ℝ) : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) = (Real.sqrt (p j) : ℂ)*b j i
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero _ (by linarith [hs i]))]
    simp
  have hAp : A.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp hA.nonneg
  have hsum : Summable (fun j => (inner ℂ (y j) (A (y j))).re) := by
    apply Summable.of_nonneg_of_le (fun j => hAp.re_inner_nonneg_right _) _ (hyS.mul_left ‖A‖)
    intro j
    calc
      _ ≤ ‖inner ℂ (y j) (A (y j))‖ := Complex.re_le_norm _
      _ ≤ ‖y j‖*‖A (y j)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y j‖*(‖A‖*‖y j‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  let f : J × L → ℝ := fun a => u a.2*(p a.1*‖inner ℂ (c a.2) (b a.1)‖^2)
  have hf0 (a : J × L) : 0 ≤ f a := mul_nonneg (hu _).le (mul_nonneg (hp _) (sq_nonneg _))
  have hrow (j : J) : HasSum (fun l => f (j,l)) (inner ℂ (y j) (A (y j))).re := by
    have hh := inverse_factor_form_parseval c A (inversePower s hs 4) hA
      (inversePower_positive s hs 4).isSymmetric (inversePower_injective s hs 4) u hu heU (y j)
    rw [hxy] at hh
    simpa only [f, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs, Real.sq_sqrt (hp j)] using hh
  have hf : Summable f := by
    apply (summable_prod_of_nonneg hf0).mpr
    refine ⟨fun j => (hrow j).summable, ?_⟩
    simpa only [(hrow _).tsum_eq] using hsum
  have hcol (l : L) : HasSum (fun j => f (j,l)) (u l*(inner ℂ (c l) (T (c l))).re) := by
    have hh := (hasSum_quadratic_eigenbasis b T p heT (c l)).mul_left (u l)
    simpa only [f, norm_inner_symm] using hh
  have hh : HasSum (fun l => u l*(inner ℂ (c l) (T (c l))).re)
      (∑' j, (inner ℂ (y j) (A (y j))).re) := by
    have hcols : Summable (fun l => u l*(inner ℂ (c l) (T (c l))).re) := by
      have hc : Summable (fun l => ∑' j, f (j,l)) := hf.prod_symm.prod
      simpa only [(hcol _).tsum_eq] using hc
    have heq : (∑' l, u l*(inner ℂ (c l) (T (c l))).re) =
        ∑' j, (inner ℂ (y j) (A (y j))).re := calc
      _ = ∑' l, ∑' j, f (j,l) := tsum_congr (fun l => (hcol l).tsum_eq.symm)
      _ = ∑' j, ∑' l, f (j,l) := Summable.tsum_comm (f := fun j l => f (j,l)) hf
      _ = _ := tsum_congr (fun j => (hrow j).tsum_eq)
    exact heq ▸ hcols.hasSum
  refine ⟨y, ?_, hxy, hyS, ?_, hsum, hh⟩
  · intro j i
    simpa only [Complex.ofReal_pow] using hy j i
  · simpa only [← pow_mul] using hyE

end

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J K : Type*}

theorem sliceMoment_ensemble (b : HilbertBasis K ℂ E) (w : K → ℝ≥0∞)
    (V : I → E →L[ℂ] E) {v : J → E}
    (hs : Summable (fun ij : I × J => ‖V ij.1 (v ij.2)‖^2)) :
    (∑' j, sliceMoment b w V (v j)) =
      basisExpectation b w (TraceEnsemble.operator (fun ij : I × J => V ij.1 (v ij.2))) := by
  rw [basisExpectation_ensemble b w hs]
  simp only [sliceMoment, ENNReal.tsum_prod']
  exact ENNReal.tsum_comm

omit [CompleteSpace E] in
theorem basisMoment_smul (b : HilbertBasis K ℂ E) (w : K → ℝ≥0∞) (x : E) (c : ℂ) :
    basisMoment b w (c • x) = ENNReal.ofReal (‖c‖^2)*basisMoment b w x := by
  simp only [basisMoment, inner_smul_right, norm_mul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro i
  ring

omit [CompleteSpace E] in
theorem sliceMoment_smul (b : HilbertBasis K ℂ E) (w : K → ℝ≥0∞)
    (V : I → E →L[ℂ] E) (x : E) (c : ℂ) :
    sliceMoment b w V (c • x) = ENNReal.ofReal (‖c‖^2)*sliceMoment b w V x := by
  simp only [sliceMoment, map_smul, basisMoment_smul, ENNReal.tsum_mul_left]

end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

theorem firstKraus_slice_expectation {n : ℕ} {K : Type*}
    (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ σ : State n)
    (b : HilbertBasis K ℂ (Fock n)) (w : K → ℝ≥0∞) :
    (∑' j, sliceMoment b w (firstKraus η hη σ) (rootColumn ρ j)) =
      basisExpectation b w (beamOutput η hη ρ σ).op := by
  rw [sliceMoment_ensemble b w (firstKraus η hη σ)
    (TraceEnsemble.kraus_hasSum (firstKraus_norm η hη σ) (rootColumn_norm ρ)).summable,
    firstKraus_ensemble η hη ρ σ (rootColumn ρ) (rootColumn_norm ρ) (rootColumn_operator ρ)]

theorem secondKraus_slice_expectation {n : ℕ} {K : Type*}
    (η : ℝ) (hη : η ∈ Set.Icc 0 1) (ρ σ : State n)
    (b : HilbertBasis K ℂ (Fock n)) (w : K → ℝ≥0∞) :
    (∑' j, sliceMoment b w (secondKraus η hη ρ) (rootColumn σ j)) =
      basisExpectation b w (beamOutput η hη ρ σ).op := by
  rw [sliceMoment_ensemble b w (secondKraus η hη ρ)
    (TraceEnsemble.kraus_hasSum (secondKraus_norm η hη ρ) (rootColumn_norm σ)).summable,
    secondKraus_ensemble η hη ρ σ (rootColumn σ) (rootColumn_norm σ) (rootColumn_operator σ)]

theorem composedKraus_first_ensemble {n : ℕ} {J : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (v : J → Fock n) (hv : HasSum (fun j => ‖v j‖^2) 1)
    (he : TraceEnsemble.operator v = ρ.op) :
    TraceEnsemble.operator (fun z : ((NumberIndex n × NumberIndex n) ×
      (NumberIndex n × NumberIndex n)) × J =>
      composeKraus (firstKraus θ hθ τ) (firstKraus η hη σ) z.1 (v z.2)) =
      (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  have hV := TraceEnsemble.kraus_hasSum (firstKraus_norm η hη σ) hv
  have heV := firstKraus_ensemble η hη ρ σ v hv he
  have heU := firstKraus_ensemble θ hθ (beamOutput η hη ρ σ) τ _ hV heV
  exact (composeKraus_ensemble (firstKraus θ hθ τ) (firstKraus η hη σ) v).trans heU

theorem composed_slice_expectation {n : ℕ} {K : Type*}
    (η θ : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1) (ρ σ τ : State n)
    (b : HilbertBasis K ℂ (Fock n)) (w : K → ℝ≥0∞) :
    (∑' j, sliceMoment b w (composeKraus (firstKraus θ hθ τ) (firstKraus η hη σ))
        (rootColumn ρ j)) =
      basisExpectation b w (beamOutput θ hθ (beamOutput η hη ρ σ) τ).op := by
  have hV := composeKraus_norm (firstKraus θ hθ τ) (firstKraus η hη σ)
      (firstKraus_norm θ hθ τ) (firstKraus_norm η hη σ)
  rw [sliceMoment_ensemble b w _ (TraceEnsemble.kraus_hasSum hV (rootColumn_norm ρ)).summable,
    composedKraus_first_ensemble η θ hη hθ ρ σ τ (rootColumn ρ) (rootColumn_norm ρ)
      (rootColumn_operator ρ)]

end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {J : Type*}

theorem basisExpectation_ofReal (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) {T : E →L[ℂ] E} (hp : T.IsPositive)
    (hs : Summable (fun j => w j*(inner ℂ (b j) (T (b j))).re)) :
    basisExpectation b (fun j => ENNReal.ofReal (w j)) T =
      ENNReal.ofReal (∑' j, w j*(inner ℂ (b j) (T (b j))).re) := by
  simp only [basisExpectation, ← ENNReal.ofReal_mul (hw _)]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (hw j)
    (hp.re_inner_nonneg_right _)) hs).symm

theorem basisExpectation_finite_iff (b : HilbertBasis J ℂ E) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) {T : E →L[ℂ] E} (hp : T.IsPositive) :
    basisExpectation b (fun j => ENNReal.ofReal (w j)) T < ⊤ ↔
      Summable (fun j => w j*(inner ℂ (b j) (T (b j))).re) := by
  simp only [basisExpectation, ← ENNReal.ofReal_mul (hw _)]
  constructor
  · intro h
    have hs := ENNReal.summable_toReal h.ne
    convert hs using 1
    funext j
    exact (ENNReal.toReal_ofReal (mul_nonneg (hw j) (hp.re_inner_nonneg_right (b j)))).symm
  · intro h
    exact h.tsum_ofReal_lt_top

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

theorem diagonalVector_operator (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : Summable p) (T : E →L[ℂ] E)
    (he : ∀ j, T (b j) = (p j : ℂ) • b j) : operator (diagonalVector b p) = T := by
  have hb (j : J) : operator (diagonalVector b p) (b j) = T (b j) := by
    rw [diagonalVector_eigen b p hp hs j, he]
  ext x
  have hh := (operator (diagonalVector b p)).hasSum (b.hasSum_repr x)
  apply hh.unique
  convert T.hasSum (b.hasSum_repr x) using 1
  funext j
  simp only [ContinuousLinearMap.map_smul, hb]

end TraceEnsemble

namespace EntropyPhotonNumber
open QuantumTrace TraceEnsemble

theorem sequenceBasis_numberKet {n : ℕ} (i : NumberIndex n) :
    sequenceBasis (NumberIndex n) i = numberKet i := by
  apply lp.ext
  funext j
  by_cases h : i = j
  · subst j; simp [sequenceBasis_apply, numberKet, lp.single_apply]
  · simp [sequenceBasis_apply, numberKet, lp.single_apply, h]

theorem gibbs_slice_trace {n : ℕ} {J L K I : Type*}
    (c : HilbertBasis L ℂ (Fock n)) (u : L → ℝ) (hu : ∀ l, 0 < u l)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (ρ : State n) (heρ : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (hm : FiniteMoment 4 ρ)
    (a : HilbertBasis K ℂ (Fock n)) (w : K → ℝ≥0∞)
    (V : I → Fock n →L[ℂ] Fock n) (hV : ∀ x, HasSum (fun i => ‖V i x‖^2) (‖x‖^2))
    (σ : State n)
    (heσ : TraceEnsemble.operator (fun z : I × J => V z.1 (diagonalVector b p z.2)) = σ.op)
    {B : Fock n →L[ℂ] Fock n} (hB : B.IsPositive) {α β : ℝ}
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (B x)).re =
      ENNReal.ofReal α*sliceMoment a w V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x))
    {k : ℝ} (hk : 0 < k)
    (heK : ∀ l, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (c l) =
      (((u l)⁻¹ : ℝ) : ℂ) • c l) :
    ∃ E : ℝ, HasSum (fun l => u l*(inner ℂ (c l) (ρ.op (c l))).re) E ∧
      ENNReal.ofReal E = ENNReal.ofReal k*ENNReal.ofReal (numberMoment 4 ρ)+
        (ENNReal.ofReal α*basisExpectation a w σ.op+
         ENNReal.ofReal β*ENNReal.ofReal (energy ρ)) := by
  classical
  have hm' : Summable (fun i => rootNumberWeight i^8*
      (inner ℂ (sequenceBasis _ i) (ρ.op (sequenceBasis _ i))).re) := by
    simpa only [rootNumberWeight_pow_eight, numberWeight_eq, sequenceBasis_numberKet,
      FiniteMoment, entry] using hm
  obtain ⟨y, _, hy, hyS, hyE, hyA, hK⟩ := gibbs_form_energy_identity
    rootNumberWeight rootNumberWeight_one_le (gibbsFactor rootNumberWeight rootNumberWeight_one_le k B)
    (gibbsFactor_strictPositive _ _ hk hB) c u hu heK b ρ.op p hp heρ hm'
  have hnorm : (∑' j, ‖y j‖^2) = numberMoment 4 ρ := by
    simpa only [rootNumberWeight_pow_eight, numberWeight_eq, numberMoment,
      sequenceBasis_numberKet, entry] using hyE
  have hv : HasSum (fun j => ‖diagonalVector b p j‖^2) 1 := by
    simpa only [diagonalVector_norm_sq b p hp] using hs
  have hρv := diagonalVector_operator b p hp hs.summable ρ.op heρ
  have hSv : (∑' j, sliceMoment a w V (diagonalVector b p j)) = basisExpectation a w σ.op := by
    rw [sliceMoment_ensemble a w V (TraceEnsemble.kraus_hasSum hV hv).summable, heσ]
  have hNv : (∑' j, numberVectorMoment (diagonalVector b p j)) = ENNReal.ofReal (energy ρ) := by
    rw [show (∑' j, numberVectorMoment (diagonalVector b p j)) =
      basisExpectation (numberBasis n) (fun i => (totalNumber i : ℝ≥0∞))
        (TraceEnsemble.operator (diagonalVector b p)) from
      (basisExpectation_ensemble _ _ hv.summable).symm, hρv]
    have he := basisExpectation_ofReal (numberBasis n) (fun i => (totalNumber i : ℝ))
      (fun _ => Nat.cast_nonneg _) ρ.positive (by simpa only [FiniteEnergy, numberBasis_apply, entry] using (finiteMoment_finiteEnergy (by norm_num : 1 ≤ 4) hm))
    simpa only [ENNReal.ofReal_natCast, energy, numberBasis_apply, entry] using he
  let A := gibbsFactor rootNumberWeight rootNumberWeight_one_le k B
  have hA : A.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (gibbsFactor_strictPositive _ _ hk hB).nonneg
  refine ⟨_, hK, ?_⟩
  change ENNReal.ofReal (∑' j, (inner ℂ (y j) (A (y j))).re) = _
  have hsum : ENNReal.ofReal (∑' j, (inner ℂ (y j) (A (y j))).re) =
      ∑' j, ENNReal.ofReal (inner ℂ (y j) (A (y j))).re :=
    ENNReal.ofReal_tsum_of_nonneg (fun j => hA.re_inner_nonneg_right (y j)) hyA
  rw [hsum]
  have hQ (j : J) : ENNReal.ofReal (inner ℂ (y j) (A (y j))).re =
      ENNReal.ofReal k*ENNReal.ofReal (‖y j‖^2)+
      (ENNReal.ofReal α*sliceMoment a w V (diagonalVector b p j)+
       ENNReal.ofReal β*numberVectorMoment (diagonalVector b p j)) := by
    have hh := gibbsFactor_slice_form a w V hB hform hk.le (y j)
    simpa only [hy, diagonalVector, A] using hh
  simp_rw [hQ]
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hSv, hNv,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hyS, hnorm]

end EntropyPhotonNumber

end

end OAI
