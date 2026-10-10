import Mathlib

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate

namespace Coulomb

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Configuration (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin 3)
abbrev Spins (n : ℕ) := Fin n → Fin 2

structure Nuclei (M : ℕ) where
  nonempty : 0 < M
  position : Fin M → Space
  distinct : Function.Injective position
  charge : Fin M → ℝ
  charge_ge_one : ∀ j, 1 ≤ charge j

noncomputable def totalCharge {M : ℕ} (S : Nuclei M) : ℝ := ∑ j, S.charge j

noncomputable def position {n : ℕ} (x : Configuration n) (i : Fin n) : Space :=
  WithLp.toLp 2 (fun b => x (i, b))

noncomputable def coulombKernel (x : Space) : ℝ := ‖x‖⁻¹

noncomputable def attraction {M : ℕ} (S : Nuclei M) (x : Space) : ℝ :=
  ∑ j, S.charge j * coulombKernel (x - S.position j)

noncomputable def permute {n : ℕ} (p : Equiv.Perm (Fin n))
    (x : Configuration n) : Configuration n :=
  WithLp.toLp 2 (fun ib => x (p ib.1, ib.2))

structure H1Vector (n : ℕ) where
  value : Spins n → Configuration n → ℂ
  gradient : Spins n → (Fin n × Fin 3) → Configuration n → ℂ
  value_L2 : ∀ s, MemLp (value s) 2 volume
  partial_L2 : ∀ s a, MemLp (gradient s a) 2 volume
  weak_partial : ∀ s a (φ : Configuration n → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, value s x * (fderiv ℝ φ x (EuclideanSpace.single a 1) : ℂ)) =
        -(∫ x, gradient s a x * (φ x : ℂ))

def Antisymmetric {n : ℕ} (ψ : H1Vector n) : Prop :=
  ∀ (p : Equiv.Perm (Fin n)) (s : Spins n),
    ∀ᵐ x ∂volume,
      ψ.value (s ∘ p) (permute p x) = ((p.sign : ℤ) : ℂ) * ψ.value s x

noncomputable def mass {n : ℕ} (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, ‖ψ.value s x‖ ^ 2

noncomputable def kinetic {n : ℕ} (ψ : H1Vector n) : ℝ :=
  (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x, ‖ψ.gradient s a x‖ ^ 2

noncomputable def nuclearEnergy {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, (∑ i, attraction S (position x i)) * ‖ψ.value s x‖ ^ 2

noncomputable def pairEnergy {n : ℕ} (ψ : H1Vector n) : ℝ :=
  ∑ s, ∫ x, (∑ i : Fin n, ∑ j : Fin n,
    if i < j then coulombKernel (position x i - position x j) else 0) *
      ‖ψ.value s x‖ ^ 2

noncomputable def form {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) : ℝ :=
  kinetic ψ - nuclearEnergy S ψ + pairEnergy ψ

noncomputable def energy {M : ℕ} (S : Nuclei M) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    sInf {e : ℝ | ∃ ψ : H1Vector n, Antisymmetric ψ ∧ mass ψ = 1 ∧ form S ψ = e}

def GroundState {M n : ℕ} (S : Nuclei M) (ψ : H1Vector n) : Prop :=
  Antisymmetric ψ ∧ mass ψ = 1 ∧ form S ψ = energy S n

def atom (Z : ℕ) (hZ : 1 ≤ Z) : Nuclei 1 where
  nonempty := by decide
  position := fun _ => 0
  distinct := fun a b _ => Subsingleton.elim a b
  charge := fun _ => Z
  charge_ge_one := by intro j; exact_mod_cast hZ

noncomputable def exteriorMass {n : ℕ} (ψ : H1Vector n) (r : ℝ) : ℝ :=
  ∑ s, ∫ x, (∑ i : Fin n, if r < ‖position x i‖ then (1 : ℝ) else 0) *
    ‖ψ.value s x‖ ^ 2

noncomputable def outerRadius {n : ℕ} (ψ : H1Vector n) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ exteriorMass ψ r ≤ (1 / 2 : ℝ)}

theorem bounded_quadratic_bootstrap (h : ℕ → ℝ) (B : ℝ)
    (hB : ∀ j, h j ≤ B) (hgrowth : ∀ j, (h j) ^ 2 ≤ 1 + h (j + 1)) :
    h 0 ≤ 2 := by
  by_contra hbad
  have hstart : 2 < h 0 := lt_of_not_ge hbad
  have hlinear : ∀ j : ℕ, 2 + (j : ℝ) ≤ h j := by
    intro j
    induction j with
    | zero => simpa using hstart.le
    | succ j ih =>
      have hjnonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hj : 2 ≤ h j := by linarith
      have hprod : 0 ≤ (h j - 2) * (h j + 1) :=
        mul_nonneg (by linarith) (by linarith)
      have hg := hgrowth j
      push_cast
      nlinarith
  obtain ⟨j, hj⟩ := exists_nat_gt B
  have hb := hB j
  have hl := hlinear j
  linarith

theorem geometric_quadratic_bootstrap (g : ℕ → ℝ) (C D : ℝ)
    (hC : 1 ≤ C)
    (hbound : ∀ j, g j ≤ D * C ^ (j + 2))
    (hrec : ∀ j, (g j) ^ 2 ≤ C ^ (j + 1) * (1 + g (j + 1))) :
    g 0 ≤ 2 * C ^ 2 := by
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let h : ℕ → ℝ := fun j => g j / C ^ (j + 2)
  have hbounded : ∀ j, h j ≤ D := by
    intro j
    exact (div_le_iff₀ (pow_pos hCpos _)).2 (hbound j)
  have hrec' : ∀ j, (h j) ^ 2 ≤ 1 + h (j + 1) := by
    intro j
    have hpow : 1 ≤ C ^ (j + 3) := one_le_pow₀ hC
    have hpower : (C ^ (j + 2)) ^ 2 = C ^ (j + 1) * C ^ (j + 3) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hratio : C ^ (j + 1) / (C ^ (j + 2)) ^ 2 ≤ 1 := by
      apply (div_le_iff₀ (sq_pos_of_pos (pow_pos hCpos _))).2
      rw [one_mul, hpower]
      exact le_mul_of_one_le_right (le_of_lt (pow_pos hCpos _)) hpow
    calc
      (h j) ^ 2 = (g j) ^ 2 / (C ^ (j + 2)) ^ 2 := div_pow _ _ _
      _ ≤ (C ^ (j + 1) * (1 + g (j + 1))) / (C ^ (j + 2)) ^ 2 :=
        div_le_div_of_nonneg_right (hrec j) (sq_nonneg _)
      _ = C ^ (j + 1) / (C ^ (j + 2)) ^ 2 + h (j + 1) := by
        dsimp [h]
        rw [hpower]
        have heq : j + 1 + 2 = j + 3 := by omega
        rw [heq]
        field_simp
      _ ≤ 1 + h (j + 1) := by linarith
  have hzero := bounded_quadratic_bootstrap h D hbounded hrec'
  exact (div_le_iff₀ (pow_pos hCpos 2)).1 hzero

theorem memLp_two_real_mul {n : ℕ} {u : Configuration n → ℂ}
    (hu : MemLp u 2 volume) {f : Configuration n → ℝ} (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    MemLp (fun x => (f x : ℂ) * u x) 2 volume := by
  apply hu.of_le_mul (c := B) ((Complex.continuous_ofReal.comp hf).aestronglyMeasurable.mul
    hu.aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right (hB x) (norm_nonneg (u x))

noncomputable def H1Vector.smoothMul {n : ℕ} (ψ : H1Vector n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D) : H1Vector n where
  value s x := (f x : ℂ) * ψ.value s x
  gradient s a x :=
    (fderiv ℝ f x (EuclideanSpace.single a 1) : ℂ) * ψ.value s x +
      (f x : ℂ) * ψ.gradient s a x
  value_L2 s := memLp_two_real_mul (ψ.value_L2 s) hf.continuous hB
  partial_L2 s a :=
    (memLp_two_real_mul (ψ.value_L2 s)
      ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a)).add
      (memLp_two_real_mul (ψ.partial_L2 s a) hf.continuous hB)
  weak_partial s a φ hφ hφc := by
    let v := EuclideanSpace.single a (1 : ℝ)
    have hφL : MemLp (fun x => (φ x : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
        (hφc.comp_left (by simp))
    have hdφL : MemLp (fun x => (fderiv ℝ φ x v : ℂ)) 2 volume :=
      (Complex.continuous_ofReal.comp
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hφc.fderiv_apply ℝ v).comp_left (by simp))
    have hA : Integrable (fun x => ((f x : ℂ) * ψ.value s x) *
        (fderiv ℝ φ x v : ℂ)) volume :=
      (memLp_two_real_mul (ψ.value_L2 s) hf.continuous hB).integrable_mul hdφL
    have hB' : Integrable (fun x =>
        ((fderiv ℝ f x v : ℂ) * ψ.value s x) * (φ x : ℂ)) volume :=
      (memLp_two_real_mul (ψ.value_L2 s)
        ((hf.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a)).integrable_mul hφL
    have hC : Integrable (fun x => ((f x : ℂ) * ψ.gradient s a x) *
        (φ x : ℂ)) volume :=
      (memLp_two_real_mul (ψ.partial_L2 s a) hf.continuous hB).integrable_mul hφL
    have hweak := ψ.weak_partial s a (f * φ) (hf.mul hφ) hφc.mul_left
    have hprod : ∀ x, ψ.value s x * (fderiv ℝ (f * φ) x v : ℂ) =
        ((f x : ℂ) * ψ.value s x) * (fderiv ℝ φ x v : ℂ) +
        ((fderiv ℝ f x v : ℂ) * ψ.value s x) * (φ x : ℂ) := by
      intro x
      rw [fderiv_mul (hf.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
      simp only [add_apply, smul_apply,
        smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul]
      ring
    change (∫ x, ψ.value s x * (fderiv ℝ (f * φ) x v : ℂ)) = _ at hweak
    simp_rw [hprod] at hweak
    rw [integral_add hA hB'] at hweak
    have hr : ∀ x, ψ.gradient s a x * ((f * φ) x : ℂ) =
        ((f x : ℂ) * ψ.gradient s a x) * (φ x : ℂ) := by
      intro x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
      ring
    simp_rw [hr] at hweak
    change (∫ x, ((f x : ℂ) * ψ.value s x) * (fderiv ℝ φ x v : ℂ)) = _
    simp_rw [add_mul]
    rw [integral_add hB' hC]
    linear_combination hweak

theorem H1Vector.smoothMul_antisymmetric {n : ℕ} (ψ : H1Vector n)
    (hψ : Antisymmetric ψ) (f : Configuration n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (B D : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hD : ∀ a x, |fderiv ℝ f x (EuclideanSpace.single a 1)| ≤ D)
    (hsymm : ∀ p x, f (permute p x) = f x) :
    Antisymmetric (ψ.smoothMul f hf B D hB hD) := by
  intro p s
  filter_upwards [hψ p s] with x hx
  dsimp [H1Vector.smoothMul]
  rw [hsymm p x, hx]
  ring

lemma norm_real_mul_sq (a : ℝ) (z : ℂ) :
    ‖(a : ℂ) * z‖ ^ 2 = a ^ 2 * ‖z‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

lemma norm_real_mul_add_sq (a b : ℝ) (u v : ℂ) :
    ‖(a : ℂ) * u + (b : ℂ) * v‖ ^ 2 =
      a ^ 2 * ‖u‖ ^ 2 + b ^ 2 * ‖v‖ ^ 2 +
        2 * a * b * (u.re * v.re + u.im * v.im) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem quadratic_partition_derivative {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Configuration n → ℝ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) (x v : Configuration n) :
    ∑ i, f i x * fderiv ℝ (f i) x v = 0 := by
  classical
  have heq : (fun y => ∑ i, f i y ^ 2) = fun _ => (1 : ℝ) := funext hpart
  have hd := congrArg (fun g : Configuration n → ℝ => fderiv ℝ g x v) heq
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y => f i y ^ 2)
    (fun i _ => (hf i).differentiable (by simp) x |>.pow 2)] at hd
  simp only [sum_apply] at hd
  have hp : ∀ i, fderiv ℝ (fun y => f i y ^ 2) x v =
      2 * (f i x * fderiv ℝ (f i) x v) := by
    intro i
    change fderiv ℝ (f i ^ 2) x v = _
    rw [fderiv_pow 2 ((hf i).differentiable (by simp) x)]
    simp
    ring
  simp_rw [hp] at hd
  simp only [← Finset.mul_sum] at hd
  have hz : fderiv ℝ (fun _ : Configuration n => (1 : ℝ)) x v = 0 := by simp
  rw [hz] at hd
  linarith

theorem ims_pointwise {n : ℕ} {ι : Type*} [Fintype ι]
    (f : ι → Configuration n → ℝ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) (x e : Configuration n) (u v : ℂ) :
    (∑ i, ‖(fderiv ℝ (f i) x e : ℂ) * u + (f i x : ℂ) * v‖ ^ 2) =
      ‖v‖ ^ 2 + (∑ i, (fderiv ℝ (f i) x e) ^ 2) * ‖u‖ ^ 2 := by
  classical
  simp_rw [norm_real_mul_add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, hpart, one_mul]
  have hcross : (∑ i, 2 * fderiv ℝ (f i) x e * f i x *
      (u.re * v.re + u.im * v.im)) = 0 := by
    conv_lhs => arg 2; intro i; rw [show
      2 * fderiv ℝ (f i) x e * f i x * (u.re * v.re + u.im * v.im) =
        (f i x * fderiv ℝ (f i) x e) *
          (2 * (u.re * v.re + u.im * v.im)) by ring]
    rw [← Finset.sum_mul, quadratic_partition_derivative f hf hpart, zero_mul]
  rw [hcross]
  ring

theorem mass_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, mass (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) = mass ψ := by
  classical
  let χ := fun i => ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)
  change (∑ i, mass (χ i)) = mass ψ
  have hblock : ∀ s, (∑ i, ∫ x, ‖(χ i).value s x‖ ^ 2) =
      ∫ x, ‖ψ.value s x‖ ^ 2 := by
    intro s
    rw [← integral_finsetSum _ (fun i _ =>
      ((χ i).value_L2 s).integrable_norm_pow (p := 2) (by decide))]
    apply integral_congr_ae
    filter_upwards [] with x
    change (∑ i, ‖(f i x : ℂ) * ψ.value s x‖ ^ 2) = ‖ψ.value s x‖ ^ 2
    simp_rw [norm_real_mul_sq]
    rw [← Finset.sum_mul, hpart, one_mul]
  unfold mass
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun s _ => hblock s)

theorem kinetic_smooth_partition {n : ℕ} {ι : Type*} [Fintype ι]
    (ψ : H1Vector n) (f : ι → Configuration n → ℝ)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i)) (B D : ℝ)
    (hB : ∀ i x, |f i x| ≤ B)
    (hD : ∀ i a x, |fderiv ℝ (f i) x (EuclideanSpace.single a 1)| ≤ D)
    (hpart : ∀ x, ∑ i, f i x ^ 2 = 1) :
    (∑ i, kinetic (ψ.smoothMul (f i) (hf i) B D (hB i) (hD i))) =
      kinetic ψ + (1 / 2 : ℝ) * ∑ s, ∑ a, ∫ x,
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖ ^ 2 := by
  classical
  let χ := fun i => ψ.smoothMul (f i) (hf i) B D (hB i) (hD i)
  have hblock : ∀ s a, (∑ i, ∫ x, ‖(χ i).gradient s a x‖ ^ 2) =
      (∫ x, ‖ψ.gradient s a x‖ ^ 2) +
      ∫ x, (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
        ‖ψ.value s x‖ ^ 2 := by
    intro s a
    have hi : ∀ i, Integrable (fun x =>
        (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2 * ‖ψ.value s x‖ ^ 2)
        volume := by
      intro i
      have hL := memLp_two_real_mul (ψ.value_L2 s)
        (((hf i).continuous_fderiv (by simp)).clm_apply continuous_const) (hD i a)
      simpa only [norm_real_mul_sq] using hL.integrable_norm_pow (p := 2) (by decide)
    have herr : Integrable (fun x =>
        (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
          ‖ψ.value s x‖ ^ 2) volume := by
      simp_rw [Finset.sum_mul]
      exact integrable_finsetSum _ (fun i _ => hi i)
    rw [← integral_finsetSum _ (fun i _ =>
      ((χ i).partial_L2 s a).integrable_norm_pow (p := 2) (by decide))]
    have heq : (fun x => ∑ i, ‖(χ i).gradient s a x‖ ^ 2) =
        fun x => ‖ψ.gradient s a x‖ ^ 2 +
          (∑ i, (fderiv ℝ (f i) x (EuclideanSpace.single a 1)) ^ 2) *
            ‖ψ.value s x‖ ^ 2 := by
      funext x
      exact ims_pointwise f hf hpart x (EuclideanSpace.single a 1)
        (ψ.value s x) (ψ.gradient s a x)
    rw [heq, integral_add ((ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)) herr]
  change (∑ i, kinetic (χ i)) = _
  unfold kinetic
  rw [← Finset.mul_sum]
  have hswap : (∑ i, ∑ s, ∑ a, ∫ x, ‖(χ i).gradient s a x‖ ^ 2) =
      ∑ s, ∑ a, ∑ i, ∫ x, ‖(χ i).gradient s a x‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
  rw [hswap]
  simp_rw [hblock, Finset.sum_add_distrib]
  ring

open ContinuousLinearMap
open scoped Convolution

structure HardyCoordinates (n : ℕ) (i : Fin n) where
  coord : Fin 3 → Configuration n → ℝ
  smooth : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (coord b)
  directional : ∀ a b x, fderiv ℝ (coord a) x (EuclideanSpace.single (i,b) 1) =
    if a = b then 1 else 0

noncomputable def blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) : ℝ := ∑ b : Fin 3, (R.coord b x)^2

lemma blockRadiusSq_nonneg {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) (x : Configuration n) :
    0 ≤ blockRadiusSq i R x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma contDiff_blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i) :
    ContDiff ℝ (⊤ : ℕ∞) (blockRadiusSq i R) := by
  apply ContDiff.sum
  intro b _
  exact (R.smooth b).pow 2

lemma fderiv_blockRadiusSq {n : ℕ} (i : Fin n) (R : HardyCoordinates n i)
    (x : Configuration n) (b : Fin 3) :
    fderiv ℝ (blockRadiusSq i R) x (EuclideanSpace.single (i,b) 1) =
      2 * R.coord b x := by
  unfold blockRadiusSq
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun a (y : Configuration n) => (R.coord a y)^2)
    (fun a _ => ((R.smooth a).differentiable (by simp) x).pow 2)]
  simp only [sum_apply]
  have heach : ∀ a : Fin 3,
      fderiv ℝ (fun y : Configuration n => (R.coord a y)^2) x
        (EuclideanSpace.single (i,b) 1) =
          if a = b then 2 * R.coord b x else 0 := by
    intro a
    have hd := (((R.smooth a).differentiable (by simp) x).hasFDerivAt).pow 2
    rw [hd.fderiv]
    simp only [smul_apply, smul_eq_mul, R.directional]
    by_cases hab : a = b <;> simp [hab]
  simp_rw [heach]
  simp

end Coulomb
end
end

end OAI
