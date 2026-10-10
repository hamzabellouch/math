import Mathlib
import OAI.Probability.SKBarriers.Model

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK

def MainStatement (β : ℝ) : Prop :=
  Tendsto (continuousBadMass β) atTop (𝓝 1) ∧
  Tendsto (discreteBadMass β) atTop (𝓝 1)

def overlap {n : ℕ} (x y : Config n) : ℝ :=
  (∑ i : Fin n, spin (x i) * spin (y i)) / n

def flip {n : ℕ} (x : Config n) : Config n := fun i => !(x i)

@[simp] theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> norm_num [spin]

@[simp] theorem spin_sq (b : Bool) : spin b ^ 2 = 1 := by
  cases b <;> norm_num [spin]

@[simp] theorem flip_flip {n : ℕ} (x : Config n) : flip (flip x) = x := by
  funext i
  simp [flip]

@[simp] theorem hamiltonian_flip {n : ℕ} (J : Disorder n) (x : Config n) :
    hamiltonian J (flip x) = hamiltonian J x := by
  simp [hamiltonian, flip]

@[simp] theorem gibbs_flip {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    gibbs β J (flip x) = gibbs β J x := by
  simp [gibbs]

theorem partition_pos {n : ℕ} (β : ℝ) (J : Disorder n) : 0 < partition β J := by
  unfold partition
  exact Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty

theorem gibbs_pos {n : ℕ} (β : ℝ) (J : Disorder n) (x : Config n) :
    0 < gibbs β J x := by
  exact div_pos (Real.exp_pos _) (partition_pos β J)

theorem gibbs_sum {n : ℕ} (β : ℝ) (J : Disorder n) :
    ∑ x : Config n, gibbs β J x = 1 := by
  simp only [gibbs, ← Finset.sum_div]
  exact div_self (ne_of_gt (partition_pos β J))

@[simp] theorem overlap_flip_right {n : ℕ} (x y : Config n) :
    overlap x (flip y) = -overlap x y := by
  simp [overlap, flip, Finset.sum_neg_distrib, neg_div]

theorem overlap_comm {n : ℕ} (x y : Config n) : overlap x y = overlap y x := by
  simp only [overlap, mul_comm]

instance disorderLaw_probability (n : ℕ) : IsProbabilityMeasure (disorderLaw n) := by
  unfold disorderLaw
  infer_instance

theorem disorder_coordinate_law {n : ℕ} (e : Edge n) :
    HasLaw (fun J : Disorder n => J e) (gaussianReal 0 1) (disorderLaw n) := by
  exact (measurePreserving_eval (fun _ : Edge n => gaussianReal 0 1) e).hasLaw

theorem disorder_coordinate_gaussian {n : ℕ} (e : Edge n) :
    HasGaussianLaw (fun J : Disorder n => J e) (disorderLaw n) :=
  (disorder_coordinate_law e).hasGaussianLaw

theorem disorder_independent (n : ℕ) :
    iIndepFun (fun e (J : Disorder n) => J e) (disorderLaw n) := by
  exact iIndepFun_pi (fun _ => aemeasurable_id)

theorem disorder_gaussian (n : ℕ) : HasGaussianLaw (fun J : Disorder n => J) (disorderLaw n) :=
  (disorder_independent n).hasGaussianLaw disorder_coordinate_gaussian

theorem hamiltonian_gaussian {n : ℕ} (x : Config n) :
    HasGaussianLaw (fun J : Disorder n => hamiltonian J x) (disorderLaw n) := by
  have h : HasGaussianLaw
      (fun J : Disorder n => fun e : Edge n =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
    have hi : iIndepFun (fun e (J : Disorder n) =>
        J e * spin (x e.val.1) * spin (x e.val.2)) (disorderLaw n) := by
      exact iIndepFun_pi (μ := fun _ : Edge n => gaussianReal 0 1)
        (X := fun e z => z * spin (x e.val.1) * spin (x e.val.2))
        (fun _ => by fun_prop)
    apply hi.hasGaussianLaw
    intro e
    convert (disorder_coordinate_gaussian e).fun_smul
      (spin (x e.val.1) * spin (x e.val.2)) using 1
    simp only [smul_eq_mul]
    funext J
    ring
  simpa only [hamiltonian, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    h.fun_sum.fun_smul (Real.sqrt n)⁻¹

theorem hamiltonian_integrable {n : ℕ} (x : Config n) :
    Integrable (fun J : Disorder n => hamiltonian J x) (disorderLaw n) :=
  (hamiltonian_gaussian x).integrable

theorem disorder_mean_zero {n : ℕ} (e : Edge n) :
    ∫ J : Disorder n, J e ∂disorderLaw n = 0 := by
  rw [disorderLaw, integral_eval]
  exact integral_id_gaussianReal

theorem hamiltonian_mean_zero {n : ℕ} (x : Config n) :
    ∫ J : Disorder n, hamiltonian J x ∂disorderLaw n = 0 := by
  simp only [hamiltonian, div_eq_mul_inv]
  rw [integral_mul_const, integral_finsetSum]
  · simp only [integral_mul_const, disorder_mean_zero, zero_mul, Finset.sum_const_zero]
  · intro e _
    exact ((disorder_coordinate_gaussian e).integrable.mul_const _).mul_const _

theorem disorder_covariance {n : ℕ} (e f : Edge n) :
    cov[fun J : Disorder n => J e, fun J : Disorder n => J f; disorderLaw n] =
      if e = f then 1 else 0 := by
  classical
  by_cases hef : e = f
  · subst f
    rw [covariance_self (disorder_coordinate_gaussian e).aemeasurable, (disorder_coordinate_law e).variance_eq]
    simp
  · rw [(disorder_independent n).indepFun hef |>.covariance_eq_zero
      (disorder_coordinate_gaussian e).memLp_two
      (disorder_coordinate_gaussian f).memLp_two]
    simp [hef]

theorem hamiltonian_covariance_edges {n : ℕ} (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
    (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) / n := by
  classical
  simp only [hamiltonian, div_eq_mul_inv, covariance_mul_const_left,
    covariance_mul_const_right]
  rw [covariance_fun_sum_fun_sum]
  · simp only [covariance_mul_const_left, covariance_mul_const_right, disorder_covariance]
    have hsum : (∑ e : Edge n, ∑ f : Edge n,
        (if e = f then (1 : ℝ) else 0) * spin (x e.val.1) * spin (x e.val.2) *
          spin (y f.val.1) * spin (y f.val.2)) =
        ∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
          (spin (y e.val.1) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_eq_single e]
      · simp [mul_assoc]
      · intro f _ hfe
        simp [Ne.symm hfe]
      · simp
    rw [hsum]
    rw [mul_assoc, ← mul_inv, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg n)]
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _
  · intro e
    exact ((disorder_coordinate_gaussian e).memLp_two.mul_const _).mul_const _

theorem sum_edges {n : ℕ} (f : Fin n × Fin n → ℝ) :
    (∑ e : Edge n, f e.val) = ∑ i : Fin n, ∑ j : Fin n,
      if i < j then f (i, j) else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2))
    (by simp) f]
  rw [Finset.sum_filter, Fintype.sum_prod_type]

theorem sum_sq_eq_edges {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 = (∑ i, (a i) ^ 2) + 2 * ∑ e : Edge n, a e.val.1 * a e.val.2 := by
  classical
  rw [sum_edges (fun p : Fin n × Fin n => a p.1 * a p.2), pow_two, Fintype.sum_mul_sum]
  have hsplit (i j : Fin n) : a i * a j =
      (if i = j then a i ^ 2 else 0) +
      (if i < j then a i * a j else 0) +
      (if j < i then a i * a j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j
      simp [pow_two]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, a i * a j) =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i = j then a i ^ 2 else 0) +
        (if i < j then a i * a j else 0) +
        (if j < i then a i * a j else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsplit i j
  rw [hsum]
  simp only [Finset.sum_add_distrib]
  have hd : (∑ i : Fin n, ∑ j : Fin n, if i = j then a i ^ 2 else 0) =
      ∑ i, a i ^ 2 := by simp
  have hs : (∑ i : Fin n, ∑ j : Fin n, if j < i then a i * a j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then a i * a j else 0 := by
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [hd, hs]
  ring

theorem overlap_self {n : ℕ} (hn : 0 < n) (x : Config n) : overlap x x = 1 := by
  simp only [overlap, ← pow_two, spin_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hn.ne')

theorem hamiltonian_covariance {n : ℕ} (hn : 0 < n) (x y : Config n) :
    cov[fun J : Disorder n => hamiltonian J x,
      fun J : Disorder n => hamiltonian J y; disorderLaw n] =
      ((n : ℝ) * overlap x y ^ 2 - 1) / 2 := by
  rw [hamiltonian_covariance_edges]
  have hs := sum_sq_eq_edges (fun i => spin (x i) * spin (y i))
  have hd : (∑ i : Fin n, (spin (x i) * spin (y i)) ^ 2) = (n : ℝ) := by
    simp [mul_pow]
  rw [hd] at hs
  have he : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
      (spin (y e.val.1) * spin (y e.val.2))) =
      ((∑ i : Fin n, spin (x i) * spin (y i)) ^ 2 - n) / 2 := by
    have hr : (∑ e : Edge n, spin (x e.val.1) * spin (x e.val.2) *
        (spin (y e.val.1) * spin (y e.val.2))) =
        ∑ e : Edge n, (spin (x e.val.1) * spin (y e.val.1)) *
          (spin (x e.val.2) * spin (y e.val.2)) := by
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [hr]
    linarith
  rw [he, overlap]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn']

theorem disorder_linear_gaussian {n : ℕ} (a : Edge n → ℝ) :
    HasGaussianLaw (fun J : Disorder n => ∑ e, a e * J e) (disorderLaw n) := by
  simpa only [sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul] using
    (disorder_gaussian n).map_fun
      (∑ e : Edge n, a e • (ContinuousLinearMap.proj e : Disorder n →L[ℝ] ℝ))

theorem hamiltonian_add_gaussian {n : ℕ} (x y : Config n) :
    HasGaussianLaw (fun J : Disorder n => hamiltonian J x + hamiltonian J y)
      (disorderLaw n) := by
  convert disorder_linear_gaussian (fun e : Edge n =>
      (spin (x e.val.1) * spin (x e.val.2) +
       spin (y e.val.1) * spin (y e.val.2)) / Real.sqrt n) using 1
  funext J
  simp only [hamiltonian, div_eq_mul_inv, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem hamiltonian_variance {n : ℕ} (hn : 0 < n) (x : Config n) :
    Var[fun J : Disorder n => hamiltonian J x; disorderLaw n] = ((n : ℝ) - 1) / 2 := by
  rw [← covariance_self (hamiltonian_gaussian x).aemeasurable,
    hamiltonian_covariance hn, overlap_self hn]
  ring

theorem gaussian_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    (∫ ω, Real.exp (t * X ω) ∂μ) =
      Real.exp ((∫ ω, X ω ∂μ) * t + Var[X; μ] * t ^ 2 / 2) := by
  change mgf X μ t = _
  rw [mgf_gaussianReal ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩,
    Real.coe_toNNReal _ (variance_nonneg X μ)]

theorem gaussian_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : HasGaussianLaw X μ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  have := hX.isProbabilityMeasure
  rw [← mgf_pos_iff, mgf_gaussianReal ⟨hX.aemeasurable, hX.map_eq_gaussianReal⟩]
  exact Real.exp_pos _

theorem hamiltonian_exp_integral {n : ℕ} (hn : 0 < n) (x : Config n) (t : ℝ) :
    (∫ J : Disorder n, Real.exp (t * hamiltonian J x) ∂disorderLaw n) =
      Real.exp (t ^ 2 * ((n : ℝ) - 1) / 4) := by
  rw [gaussian_exp_integral (hamiltonian_gaussian x),
    hamiltonian_mean_zero, hamiltonian_variance hn]
  congr 1
  ring

theorem hamiltonian_add_exp_integral {n : ℕ} (hn : 0 < n)
    (x y : Config n) (t : ℝ) :
    (∫ J : Disorder n, Real.exp (t * (hamiltonian J x + hamiltonian J y))
      ∂disorderLaw n) =
      Real.exp (t ^ 2 * ((n : ℝ) - 1) / 2 +
        t ^ 2 * ((n : ℝ) * overlap x y ^ 2 - 1) / 2) := by
  rw [gaussian_exp_integral (hamiltonian_add_gaussian x y),
    integral_add (hamiltonian_integrable x) (hamiltonian_integrable y),
    hamiltonian_mean_zero, hamiltonian_mean_zero,
    variance_fun_add (hamiltonian_gaussian x).memLp_two (hamiltonian_gaussian y).memLp_two,
    hamiltonian_variance hn, hamiltonian_variance hn, hamiltonian_covariance hn]
  congr 1
  ring

end SK
end
end
end

end OAI
