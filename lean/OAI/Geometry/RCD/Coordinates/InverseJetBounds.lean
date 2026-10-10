import OAI.Geometry.RCD.Coordinates.FactorialMajorant
import OAI.Geometry.RCD.Coordinates.InverseDerivative
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-!
# Higher derivatives of inverse fields

The resolvent identity subtracts the value of the original field at the
base point before the higher product estimate is applied.  Its zeroth
derivative is then zero, so the inverse recurrence has no occurrence of
the current unknown derivative on the right.  These are actual iterated
Fréchet derivatives in a real Banach algebra, including bounded operators.
-/

open Finset Filter
open scoped BigOperators ContDiff Topology

noncomputable section

namespace RegularPointCoordinates

variable {X A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedRing A] [NormedAlgebra ℝ A]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAlgebra ℝ A] in
/-- The resolvent identity in the order needed for a one-sided inverse. -/
theorem inverse_field_resolvent {J K : X → A} {s : Set X} {x : X}
    (hleft : K x * J x = 1)
    (hright : ∀ y ∈ s, J y * K y = 1) :
    Set.EqOn K (fun y => K x - K x * ((J y - J x) * K y)) s := by
  intro y hy
  change K y = K x - K x * ((J y - J x) * K y)
  rw [sub_mul, mul_sub, hright y hy, mul_one,
    ← mul_assoc (K x) (J x) (K y), hleft, one_mul]
  abel

/-- At positive orders, subtracting the value at the base point does not
change the iterated derivative. -/
theorem iteratedFDerivWithin_sub_basepoint {J : X → A} {s : Set X} {x : X}
    {n : ℕ} (hJ : ContDiffWithinAt ℝ n J s x)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hn : n ≠ 0) :
    iteratedFDerivWithin ℝ n (fun y => J y - J x) s x =
      iteratedFDerivWithin ℝ n J s x := by
  rw [show (fun y => J y - J x) = J - (fun _ => J x) from rfl,
    iteratedFDerivWithin_sub_apply hJ contDiffWithinAt_const hs hx,
    iteratedFDerivWithin_const_of_ne hn]
  simp

/-- A higher inverse derivative is bounded by strictly lower inverse
derivatives.  The smoothness and inverse identities are explicit. -/
theorem norm_iteratedFDerivWithin_inverse_field_le
    {J K : X → A} {s : Set X} {x : X} {n : ℕ}
    (hJ : ContDiffOn ℝ n J s) (hK : ContDiffOn ℝ n K s)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hn : 0 < n)
    (hleft : K x * J x = 1) (hright : ∀ y ∈ s, J y * K y = 1) :
    ‖iteratedFDerivWithin ℝ n K s x‖ ≤ ‖K x‖ *
      ∑ i ∈ Finset.Icc 1 n, (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i J s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) K s x‖ := by
  let f : X → A := fun y => J y - J x
  let g : X → A := fun y => f y * K y
  let L : A →L[ℝ] A := ContinuousLinearMap.mul ℝ A (K x)
  have hf : ContDiffOn ℝ n f s := hJ.sub contDiffOn_const
  have hg : ContDiffOn ℝ n g s := hf.mul hK
  have hLg : ContDiffOn ℝ n (L ∘ g) s := L.contDiff.comp_contDiffOn hg
  have hres : Set.EqOn K ((fun _ => K x) - (L ∘ g)) s :=
    inverse_field_resolvent hleft hright
  have hnorm : ‖iteratedFDerivWithin ℝ n K s x‖ ≤
      ‖K x‖ * ‖iteratedFDerivWithin ℝ n g s x‖ := by
    rw [iteratedFDerivWithin_congr hres hx n,
      iteratedFDerivWithin_sub_apply contDiffWithinAt_const (hLg x hx) hs hx,
      iteratedFDerivWithin_const_of_ne (Nat.ne_of_gt hn)]
    simp only [Pi.zero_apply, zero_sub, norm_neg]
    exact (L.norm_iteratedFDerivWithin_comp_left (hg x hx) hs hx le_rfl).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℝ A (K x))
        (norm_nonneg _))
  have hsum :
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) K s x‖) =
      ∑ i ∈ Finset.Icc 1 n, (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i J s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) K s x‖ := by
    symm
    calc
      _ = ∑ i ∈ Finset.Icc 1 n, (n.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i f s x‖ *
          ‖iteratedFDerivWithin ℝ (n - i) K s x‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [iteratedFDerivWithin_sub_basepoint
          ((hJ x hx).of_le (by exact_mod_cast (Finset.mem_Icc.mp hi).2)) hs hx
          (by have := (Finset.mem_Icc.mp hi).1; omega)]
      _ = _ := by
        apply Finset.sum_subset
        · intro i hi
          exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hi).2; omega)
        · intro i hi hnot
          have hi0 : i = 0 := by
            have := Finset.mem_range.mp hi
            simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
            omega
          subst i
          simp [norm_iteratedFDerivWithin_zero, f]
  exact hnorm.trans (mul_le_mul_of_nonneg_left
    ((norm_iteratedFDerivWithin_mul_le hf hK hs hx le_rfl).trans_eq hsum)
    (norm_nonneg _))

/-- A unit-valued smooth field has a smooth inverse field on the same set. -/
theorem contDiffOn_ringInverse_field [CompleteSpace A]
    {J : X → A} {s : Set X} {n : ℕ∞ω}
    (hJ : ContDiffOn ℝ n J s) (hunit : ∀ y ∈ s, IsUnit (J y)) :
    ContDiffOn ℝ n (fun y => Ring.inverse (J y)) s := by
  intro y hy
  obtain ⟨u, hu⟩ := hunit y hy
  have hi := contDiffAt_ringInverse ℝ (n := n) u
  rw [hu] at hi
  exact hi.comp_contDiffWithinAt y (hJ y hy)

/-- The preceding recurrence for the genuine inverse in a Banach algebra. -/
theorem norm_iteratedFDerivWithin_ringInverse_le [CompleteSpace A]
    {J : X → A} {s : Set X} {x : X} {n : ℕ}
    (hJ : ContDiffOn ℝ n J s) (hunit : ∀ y ∈ s, IsUnit (J y))
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hn : 0 < n) :
    ‖iteratedFDerivWithin ℝ n (fun y => Ring.inverse (J y)) s x‖ ≤
      ‖Ring.inverse (J x)‖ * ∑ i ∈ Finset.Icc 1 n, (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i J s x‖ *
        ‖iteratedFDerivWithin ℝ (n - i) (fun y => Ring.inverse (J y)) s x‖ := by
  exact norm_iteratedFDerivWithin_inverse_field_le hJ
    (contDiffOn_ringInverse_field hJ hunit) hs hx hn
    (Ring.inverse_mul_cancel _ (hunit x hx))
    (fun y hy => Ring.mul_inverse_cancel _ (hunit y hy))

/-- The pointwise recurrence requires invertibility only at the base
point: continuity supplies an invertible neighborhood. -/
theorem norm_iteratedFDeriv_ringInverse_le [CompleteSpace A]
    {J : X → A} {x : X} {n : ℕ}
    (hJ : ContDiffAt ℝ n J x) (hunit : IsUnit (J x)) (hn : 0 < n) :
    ‖iteratedFDeriv ℝ n (fun y => Ring.inverse (J y)) x‖ ≤
      ‖Ring.inverse (J x)‖ * ∑ i ∈ Finset.Icc 1 n, (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i J x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y => Ring.inverse (J y)) x‖ := by
  obtain ⟨u, hu, hJu⟩ := hJ.contDiffOn le_rfl (by simp)
  have hv : {y | IsUnit (J y)} ∈ nhds x :=
    hJ.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hunit)
  obtain ⟨s, hsu, hs, hx⟩ := mem_nhds_iff.mp (inter_mem hu hv)
  have hJs : ContDiffOn ℝ n J s := hJu.mono (fun y hy => (hsu hy).1)
  have hus : ∀ y ∈ s, IsUnit (J y) := fun y hy => (hsu hy).2
  have h := norm_iteratedFDerivWithin_ringInverse_le hJs hus hs.uniqueDiffOn hx hn
  have heq (m : ℕ) (f : X → A) : iteratedFDerivWithin ℝ m f s x =
      iteratedFDeriv ℝ m f x := iteratedFDerivWithin_of_isOpen m hs hx
  simpa only [heq] using h

/-- Exponential and factorial scaling for the coefficient of order `m`. -/
def jetCoefficientScale (B : ℝ) (m : ℕ) : ℝ :=
  B ^ m * (m.factorial : ℝ)

theorem jetCoefficientScale_pos {B : ℝ} (hB : 0 < B) (m : ℕ) :
    0 < jetCoefficientScale B m := by
  unfold jetCoefficientScale
  positivity

@[simp] theorem jetCoefficientScale_zero (B : ℝ) : jetCoefficientScale B 0 = 1 := by
  simp [jetCoefficientScale]

/-- Binomial coefficients exactly cancel the factorial scaling; there
is no loss in the exponential base. -/
theorem choose_mul_jetCoefficientScale {B : ℝ} {m i : ℕ} (hi : i ≤ m) :
    (m.choose i : ℝ) * jetCoefficientScale B i * jetCoefficientScale B (m - i) =
      jetCoefficientScale B m := by
  have hfactorial : (m.choose i : ℝ) * (i.factorial : ℝ) *
      ((m - i).factorial : ℝ) = (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hp : B ^ i * B ^ (m - i) = B ^ m := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  unfold jetCoefficientScale
  calc
    _ = ((m.choose i : ℝ) * (i.factorial : ℝ) * ((m - i).factorial : ℝ)) *
        (B ^ i * B ^ (m - i)) := by ring
    _ = _ := by rw [hfactorial, hp]; ring

/-- A binomial inverse recurrence becomes the convolution recurrence
after division by its exact exponential-factorial scaling. -/
theorem normalized_inverse_jet_recurrence {B H : ℝ} {j k : ℕ → ℝ}
    (hB : 0 < B) (hH : 0 ≤ H) (hk : ∀ m, 0 ≤ k m)
    (hj : ∀ m, 0 < m → j m ≤ factorialMajorant m * jetCoefficientScale B m)
    (hrec : ∀ m, 0 < m → k m ≤ H * ∑ i ∈ Finset.Icc 1 m,
      (m.choose i : ℝ) * j i * k (m - i))
    {m : ℕ} (hm : 0 < m) :
    k m / jetCoefficientScale B m ≤ H * ∑ i ∈ Finset.Icc 1 m,
      factorialMajorant i * (k (m - i) / jetCoefficientScale B (m - i)) := by
  apply (div_le_iff₀ (jetCoefficientScale_pos hB m)).mpr
  calc
    _ ≤ H * ∑ i ∈ Finset.Icc 1 m, (m.choose i : ℝ) * j i * k (m - i) := hrec m hm
    _ ≤ H * ∑ i ∈ Finset.Icc 1 m, jetCoefficientScale B m *
        (factorialMajorant i * (k (m - i) / jetCoefficientScale B (m - i))) := by
      apply mul_le_mul_of_nonneg_left _ hH
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hkm : 0 ≤ k (m - i) := hk (m - i)
      calc
        _ ≤ (m.choose i : ℝ) * (factorialMajorant i * jetCoefficientScale B i) *
            k (m - i) := by
          gcongr
          exact hj i (by omega)
        _ = _ := by
          rw [← choose_mul_jetCoefficientScale (B := B) hi'.2]
          field_simp [ne_of_gt (jetCoefficientScale_pos hB (m - i))]
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The normalized inverse recurrence has the form required by the
factorial majorant, including its zeroth-order endpoint. -/
theorem normalized_inverse_jet_hasMajorant {B D : ℝ} {j k : ℕ → ℝ}
    (hB : 0 < B) (hD : 0 ≤ D) (hk : ∀ m, 0 ≤ k m)
    (hkzero : k 0 ≤ Real.sqrt D)
    (hj : ∀ m, 0 < m → j m ≤ factorialMajorant m * jetCoefficientScale B m)
    (hrec : ∀ m, 0 < m → k m ≤ Real.sqrt D * ∑ i ∈ Finset.Icc 1 m,
      (m.choose i : ℝ) * j i * k (m - i)) :
    HasInverseMajorantRecurrence factorialMajorant
      (fun m => k m / jetCoefficientScale B m) D := by
  intro m hm
  have hsplit : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hmnot : m ∉ Finset.Icc 1 (m - 1) := by simp; omega
  have h := normalized_inverse_jet_recurrence hB (Real.sqrt_nonneg D) hk hj hrec hm
  rw [hsplit, Finset.sum_insert hmnot, Nat.sub_self, jetCoefficientScale_zero, div_one] at h
  calc
    _ ≤ Real.sqrt D * (factorialMajorant m * k 0 +
        ∑ i ∈ Finset.Icc 1 (m - 1),
          factorialMajorant i * (k (m - i) / jetCoefficientScale B (m - i))) := h
    _ ≤ D * factorialMajorant m + Real.sqrt D *
        ∑ i ∈ Finset.Icc 1 (m - 1),
          factorialMajorant i * (k (m - i) / jetCoefficientScale B (m - i)) := by
      have he := mul_le_mul_of_nonneg_left hkzero
        (mul_nonneg (Real.sqrt_nonneg D) (factorialMajorant_pos m).le)
      have hsq : Real.sqrt D * factorialMajorant m * Real.sqrt D =
          D * factorialMajorant m := by
        calc
          _ = Real.sqrt D ^ 2 * factorialMajorant m := by ring
          _ = _ := by rw [Real.sq_sqrt hD]
      nlinarith

/-- Uniform inverse bounds for every order, with exactly the original
exponential base and one order-independent constant. -/
theorem inverse_jet_uniform_bound {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, Real.sqrt D ≤ C ∧ 2 * D ≤ C ∧ ∀ B : ℝ, 0 < B → ∀ j k : ℕ → ℝ,
      (∀ m, 0 ≤ k m) → k 0 ≤ Real.sqrt D →
      (∀ m, 0 < m → j m ≤ factorialMajorant m * jetCoefficientScale B m) →
      (∀ m, 0 < m → k m ≤ Real.sqrt D * ∑ i ∈ Finset.Icc 1 m,
        (m.choose i : ℝ) * j i * k (m - i)) →
      ∀ m, k m ≤ C * factorialMajorant m * jetCoefficientScale B m := by
  obtain ⟨C, hC0, hCD, hC⟩ := factorial_inverse_coefficients_uniform_bound hD
  refine ⟨C, hC0, hCD, ?_⟩
  intro B hB j k hk hkzero hj hrec m
  have ha0 : k 0 / jetCoefficientScale B 0 ≤ Real.sqrt D := by simpa using hkzero
  have hbound := hC (fun m => k m / jetCoefficientScale B m) ha0
    (normalized_inverse_jet_hasMajorant hB (zero_le_one.trans hD) hk hkzero hj hrec) m
  exact (div_le_iff₀ (jetCoefficientScale_pos hB m)).mp hbound

/-- Applying a field of operators preserves the same factorial weights.
This is the product estimate used for the coordinate increment. -/
theorem clm_apply_factorialMajorant_bound
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : X → F →L[ℝ] G} {g : X → F} {s : Set X} {x : X}
    {B C D : ℝ} {m : ℕ} (hB : 0 < B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : ContDiffOn ℝ m f s) (hg : ContDiffOn ℝ m g s)
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s)
    (hfbound : ∀ i, i ≤ m → ‖iteratedFDerivWithin ℝ i f s x‖ ≤
      C * factorialMajorant i * jetCoefficientScale B i)
    (hgbound : ∀ i, i ≤ m → ‖iteratedFDerivWithin ℝ i g s x‖ ≤
      D * factorialMajorant i * jetCoefficientScale B i) :
    ‖iteratedFDerivWithin ℝ m (fun y => f y (g y)) s x‖ ≤
      (10 * C * D) * factorialMajorant m * jetCoefficientScale B m := by
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i f s x‖ *
        ‖iteratedFDerivWithin ℝ (m - i) g s x‖ :=
      norm_iteratedFDerivWithin_clm_apply hf hg hs hx le_rfl
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        (C * D * jetCoefficientScale B m) *
          (factorialMajorant i * factorialMajorant (m - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
      calc
        _ ≤ (m.choose i : ℝ) *
            (C * factorialMajorant i * jetCoefficientScale B i) *
            (D * factorialMajorant (m - i) * jetCoefficientScale B (m - i)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hfbound i hi') (Nat.cast_nonneg _)
          · exact hgbound (m - i) (Nat.sub_le _ _)
          · exact norm_nonneg _
          · exact mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (mul_nonneg hC (factorialMajorant_pos i).le)
                (jetCoefficientScale_pos hB i).le)
        _ = _ := by rw [← choose_mul_jetCoefficientScale (B := B) hi']; ring
    _ = (C * D * jetCoefficientScale B m) *
        ∑ i ∈ Finset.range (m + 1), factorialMajorant i * factorialMajorant (m - i) := by
      rw [Finset.mul_sum]
    _ ≤ (C * D * jetCoefficientScale B m) * (10 * factorialMajorant m) :=
      mul_le_mul_of_nonneg_left (factorialMajorant_full_convolution_le m)
        (mul_nonneg (mul_nonneg hC hD) (jetCoefficientScale_pos hB m).le)
    _ = _ := by ring

/-- Actual higher derivatives of the inverse of a unit-valued Banach
algebra field satisfy the factorial majorant without changing `B`.
The same constant works for every field, set, and base point. -/
theorem ringInverse_iteratedFDerivWithin_uniform_bound [CompleteSpace A]
    {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, Real.sqrt D ≤ C ∧ 2 * D ≤ C ∧
      ∀ (B : ℝ), 0 < B → ∀ (J : X → A) (s : Set X) (x : X),
      (∀ m : ℕ, ContDiffOn ℝ m J s) → (∀ y ∈ s, IsUnit (J y)) →
      UniqueDiffOn ℝ s → x ∈ s → ‖Ring.inverse (J x)‖ ≤ Real.sqrt D →
      (∀ m, 0 < m → ‖iteratedFDerivWithin ℝ m J s x‖ ≤
        factorialMajorant m * jetCoefficientScale B m) →
      ∀ m, ‖iteratedFDerivWithin ℝ m (fun y => Ring.inverse (J y)) s x‖ ≤
        C * factorialMajorant m * jetCoefficientScale B m := by
  obtain ⟨C, hC0, hCD, hC⟩ := inverse_jet_uniform_bound hD
  refine ⟨C, hC0, hCD, ?_⟩
  intro B hB J s x hJ hunit hs hx hInv hbound
  apply hC B hB (fun m => ‖iteratedFDerivWithin ℝ m J s x‖)
    (fun m => ‖iteratedFDerivWithin ℝ m (fun y => Ring.inverse (J y)) s x‖)
  · exact fun _ => norm_nonneg _
  · simpa only [norm_iteratedFDerivWithin_zero] using hInv
  · exact hbound
  · intro m hm
    apply (norm_iteratedFDerivWithin_ringInverse_le (hJ m) hunit hs hx hm).trans
    apply mul_le_mul_of_nonneg_right hInv
    apply Finset.sum_nonneg
    intro i _
    positivity

/-- Pointwise form of the manuscript's inverse majorant: only smoothness
and invertibility at the point are assumed, and the constant is uniform
in both the order and the exponential base. -/
theorem ringInverse_iteratedFDeriv_uniform_bound [CompleteSpace A]
    {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, Real.sqrt D ≤ C ∧ 2 * D ≤ C ∧
      ∀ (B : ℝ), 0 < B → ∀ (J : X → A) (x : X),
      (∀ m : ℕ, ContDiffAt ℝ m J x) → IsUnit (J x) →
      ‖Ring.inverse (J x)‖ ≤ Real.sqrt D →
      (∀ m, 0 < m → ‖iteratedFDeriv ℝ m J x‖ ≤
        factorialMajorant m * jetCoefficientScale B m) →
      ∀ m, ‖iteratedFDeriv ℝ m (fun y => Ring.inverse (J y)) x‖ ≤
        C * factorialMajorant m * jetCoefficientScale B m := by
  obtain ⟨C, hC0, hCD, hC⟩ := inverse_jet_uniform_bound hD
  refine ⟨C, hC0, hCD, ?_⟩
  intro B hB J x hJ hunit hInv hbound
  apply hC B hB (fun m => ‖iteratedFDeriv ℝ m J x‖)
    (fun m => ‖iteratedFDeriv ℝ m (fun y => Ring.inverse (J y)) x‖)
  · exact fun _ => norm_nonneg _
  · simpa only [norm_iteratedFDeriv_zero] using hInv
  · exact hbound
  · intro m hm
    apply (norm_iteratedFDeriv_ringInverse_le (hJ m) hunit hm).trans
    apply mul_le_mul_of_nonneg_right hInv
    apply Finset.sum_nonneg
    intro i _
    positivity

section InverseTranspose

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Taking the transpose preserves every iterated derivative norm. -/
theorem norm_iteratedFDerivWithin_inverseTranspose
    (J : X → E →L[ℝ] E) {s : Set X} {x : X}
    (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (m : ℕ) :
    ‖iteratedFDerivWithin ℝ m (fun y => operatorInverseTranspose (J y)) s x‖ =
      ‖iteratedFDerivWithin ℝ m (fun y => Ring.inverse (J y)) s x‖ := by
  let adj : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E) := ContinuousLinearMap.adjoint
  exact adj.norm_iteratedFDerivWithin_comp_left (fun y => Ring.inverse (J y)) hs hx m

theorem norm_iteratedFDeriv_inverseTranspose
    (J : X → E →L[ℝ] E) (x : X) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => operatorInverseTranspose (J y)) x‖ =
      ‖iteratedFDeriv ℝ m (fun y => Ring.inverse (J y)) x‖ := by
  let adj : (E →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] E) := ContinuousLinearMap.adjoint
  exact adj.norm_iteratedFDeriv_comp_left (fun y => Ring.inverse (J y)) x m

/-- The all-order inverse-transpose estimate uses the same constant and
the same exponential base as the inverse estimate. -/
theorem inverseTranspose_iteratedFDerivWithin_uniform_bound
    {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, Real.sqrt D ≤ C ∧ 2 * D ≤ C ∧
      ∀ (B : ℝ), 0 < B → ∀ (J : X → E →L[ℝ] E) (s : Set X) (x : X),
      (∀ m : ℕ, ContDiffOn ℝ m J s) → (∀ y ∈ s, IsUnit (J y)) →
      UniqueDiffOn ℝ s → x ∈ s → ‖Ring.inverse (J x)‖ ≤ Real.sqrt D →
      (∀ m, 0 < m → ‖iteratedFDerivWithin ℝ m J s x‖ ≤
        factorialMajorant m * jetCoefficientScale B m) →
      ∀ m, ‖iteratedFDerivWithin ℝ m (fun y => operatorInverseTranspose (J y)) s x‖ ≤
        C * factorialMajorant m * jetCoefficientScale B m := by
  obtain ⟨C, hC0, hCD, hC⟩ :=
    ringInverse_iteratedFDerivWithin_uniform_bound (X := X) (A := E →L[ℝ] E) hD
  refine ⟨C, hC0, hCD, ?_⟩
  intro B hB J s x hJ hunit hs hx hInv hbound m
  rw [norm_iteratedFDerivWithin_inverseTranspose J hs hx m]
  exact hC B hB J s x hJ hunit hs hx hInv hbound m

/-- Pointwise inverse-transpose majorant, with the same constant as the
inverse and no loss of exponential base. -/
theorem inverseTranspose_iteratedFDeriv_uniform_bound
    {D : ℝ} (hD : 1 ≤ D) :
    ∃ C : ℝ, Real.sqrt D ≤ C ∧ 2 * D ≤ C ∧
      ∀ (B : ℝ), 0 < B → ∀ (J : X → E →L[ℝ] E) (x : X),
      (∀ m : ℕ, ContDiffAt ℝ m J x) → IsUnit (J x) →
      ‖Ring.inverse (J x)‖ ≤ Real.sqrt D →
      (∀ m, 0 < m → ‖iteratedFDeriv ℝ m J x‖ ≤
        factorialMajorant m * jetCoefficientScale B m) →
      ∀ m, ‖iteratedFDeriv ℝ m (fun y => operatorInverseTranspose (J y)) x‖ ≤
        C * factorialMajorant m * jetCoefficientScale B m := by
  obtain ⟨C, hC0, hCD, hC⟩ :=
    ringInverse_iteratedFDeriv_uniform_bound (X := X) (A := E →L[ℝ] E) hD
  refine ⟨C, hC0, hCD, ?_⟩
  intro B hB J x hJ hunit hInv hbound m
  rw [norm_iteratedFDeriv_inverseTranspose J x m]
  exact hC B hB J x hJ hunit hInv hbound m

end InverseTranspose

end RegularPointCoordinates

end

end OAI
