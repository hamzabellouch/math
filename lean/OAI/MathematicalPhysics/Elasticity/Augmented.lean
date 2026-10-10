import Mathlib

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

abbrev X := EuclideanSpace ℝ (Fin 3)
def e (i : Fin 3) : X := EuclideanSpace.single i 1

def smoothAlgebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.mul hg
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : X => (0 : ℂ))
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : X => (1 : ℂ))
    exact contDiff_const
  algebraMap_mem' a := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : X => a)
    exact contDiff_const

abbrev Smooth := smoothAlgebra

lemma smooth_coe (f : Smooth) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) := f.property

/-- Actual coordinate derivative, as a derivation of the smooth function algebra. -/
def coord (i : Fin 3) : Derivation ℂ Smooth Smooth := Derivation.mk'
  { toFun := fun f => ⟨fun x => fderiv ℝ (f : X → ℂ) x (e i),
        by
          change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ (f : X → ℂ) x (e i))
          exact ((smooth_coe f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext x
      exact congrArg (fun L : X →L[ℝ] ℂ => L (e i))
        (fderiv_add ((smooth_coe f).differentiable (by simp) x)
          ((smooth_coe g).differentiable (by simp) x))
    map_smul' := by
      intro a f
      apply Subtype.ext
      funext x
      exact congrArg (fun L : X →L[ℝ] ℂ => L (e i))
        (fderiv_const_smul ((smooth_coe f).differentiable (by simp) x) a) }
  (by
    intro f g
    apply Subtype.ext
    funext x
    exact congrArg (fun L : X →L[ℝ] ℂ => L (e i))
      (fderiv_mul ((smooth_coe f).differentiable (by simp) x)
        ((smooth_coe g).differentiable (by simp) x)))

lemma coord_apply (i : Fin 3) (f : Smooth) (x : X) :
    (coord i f : X → ℂ) x = fderiv ℝ (f : X → ℂ) x (e i) := rfl

lemma coord_coord (f : Smooth) (i j : Fin 3) (x : X) :
    (coord i (coord j f) : X → ℂ) x = fderiv ℝ (fderiv ℝ (f : X → ℂ)) x (e i) (e j) := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℂ)) :=
    ((smooth_coe f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℂ) y (e j)) x (e i) = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (e j))]
  simp

lemma coord_commute (i j : Fin 3) (f : Smooth) : coord i (coord j f) = coord j (coord i f) := by
  apply Subtype.ext
  funext x
  rw [coord_coord, coord_coord]
  exact (smooth_coe f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

def lap (f : A) : A := ∑ i, D i (D i f)
def div (u : ι → A) : A := ∑ i, D i (u i)
def cm (m : A) (u : ι → A) (i : ι) : A :=
  ∑ j, D j m * (D j (u i) + D i (u j))
def R (lam m : A) (u : ι → A) (d : A) (i : ι) : A :=
  m * lap D (u i) + (lam+m)*D i d + cm D m u i + D i lam*d
def S (lam m : A) (u : ι → A) (d : A) : A :=
  (lam+m+m)*lap D d + 2*(∑ i, D i (lam+m)*D i d) +
  2*(∑ i, D i m*lap D (u i)) +
  2*(∑ i, ∑ j, D i (D j m)*D i (u j)) + lap D lam*d
def P (m : A) (f : A) : A := m*lap D f + ∑ i, D i m*D i f

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
include hD

lemma partial_lap (i : ι) (f : A) : D i (lap D f) = lap D (D i f) := by
  simp only [lap, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hD i j, hD i j]

lemma div_lap (u : ι → A) : div D (fun i => lap D (u i)) = lap D (div D u) := by
  simp only [div, lap, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hD i j, hD i j]

lemma div_cm (m : A) (u : ι → A) :
    div D (cm D m u) =
    2*(∑ i, ∑ j, D i (D j m)*D i (u j)) +
      (∑ i, D i m*D i (div D u)) + (∑ i, D i m*lap D (u i)) := by
  have hH : (∑ i, ∑ j, D i (D j m)*D j (u i)) =
      ∑ i, ∑ j, D i (D j m)*D i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hD j i]
  have hv : (∑ i, ∑ j, D j m * D i (D j (u i))) =
      ∑ j, D j m*D j (div D u) := by
    rw [Finset.sum_comm]
    simp only [div, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hD i j]
  have hl : (∑ i, ∑ j, D j m * D i (D i (u j))) =
      ∑ j, D j m*lap D (u j) := by
    rw [Finset.sum_comm]
    simp only [lap, Finset.mul_sum]
  simp only [div, cm, map_sum, partial_mul, map_add, mul_add, Finset.sum_add_distrib]
  rw [hH, hv, hl]
  simp only [div, map_sum]
  ring

/-- The independent scalar compatibility identity, before imposing d=div u. -/
theorem augmented_identity (lam m : A) (u : ι → A) (d : A) :
    div D (R D lam m u d) - S D lam m u d = P D m (div D u-d) := by
  have hL := div_lap D hD u
  have hC := div_cm D hD m u
  simp only [div] at hL hC
  simp only [div, R, map_add, partial_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hL, hC]
  simp only [S, P, lap, map_sub, map_add, map_sum, mul_sub, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

end DifferentialAlgebra

/-- No commuting-derivation hypothesis remains for actual smooth functions. -/
theorem smooth_augmented_identity (lam m : Smooth) (u : Fin 3 → Smooth) (d : Smooth) :
    div coord (R coord lam m u d) - S coord lam m u d = P coord m (div coord u-d) :=
  augmented_identity coord coord_commute lam m u d

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

def lapT (f : A) : A := ∑ i, T i (T i f)
def divT (u : ι → A) : A := ∑ i, T i (u i)
def cmT (m : A) (u : ι → A) (i : ι) : A :=
  ∑ j, D j m * (T j (u i) + T i (u j))
def RT (lam m : A) (u : ι → A) (d : A) (i : ι) : A :=
  m * lapT T (u i) + (lam+m)*T i d + cmT D T m u i + D i lam*d
def ST (lam m : A) (u : ι → A) (d : A) : A :=
  (lam+m+m)*lapT T d + 2*(∑ i, D i (lam+m)*T i d) +
  2*(∑ i, D i m*lapT T (u i)) +
  2*(∑ i, ∑ j, D i (D j m)*T i (u j)) + lap D lam*d
def PT (m : A) (f : A) : A := m*lapT T f + ∑ i, D i m*T i f

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

include hT in
lemma covariant_div_lap (u : ι → A) : divT T (fun i => lapT T (u i)) = lapT T (divT T u) := by
  simp only [divT, lapT, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hT i j, hT i j]

include hD hT hTD in
lemma covariant_div_cm (m : A) (u : ι → A) :
    divT T (cmT D T m u) =
    2*(∑ i, ∑ j, D i (D j m)*T i (u j)) +
      (∑ i, D i m*T i (divT T u)) + (∑ i, D i m*lapT T (u i)) := by
  have hH : (∑ i, ∑ j, D i (D j m)*T j (u i)) =
      ∑ i, ∑ j, D i (D j m)*T i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hD j i]
  have hv : (∑ i, ∑ j, D j m * T i (T j (u i))) =
      ∑ j, D j m*T j (divT T u) := by
    rw [Finset.sum_comm]
    simp only [divT, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [hT i j]
  have hl : (∑ i, ∑ j, D j m * T i (T i (u j))) =
      ∑ j, D j m*lapT T (u j) := by
    rw [Finset.sum_comm]
    simp only [lapT, Finset.mul_sum]
  simp only [divT, cmT, map_sum, hTD, map_add, mul_add, Finset.sum_add_distrib]
  rw [hH, hv, hl]
  simp only [divT, map_sum]
  ring

include hD hT hTD in
/-- Compatibility after conjugation, proved for the genuine connection
Leibniz rule rather than falsely treating a shifted derivative as a derivation. -/
theorem covariant_augmented_identity (lam m : A) (u : ι → A) (d : A) :
    divT T (RT D T lam m u d) - ST D T lam m u d = PT D T m (divT T u-d) := by
  have hL := covariant_div_lap T hT u
  have hC := covariant_div_cm D T hD hT hTD m u
  simp only [divT] at hL hC
  simp only [divT, RT, map_add, hTD, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hL, hC]
  simp only [ST, PT, lap, lapT, map_sub, map_add, map_sum, mul_sub, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  ring_nf
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The physical stress-divergence, using the conjugated coordinate derivative. -/
def LT (lam m : A) (u : ι → A) (i : ι) : A :=
  T i (lam * divT T u) + ∑ j, T j (m*(T j (u i)+T i (u j)))

include hT hTD in
lemma physical_conjugated_expansion (lam m : A) (u : ι → A) (i : ι) :
    LT T lam m u i = RT D T lam m u (divT T u) i := by
  have ht : (∑ j, T j (T i (u j))) = T i (divT T u) := by
    simp only [divT, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
  simp only [LT, RT, hTD, map_add, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ht]
  simp only [cmT, lapT, mul_add, Finset.sum_add_distrib]
  ring

/-- A complex constant phase shifts an actual coordinate derivative. -/
def shifted (z : ι → ℂ) (i : ι) : A →ₗ[ℂ] A :=
  (D i).toLinearMap + z i • LinearMap.id

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

omit [Fintype ι] in
lemma shifted_mul (z : ι → ℂ) (i : ι) (a b : A) :
    shifted D z i (a*b) = D i a*b+a*shifted D z i b := by
  simp only [shifted_apply, partial_mul, Algebra.smul_def]
  ring

include hD in
omit [Fintype ι] in
lemma shifted_commute (z : ι → ℂ) (i j : ι) (f : A) :
    shifted D z i (shifted D z j f) = shifted D z j (shifted D z i f) := by
  simp only [shifted_apply, map_add, map_smul, smul_add, smul_smul, hD i j]
  simp only [Algebra.smul_def]
  ring_nf

theorem shifted_physical_expansion (z : ι → ℂ) (lam m : A) (u : ι → A)
    (hc : ∀ i j f, D i (D j f) = D j (D i f)) (i : ι) :
    LT (shifted D z) lam m u i = RT D (shifted D z) lam m u (divT (shifted D z) u) i :=
  physical_conjugated_expansion D (shifted D z) (shifted_commute D hc z) (shifted_mul D z) lam m u i

theorem shifted_physical_divergence (z : ι → ℂ) (lam m : A) (u : ι → A)
    (hc : ∀ i j f, D i (D j f) = D j (D i f)) :
    divT (shifted D z) (LT (shifted D z) lam m u) =
      ST D (shifted D z) lam m u (divT (shifted D z) u) := by
  have he := covariant_augmented_identity D (shifted D z) hc (shifted_commute D hc z)
    (shifted_mul D z) lam m u (divT (shifted D z) u)
  rw [sub_self] at he
  simp only [PT, lapT, map_zero, mul_zero, Finset.sum_const_zero, add_zero] at he
  rw [← sub_eq_zero]
  convert he using 1
  congr 2
  funext i
  exact shifted_physical_expansion D z lam m u hc i

end CovariantAlgebra

variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

lemma grad_cm (m : A) (u : ι → A) :
    (∑ i, D i m*cmT D T m u i) =
      2*(∑ i, ∑ j, D i m*D j m*T i (u j)) := by
  have hs : (∑ i, ∑ j, D i m*D j m*T j (u i)) =
      ∑ i, ∑ j, D i m*D j m*T i (u j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [cmT, Finset.mul_sum, mul_add, ← mul_assoc, Finset.sum_add_distrib]
  rw [hs]
  ring_nf
  simp only [← Finset.sum_mul]

lemma grad_RT (lam m : A) (u : ι → A) (d : A) :
    (∑ i, D i m*RT D T lam m u d i) =
      m*(∑ i, D i m*lapT T (u i)) +
      (lam+m)*(∑ i, D i m*T i d) +
      2*(∑ i, ∑ j, D i m*D j m*T i (u j)) +
      (∑ i, D i m*D i lam)*d := by
  have hc := grad_cm D T m u
  simp only [RT, mul_add, Finset.sum_add_distrib]
  rw [hc]
  simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

lemma normalized_vector (lam m n : A) (hn : n*m=1) (u : ι → A) (d : A) (i : ι) :
    n*RT D T lam m u d i = lapT T (u i) + ((lam+m)*n)*T i d +
      (∑ j, ((n*D j m)*T j (u i) + (n*D j m)*T i (u j))) +
      (n*D i lam)*d := by
  simp only [RT, cmT, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [← mul_assoc]
  linear_combination lapT T (u i)*hn

lemma normalized_scalar_numerator (lam m n : A) (hn : n*m=1)
    (u : ι → A) (d : A) :
    ST D T lam m u d - 2*n*(∑ i, D i m*RT D T lam m u d i) =
      (lam+m+m)*lapT T d +
      2*(∑ i, (D i (lam+m)-(lam+m)*n*D i m)*T i d) +
      2*(∑ i, ∑ j, (D i (D j m)-2*n*D i m*D j m)*T i (u j)) +
      (lap D lam-2*n*(∑ i, D i m*D i lam))*d := by
  rw [grad_RT]
  simp only [ST, sub_mul, Finset.sum_sub_distrib]
  simp only [mul_assoc, ← Finset.mul_sum]
  linear_combination -2*(∑ i, D i m*lapT T (u i))*hn

lemma normalized_scalar (lam m n o : A) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (u : ι → A) (d : A) :
    o*(ST D T lam m u d - 2*n*(∑ i, D i m*RT D T lam m u d i)) =
      lapT T d +
      (∑ i, (2*o*(D i (lam+m)-(lam+m)*n*D i m))*T i d) +
      (∑ i, ∑ j, (2*o*(D i (D j m)-2*n*D i m*D j m))*T i (u j)) +
      (o*(lap D lam-2*n*(∑ i, D i m*D i lam)))*d := by
  rw [normalized_scalar_numerator D T lam m n hn]
  simp only [mul_add, Finset.mul_sum, ← mul_assoc, ho, one_mul]
  ring_nf

end ElasticityAugmented

end

end OAI
