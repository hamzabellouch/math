import OAI.Algebra.OddKaplansky.HeisenbergSector

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9

section

noncomputable section
open scoped Classical BigOperators
namespace OddKaplansky.MatrixBlock
variable {S : Type portUniverse1} {R : Type portUniverse2} {m : Type portUniverse3} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def block (X : Matrix m m S) : R := ∑ i, ∑ j, f (X i j) * q i j

lemma block_zero : block f q 0 = 0 := by simp [block]
lemma block_add (X Y : Matrix m m S) : block f q (X + Y) = block f q X + block f q Y := by
  simp [block, add_mul, Finset.sum_add_distrib]
lemma block_sub (X Y : Matrix m m S) : block f q (X - Y) = block f q X - block f q Y := by
  simp [block, sub_mul, Finset.sum_sub_distrib]
lemma block_one : block f q 1 = ∑ i, q i i := by
  simp [block, Matrix.one_apply, apply_ite]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))
include hqq hcomm

lemma block_mul (X Y : Matrix m m S) : block f q (X * Y) = block f q X * block f q Y := by
  have hterm (i j k r : m) :
      (f (X i j) * q i j) * (f (Y k r) * q k r) =
        if j = k then f (X i j * Y k r) * q i r else 0 := by
    calc
      _ = f (X i j * Y k r) * (q i j * q k r) := by
        rw [map_mul, ← mul_assoc, mul_assoc (f (X i j)),
          (hcomm (Y k r) i j).eq.symm]
        simp only [mul_assoc]
      _ = _ := by rw [hqq]; split_ifs <;> simp
  have hmulij (i j : m) : (f (X i j) * q i j) * block f q Y =
      ∑ r, f (X i j * Y j r) * q i r := by
    simp only [block, Finset.mul_sum, hterm]
    rw [Finset.sum_comm]
    simp
  symm
  calc
    block f q X * block f q Y = ∑ i, ∑ j, (f (X i j) * q i j) * block f q Y := by
      change (∑ i, ∑ j, f (X i j) * q i j) * block f q Y = _
      simp only [Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ r, f (X i j * Y j r) * q i r := by simp_rw [hmulij]
    _ = block f q (X * Y) := by
      simp only [block, Matrix.mul_apply, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm

lemma block_sandwich (X : Matrix m m S) (i j : m) :
    q i i * block f q X * q j j = f (X i j) * q i j := by
  have hterm (k r : m) : q i i * (f (X k r) * q k r) * q j j =
      if i = k then if r = j then f (X k r) * q i j else 0 else 0 := by
    calc
      _ = f (X k r) * (q i i * q k r * q j j) := by
        rw [← mul_assoc, (hcomm (X k r) i i).eq.symm]
        simp only [mul_assoc]
      _ = _ := by
        by_cases hik : i = k <;> by_cases hrj : r = j <;>
          simp [hqq, hik, hrj]

  simp only [block, Finset.mul_sum, Finset.sum_mul, hterm]
  simp

lemma block_injective (hpure : ∀ x i j, f x * q i j = 0 → x = 0) :
    Function.Injective (block f q) := by
  intro X Y h
  have hz : block f q (X - Y) = 0 := by rw [block_sub, h, sub_self]
  have hXY : X - Y = 0 := by
    ext i j
    apply hpure _ i j
    rw [← block_sandwich f q hqq hcomm, hz, mul_zero, zero_mul]
  exact sub_eq_zero.mp hXY

theorem scalar_witnesses
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    ∃ a' b' : R, a' * b' = 1 ∧ b' * a' ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  refine ⟨a',b',?_,?_⟩
  · dsimp [a',b']
    noncomm_ring [he, hea, hae, heb, hbe, hab']
  · intro h
    have h' : block f q b * block f q a = e := by
      apply add_left_cancel (a := 1 - e)
      calc
        1 - e + block f q b * block f q a =
            (1 - e + block f q b) * (1 - e + block f q a) := by
          noncomm_ring [he, hea, hae, heb, hbe]
        _ = 1 := h
        _ = 1 - e + e := by abel
    apply hba
    apply block_injective f q hqq hcomm hpure
    rw [block_mul f q hqq hcomm]
    exact h'

end OddKaplansky.MatrixBlock
namespace OddKaplansky.ProductAlgebras
variable {K : Type portUniverse4} {G : Type portUniverse5} {H : Type portUniverse6} [Field K] [Group G] [Group H]

def leftMap : MonoidAlgebra K G →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inl G H)
def rightMap : MonoidAlgebra K H →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inr G H)

lemma left_right_commute (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) :
    Commute (leftMap x) (rightMap y) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      change _ * _ = _ * _
      simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
    | add y z hy hz => simpa only [map_add] using hy.add_right hz
    | smul c y hy => simpa only [map_smul] using hy.smul_right c
  | add x z hx hz => simpa only [map_add] using hx.add_left hz
  | smul c x hx => simpa only [map_smul] using hx.smul_left c

lemma product_coeff (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) (g : G) (h : H) :
    (leftMap x * rightMap y).coeff (g,h) = x.coeff g * y.coeff h := by
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    induction y using MonoidAlgebra.induction_on with
    | of b =>
      by_cases hag : a = g <;> by_cases hbh : b = h <;>
        simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          hag, hbh, Prod.ext_iff]
    | add y z hy hz =>
      simp only [map_add, mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hy, hz]
    | smul c y hy =>
      simp only [map_smul, mul_smul_comm, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        smul_eq_mul, hy]
      ring
  | add x z hx hz =>
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hz]
  | smul c x hx =>
    simp only [map_smul, smul_mul_assoc, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, hx]
    ring

lemma product_ne_zero {x : MonoidAlgebra K G} {y : MonoidAlgebra K H}
    (hx : x ≠ 0) (hy : y ≠ 0) : leftMap x * rightMap y ≠ 0 := by
  obtain ⟨g,hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra! h
    apply hx
    ext g
    exact h g
  obtain ⟨h,hh⟩ : ∃ h, y.coeff h ≠ 0 := by
    by_contra! h
    apply hy
    ext a
    exact h a
  intro he
  have he' := congrArg (fun z : MonoidAlgebra K (G × H) => z.coeff (g,h)) he
  rw [product_coeff] at he'
  exact mul_ne_zero hg hh he'

end OddKaplansky.ProductAlgebras
namespace OddKaplansky.MatrixBlock
variable {S : Type portUniverse7} {R : Type portUniverse8} {m : Type portUniverse9} [Ring S] [Ring R] [Fintype m]
variable (f : S →+* R) (q : m → m → R)

def output (X : Matrix m m S) : R := 1 - block f q 1 + block f q X

lemma output_formula (X : Matrix m m S) :
    output f q X = 1 - ∑ i, q i i + ∑ i, ∑ j, f (X i j)*q i j := by
  rw [output,block_one,block]

variable (hqq : ∀ i j k r, q i j * q k r = if j = k then q i r else 0)
variable (hcomm : ∀ x i j, Commute (f x) (q i j))

include hqq hcomm in
theorem prescribed_scalar_products
    (hpure : ∀ x i j, f x * q i j = 0 → x = 0)
    (a b : Matrix m m S) (hab : a * b = 1) (hba : b * a ≠ 1) :
    output f q a * output f q b = 1 ∧ output f q b * output f q a ≠ 1 := by
  let e := block f q 1
  let a' := 1 - e + block f q a
  let b' := 1 - e + block f q b
  have he : e * e = e := by rw [← block_mul f q hqq hcomm, mul_one]
  have hea : e * block f q a = block f q a := by rw [← block_mul f q hqq hcomm, one_mul]
  have hae : block f q a * e = block f q a := by rw [← block_mul f q hqq hcomm, mul_one]
  have heb : e * block f q b = block f q b := by rw [← block_mul f q hqq hcomm, one_mul]
  have hbe : block f q b * e = block f q b := by rw [← block_mul f q hqq hcomm, mul_one]
  have hab' : block f q a * block f q b = e := by rw [← block_mul f q hqq hcomm, hab]
  change a' * b' = 1 ∧ b' * a' ≠ 1
  refine ⟨?_,?_⟩
  · dsimp [a',b']
    noncomm_ring [he, hea, hae, heb, hbe, hab']
  · intro h
    have h' : block f q b * block f q a = e := by
      apply add_left_cancel (a := 1 - e)
      calc
        1 - e + block f q b * block f q a =
            (1 - e + block f q b) * (1 - e + block f q a) := by
          noncomm_ring [he, hea, hae, heb, hbe]
        _ = 1 := h
        _ = 1 - e + e := by abel
    apply hba
    apply block_injective f q hqq hcomm hpure
    rw [block_mul f q hqq hcomm]
    exact h'

end OddKaplansky.MatrixBlock
end

end

end OAI
