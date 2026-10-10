import OAI.Algebra.FormulaHitting.ScaledDerivatives
import OAI.Algebra.FormulaHitting.WronskianBound
import OAI.Algebra.FormulaHitting.MinorFactor
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Polynomial Matrix Submodule

variable {F : Type*} [Field F] [CharZero F]

def derivativeMatrix {I : Type*} (k : ℕ) (h : I → PowerSeries F) :
    Matrix (Fin k) I (PowerSeries F) := fun j t => derivativeIter j.val (h t)

omit [CharZero F] in
theorem derivativeMatrix_combination {I J : Type*} [Fintype I]
    (k : ℕ) (h : I → PowerSeries F) (C : Matrix I J F) :
    derivativeMatrix k (fun l => ∑ t : I, C t l • h t) =
      derivativeMatrix k h * C.map PowerSeries.C := by
  classical
  funext j l
  change derivativeIter j.val (∑ t : I, C t l • h t) =
    ∑ t : I, derivativeIter j.val (h t) * PowerSeries.C (C t l)
  rw [derivativeIter_sum]
  simp only [derivativeIter_smul]
  simp only [PowerSeries.smul_eq_C_mul]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

omit [CharZero F] in
theorem order_le_natDegree_of_dvd (f : PowerSeries F) (p : F[X])
    (hp : p ≠ 0) (h : f ∣ (p : PowerSeries F)) : f.order.toNat ≤ p.natDegree := by
  by_contra hn
  have hd : PowerSeries.X^f.order.toNat ∣ (p : PowerSeries F) :=
    PowerSeries.X_pow_order_dvd.trans h
  have hz := (PowerSeries.X_pow_dvd_iff.mp hd) p.natDegree (by omega)
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp) (by simpa using hz)

theorem sum_fin_eq_choose (k : ℕ) : (∑ j : Fin k, j.val) = k.choose 2 := by
  calc
    (∑ j : Fin k, j.val) = ∑ j ∈ Finset.range k, j :=
      Fin.sum_univ_eq_sum_range (fun j => j) k
    _ = k.choose 2 := by rw [Finset.sum_range_id, Nat.choose_two_right]

variable {I : Type*} [Fintype I] [DecidableEq I]

def systemScalarOutput (u v : I → F) (G : Matrix I I (PowerSeries F)) :
    PowerSeries F := ∑ l : I, (∑ t : I, PowerSeries.C (u t) * G t l) * PowerSeries.C (v l)

theorem system_multiplicity (n : ℕ) (hn : 0 < n)
    (q : F[X]) (P : Matrix I I F[X]) (u v : I → F)
    (G : Matrix I I (PowerSeries F))
    (hq : q.natDegree ≤ n) (hqn : q ≠ 0)
    (hP : ∀ t l, (P t l).natDegree ≤ n-1) (hG : IsUnit G)
    (hD : ∀ t l, (q : PowerSeries F) * PowerSeries.derivative (R := F) (G t l) =
      ∑ a : I, (P t a : PowerSeries F) * G a l)
    (hy : systemScalarOutput u v G ≠ 0) :
    (systemScalarOutput u v G).order.toNat <
      (n-1) * (Fintype.card I).choose 2 + Fintype.card I := by
  classical
  let h : I → PowerSeries F := fun l => ∑ t : I, PowerSeries.C (u t) * G t l
  let V := Submodule.span F (Set.range h)
  let : FiniteDimensional F V := FiniteDimensional.span_of_finite F (Set.finite_range h)
  obtain ⟨k, b, a, hbi, hspan, ha, hlead, hzero⟩ := hasOrderBasis V
  have hbn : wronskian b ≠ 0 := (wronskian_order_sum b a ha hlead hzero).1
  have hk : k ≤ Fintype.card I := by
    have hkdim : Module.finrank F (Submodule.span F (Set.range b)) = k := by
      simpa using finrank_span_eq_card hbi
    rw [hspan] at hkdim
    rw [← hkdim]
    exact finrank_range_le_card h
  have hhmem : ∀ l, h l ∈ Submodule.span F (Set.range b) := by
    intro l
    rw [hspan]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hbmem : ∀ l, b l ∈ Submodule.span F (Set.range h) := by
    intro l
    change b l ∈ V
    rw [← hspan]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hc : ∀ l : I, ∃ c : Fin k → F, ∑ j : Fin k, c j • b j = h l := by
    intro l
    exact (Submodule.mem_span_range_iff_exists_fun F).mp (hhmem l)
  have he : ∀ l : Fin k, ∃ c : I → F, ∑ j : I, c j • h j = b l := by
    intro l
    exact (Submodule.mem_span_range_iff_exists_fun F).mp (hbmem l)
  choose c hc using hc
  choose e he using he
  let H := derivativeMatrix k h
  let W := wronskianMatrix b
  let C : Matrix (Fin k) I (PowerSeries F) :=
    fun j l => PowerSeries.C (c l j)
  let E : Matrix I (Fin k) (PowerSeries F) :=
    fun j l => PowerSeries.C (e l j)
  let D : Matrix (Fin k) (Fin k) (PowerSeries F) :=
    Matrix.diagonal (fun j => (q : PowerSeries F)^j.val)
  let Zp : Matrix (Fin k) I F[X] := fun j t => numeratorRow q P u j.val t
  let Z : Matrix (Fin k) I (PowerSeries F) :=
    fun j t => (Zp j t : PowerSeries F)
  have hHC : H = W * C := by
    funext j l
    change derivativeIter j.val (h l) =
      ∑ t : Fin k, derivativeIter j.val (b t) * PowerSeries.C (c l t)
    rw [← hc l, derivativeIter_sum]
    simp only [derivativeIter_smul]
    simp only [PowerSeries.smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro t _
    exact mul_comm _ _
  have hHE : W = H * E := by
    funext j l
    change derivativeIter j.val (b l) =
      ∑ t : I, derivativeIter j.val (h t) * PowerSeries.C (e l t)
    rw [← he l, derivativeIter_sum]
    simp only [derivativeIter_smul]
    simp only [PowerSeries.smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro t _
    exact mul_comm _ _
  have hZG : Z * G = D * H := by
    funext j l
    rw [Matrix.diagonal_mul]
    exact (scaled_derivative_row q P u G hD j.val l).symm
  have hDn : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact pow_ne_zero _ (Polynomial.coe_eq_zero_iff.not.mpr hqn)
  obtain ⟨f, hfn, hdiv⟩ := exists_nonzero_divisible_minor Z H G D W C E hG hDn hbn hZG hHC hHE
  let p : F[X] := (Zp.submatrix id f).det
  have hpcoe : (p : PowerSeries F) = (Z.submatrix id f).det := by
    exact RingHom.map_det Polynomial.coeToPowerSeries.ringHom (Zp.submatrix id f)
  have hpn : p ≠ 0 := by
    intro hp
    apply hfn
    rw [← hpcoe, hp, Polynomial.coe_zero]
  have hdegree : p.natDegree ≤ (n-1) * k.choose 2 := by
    calc
      p.natDegree ≤ ∑ j : Fin k, j.val * (n-1) := by
        apply natDegree_det_le_sum
        intro j l
        exact numeratorRow_degree hn q P u hq hP j.val (f l)
      _ = (n-1) * k.choose 2 := by
        rw [← Finset.sum_mul, sum_fin_eq_choose, mul_comm]
  have horder : (wronskian b).order.toNat ≤ (n-1) * k.choose 2 := by
    apply (order_le_natDegree_of_dvd (wronskian b) p hpn ?_).trans hdegree
    rwa [hpcoe]
  have hymem : systemScalarOutput u v G ∈ Submodule.span F (Set.range b) := by
    apply Submodule.sum_mem
    intro l _
    change h l * PowerSeries.C (v l) ∈ _
    rw [mul_comm, ← PowerSeries.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hhmem l)
  have hybound := order_le_wronskian_add b hbn (systemScalarOutput u v G) hy hymem
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    subst k
    have : systemScalarOutput u v G = 0 := by simpa using hymem
    exact hy this
  have hchoose : k.choose 2 ≤ (Fintype.card I).choose 2 := Nat.choose_le_choose 2 hk
  have hmul := Nat.mul_le_mul_left (n-1) hchoose
  omega

end NCHitting

end

end OAI
