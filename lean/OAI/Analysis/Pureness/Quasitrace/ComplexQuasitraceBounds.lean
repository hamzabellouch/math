import OAI.Analysis.Pureness.Quasitrace.QuasitraceFamily
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule IsMulCommutative
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace ComplexQuasitrace
variable (T : ComplexQuasitrace A)

lemma nonneg (x : A) (hx : 0 ≤ x) : 0 ≤ T x := by
  have h := T.square_nonneg (CFC.sqrt x)
  rwa [(CFC.sqrt_nonneg x).star_eq, CFC.sqrt_mul_sqrt_self x hx] at h

def subalgebraLinear (S : StarSubalgebra ℂ A) [IsMulCommutative S] : S →ₗ[ℂ] ℂ :=
  Classical.choose (T.abelian_linear S.toNonUnitalStarSubalgebra)

omit [PartialOrder A] [StarOrderedRing A] in
lemma subalgebraLinear_apply (S : StarSubalgebra ℂ A) [IsMulCommutative S] (x : S) :
    T.subalgebraLinear S x = T x.1 :=
  Classical.choose_spec (T.abelian_linear S.toNonUnitalStarSubalgebra) x

def subalgebraPositiveLinear (S : StarSubalgebra ℂ A) [IsMulCommutative S]
    [hS : PartialOrder S] [StarOrderedRing S] : S →ₚ[ℂ] ℂ where
  toLinearMap := T.subalgebraLinear S
  monotone' := by
    let : LE S := hS.toLE
    let : Preorder S := hS.toPreorder
    intro x y hxy
    apply sub_nonneg.mp
    change 0 ≤ T.subalgebraLinear S y - T.subalgebraLinear S x
    rw [← map_sub, T.subalgebraLinear_apply]
    exact T.nonneg _ (map_nonneg S.subtype (sub_nonneg.mpr hxy))

lemma subalgebraPositiveLinear_apply (S : StarSubalgebra ℂ A) [IsMulCommutative S]
    [PartialOrder S] [StarOrderedRing S] (x : S) :
    T.subalgebraPositiveLinear S x = T x.1 := T.subalgebraLinear_apply S x

omit [PartialOrder A] [StarOrderedRing A] in
lemma map_zero : T 0 = 0 := by
  let S := StarAlgebra.elemental ℂ (1 : A)
  change T (0 : S).1 = 0
  rw [← T.subalgebraLinear_apply S (0 : S), _root_.map_zero]

lemma norm_apply_le_of_normal (x : A) [IsStarNormal x] :
    ‖T x‖ ≤ 4 * ‖T 1‖ * ‖x‖ := by
  let S := StarAlgebra.elemental ℂ x
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let : LE S := (CStarAlgebra.spectralOrder S).toLE
  let : Preorder S := (CStarAlgebra.spectralOrder S).toPreorder
  let f := T.subalgebraPositiveLinear S
  let a : S := ⟨x, StarAlgebra.elemental.self_mem ℂ x⟩
  obtain ⟨y, hypos, hynorm, hy⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hb : ‖f a‖ ≤ 4 * ‖f 1‖ * ‖a‖ := by
    nth_rw 1 [hy]
    simp only [map_sum, map_smul]
    apply (norm_sum_le _ _).trans
    simp only [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
    calc
      _ ≤ ∑ i : Fin 4, ‖f 1‖ * ‖a‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact (f.norm_apply_le_of_nonneg (y i) (hypos i)).trans
          (mul_le_mul_of_nonneg_left (hynorm i) (norm_nonneg _))
      _ = _ := by simp; ring
  simp only [f, subalgebraPositiveLinear_apply] at hb
  exact hb

theorem norm_apply_le (x : A) : ‖T x‖ ≤ 8 * ‖T 1‖ * ‖x‖ := by
  have hr := T.norm_apply_le_of_normal (ℜ x).1
  have hi := T.norm_apply_le_of_normal (ℑ x).1
  have he := T.real_add_I (ℜ x) (ℑ x)
  rw [realPart_add_I_smul_imaginaryPart] at he
  rw [he]
  calc
    _ ≤ ‖T (ℜ x).1‖ + ‖Complex.I * T (ℑ x).1‖ := norm_add_le _ _
    _ = ‖T (ℜ x).1‖ + ‖T (ℑ x).1‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ 4 * ‖T 1‖ * ‖(ℜ x).1‖ + 4 * ‖T 1‖ * ‖(ℑ x).1‖ := add_le_add hr hi
    _ ≤ 4 * ‖T 1‖ * ‖x‖ + 4 * ‖T 1‖ * ‖x‖ := by
      gcongr
      · exact realPart.norm_le x
      · exact imaginaryPart.norm_le x
    _ = _ := by ring
end ComplexQuasitrace
end CuntzPureness

end

end OAI
