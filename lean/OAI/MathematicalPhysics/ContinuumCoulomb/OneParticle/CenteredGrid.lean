import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CubeIntegral

namespace OAI

/-! A concrete finite family of lattice cubes tiles the enclosing rectangular
slab, including its boundary. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

def centeredGridIndices (r : Fin 3 → ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (-(r i : ℤ)) (r i : ℤ))

theorem mem_centeredGridIndices (r : Fin 3 → ℕ) (k : Fin 3 → ℤ) :
    k ∈ centeredGridIndices r ↔ ∀ i, -(r i : ℤ) ≤ k i ∧ k i ≤ (r i : ℤ) := by
  simp only [centeredGridIndices,Fintype.mem_piFinset,Finset.mem_Icc]

theorem exists_centered_grid_integer (N : ℕ) {h x : ℝ} (hh : 0 < h)
    (hx : |x| ≤ ((N:ℝ)+1/2)*h) :
    ∃ k : ℤ, -(N:ℤ) ≤ k ∧ k ≤ (N:ℤ) ∧ |x-h*(k:ℝ)| ≤ h/2 := by
  let j : ℤ := ⌊x/h+1/2⌋
  have hx' := abs_le.mp hx
  have he : (x/h)*h = x := div_mul_cancel₀ _ hh.ne'
  have hjl : (j:ℝ) ≤ x/h+1/2 := Int.floor_le _
  have hju : x/h+1/2 < (j:ℝ)+1 := Int.lt_floor_add_one _
  have hjlow : -(N:ℤ) ≤ j := by
    apply Int.le_floor.mpr
    push_cast
    nlinarith
  by_cases hj : j ≤ (N:ℤ)
  · refine ⟨j,hjlow,hj,abs_le.mpr ⟨?_,?_⟩⟩
    · nlinarith [mul_le_mul_of_nonneg_right hjl hh.le]
    · nlinarith [mul_lt_mul_of_pos_right hju hh]
  · refine ⟨(N:ℤ),by omega,le_rfl,abs_le.mpr ⟨?_,?_⟩⟩
    · have hjn : (N:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show (N:ℤ)+1 ≤ j by omega)
      norm_num only [Int.cast_natCast]
      nlinarith [mul_le_mul_of_nonneg_right hjn hh.le,mul_le_mul_of_nonneg_right hjl hh.le]
    · exact_mod_cast (show x-h*(N:ℝ) ≤ h/2 by nlinarith [hx'.2])

theorem centeredGrid_covers (r : Fin 3 → ℕ) {h : ℝ} (hh : 0 < h) :
    (⋃ k : {k // k ∈ centeredGridIndices r}, positionCube (gaussCellCenter h k.val) h) =
      {x : Position | ∀ i, |x i| ≤ ((r i:ℝ)+1/2)*h} := by
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    have hki := (mem_centeredGridIndices r k.val).mp k.property
    intro i
    have hc := abs_le.mp (mem_positionCube.mp hk i)
    have hb1 : -(r i:ℝ) ≤ (k.val i:ℝ) := by exact_mod_cast (hki i).1
    have hb2 : (k.val i:ℝ) ≤ (r i:ℝ) := by exact_mod_cast (hki i).2
    apply abs_le.mpr
    change -(h/2) ≤ x i-h*(k.val i:ℝ) ∧ x i-h*(k.val i:ℝ) ≤ h/2 at hc
    rcases hc with ⟨hcl,hcu⟩
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hb1 hh.le,
      mul_le_mul_of_nonneg_left hb2 hh.le]
  · intro hx
    choose k hk1 hk2 hk3 using fun i => exists_centered_grid_integer (r i) hh (hx i)
    refine Set.mem_iUnion.mpr ⟨⟨k,(mem_centeredGridIndices r k).mpr (fun i => ⟨hk1 i,hk2 i⟩)⟩,?_⟩
    rw [mem_positionCube]
    exact hk3

theorem grid_cell_integral_sum_eq {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) {B : Set Position}
    (hcover : (⋃ i, positionCube (gaussCellCenter h (index i)) h) = B)
    (f : Position → ℝ) (hf : IntegrableOn f B) :
    (∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h, f x) = ∫ x in B, f x := by
  have he (i : ι) := positionOpenCube_ae_eq (gaussCellCenter h (index i)) h
  have hsets : (⋃ i, positionOpenCube (gaussCellCenter h (index i)) h) =ᵐ[volume]
      (⋃ i, positionCube (gaussCellCenter h (index i)) h) := by
    filter_upwards [ae_all_iff.mpr he] with x hx
    simp only [Set.mem_iUnion]
    simp_rw [hx]
  have hi (i : ι) : IntegrableOn f (positionOpenCube (gaussCellCenter h (index i)) h) := by
    apply hf.mono_set
    intro x hx
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨i,positionOpenCube_subset _ _ hx⟩
  calc
    _ = ∑ i, ∫ x in positionOpenCube (gaussCellCenter h (index i)) h, f x := by
      apply Finset.sum_congr rfl
      intro i _
      exact (setIntegral_congr_set (he i)).symm
    _ = ∫ x in ⋃ i, positionOpenCube (gaussCellCenter h (index i)) h, f x :=
      (integral_iUnion_fintype (fun i => positionOpenCube_measurable _ _)
        (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he))) hi).symm
    _ = ∫ x in ⋃ i, positionCube (gaussCellCenter h (index i)) h, f x :=
      setIntegral_congr_set hsets
    _ = _ := by rw [hcover]

end ContinuumCoulomb

end

end OAI
