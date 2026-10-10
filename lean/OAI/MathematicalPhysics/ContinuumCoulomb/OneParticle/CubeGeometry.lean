import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.GaussEightNodes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! Actual Euclidean mesh cells: volume, radius, node containment, and
disjoint interiors. These retain the volume normalization of the Gauss rule. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def positionCube (b : Position) (h : ℝ) : Set Position :=
  WithLp.ofLp ⁻¹' Set.Icc (fun i => b i-h/2) (fun i => b i+h/2)

def positionOpenCube (b : Position) (h : ℝ) : Set Position :=
  WithLp.ofLp ⁻¹' Set.univ.pi (fun i => Set.Ioo (b i-h/2) (b i+h/2))

theorem mem_positionCube {x b : Position} {h : ℝ} :
    x ∈ positionCube b h ↔ ∀ i, |x i-b i| ≤ h/2 := by
  change ((fun i => b i-h/2) ≤ WithLp.ofLp x ∧
    WithLp.ofLp x ≤ (fun i => b i+h/2)) ↔ _
  constructor
  · rintro ⟨hl,hu⟩ i
    exact abs_le.mpr ⟨by linarith [hl i],by linarith [hu i]⟩
  · intro hx
    constructor <;> intro i <;> have hi := abs_le.mp (hx i) <;> linarith

theorem mem_positionOpenCube {x b : Position} {h : ℝ} :
    x ∈ positionOpenCube b h ↔ ∀ i, |x i-b i| < h/2 := by
  change (∀ i ∈ Set.univ, x i ∈ Set.Ioo (b i-h/2) (b i+h/2)) ↔ _
  simp only [Set.mem_univ,true_implies,Set.mem_Ioo]
  constructor
  · intro hx i
    exact abs_lt.mpr ⟨by linarith [(hx i).1],by linarith [(hx i).2]⟩
  · intro hx i
    have hi := abs_lt.mp (hx i)
    constructor <;> linarith

theorem positionCube_isClosed (b : Position) (h : ℝ) : IsClosed (positionCube b h) :=
  isClosed_Icc.preimage (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem positionOpenCube_measurable (b : Position) (h : ℝ) :
    MeasurableSet (positionOpenCube b h) :=
  (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ)).measurable

theorem positionOpenCube_subset (b : Position) (h : ℝ) :
    positionOpenCube b h ⊆ positionCube b h := by
  intro x hx
  exact mem_positionCube.mpr (fun i => (mem_positionOpenCube.mp hx i).le)

theorem positionCube_volume (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (positionCube b h) = h^3 := by
  have he := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (s := Set.Icc (fun i => b i-h/2) (fun i => b i+h/2)) measurableSet_Icc.nullMeasurableSet
  unfold positionCube Measure.real
  rw [he,Real.volume_Icc_pi_toReal (by intro i; linarith)]
  simp only [show ∀ i : Fin 3, b i+h/2-(b i-h/2) = h by intro; ring]
  simp

theorem positionOpenCube_volume (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    volume.real (positionOpenCube b h) = h^3 := by
  have he := (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (s := Set.univ.pi (fun i => Set.Ioo (b i-h/2) (b i+h/2)))
    (MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)).nullMeasurableSet
  unfold positionOpenCube Measure.real
  rw [he,Real.volume_pi_Ioo_toReal (by intro i; linarith)]
  simp only [show ∀ i : Fin 3, b i+h/2-(b i-h/2) = h by intro; ring]
  simp

theorem positionOpenCube_ae_eq (b : Position) (h : ℝ) :
    positionOpenCube b h =ᵐ[volume] positionCube b h := by
  have he := Measure.univ_pi_Ioo_ae_eq_Icc
    (μ := fun _ : Fin 3 => (volume : Measure ℝ))
    (f := fun i => b i-h/2) (g := fun i => b i+h/2)
  exact (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he

theorem cubePoint_mem_positionCube (b : Position) {h : ℝ} (hh : 0 ≤ h)
    {x y z : ℝ} (hx : x ∈ Set.Icc (-1:ℝ) 1)
    (hy : y ∈ Set.Icc (-1:ℝ) 1) (hz : z ∈ Set.Icc (-1:ℝ) 1) :
    cubePoint b (h/2) x y z ∈ positionCube b h := by
  rw [mem_positionCube]
  intro i
  have he : cubePoint b (h/2) x y z i-b i = (h/2)*(![x,y,z] i) := by
    fin_cases i <;> simp [cubePoint] <;> ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ h/2)]
  apply (mul_le_mul_of_nonneg_left (show |![x,y,z] i| ≤ 1 from ?_) (by positivity)).trans_eq
    (mul_one _)
  fin_cases i
  · exact abs_le.mpr hx
  · exact abs_le.mpr hy
  · exact abs_le.mpr hz

theorem positionCube_norm_sub_le {b x : Position} {h : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ positionCube b h) : ‖x-b‖ ≤ h := by
  have hi := mem_positionCube.mp hx
  have hs : ‖x-b‖^2 ≤ 3*(h/2)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, (h/2)^2 := by
        apply Finset.sum_le_sum
        intro i _
        change (x i-b i)^2 ≤ _
        nlinarith [abs_le.mp (hi i),sq_abs (x i-b i)]
      _ = _ := by simp
  nlinarith [norm_nonneg (x-b)]

theorem positionCube_isCompact (b : Position) {h : ℝ} (hh : 0 ≤ h) :
    IsCompact (positionCube b h) := by
  apply (isCompact_closedBall b h).of_isClosed_subset (positionCube_isClosed b h)
  intro x hx
  exact positionCube_norm_sub_le hh hx

theorem positionCube_diameter_bound {b x y : Position} {h : ℝ} (hh : 0 ≤ h)
    (hx : x ∈ positionCube b h) (hy : y ∈ positionCube b h) : ‖x-y‖ ≤ 2*h := by
  have ht := norm_sub_le_norm_sub_add_norm_sub x b y
  rw [norm_sub_rev b y] at ht
  linarith [positionCube_norm_sub_le hh hx,positionCube_norm_sub_le hh hy]

theorem grid_openCubes_disjoint {h : ℝ} (hh : 0 < h) {k l : Fin 3 → ℤ} (hkl : k ≠ l) :
    Disjoint (positionOpenCube (gaussCellCenter h k) h)
      (positionOpenCube (gaussCellCenter h l) h) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx := abs_lt.mp (mem_positionOpenCube.mp hx i)
  have hy := abs_lt.mp (mem_positionOpenCube.mp hy i)
  change -(h/2) < x i-h*(k i:ℝ) ∧ x i-h*(k i:ℝ) < h/2 at hx
  change -(h/2) < x i-h*(l i:ℝ) ∧ x i-h*(l i:ℝ) < h/2 at hy
  rcases lt_or_gt_of_ne hi with hi | hi
  · have hd : (k i:ℝ)+1 ≤ l i := by exact_mod_cast (show k i+1 ≤ l i by omega)
    nlinarith [mul_le_mul_of_nonneg_left hd hh.le]
  · have hd : (l i:ℝ)+1 ≤ k i := by exact_mod_cast (show l i+1 ≤ k i by omega)
    nlinarith [mul_le_mul_of_nonneg_left hd hh.le]

theorem grid_cell_integral_sum_le {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) (f : Position → ℝ) (hf : Integrable f)
    (hpos : ∀ x, 0 ≤ f x) :
    (∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h, f x) ≤ ∫ x, f x := by
  have he (i : ι) := setIntegral_congr_set
    (f := f) (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)
  simp_rw [← he]
  rw [← integral_iUnion_fintype
    (fun i => positionOpenCube_measurable (gaussCellCenter h (index i)) h)
    (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
    (fun _ => hf.integrableOn)]
  exact setIntegral_le_integral hf (Filter.Eventually.of_forall hpos)

theorem grid_cell_integral_sum_le_on {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h : ℝ} (hh : 0 < h) {B : Set Position}
    (hsub : ∀ i, positionCube (gaussCellCenter h (index i)) h ⊆ B)
    (f : Position → ℝ) (hf : IntegrableOn f B) (hpos : ∀ x, 0 ≤ f x) :
    (∑ i, ∫ x in positionCube (gaussCellCenter h (index i)) h, f x) ≤
      ∫ x in B, f x := by
  have ho (i : ι) : positionOpenCube (gaussCellCenter h (index i)) h ⊆ B :=
    (positionOpenCube_subset _ _).trans (hsub i)
  have he (i : ι) := setIntegral_congr_set
    (f := f) (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)
  simp_rw [← he]
  rw [← integral_iUnion_fintype
    (fun i => positionOpenCube_measurable (gaussCellCenter h (index i)) h)
    (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
    (fun i => hf.mono_set (ho i))]
  exact setIntegral_mono_set hf (Filter.Eventually.of_forall hpos)
    (Filter.Eventually.of_forall (Set.iUnion_subset ho))

end ContinuumCoulomb

end

end OAI
