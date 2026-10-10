import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import OAI.Geometry.NodalSets.Waves.LatticeSourceWaves

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
noncomputable section

lemma lattice_scale_pos {n : ℕ} (hn : 0 < n) : 0 < (n:ℝ)^(-1/2:ℝ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma scaledLatticePoint_injective {n : ℕ} (hn : 0 < n) : Function.Injective (scaledLatticePoint n) := by
  intro z w h
  funext i
  have hh := congrFun h i
  change (n:ℝ)^(-1/2:ℝ)*(z i:ℝ) = (n:ℝ)^(-1/2:ℝ)*(w i:ℝ) at hh
  exact_mod_cast mul_left_cancel₀ (ne_of_gt (lattice_scale_pos hn)) hh

theorem finite_source_grid {U : Set Coord} (hU : Bornology.IsBounded U)
    {n : ℕ} (hn : 0 < n) : Finite (SourceGrid U n) := by
  obtain ⟨B,hB,hbound⟩ := hU.exists_pos_norm_le
  let r : ℝ := (n:ℝ)^(-1/2:ℝ)
  have hr : 0 < r := lattice_scale_pos hn
  let M : ℤ := ⌈B/r⌉
  have hcoords (z : SourceGrid U n) (i : Fin 4) : z.val i ∈ Icc (-M) M := by
    have hi := (norm_le_pi_norm (scaledLatticePoint n z) i).trans (hbound _ z.property)
    change |r*(z.val i:ℝ)| ≤ B at hi
    rw [abs_mul,abs_of_pos hr] at hi
    have ha : |(z.val i:ℝ)| ≤ B/r := (le_div_iff₀ hr).mpr (by nlinarith)
    have hM : B/r ≤ (M:ℝ) := Int.le_ceil _
    have hpair := abs_le.mp (ha.trans hM)
    constructor
    · exact_mod_cast hpair.1
    · exact_mod_cast hpair.2
  let f : SourceGrid U n → (Fin 4 → Icc (-M) M) := fun z i ↦ ⟨z.val i,hcoords z i⟩
  apply Finite.of_injective f
  intro z w h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

def roundedLatticeIndex (n : ℕ) (x : Coord) : Fin 4 → ℤ :=
  fun i ↦ ⌊x i / (n:ℝ)^(-1/2:ℝ)⌋

theorem rounded_lattice_distance {n : ℕ} (hn : 0 < n) (x : Coord) :
    sourceEuclideanNorm (scaledLatticePoint n (roundedLatticeIndex n x)-x) ≤
      2*(n:ℝ)^(-1/2:ℝ) := by
  let r : ℝ := (n:ℝ)^(-1/2:ℝ)
  have hr : 0 < r := lattice_scale_pos hn
  have hb : ‖scaledLatticePoint n (roundedLatticeIndex n x)-x‖ ≤ r := by
    apply (pi_norm_le_iff_of_nonneg hr.le).mpr
    intro i
    have h1 := Int.floor_le (x i/r)
    have h2 := Int.lt_floor_add_one (x i/r)
    have h1' := mul_le_mul_of_nonneg_left h1 hr.le
    have h2' := mul_lt_mul_of_pos_left h2 hr
    have he : r*(x i/r) = x i := by field_simp
    rw [he] at h1' h2'
    change |r*(⌊x i/r⌋:ℝ)-x i| ≤ r
    apply abs_le.mpr
    constructor <;> nlinarith
  exact (sourceEuclideanNorm_le _).trans (by dsimp [r] at hb ⊢; linarith)

theorem rounded_lattice_mem {U : Set Coord} {n : ℕ} (hn : 0 < n) (x : Coord)
    (hball : {y | sourceEuclideanNorm (y-x) ≤ 2*(n:ℝ)^(-1/2:ℝ)} ⊆ U) :
    scaledLatticePoint n (roundedLatticeIndex n x) ∈ U :=
  hball (rounded_lattice_distance hn x)

end
end Yau.Geometry

end OAI
