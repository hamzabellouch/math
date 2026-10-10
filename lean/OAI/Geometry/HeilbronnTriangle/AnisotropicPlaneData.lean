import OAI.Geometry.HeilbronnTriangle.AnisotropicGeometry
import OAI.Geometry.HeilbronnTriangle.IntegerPlaneEstimates
import OAI.Geometry.HeilbronnTriangle.ExactPlaneCovolume
import OAI.Geometry.HeilbronnTriangle.ShortKernelVectors

namespace OAI


noncomputable section

namespace Problem355.Anisotropic

open Matrix
open scoped Matrix
open PrimitiveNormal IntegerPlaneEstimates

lemma independent_realVector_of_cross_ne_zero (u v : IntVector)
    (huv : u ⨯₃ v ≠ 0) :
    LinearIndependent ℝ (fun i : Fin 2 => LatticeBox.realVector (![u, v] i)) := by
  let uR : Fin 3 → ℝ := fun i => (u i : ℝ)
  let vR : Fin 3 → ℝ := fun i => (v i : ℝ)
  have hcross : uR ⨯₃ vR ≠ 0 := by
    intro h
    apply huv
    ext i
    have hi := congrFun h i
    fin_cases i <;>
      simp [cross_apply, uR, vR] at hi ⊢ <;> exact_mod_cast hi
  have hind := crossProduct_ne_zero_iff_linearIndependent.mp hcross
  apply LinearIndependent.of_comp (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap
  convert hind using 1 ; try rfl
  funext i
  fin_cases i <;> rfl

lemma second_le_normal_length (y z : IntVector) (hz : y ⬝ᵥ z = 1)
    (hy : y ≠ 0) : second y z hz ≤ length y := by
  obtain ⟨u, v, hu, hv, hind, hnu, hnv⟩ :=
    ShortKernelVectors.exists_short_kernel_pair y hy
  apply second_le_of_independent y z hz ![u, v]
  · intro i
    fin_cases i
    · exact hu
    · exact hv
  · convert hind using 1
    funext i
    fin_cases i <;> rfl
  · intro i
    fin_cases i
    · exact hnu
    · exact hnv

theorem exists_planeData (y : IntVector) (hy : IsPrimitive y) :
    Nonempty (PlaneData y) := by
  obtain ⟨z, hz⟩ := (isPrimitive_iff_exists_dot_eq_one y).mp hy
  refine ⟨{
    first := first y z hz
    second := second y z hz
    one_le_first := one_le_first y z hz
    first_le_second := first_le_second y z hz
    second_le_length := second_le_normal_length y z hz hy.ne_zero
    first_le := ?_
    second_le := ?_
    shortest := ?_
    large_count := ?_
    small_count := ?_
  }⟩
  · intro v hv hne
    exact first_le_norm y z hz v (by simpa only [dotProduct_comm] using hv) hne
  · intro u v hu hv huv
    apply second_le_of_independent y z hz ![u, v]
    · intro i
      fin_cases i
      · change y ⬝ᵥ u = 0
        simpa only [dotProduct_comm] using hu
      · change y ⬝ᵥ v = 0
        simpa only [dotProduct_comm] using hv
    · exact independent_realVector_of_cross_ne_zero u v huv
    · intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
  · obtain ⟨v, _, hv, he, hw⟩ := exists_primitive_shortest_integer y z hz
    exact ⟨v, (isPrimitive_iff_exists_dot_eq_one v).mpr hw,
      by simpa only [dotProduct_comm] using hv, he⟩
  · intro S R hR hS
    have hR0 : 0 ≤ R := by
      have h1 := one_le_first y z hz
      have h2 := first_le_second y z hz
      linarith
    have hc := (plane_counts y z hz S
      (fun v hv => by simpa only [dotProduct_comm] using (hS v hv).1)
      R hR0 (fun v hv => (hS v hv).2)).1 hR
    rw [IntegralPlaneLattice.lattice_covolume y z hz] at hc
    exact hc
  · intro S R hfirst hsecond hS
    have hR0 : 0 ≤ R := by linarith [one_le_first y z hz]
    exact thin_count y z hz S
      (fun v hv => by simpa only [dotProduct_comm] using (hS v hv).1)
      R hR0 (fun v hv => (hS v hv).2) hsecond hfirst

end Problem355.Anisotropic

end

end OAI
