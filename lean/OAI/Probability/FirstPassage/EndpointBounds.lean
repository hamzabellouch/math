import OAI.Probability.FirstPassage.EndpointTail
import OAI.Probability.FirstPassage.EndpointGeometry

namespace OAI

namespace PlanarFPP
open Set Finset

lemma gridMesh_le_scale (m j : ℕ) : (gridMesh m j : ℝ) ≤ (2 : ℝ)^m := by
  simp only [gridMesh,Int.cast_pow,Int.cast_ofNat]
  apply pow_le_pow_right₀ (by norm_num)
  unfold gridMeshExponent
  omega

lemma grid_endpoint_height (K : ℝ) (hK : 0 ≤ K) (k j : ℕ) (hj : j ≤ k) :
    (K+200)*(j : ℝ)^2*gridWidth k j ≤ 2*(K+200)*(2 : ℝ)^k := by
  have h := mul_le_mul_of_nonneg_left (endpointErrorTerm_le_two j)
    (show 0 ≤ (K+200)*(2 : ℝ)^k by positivity)
  rw [mul_assoc,gridWidth_endpointError k j hj]
  nlinarith

noncomputable def endpointExtensionError (K : ℝ) (k J : ℕ) : ℝ :=
  16*(K+200)*(2 : ℝ)^k*endpointErrorTail J

lemma endpoint_extension_cost_sum (K : ℝ) (hK : 0 ≤ K) (k m J : ℕ)
    (hlast : gridLastLevel m ≤ k) (hJ : J ≤ gridLastLevel m) :
    (∑ i ∈ range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i))) ≤
      endpointExtensionError K k J := by
  have heq : (∑ i ∈ range (gridLastLevel m-J+1),16*((K+200)*((J+i : ℕ) : ℝ)^2*gridWidth k (J+i))) =
      16*(K+200)*(2 : ℝ)^k*(∑ i ∈ range (gridLastLevel m-J+1),endpointErrorTerm (J+i)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    have hi' := mem_range.mp hi
    have hj : J+i ≤ k := by omega
    have hh := gridWidth_endpointError k (J+i) hj
    calc
      _ = 16*(K+200)*(((J+i : ℕ) : ℝ)^2*gridWidth k (J+i)) := by ring
      _ = _ := by rw [hh]; ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (endpointError_sum_le_tail J _ ) (by positivity)

lemma endpoint_localization (b A R C : ℝ) (_hC : 0 ≤ C) (k m : ℕ) (p z : Vertex) (d : ℤ)
    (hd : (d : ℝ) ≤ (2 : ℝ)^m)
    (hp : |(p.1 : ℝ)| ≤ A*(2 : ℝ)^m) (hr : |transverse b p| ≤ R*(2 : ℝ)^k)
    (hx : p.1-3*d ≤ z.1 ∧ z.1 ≤ p.1+3*d)
    (hz : |transverse b z-transverse b p| ≤ 2*C*(2 : ℝ)^k) :
    |(z.1 : ℝ)| ≤ (A+4)*(2 : ℝ)^m ∧
      |transverse b z| ≤ (R+2*C)*(2 : ℝ)^k := by
  have hx' : (p.1 : ℝ)-3*(d : ℝ) ≤ (z.1 : ℝ) ∧
      (z.1 : ℝ) ≤ (p.1 : ℝ)+3*(d : ℝ) := by exact_mod_cast hx
  have hp' := abs_le.mp hp
  refine ⟨abs_le.mpr ⟨?_,?_⟩,?_⟩
  · linarith [pow_pos (by norm_num : (0 : ℝ)<2) m]
  · linarith [pow_pos (by norm_num : (0 : ℝ)<2) m]
  · have hh := abs_add_le (transverse b z-transverse b p) (transverse b p)
    rw [sub_add_cancel] at hh
    linarith

end PlanarFPP

end OAI
