import OAI.Geometry.CylinderCovering.Angular.EndpointScaledDefinitions
import OAI.Geometry.CylinderCovering.Angular.EndpointCover
import OAI.Geometry.CylinderCovering.Convexity.TriangularSimilarity

namespace OAI

noncomputable section
open Set
open TriangularCovering

namespace AngularEndpoint

lemma reciprocal_H_square : (1/H)^2 = (1/2:ℝ) := by
  rw [div_pow,H_sq]
  norm_num

lemma endpointScaledBody_eq : CylinderCovering.endpointScaledBody =
    CylinderCovering.Similarity.map (0:Space) (1/H)
      (LinearIsometryEquiv.refl ℝ Space) '' K := by
  change (fun z : Space => (1/H) • z) '' K = _
  apply congrArg (fun f : Space → Space => f '' K)
  funext z
  simp [CylinderCovering.Similarity.map]

lemma endpointScaledBody_minimum :
    CylinderCovering.Similarity.minimumArea CylinderCovering.endpointScaledBody = H/2 := by
  rw [endpointScaledBody_eq,CylinderCovering.Similarity.minimumArea_map K 0
    (one_div_ne_zero H_ne_zero),reciprocal_H_square]
  change (1/2:ℝ)*A_min=H/2
  rw [projection_minimum]
  ring

theorem endpoint_scaled_cover : CylinderCovering.AngularEndpointScaledStatement := by
  refine ⟨endpointScaledBody_minimum,?_⟩
  intro k hk
  obtain ⟨C,hpres,hcover,harea,hcost,hrel⟩ := endpoint_cover k hk
  let D := fun i => (C i).similarity 0 (one_div_ne_zero H_ne_zero)
    (LinearIsometryEquiv.refl ℝ Space)
  have hDarea : totalArea D = (1/2:ℝ)*totalArea C := by
    dsimp [D]
    rw [similarity_totalArea,reciprocal_H_square]
  have hDcover : ∀ z∈CylinderCovering.endpointScaledBody,∃ i,z∈(D i).carrier := by
    rw [endpointScaledBody_eq]
    exact similarity_covers C hcover 0 (one_div_ne_zero H_ne_zero)
      (LinearIsometryEquiv.refl ℝ Space)
  have hDrel : (∑ i,area (D i).base /
      CylinderCovering.Similarity.shadowArea CylinderCovering.endpointScaledBody (D i).axis) =
      relativeCost C := by
    rw [endpointScaledBody_eq]
    exact similarity_relativeCost C 0 (one_div_ne_zero H_ne_zero)
      (LinearIsometryEquiv.refl ℝ Space)
  refine ⟨C,D,hpres,?_,hDcover,?_,?_,by rw [hDrel]; exact hrel⟩
  · intro i
    constructor
    · rfl
    · change CylinderCovering.Similarity.transportedBase (C i).base (C i).axis
        0 (1/H) (LinearIsometryEquiv.refl ℝ Space) = _
      unfold CylinderCovering.Similarity.transportedBase
      apply congrArg (fun f : Space → Space => f '' (C i).base)
      funext z
      simp [CylinderCovering.Similarity.baseMap,CylinderCovering.Similarity.project]
  · have h2div : 2/H=H := by apply (div_eq_iff H_ne_zero).2; nlinarith only [H_sq]
    have hid : totalArea D-(2/H)*(1/4-(13/12000:ℝ)*(1/(k:ℝ))^2) =
        (H/2)*(totalArea C/H-(1/2-(13/6000:ℝ)*(1/(k:ℝ))^2)) := by
      rw [hDarea,h2div]
      field_simp [H_ne_zero]
      ring
    rw [hid,abs_mul,abs_of_pos (div_pos H_pos (by norm_num))]
    calc
      _ ≤ (H/2)*(14*(1/(k:ℝ))^4) :=
        mul_le_mul_of_nonneg_left harea (div_nonneg H_pos.le (by norm_num))
      _ = 7*H*(1/(k:ℝ))^4 := by ring
  · rw [hDarea,endpointScaledBody_minimum]
    rw [projection_minimum] at hcost
    linarith only [hcost]

end AngularEndpoint

end

end OAI
