import OAI.MeasureTheory.Falconer.Estimates.EndpointCoarsening

namespace OAI

/-! All geometric inputs of the scale-product step from the actual dyadic
endpoint configuration. Local regularity is tested on the original child. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem dyadic_endpoint_local_mesh {a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b) :
    (1/(2:ℝ)^(b-a+2))/(4*(1/(2:ℝ)^(c-a+2))) = 1/(2:ℝ)^(b-c+2) := by
  rw [dyadic_local_mesh _ _ (by omega)]
  congr 2
  omega

theorem quarter_endpoint_scale_inputs {N a b c : ℕ} (hac : a ≤ c) (hcb : c ≤ b)
    (Q : DyadicCube 2) (hQ : Q.side = 1) (C : Finset (CellPath 2))
    (hC : C ⊆ cubePaths 2 N) (hbN : b ≤ N) (p₀ : CellPath 2)
    (hp₀ : p₀ ∈ C.image (List.take a)) {t KP : ℝ}
    (hball : ∀ r ∈ prefixChildren C a c p₀,
      NormalizedFiniteBallBound (1/(2:ℝ)^(b-c+2)) t KP (quarterEndpointSet Q C c b r)) :
    let P := quarterEndpointSet Q C a b p₀
    let D := quarterEndpointSet Q C a c p₀
    let δ := 1/(2:ℝ)^(b-a+2)
    let ρ := 1/(2:ℝ)^(c-a+2)
    ∃ q : Space 2 → Space 2,
      D.Nonempty ∧ D = P.image q ∧
      (∀ x ∈ P, dist x (q x) ≤ ρ) ∧
      (∀ z ∈ D, |z 0| ≤ 1/4 ∧ |z 1| ≤ 1/4) ∧
      FiniteSeparatedAt δ P ∧
      (∀ z ∈ D, NormalizedFiniteBallBound (δ/(4*ρ)) t KP
        ((P.filter fun x => q x = z).image (localPacketPoint (4*ρ) (z 0) (z 1)))) ∧
      (∀ r ∈ prefixChildren C a c p₀,
        ((P.filter fun x => q x = quarterEndpointPoint Q a p₀ r).image
          (localPacketPoint (4*ρ) (quarterEndpointPoint Q a p₀ r 0)
            (quarterEndpointPoint Q a p₀ r 1))) = quarterEndpointSet Q C c b r) ∧
      0 < δ ∧ 0 < ρ ∧ ρ ≤ 1/4 ∧ δ ≤ ρ := by
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨q,hq⟩ := exists_quarterEndpoint_prefix_map (c := c) Q hQpos C hC hbN p₀
  have hlocal (r : CellPath 2) (hr : r ∈ prefixChildren C a c p₀) :=
    quarterEndpoint_prefix_local_fiber hac hcb Q hQpos C hC hbN p₀ q hq hr
  have hgeom := quarterEndpointSet_geometry Q hQ C hC hac (hcb.trans hbN) p₀
  have hfine := quarterEndpointSet_geometry Q hQ C hC (hac.trans hcb) hbN p₀
  refine ⟨q,((prefixFiber_nonempty hp₀).image _).image _,
    (quarterEndpoint_prefix_image hcb Q C p₀ q hq).symm,
    quarterEndpoint_prefix_near hac hcb Q hQ C hC hbN p₀ q hq,
    hgeom.2.1,hfine.2.2,?_,hlocal,by positivity,by positivity,?_,?_⟩
  · intro z hz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
    rw [hlocal r hr,dyadic_endpoint_local_mesh hac hcb]
    exact hball r hr
  · apply (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(c-a+2))).2
    have hh : (2:ℝ)^2 ≤ (2:ℝ)^(c-a+2) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at hh ⊢
    linarith only [hh]
  · apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)

end Falconer

end OAI
