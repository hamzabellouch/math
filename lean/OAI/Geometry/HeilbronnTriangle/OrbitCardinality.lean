import Mathlib

namespace OAI


namespace Problem355.OrbitCardinality

variable {G U X : Type*} [Group G] [Group U] [MulAction G X]

theorem relIndex_mul_index_comm (H N : Subgroup G) :
    H.relIndex N * N.index = H.index * N.relIndex H := by
  calc
    H.relIndex N * N.index = (H ⊓ N).index := by
      rw [← Subgroup.inf_relIndex_right H N]
      exact Subgroup.relIndex_mul_index inf_le_right
    _ = N.relIndex H * H.index := by
      rw [← Subgroup.inf_relIndex_left H N]
      exact (Subgroup.relIndex_mul_index inf_le_left).symm
    _ = H.index * N.relIndex H := Nat.mul_comm _ _

theorem stabilizer_subgroup (N : Subgroup G) (x : X) :
    (MulAction.stabilizer G x).subgroupOf N = MulAction.stabilizer N x := by
  ext g
  rfl

theorem kernel_orbit_card_mul_card (f : G →* U) (hf : Function.Surjective f) (x : X) :
    Nat.card (MulAction.orbit f.ker x) * Nat.card U =
      Nat.card (MulAction.orbit G x) * Nat.card ((MulAction.stabilizer G x).map f) := by
  have h := relIndex_mul_index_comm (MulAction.stabilizer G x) f.ker
  rw [Subgroup.relIndex, stabilizer_subgroup, MulAction.index_stabilizer,
    Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup U) ≃* U).toEquiv,
    MulAction.index_stabilizer, Subgroup.relIndex_ker] at h
  exact h

def orbitFiberEquivStabilizer (x : X) (g : G) :
    {a : G // a • x = g • x} ≃ MulAction.stabilizer G x where
  toFun a := ⟨g⁻¹ * a.1, by
    change (g⁻¹ * a.1) • x = x
    rw [mul_smul, a.2, inv_smul_smul]⟩
  invFun a := ⟨g * a.1, by
    rw [mul_smul, a.2]⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv a := by
    apply Subtype.ext
    simp

theorem card_orbit_fiber (x y : X) (hy : y ∈ MulAction.orbit G x) :
    Nat.card {g : G // g • x = y} = Nat.card (MulAction.stabilizer G x) := by
  obtain ⟨g, rfl⟩ := hy
  exact Nat.card_congr (orbitFiberEquivStabilizer x g)

theorem orbit_card_mul_stabilizer_card (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) =
      Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

theorem orbit_bound_of_cardinal_estimates
    {o small total stab image u h D E c : ℝ}
    (ho : 0 ≤ o) (hu : 0 < u) (hh : 0 < h) (hD : 0 < D) (hE : 0 < E)
    (horbit : o * stab = total) (hkernel : small * u = o * image)
    (htotal : c * h ^ 9 ≤ total) (hstab : stab ≤ D ^ 3 * E ^ 3)
    (himage : E * u ≤ h * image) :
    c * h ^ 8 / (D ^ 3 * E ^ 2) ≤ small := by
  have hmul : (c * h ^ 8) * (h * E * u) ≤
      (small * (D ^ 3 * E ^ 2)) * (h * E * u) := by
    calc
      (c * h ^ 8) * (h * E * u) = c * h ^ 9 * (E * u) := by ring
      _ ≤ total * (E * u) := mul_le_mul_of_nonneg_right htotal (by positivity)
      _ = o * stab * (E * u) := by rw [horbit]
      _ ≤ o * (D ^ 3 * E ^ 3) * (E * u) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hstab ho
        · positivity
      _ ≤ o * (D ^ 3 * E ^ 3) * (h * image) :=
        mul_le_mul_of_nonneg_left himage (by positivity)
      _ = (o * image) * (D ^ 3 * E ^ 3) * h := by ring
      _ = (small * u) * (D ^ 3 * E ^ 3) * h := by rw [hkernel]
      _ = (small * (D ^ 3 * E ^ 2)) * (h * E * u) := by ring
  apply (div_le_iff₀ (show 0 < D ^ 3 * E ^ 2 by positivity)).2
  exact le_of_mul_le_mul_right hmul (by positivity)

theorem kernel_orbit_bound [Finite G] [Finite U]
    (f : G →* U) (hf : Function.Surjective f) (x : X)
    {h D E c : ℝ} (hh : 0 < h) (hD : 0 < D) (hE : 0 < E)
    (htotal : c * h ^ 9 ≤ (Nat.card G : ℝ))
    (hstab : (Nat.card (MulAction.stabilizer G x) : ℝ) ≤ D ^ 3 * E ^ 3)
    (himage : E * (Nat.card U : ℝ) ≤
      h * (Nat.card ((MulAction.stabilizer G x).map f) : ℝ)) :
    c * h ^ 8 / (D ^ 3 * E ^ 2) ≤ (Nat.card (MulAction.orbit f.ker x) : ℝ) := by
  have hu : (0 : ℝ) < Nat.card U := by exact_mod_cast Nat.card_pos (α := U)
  have horbit : (Nat.card (MulAction.orbit G x) : ℝ) *
      Nat.card (MulAction.stabilizer G x) = Nat.card G := by
    exact_mod_cast orbit_card_mul_stabilizer_card (G := G) x
  have hkernel : (Nat.card (MulAction.orbit f.ker x) : ℝ) * Nat.card U =
      (Nat.card (MulAction.orbit G x) : ℝ) *
        Nat.card ((MulAction.stabilizer G x).map f) := by
    exact_mod_cast kernel_orbit_card_mul_card f hf x
  exact orbit_bound_of_cardinal_estimates (Nat.cast_nonneg _) hu hh hD hE
    horbit hkernel htotal hstab himage

end Problem355.OrbitCardinality

end OAI
