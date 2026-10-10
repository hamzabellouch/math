import OAI.GroupTheory.PolycyclicRecognition.Geometry.CentralRootGenerators

namespace OAI

/-! # Root cores lift through an actual central kernel -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem central_extension_rootCore (N : Subgroup G) [N.Normal]
    (hcentral : N ≤ Subgroup.center G)
    (hN : ∃ L : Subgroup N, L.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ L)
    (hQ : ∃ L : Subgroup (G ⧸ N), L.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ L) :
    ∃ H : Subgroup G, H.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H := by
  obtain ⟨LN, hLN, hn⟩ := hN
  obtain ⟨LQ, hLQ, hq⟩ := hQ
  let q := QuotientGroup.mk' N
  let P := LQ.comap q
  let : Group.FG LQ := (Group.fg_iff_subgroup_fg LQ).mpr hLQ
  obtain ⟨F, hF, hFsurj⟩ := exists_fg_subgroup_surjective
    (quotientSubgroupMap q LQ)
    (quotientSubgroupMap_surjective q (QuotientGroup.mk'_surjective _) LQ)
  let K := F.map P.subtype
  let Z := LN.map N.subtype
  let H := K ⊔ Z
  refine ⟨H, (fg_subgroup_map hF P.subtype).sup (fg_subgroup_map hLN N.subtype), ?_⟩
  intro g
  obtain ⟨n, hnpos, hgn⟩ := hq (q g)
  have hgn' : q (g ^ n) ∈ LQ := by simpa only [map_pow] using hgn
  obtain ⟨x, hx⟩ := hFsurj ⟨q (g ^ n), hgn'⟩
  let k : G := x.val.val
  have hk : k ∈ K := ⟨x.val, x.property, rfl⟩
  have hqk : q k = q (g ^ n) := congrArg Subtype.val hx
  let z := g ^ n * k⁻¹
  have hzN : z ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g ^ n * k⁻¹) = 1
    rw [map_mul, map_inv, hqk, mul_inv_cancel]
  obtain ⟨m, hm, hzm⟩ := hn ⟨z, hzN⟩
  have hzm' : z ^ m ∈ Z := ⟨(⟨z, hzN⟩ : N) ^ m, hzm, rfl⟩
  have hcomm : Commute z k := (Subgroup.mem_center_iff.mp (hcentral hzN) k).symm
  have he : g ^ n = z * k := by simp [z, mul_assoc]
  refine ⟨n * m, Nat.mul_pos hnpos hm, ?_⟩
  rw [pow_mul, he, hcomm.mul_pow]
  exact H.mul_mem ((show Z ≤ H from le_sup_right) hzm')
    (H.pow_mem ((show K ≤ H from le_sup_left) hk) m)

end PolycyclicRecognition

end

end OAI
