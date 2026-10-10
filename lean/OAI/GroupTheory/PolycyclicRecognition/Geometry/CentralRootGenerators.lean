import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianRootGenerators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentQuotientRank

namespace OAI

/-! # Finite generation up to roots through a central extension -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G]

theorem exists_fg_subgroup_containing_powers_of_center
    (hZ : ∃ L : Subgroup (Subgroup.center G), L.FG ∧
      ∀ z, ∃ n : ℕ, 0 < n ∧ z ^ n ∈ L)
    (hQ : ∃ L : Subgroup (G ⧸ Subgroup.center G), L.FG ∧
      ∀ x, ∃ n : ℕ, 0 < n ∧ x ^ n ∈ L) :
    ∃ H : Subgroup G, H.FG ∧ ∀ g, ∃ n : ℕ, 0 < n ∧ g ^ n ∈ H := by
  obtain ⟨LZ, hLZ, hz⟩ := hZ
  obtain ⟨LQ, hLQ, hq⟩ := hQ
  let q := QuotientGroup.mk' (Subgroup.center G)
  let P := LQ.comap q
  let : Group.FG LQ := (Group.fg_iff_subgroup_fg LQ).mpr hLQ
  obtain ⟨F, hF, hFsurj⟩ := exists_fg_subgroup_surjective
    (quotientSubgroupMap q LQ)
    (quotientSubgroupMap_surjective q (QuotientGroup.mk'_surjective _) LQ)
  let K := F.map P.subtype
  let Z := LZ.map (Subgroup.center G).subtype
  let H := K ⊔ Z
  refine ⟨H, (fg_subgroup_map hF P.subtype).sup
    (fg_subgroup_map hLZ (Subgroup.center G).subtype), ?_⟩
  intro g
  obtain ⟨n, hn, hgn⟩ := hq (q g)
  have hgn' : q (g ^ n) ∈ LQ := by simpa only [map_pow] using hgn
  obtain ⟨x, hx⟩ := hFsurj ⟨q (g ^ n), hgn'⟩
  let k : G := x.val.val
  have hk : k ∈ K := ⟨x.val, x.property, rfl⟩
  have hqk : q k = q (g ^ n) := congrArg Subtype.val hx
  let z := g ^ n * k⁻¹
  have hzZ : z ∈ Subgroup.center G := by
    apply (QuotientGroup.eq_one_iff z).mp
    change q z = 1
    change q (g ^ n * k⁻¹) = 1
    rw [map_mul, map_inv, hqk, mul_inv_cancel]
  obtain ⟨m, hm, hzm⟩ := hz ⟨z, hzZ⟩
  have hzm' : z ^ m ∈ Z := ⟨(⟨z, hzZ⟩ : Subgroup.center G) ^ m, hzm, rfl⟩
  have hcomm : Commute z k := (Subgroup.mem_center_iff.mp hzZ k).symm
  have he : g ^ n = z * k := by simp [z, mul_assoc]
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [pow_mul, he, hcomm.mul_pow]
  exact H.mul_mem ((show Z ≤ H from le_sup_right) hzm')
    (H.pow_mem ((show K ≤ H from le_sup_left) hk) m)

end PolycyclicRecognition

end

end OAI
