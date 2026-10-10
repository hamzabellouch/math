import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingBaseCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BarChainExhaustion

namespace OAI

/-! # Lifting a stable finite generating base through a characteristic subgroup

Finite many lift errors fit in one inverse-image stage of the kernel base.
Adjoining that stage makes the lifted base stable. Exhaustion of the quotient
and kernel then gives exhaustion of the whole group.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem automorphism_exhaustive_of_kernel_quotient
    (N : Subgroup G) [N.Characteristic] (α : MulAut G)
    (C : Subgroup N) (P : Subgroup (G ⧸ N)) (B : Subgroup G)
    (hCcover : ∀ g, ∃ n, g ∈ automorphismStage (MulAut.characteristic N α) C n)
    (hPcover : ∀ g, ∃ n, g ∈ automorphismStage (characteristicQuotientAut N α) P n)
    (hBmap : B.map (QuotientGroup.mk' N) = P)
    (hCB : C.map N.subtype ≤ B) (hBstable : B.map α.toMonoidHom ≤ B) :
    ∀ g, ∃ n, g ∈ automorphismStage α B n := by
  intro g
  let q := QuotientGroup.mk' N
  obtain ⟨n, hn⟩ := hPcover (q g)
  have hqn : q ((α ^ n) g) ∈ P := by
    rw [← characteristicQuotient_pow_mk]
    exact (mem_automorphismStage_iff _ _ _ _).mp hn
  obtain ⟨b, hb, hqb⟩ := (show q ((α ^ n) g) ∈ B.map q from hBmap ▸ hqn)
  let z : N := ⟨(α ^ n) g * b⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((α ^ n) g * b⁻¹) = 1
    rw [map_mul, map_inv, hqb, mul_inv_cancel]⟩
  obtain ⟨m, hm⟩ := hCcover z
  have hmC := (mem_automorphismStage_iff _ _ _ _).mp hm
  have hmB : (((MulAut.characteristic N α) ^ m) z : G) ∈ B :=
    hCB ⟨_, hmC, rfl⟩
  have hbB := automorphism_pow_mem_of_stable α B hBstable m hb
  have he : (((MulAut.characteristic N α) ^ m) z : G) * (α ^ m) b =
      (α ^ (m + n)) g := by
    rw [characteristic_pow_apply]
    change (α ^ m) ((α ^ n) g * b⁻¹) * (α ^ m) b = _
    rw [map_mul, map_inv, inv_mul_cancel_right, pow_add, MulAut.mul_apply]
  exact ⟨m + n, (mem_automorphismStage_iff _ _ _ _).mpr (he ▸ B.mul_mem hmB hbB)⟩

theorem exists_fg_stable_lift
    (N : Subgroup G) [N.Characteristic] (α : MulAut G)
    (C : Subgroup N) (hCfg : C.FG)
    (hCstable : C.map (MulAut.characteristic N α).toMonoidHom ≤ C)
    (hCcover : ∀ g, ∃ n, g ∈ automorphismStage (MulAut.characteristic N α) C n)
    (P : Subgroup (G ⧸ N)) (hPfg : P.FG)
    (hPstable : P.map (characteristicQuotientAut N α).toMonoidHom ≤ P) :
    ∃ B : Subgroup G, B.FG ∧ B.map α.toMonoidHom ≤ B ∧
      B.map (QuotientGroup.mk' N) = P ∧ C.map N.subtype ≤ B := by
  classical
  let q := QuotientGroup.mk' N
  let γ := MulAut.characteristic N α
  obtain ⟨H, hHfg, hHmap⟩ := exists_fg_subgroup_map_eq q (QuotientGroup.mk'_surjective N) P hPfg
  obtain ⟨S, hS⟩ := hHfg
  have hsH (s : S) : (s : G) ∈ H := hS ▸ Subgroup.subset_closure s.property
  have herrors (s : S) : ∃ b : G, b ∈ H ∧ q b = q (α s) := by
    have hsP : q s ∈ P := hHmap ▸ (Subgroup.mem_map.mpr ⟨s, hsH s, rfl⟩)
    have hsα : q (α s) ∈ P := by
      change characteristicQuotientAut N α (q s) ∈ P
      exact hPstable ⟨_, hsP, rfl⟩
    exact (show q (α s) ∈ H.map q from hHmap ▸ hsα)
  choose lift hlift hliftq using herrors
  let err (s : S) : N := ⟨α s * (lift s)⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (α s * (lift s)⁻¹) = 1
    rw [map_mul, map_inv, hliftq, mul_inv_cancel]⟩
  obtain ⟨m, hm⟩ := finite_subset_subgroup_exhaustion (automorphismStage γ C)
    (automorphismStage_monotone γ C hCstable) hCcover (Finset.univ.image err)
  let K : Subgroup G := (automorphismStage γ C m).map N.subtype
  let B : Subgroup G := H ⊔ K
  have hKB : K ≤ B := le_sup_right
  have hHB : H ≤ B := le_sup_left
  have herrB (s : S) : (err s : G) ∈ B :=
    hKB ⟨err s, hm _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩), rfl⟩
  have hHstable : H.map α.toMonoidHom ≤ B := by
    apply Subgroup.map_le_iff_le_comap.mpr
    rw [← hS, Subgroup.closure_le]
    intro s hs
    change α s ∈ B
    have he : (err ⟨s, hs⟩ : G) * lift ⟨s, hs⟩ = α s := by
      dsimp [err]
      exact inv_mul_cancel_right _ _
    exact he ▸ B.mul_mem (herrB ⟨s, hs⟩) (hHB (hlift _))
  have hKstable : K.map α.toMonoidHom ≤ K := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨γ b, automorphismStage_stable γ C hCstable m ⟨b, hb, rfl⟩, rfl⟩
  have hBstable : B.map α.toMonoidHom ≤ B := by
    rw [Subgroup.map_sup]
    exact sup_le hHstable (hKstable.trans hKB)
  have hKker : K ≤ N := by
    rintro _ ⟨b, _, rfl⟩
    exact b.property
  have hHpre : H ≤ P.comap q := Subgroup.map_le_iff_le_comap.mp hHmap.le
  have hKpre : K ≤ P.comap q := by
    intro k hk
    change q k ∈ P
    have hkq : q k = 1 := (QuotientGroup.eq_one_iff k).mpr (hKker hk)
    rw [hkq]
    exact P.one_mem
  have hBmap : B.map q = P := le_antisymm
    (Subgroup.map_le_iff_le_comap.mpr (sup_le hHpre hKpre))
    (hHmap ▸ Subgroup.map_mono hHB)
  have hKfg : K.FG := fg_subgroup_map
    (fg_subgroup_map hCfg ((γ⁻¹) ^ m).toMonoidHom) N.subtype
  refine ⟨B, (show H.FG from ⟨S, hS⟩).sup hKfg, hBstable, hBmap, ?_⟩
  apply (Subgroup.map_mono ?_).trans hKB
  have hcm := automorphismStage_monotone γ C hCstable (Nat.zero_le m)
  simpa only [automorphismStage_zero] using hcm


theorem exists_fg_ascending_base_of_kernel_quotient
    (N : Subgroup G) [N.Characteristic] (α : MulAut G)
    (C : Subgroup N) (hCfg : C.FG)
    (hCstable : C.map (MulAut.characteristic N α).toMonoidHom ≤ C)
    (hCcover : ∀ g, ∃ n, g ∈ automorphismStage (MulAut.characteristic N α) C n)
    (P : Subgroup (G ⧸ N)) (hPfg : P.FG)
    (hPstable : P.map (characteristicQuotientAut N α).toMonoidHom ≤ P)
    (hPcover : ∀ g, ∃ n, g ∈ automorphismStage (characteristicQuotientAut N α) P n) :
    ∃ B : Subgroup G, B.FG ∧ B.map α.toMonoidHom ≤ B ∧
      ∀ g, ∃ n, g ∈ automorphismStage α B n := by
  obtain ⟨B, hBfg, hBstable, hBmap, hCB⟩ :=
    exists_fg_stable_lift N α C hCfg hCstable hCcover P hPfg hPstable
  exact ⟨B, hBfg, hBstable, automorphism_exhaustive_of_kernel_quotient
    N α C P B hCcover hPcover hBmap hCB hBstable⟩

end PolycyclicRecognition

end

end OAI
