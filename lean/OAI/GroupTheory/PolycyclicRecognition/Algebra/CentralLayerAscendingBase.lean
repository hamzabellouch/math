import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingBaseLifting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralJoinLowerCentral
import OAI.GroupTheory.PolycyclicRecognition.Algebra.LowerCentralExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-! # A stable base in a central lower-central term

Commutators of a finitely generated lift provide the kernel base. Central
errors disappear in positive lower-central terms, while the quotient
exhaustion ensures that these commutators exhaust the actual kernel.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem exists_ascending_base_in_central_lowerCentral
    (N : Subgroup G) [N.Characteristic] (k : ℕ)
    (hN : N = (⊤ : Subgroup G).lowerCentralSeries (k + 1))
    (hcentral : N ≤ Subgroup.center G) (α : MulAut G)
    (P : Subgroup (G ⧸ N)) (hPfg : P.FG)
    (hPstable : P.map (characteristicQuotientAut N α).toMonoidHom ≤ P)
    (hPcover : ∀ g, ∃ n, g ∈ automorphismStage (characteristicQuotientAut N α) P n) :
    ∃ C : Subgroup N, C.FG ∧ C.map (MulAut.characteristic N α).toMonoidHom ≤ C ∧
      ∀ g, ∃ n, g ∈ automorphismStage (MulAut.characteristic N α) C n := by
  let q := QuotientGroup.mk' N
  let γ := MulAut.characteristic N α
  obtain ⟨H, hHfg, hHmap⟩ := exists_fg_subgroup_map_eq q (QuotientGroup.mk'_surjective N) P hPfg
  have hpre : P.comap q = H ⊔ N := by
    rw [← hHmap, Subgroup.comap_map_eq]
    change H ⊔ (QuotientGroup.mk' N).ker = H ⊔ N
    rw [QuotientGroup.ker_mk']
  have hHmod : H.map α.toMonoidHom ≤ H ⊔ N := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← hpre]
    change q (α g) ∈ P
    exact hPstable ⟨q g, hHmap ▸ Subgroup.mem_map.mpr ⟨g, hg, rfl⟩, rfl⟩
  let K := H.lowerCentralSeries (k + 1)
  have hKN : K ≤ N := by
    rw [hN]
    exact Subgroup.lowerCentralSeries_mono _ le_top
  have hKstable : K.map α.toMonoidHom ≤ K := by
    change (H.lowerCentralSeries (k + 1)).map α.toMonoidHom ≤ H.lowerCentralSeries (k + 1)
    rw [Subgroup.map_lowerCentralSeries]
    exact (Subgroup.lowerCentralSeries_mono _ hHmod).trans
      (lowerCentralSeries_sup_central H N hcentral k).le
  let C := K.subgroupOf N
  have hCstable : C.map γ.toMonoidHom ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    exact hKstable ⟨(g : G), hg, rfl⟩
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr hHfg
  let : Group.FG (K.subgroupOf H) := CriticalPercolation.nilpotent_subgroup_fg H _
  let eKH := Subgroup.subgroupOfEquivOfLe (H.lowerCentralSeries_le_self (k + 1))
  let : Group.FG K := Group.fg_of_surjective (f := eKH.toMonoidHom) eKH.surjective
  let eKN := (Subgroup.subgroupOfEquivOfLe hKN).symm
  let : Group.FG C := Group.fg_of_surjective (f := eKN.toMonoidHom) eKN.surjective
  refine ⟨C, (Group.fg_iff_subgroup_fg C).mp inferInstance, hCstable, ?_⟩
  have hSstable : (H ⊔ N).map α.toMonoidHom ≤ H ⊔ N := by
    rw [Subgroup.map_sup]
    apply sup_le hHmod
    exact (Subgroup.characteristic_iff_map_eq.mp inferInstance α).le.trans le_sup_right
  have hScover (g : G) : ∃ n, g ∈ automorphismStage α (H ⊔ N) n := by
    obtain ⟨n, hn⟩ := hPcover (q g)
    refine ⟨n, (mem_automorphismStage_iff _ _ _ _).mpr ?_⟩
    rw [← hpre]
    change q ((α ^ n) g) ∈ P
    rw [← characteristicQuotient_pow_mk]
    exact (mem_automorphismStage_iff _ _ _ _).mp hn
  have hterms (n : ℕ) :
      (automorphismStage α (H ⊔ N) n).lowerCentralSeries (k + 1) =
        automorphismStage α K n := by
    change ((H ⊔ N).map ((α⁻¹) ^ n).toMonoidHom).lowerCentralSeries (k + 1) = _
    rw [← Subgroup.map_lowerCentralSeries, lowerCentralSeries_sup_central H N hcentral k]
    rfl
  intro g
  have hg : (g : G) ∈ (⊤ : Subgroup G).lowerCentralSeries (k + 1) := hN ▸ g.property
  obtain ⟨n, hn⟩ := lowerCentral_element_in_exhaustion (automorphismStage α (H ⊔ N))
    (automorphismStage_monotone α (H ⊔ N) hSstable) hScover (k + 1) g hg
  rw [hterms] at hn
  refine ⟨n, (mem_automorphismStage_iff _ _ _ _).mpr ?_⟩
  change ((γ ^ n) g : G) ∈ K
  rw [characteristic_pow_apply]
  exact (mem_automorphismStage_iff _ _ _ _).mp hn

theorem exists_ascending_base_of_central_lowerCentral_quotient
    (N : Subgroup G) [N.Characteristic] (k : ℕ)
    (hN : N = (⊤ : Subgroup G).lowerCentralSeries (k + 1))
    (hcentral : N ≤ Subgroup.center G) (α : MulAut G)
    (P : Subgroup (G ⧸ N)) (hPfg : P.FG)
    (hPstable : P.map (characteristicQuotientAut N α).toMonoidHom ≤ P)
    (hPcover : ∀ g, ∃ n, g ∈ automorphismStage (characteristicQuotientAut N α) P n) :
    ∃ B : Subgroup G, B.FG ∧ B.map α.toMonoidHom ≤ B ∧
      ∀ g, ∃ n, g ∈ automorphismStage α B n := by
  obtain ⟨C, hCfg, hCstable, hCcover⟩ :=
    exists_ascending_base_in_central_lowerCentral N k hN hcentral α P hPfg hPstable hPcover
  exact exists_fg_ascending_base_of_kernel_quotient
    N α C hCfg hCstable hCcover P hPfg hPstable hPcover

end PolycyclicRecognition

end

end OAI
