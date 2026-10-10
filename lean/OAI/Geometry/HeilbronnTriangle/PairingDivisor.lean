import Mathlib

namespace OAI


namespace Problem355.PairingDivisor

variable {ι : Type*} [Fintype ι]

def dotHom (x : ι → ℤ) : (ι → ℤ) →+ ℤ :=
  (dotProductBilin ℤ ℤ x).toAddMonoidHom

@[simp] theorem dotHom_apply (x v : ι → ℤ) : dotHom x v = dotProduct x v := rfl

theorem exists_pairing_divisor
    (L : AddSubgroup (ι → ℤ)) (x z : ι → ℤ) (hprimitive : dotProduct x z = 1)
    (E : ℕ) (hE : 0 < E) (hcontain : ∀ v : ι → ℤ, E • v ∈ L) :
    ∃ g : ℕ, 0 < g ∧ g ∣ E ∧
      L.map (dotHom x) = AddSubgroup.zmultiples (g : ℤ) ∧
      (∀ v ∈ L, (g : ℤ) ∣ dotProduct x v) ∧
      ∃ u ∈ L, dotProduct x u = (g : ℤ) := by
  have hEimage : (E : ℤ) ∈ L.map (dotHom x) := by
    apply AddSubgroup.mem_map.mpr
    refine ⟨E • z, hcontain z, ?_⟩
    change dotProduct x (E • z) = (E : ℤ)
    rw [dotProduct_smul, hprimitive]
    simp
  obtain ⟨a, ha⟩ :=
    (L.map (dotHom x)).isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
  have ha0 : a ≠ 0 := by
    intro hz
    have hbad := hEimage
    rw [← ha, hz] at hbad
    have heq : (E : ℤ) = 0 := by simpa using hbad
    exact (Nat.ne_of_gt hE) (by exact_mod_cast heq)
  have hmap : L.map (dotHom x) = AddSubgroup.zmultiples (a.natAbs : ℤ) :=
    ((Int.zmultiples_natAbs a).trans ha).symm
  have hdivE : (a.natAbs : ℤ) ∣ (E : ℤ) := by
    apply Int.mem_zmultiples_iff.mp
    rw [← hmap]
    exact hEimage
  refine ⟨a.natAbs, Int.natAbs_pos.mpr ha0, by exact_mod_cast hdivE, hmap, ?_, ?_⟩
  · intro v hv
    apply Int.mem_zmultiples_iff.mp
    rw [← hmap]
    exact AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩
  · have hgmem : (a.natAbs : ℤ) ∈ L.map (dotHom x) := by
      rw [hmap]
      exact AddSubgroup.mem_zmultiples _
    obtain ⟨u, hu, heq⟩ := AddSubgroup.mem_map.mp hgmem
    exact ⟨u, hu, heq⟩

theorem integer_subgroup_eq_zmultiples_index (H : AddSubgroup ℤ) :
    H = AddSubgroup.zmultiples (H.index : ℤ) := by
  obtain ⟨a, ha⟩ := H.isAddCyclic_iff_exists_zmultiples_eq_top.mp inferInstance
  have hindex : H.index = a.natAbs := by rw [← ha, Int.index_zmultiples]
  rw [hindex, Int.zmultiples_natAbs]
  exact ha.symm

noncomputable def pairingDivisor (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) : ℕ :=
  (L.map (dotHom x)).index

theorem pairing_image (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) :
    L.map (dotHom x) = AddSubgroup.zmultiples (pairingDivisor L x : ℤ) :=
  integer_subgroup_eq_zmultiples_index _

theorem pairingDivisor_dvd_pairing (L : AddSubgroup (ι → ℤ)) (x v : ι → ℤ)
    (hv : v ∈ L) : (pairingDivisor L x : ℤ) ∣ dotProduct x v := by
  apply Int.mem_zmultiples_iff.mp
  rw [← pairing_image]
  exact AddSubgroup.mem_map.mpr ⟨v, hv, rfl⟩

theorem exists_pairing_eq_divisor (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) :
    ∃ u ∈ L, dotProduct x u = (pairingDivisor L x : ℤ) := by
  have hgmem : (pairingDivisor L x : ℤ) ∈ L.map (dotHom x) := by
    rw [pairing_image]
    exact AddSubgroup.mem_zmultiples _
  exact AddSubgroup.mem_map.mp hgmem

theorem dvd_pairingDivisor_iff (L : AddSubgroup (ι → ℤ)) (x : ι → ℤ) (d : ℕ) :
    d ∣ pairingDivisor L x ↔ ∀ v ∈ L, (d : ℤ) ∣ dotProduct x v := by
  constructor
  · intro hd v hv
    have hdInt : (d : ℤ) ∣ (pairingDivisor L x : ℤ) := by exact_mod_cast hd
    exact hdInt.trans (pairingDivisor_dvd_pairing L x v hv)
  · intro hd
    obtain ⟨u, hu, heq⟩ := exists_pairing_eq_divisor L x
    have h := hd u hu
    rw [heq] at h
    exact_mod_cast h

theorem pairingDivisor_pos_and_dvd
    (L : AddSubgroup (ι → ℤ)) (x z : ι → ℤ) (hprimitive : dotProduct x z = 1)
    (E : ℕ) (hE : 0 < E) (hcontain : ∀ v : ι → ℤ, E • v ∈ L) :
    0 < pairingDivisor L x ∧ pairingDivisor L x ∣ E := by
  obtain ⟨g, hg, hdiv, himage, _, _⟩ :=
    exists_pairing_divisor L x z hprimitive E hE hcontain
  have heq : pairingDivisor L x = g := by
    unfold pairingDivisor
    rw [himage, Int.index_zmultiples, Int.natAbs_natCast]
  exact heq.symm ▸ ⟨hg, hdiv⟩

end Problem355.PairingDivisor

end OAI
