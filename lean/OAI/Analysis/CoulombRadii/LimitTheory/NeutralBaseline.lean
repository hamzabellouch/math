import Mathlib
import OAI.Analysis.CoulombRadii.SpectralTheory.GlobalSectorMinimum
import OAI.Analysis.CoulombRadii.Variational.PhysicalOffsetMean

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace NeutralAtom

theorem physical_uniform_predecessor_offset : ∃ D:ℝ,0≤D ∧ ∃ Zmin:ℕ,
    ∀ Z:ℕ,Zmin≤Z → ∀ hZ:1≤Z,
    (Coulomb.sectorFormBottom (Coulomb.atom Z hZ) (Z-1)).toReal ≤
      (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal+D := by
  obtain ⟨D,hD,Zmin,H⟩:=predecessor_bound_from_attained_physical_state
  refine ⟨D,hD,Zmin,?_⟩
  intro Z hZm hZ
  obtain ⟨n,hn,hnb,u,ha,hm,he⟩:=Coulomb.atom_global_sector_minimum Z hZ
  obtain ⟨N,hN⟩:=Nat.exists_eq_add_of_le hn
  have hn' : n=N+1 := by omega
  clear hN
  subst n
  have hr:Coulomb.form (Coulomb.atom Z hZ) u=
      (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal := by
    rw [←he,EReal.toReal_coe]
  apply H Z hZm hZ (N:=N) (ψ:=fromH1Wave u) (g:=fromH1Gradient u)
    (fromH1_domain u ha) ((fromH1_mass u).trans hm)
  · intro χ g hd hnorm
    rw [fromH1_energy Z hZ]
    have HH:=Coulomb.unrestrictedFormBottom_le_trial (Coulomb.atom Z hZ)
      (asH1 χ g hd.2.1 hd.2.2.1 hd.2.2.2.1) (asH1_antisymmetric hd)
      ((asH1_mass ..).trans hnorm)
    rw [←he,asH1_energy Z hZ] at HH
    exact EReal.coe_le_coe_iff.mp HH
  · exact (Coulomb.atom_unrestricted_bottom_real Z hZ u ha hm).le
  · rw [fromH1_energy Z hZ,hr]
  · exact_mod_cast hnb

theorem physical_neutral_energy_offset : ∃ D:ℝ,0≤D ∧ ∃ Zmin:ℕ,
    ∀ Z:ℕ,Zmin≤Z → ∀ hZ:1≤Z,
    ∀ {ψ:Wavefunction Z} {g:Gradient Z},FormDomain ψ g → normSquared ψ=1 →
    (∀ (χ:Wavefunction Z) (h:Gradient Z),FormDomain χ h → normSquared χ=1 → energy Z ψ g≤energy Z χ h) →
    energy Z ψ g ≤ (Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ)).toReal+D := by
  obtain ⟨D,hD,Zmin,H⟩:=physical_uniform_predecessor_offset
  refine ⟨D,hD,Zmin,?_⟩
  intro Z hZm hZ ψ g hd hn hmin
  have he:(energy Z ψ g:EReal)=Coulomb.sectorFormBottom (Coulomb.atom Z hZ) Z := by
    rw [←sectorEnergy_eq_formBottom Z hZ]
    apply le_antisymm
    · apply le_sInf
      rintro e ⟨χ,h,hχ,hm,rfl⟩
      exact EReal.coe_le_coe_iff.mpr (hmin χ h hχ hm)
    · exact sectorEnergy_le_trial hd hn
  have hle:Coulomb.sectorFormBottom (Coulomb.atom Z hZ) Z ≤
      Coulomb.sectorFormBottom (Coulomb.atom Z hZ) (Z-1):=
    Coulomb.atom_sectorFormBottom_antitone Z hZ (Nat.sub_le ..)
  have hr:=Coulomb.atom_sectorFormBottom_real Z hZ (Z-1)
  rw [←he,←hr] at hle
  exact (EReal.coe_le_coe_iff.mp hle).trans (H Z hZm hZ)
end NeutralAtom
end

end

end OAI
