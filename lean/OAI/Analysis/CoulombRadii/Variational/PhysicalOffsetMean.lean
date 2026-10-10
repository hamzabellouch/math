import Mathlib
import OAI.Analysis.CoulombRadii.Variational.PhysicalCoreMean
import OAI.Analysis.CoulombRadii.SpectralTheory.CorePredecessor

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace NeutralAtom

theorem zero_offset_physical_core_mean : ∃ t : ℝ,0<t ∧ ∃ Zmin : ℕ,∀ Z : ℕ,Zmin ≤ Z →
    ∀ (hZ : 1 ≤ Z) {N : ℕ} {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (_ : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      (Metric.ball (0:Position) (2*t)) ≤ (Z:ℝ)-1 := by
  obtain ⟨a,M,ha,hM,H⟩ := physical_propagated_core_mean
  obtain ⟨s₀,hs₀,H⟩ := H 0 (by norm_num)
  have ht : Tendsto (fun s : ℝ => s^3+M*s^12) (𝓝[>] 0) (𝓝 0) := by
    convert ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 3).add
      (((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 12).const_mul M) using 1 <;> simp
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0,0<s ∧ s<s₀ ∧ s^3+M*s^12<a :=
    (show ∀ᶠ s : ℝ in 𝓝[>] 0,0<s from self_mem_nhdsWithin).and (((gt_mem_nhds hs₀).filter_mono nhdsWithin_le_nhds).and (ht.eventually (gt_mem_nhds ha)))
  obtain ⟨s,hs,hss,hsa⟩ := hsmall.exists
  obtain ⟨Zmin,H⟩ := H s hs hss
  refine ⟨s/8,by positivity,Zmin,?_⟩
  intro Z hZm hZ N ψ g hd hn hmin E hE he hnum
  have HH := H Z hZm hZ hd hn hmin hE (by simpa only [add_zero] using he) hnum
  have hnum' : 1+M*s^9 ≤ a/s^3 := by
    apply (le_div_iff₀ (pow_pos hs 3)).mpr
    calc
      _=s^3+M*s^12 := by ring
      _≤a := hsa.le
  have heq : 2*(s/8)=s/4 := by ring
  rw [heq]
  linarith only [HH,hnum']

theorem predecessor_bound_from_attained_physical_state : ∃ D : ℝ,0 ≤ D ∧ ∃ Zmin : ℕ,
    ∀ Z : ℕ,Zmin ≤ Z → ∀ (hZ : 1 ≤ Z) {N : ℕ}
      {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (_ : FormDomain ψ g) (_ : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    (Coulomb.sectorFormBottom (Coulomb.atom Z hZ) (Z-1)).toReal ≤ E+D := by
  obtain ⟨t,ht,Zmin,HM⟩ := zero_offset_physical_core_mean
  obtain ⟨C,hC,HC⟩ := Coulomb.atomic_predecessor_from_physical_mean
  let D := fixedCoreMomentBound t*C*((Coulomb.screenMass 0 (t/4))^2/t+Coulomb.screenMass 0 t/t^2)
  have hD : 0 ≤ D := by
    dsimp [D]
    have hm := (fixedCoreMomentBound_pos t).le
    have hs := (Coulomb.screenMass_pos 0 t).le
    positivity
  refine ⟨D,hD,Zmin,?_⟩
  intro Z hZm hZ N ψ g hd hn hmin E hE he hnum
  let u := asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
  have hf : Coulomb.form (Coulomb.atom Z hZ) u=energy Z ψ g := asH1_energy Z hZ hd.2.1 hd.2.2.1 hd.2.2.2.1
  exact HC Z hZ u (asH1_antisymmetric hd)
    (by simpa only [u,asH1_mass] using hn) hE (hf.le.trans he) ht
    (HM Z hZm hZ hd hn hmin hE he hnum)
end NeutralAtom
end

end

end OAI
