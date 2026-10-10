import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.RawThomasFermiEnergy
import OAI.Analysis.CoulombRadii.FieldAnalysis.AtomicStability
import OAI.Analysis.CoulombRadii.Variational.PhysicalBridge
import OAI.Analysis.CoulombRadii.FormDomain.ParticleGradientNorm

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem sectorEnergy_eq_formBottom (Z : ℕ) (hZ : 1≤Z) (n : ℕ) :
    sectorEnergy Z n=Coulomb.sectorFormBottom (Coulomb.atom Z hZ) n := by
  apply le_antisymm
  · apply le_sInf
    rintro e ⟨u,ha,hm,rfl⟩
    have H := sectorEnergy_le_trial (Z:=Z) (fromH1_domain u ha) ((fromH1_mass u).trans hm)
    rwa [fromH1_energy Z hZ] at H
  · apply le_sInf
    rintro e ⟨ψ,g,hd,hn,rfl⟩
    let u := asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    have H : Coulomb.sectorFormBottom (Coulomb.atom Z hZ) n≤
        (Coulomb.form (Coulomb.atom Z hZ) u:EReal) :=
      sInf_le ⟨u,asH1_antisymmetric hd,(asH1_mass ..).trans hn,rfl⟩
    rwa [asH1_energy Z hZ] at H

lemma unrestrictedEnergy_eq_formBottom (Z : ℕ) (hZ : 1≤Z) :
    unrestrictedEnergy Z=Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) := by
  simp only [unrestrictedEnergy,Coulomb.unrestrictedFormBottom,sectorEnergy_eq_formBottom Z hZ]

end NeutralAtom
namespace Coulomb
lemma atom_sectorFormBottom_antitone (Z : ℕ) (hZ : 1≤Z) :
    Antitone (sectorFormBottom (atom Z hZ)) := by
  intro a b hab
  rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ,←NeutralAtom.sectorEnergy_eq_formBottom Z hZ]
  exact NeutralAtom.sectorEnergy_antitone Z hab

lemma atom_sectorFormBottom_real (Z : ℕ) (hZ : 1≤Z) (n : ℕ) :
    ((sectorFormBottom (atom Z hZ) n).toReal:EReal)=sectorFormBottom (atom Z hZ) n := by
  apply EReal.coe_toReal
  · intro he
    have H : sectorFormBottom (atom Z hZ) n≤0 := by
      rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ]
      exact NeutralAtom.sectorEnergy_nonpos Z n
    rw [he] at H
    exact EReal.coe_ne_top (0:ℝ) (by simpa using top_le_iff.mp H)
  · intro he
    have H := (atom_unrestricted_bottom_lower Z hZ).trans
      (iInf_le (fun k => sectorFormBottom (atom Z hZ) k) n)
    rw [he] at H
    exact EReal.coe_ne_bot _ (le_bot_iff.mp H)

lemma slice_core_form_ge_sector {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {P : ℝ} (hP : (P:EReal)≤ sectorFormBottom S k) :
    P*mass u≤ sliceExpectation u (fun s x => form S (u.coreSlice s x).normalized) := by
  rw [←sliceExpectation_number u P]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) P] using (mass_coreSlice_integrable u s).const_mul P)
    (normalized_coreForm_weight_integrable S u s)
  filter_upwards [ha s] with x hx
  by_cases hz : mass (u.coreSlice s x)=0
  · simp [hz]
  · have hp := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact EReal.coe_le_coe_iff.mp (hP.trans (sInf_le
      ⟨(u.coreSlice s x).normalized,hx.normalized,mass_normalized _ hp,rfl⟩))

end Coulomb

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
namespace Coulomb
lemma atom_sector_trial_approx (Z:ℕ) (hZ:1 ≤ Z) (n:ℕ) (E:ℝ)
    (hE:(E:EReal)=sectorFormBottom (atom Z hZ) n) {ε:ℝ} (hε:0<ε) :
    ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧ form (atom Z hZ) u<E+ε := by
  have hh:sectorFormBottom (atom Z hZ) n<(E+ε:EReal) := by
    rw [←hE]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  obtain ⟨e,he,helt⟩:=sInf_lt_iff.mp hh
  obtain ⟨u,ha,hm,rfl⟩:=he
  exact ⟨u,ha,hm,EReal.coe_lt_coe_iff.mp helt⟩

lemma kinetic_bound_of_form_bound {M n:ℕ} (S:Nuclei M) (u:H1Vector n) :
    kinetic u ≤ 2*form S u+8*(n:ℝ)*(totalCharge S)^2*mass u := by
  let η:ℝ:=1/(16*totalCharge S)
  have hZ:=totalCharge_pos S
  have hη:0<η := by dsimp [η]; positivity
  have H:=nuclearEnergy_bound S u hη
  have h1:8*η*totalCharge S=(1/2:ℝ) := by dsimp [η]; field_simp; ring
  have h2:(n:ℝ)*totalCharge S/(4*η)=4*(n:ℝ)*(totalCharge S)^2 := by dsimp [η]; field_simp; ring
  rw [h1,h2] at H
  have hp:=pairEnergy_nonneg u
  unfold form
  linarith

lemma atom_normalized_form_ge_bottom (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ} (u:H1Vector n)
    (ha:Antisymmetric u) (hm:mass u=1) (E:ℝ) (hE:(E:EReal) ≤ sectorFormBottom (atom Z hZ) n) :
    E ≤ form (atom Z hZ) u :=
  EReal.coe_le_coe_iff.mp (hE.trans (sInf_le ⟨u,ha,hm,rfl⟩))

lemma atom_minimizing_sequence (Z:ℕ) (hZ:1 ≤ Z) (n:ℕ) (E:ℝ)
    (hE:(E:EReal)=sectorFormBottom (atom Z hZ) n) :
    ∃ u:ℕ → H1Vector n,(∀ k,Antisymmetric (u k)) ∧ (∀ k,mass (u k)=1) ∧
      (∀ k,kinetic (u k) ≤ 2*(E+1)+8*(n:ℝ)*(Z:ℝ)^2) ∧
      Tendsto (fun k => form (atom Z hZ) (u k)) atTop (𝓝 E) := by
  choose u ha hm hf using fun k:ℕ => atom_sector_trial_approx Z hZ n E hE (show 0<(1:ℝ)/(k+1) by positivity)
  refine ⟨u,ha,hm,?_,?_⟩
  · intro k
    have H:=kinetic_bound_of_form_bound (atom Z hZ) (u k)
    have htotal:totalCharge (atom Z hZ)=(Z:ℝ) := by simp [totalCharge,atom]
    rw [hm k,htotal,mul_one] at H
    have hsmall:(1:ℝ)/(k+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) k])
    linarith [hf k]
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun k:ℕ => E+1/((k:ℝ)+1)) atTop (𝓝 E) from by
        simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)))
    · intro k; exact atom_normalized_form_ge_bottom Z hZ (u k) (ha k) (hm k) E hE.le
    · exact fun k => (hf k).le
end Coulomb

end

end OAI
