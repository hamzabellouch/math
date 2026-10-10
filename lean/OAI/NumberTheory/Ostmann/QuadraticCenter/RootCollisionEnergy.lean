import OAI.NumberTheory.Ostmann.Preliminaries.CollisionIdentity
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorCollision

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open Preliminaries
open scoped BigOperators

def rootCollisionProbability (U : Finset ℕ) (p : ℕ) : ℝ :=
  congruenceCollisionEnergy p (fun a : U => a.val) (fun _ => (U.card:ℝ)⁻¹)

lemma rootUniformMass_sum (U : Finset ℕ) (hU : U.Nonempty) :
    (∑ _a : U,(U.card:ℝ)⁻¹) = 1 := by
  have hc : (U.card:ℝ)≠0 := by exact_mod_cast hU.card_pos.ne'
  simp [hc]

theorem rootCollisionProbability_ge_inv (U : Finset ℕ) (hU : U.Nonempty)
    (p : ℕ) [NeZero p] : (p:ℝ)⁻¹ ≤ rootCollisionProbability U p := by
  classical
  let μ := projectedMass (fun a : U => (a.val:ZMod p)) (fun _ => (U.card:ℝ)⁻¹)
  have hmass : ∑ x,μ x = 1 := by
    rw [projectedMass_sum]
    exact rootUniformMass_sum U hU
  have h := uniformDefect_nonneg (Finset.univ : Finset (ZMod p)) μ
  rw [uniformDefect_eq_energy_sub _ Finset.univ_nonempty _ hmass
    (by simp),Finset.card_univ,ZMod.card] at h
  rw [rootCollisionProbability,congruenceCollisionEnergy_eq_projected]
  exact sub_nonneg.mp h

theorem rootCollisionProbability_add_ge_four
    (U V : Finset ℕ) (hU : U.Nonempty) (hV : V.Nonempty)
    {p : ℕ} [Fact p.Prime] (c : ZMod p) (hc : c ≠ 0)
    (hdisj : ∀ a ∈ U,∀ b ∈ V,(a:ZMod p) ≠ c*(b:ZMod p)) :
    4/(p:ℝ) ≤ rootCollisionProbability U p+rootCollisionProbability V p := by
  classical
  let π : U → ZMod p := fun a => a.val
  let ρ : V → ZMod p := fun b => c*(b.val:ZMod p)
  let μ := projectedMass π (fun _ => (U.card:ℝ)⁻¹)
  let ν := projectedMass ρ (fun _ => (V.card:ℝ)⁻¹)
  let S : Finset (ZMod p) := Finset.univ.image π
  have hS : S.Nonempty := by
    obtain ⟨a,ha⟩ := hU
    exact ⟨π ⟨a,ha⟩,Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,rfl⟩⟩
  have hrho : ∀ b : V,ρ b ∈ Sᶜ := by
    intro b
    apply Finset.mem_compl.mpr
    intro h
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h
    exact hdisj a.val a.property b.val b.property he
  have hSc : Sᶜ.Nonempty := by
    obtain ⟨b,hb⟩ := hV
    exact ⟨ρ ⟨b,hb⟩,hrho ⟨b,hb⟩⟩
  have hμ : ∑ x,μ x = 1 := by rw [projectedMass_sum];exact rootUniformMass_sum U hU
  have hν : ∑ x,ν x = 1 := by rw [projectedMass_sum];exact rootUniformMass_sum V hV
  have hμS : ∀ x ∉ S,μ x = 0 := by
    intro x hx
    exact projectedMass_eq_zero π _ S
      (fun a _ => Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩) hx
  have hνS : ∀ x ∉ Sᶜ,ν x = 0 := by
    intro x hx
    exact projectedMass_eq_zero ρ _ Sᶜ (fun b _ => hrho b) hx
  have he := collision_stability_identity S hS hSc μ ν hμ hν hμS hνS
  obtain ⟨h1,h2,h3⟩ := collision_stability_terms_nonneg S hS hSc μ ν
  have hμE : massEnergy μ = rootCollisionProbability U p := by
    rw [rootCollisionProbability,congruenceCollisionEnergy_eq_projected]
  have hνE : massEnergy ν = rootCollisionProbability V p := by
    rw [projectedMass_energy]
    simp only [ρ,mul_right_inj' hc,rootCollisionProbability,congruenceCollisionEnergy]
  rw [hμE,hνE] at he
  linarith

end Ostmann.QuadraticCenter

end

end OAI
