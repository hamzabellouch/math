import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SpatialProductFactor
import OAI.Analysis.CoulombIonization.Variational.OutRetainedLower

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma fresh_cut_total_excess_identity {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ c : Fin L → Fin 2, corePriceExcess Z lam (orderedCutForm p hp ψ c)) =
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p) := by
  have hn (c : Fin L → Fin 2) : ((cutCoreNumber c+cutOutNumber c:ℕ):ℝ) = L := by
    exact_mod_cast cutNumbers_sum c
  simp_rw [corePriceExcess,hn,orderedCutForm_energy,orderedCutForm_mass]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    spatial_cut_mass p hp hψ,spatial_cut_ims p hp hψ Z]
  unfold weightedParticleCount
  ring

theorem fresh_cut_patch_budget {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevFermion ψ) (y : Space) {R : ℝ} (hR : 0 < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space)
    (hv : ∀ x ∉ A, (p 0).value x = 0)
    (hd : ∀ x ∉ A, ∀ a, lineDeriv ℝ (p 0).value x (spaceDirections a) = 0)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : OuterCutRetention L)
    (hS : ∀ c t i, MeasurableSet {u | i ∈ S c t u})
    (hmargin : ∀ c t u, ∀ i ∈ S c t u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ c t u, ∀ i ∈ S c t u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ c t u, ∀ i ∈ S c t u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
      weightedPatchGap (orderedCutForm p hp ψ c) t Z lam y R hb (S c t) u) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        b⁻¹^2*neumannRemainderConstant*(∑ c : Fin L → Fin 2,
          ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*formMass (orderedCutForm p hp ψ c))+
        (((2*Real.pi+1)/2)/b)*(∑ c : Fin L → Fin 2,
          (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c))+
        (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) t u-
          conditionalRetainedFieldSum Z lam (orderedCutForm p hp ψ c) t (S c t) u+
          ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass (orderedCutForm p hp ψ c) t Z lam y R u) := by
  have hc (c : Fin L → Fin 2) (t : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (x : Configuration (cutCoreNumber c))
      (i : Fin (cutCoreNumber c)) (hi : x i ∉ A) :
      FormZeroAt (coreSlice (orderedCutForm p hp ψ c) t u) x := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole p hp ψ c Aᶜ hv hd (joinLists x u) i
      (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbr (c : Fin L → Fin 2) := integrated_conditional_patch_budget
    (orderedCutForm_sobolev p hp hψ.sobolevVector c)
    (orderedCutForm_core_antisymmetric p hp hψ c)
    (orderedCutForm_out_antisymmetric p hp hψ c) y hR hZ hlam hg hcg hgn hr hgs hb A
    (hc c) hsep hnuc hcs (S c) (hS c) (hmargin c) (hret_nuc c) (hret_core c)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hbr c)
  have he (c : Fin L → Fin 2) :
      formEnergy Z (orderedCutForm p hp ψ c)+lam*((cutCoreNumber c:ℝ)+cutOutNumber c)*
        formMass (orderedCutForm p hp ψ c)-priceEnergy (energy Z) lam*formMass (orderedCutForm p hp ψ c) =
      corePriceExcess Z lam (orderedCutForm p hp ψ c) := by
    simp only [corePriceExcess,Nat.cast_add]
  have hd (c : Fin L → Fin 2) : (((2*Real.pi+1)/2)*(cutOutNumber c:ℝ)/b)*
      formMass (orderedCutForm p hp ψ c) =
      (((2*Real.pi+1)/2)/b)*((cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) := by ring
  simp only [he] at hh
  simp only [hd,Finset.sum_add_distrib,mul_assoc,←Finset.mul_sum] at hh
  rw [fresh_cut_total_excess_identity p hp hψ.sobolevVector Z lam] at hh
  simpa only [mul_assoc] using hh

end CoulombAtom

end

end OAI
