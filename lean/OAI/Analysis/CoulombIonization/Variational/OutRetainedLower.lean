import Mathlib
import OAI.Analysis.CoulombIonization.Localization.ConditionalRetainedGap
import OAI.Analysis.CoulombIonization.ThomasFermi.OutCutAntisymmetry

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OutRetainedLower_scope

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombNeumann CoulombAnalysis

lemma out_retained_kinetic {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric (swapBlocks ψ))
    {b : ℝ} (hb : 0 < b)
    (S : Spins M → Configuration M → Finset (Fin M))
    (hS : ∀ t i, MeasurableSet {x | i ∈ S t x}) :
    tfKinetic*(∑ t : Spins M, ∫ x : Configuration M,
      retainedPressure b (S t x) x*formMass (coreSlice ψ t x)) ≤
      outKinetic ψ+b⁻¹^2*neumannRemainderConstant*((M:ℝ)^(4/3:ℝ)+(M:ℝ))*formMass ψ := by
  have hs (t : Spins M) (i : Fin M) : MeasurableSet {p : Configuration M × Configuration N | i ∈ S t p.1} :=
    measurable_fst (hS t i)
  have hh := ha.neumann_retained_slices (swapBlocks_sobolev hψ) hb
    (fun _ t p => S t p.1) (fun _ t i => hs t i)
  rw [weighted_coreSlice_reorder ψ (fun t x => retainedPressure b (S t x) x)
    (fun s t => retained_pressure_join_integrable (swapBlocks_sobolev hψ) hb
      (fun p => S s p.1) (hs s) s t),swapBlocks_coreKinetic,swapBlocks_mass] at hh
  exact hh

lemma out_retained_repulsion {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (ha : CoreAntisymmetric (swapBlocks ψ))
    {b : ℝ} (hb : 0 < b)
    (S : Spins M → Configuration M → Finset (Fin M))
    (hS : ∀ t i, MeasurableSet {x | i ∈ S t x}) :
    (∑ t : Spins M, ∫ x : Configuration M,
      retainedDirect b (S t x) x*formMass (coreSlice ψ t x)) ≤
      outRepulsion ψ+(((2*Real.pi+1)/2)*(M:ℝ)/b)*formMass ψ := by
  have hs (t : Spins M) (i : Fin M) : MeasurableSet {p : Configuration M × Configuration N | i ∈ S t p.1} :=
    measurable_fst (hS t i)
  have hh := ha.retained_repulsion_slices (swapBlocks_sobolev hψ) hb
    (fun _ t p => S t p.1) (fun _ t i => hs t i)
  rw [weighted_coreSlice_reorder ψ (fun t x => retainedDirect b (S t x) x)
    (fun s t => retained_direct_join_integrable (swapBlocks_sobolev hψ) hb
      (fun p => S s p.1) (hs s) s t),swapBlocks_coreRepulsion,swapBlocks_mass] at hh
  exact hh

abbrev OuterCutRetention (L : ℕ) := ∀ c : Fin L → Fin 2,
  Spins (cutOutNumber c) → Configuration (cutOutNumber c) → Finset (Fin (cutOutNumber c))

theorem fresh_cut_out_retained_kinetic {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a : Fin 2, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : OuterCutRetention L)
    (hS : ∀ c t i, MeasurableSet {x | i ∈ S c t x}) :
    tfKinetic*(∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ x,
      retainedPressure b (S c t x) x*formMass (coreSlice (orderedCutForm p hp ψ c) t x)) ≤
      (∑ c : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ c))+
        b⁻¹^2*neumannRemainderConstant*(∑ c : Fin L → Fin 2,
          ((cutOutNumber c:ℝ)^(4/3:ℝ)+(cutOutNumber c:ℝ))*formMass (orderedCutForm p hp ψ c)) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    out_retained_kinetic (orderedCutForm_sobolev p hp hψ.sobolevVector c)
      (orderedCutForm_out_antisymmetric p hp hψ c) hb (S c) (hS c))
  simpa only [Finset.sum_add_distrib,←Finset.mul_sum,mul_assoc] using hh

theorem fresh_cut_out_retained_repulsion {L : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a : Fin 2, (p a).value x^2 = 1) {ψ : FormVector L} (hψ : SobolevFermion ψ)
    {b : ℝ} (hb : 0 < b) (S : OuterCutRetention L)
    (hS : ∀ c t i, MeasurableSet {x | i ∈ S c t x}) :
    (∑ c : Fin L → Fin 2, ∑ t : Spins (cutOutNumber c), ∫ x,
      retainedDirect b (S c t x) x*formMass (coreSlice (orderedCutForm p hp ψ c) t x)) ≤
      (∑ c : Fin L → Fin 2, outRepulsion (orderedCutForm p hp ψ c))+
        (((2*Real.pi+1)/2)/b)*(∑ c : Fin L → Fin 2,
          (cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    out_retained_repulsion (orderedCutForm_sobolev p hp hψ.sobolevVector c)
      (orderedCutForm_out_antisymmetric p hp hψ c) hb (S c) (hS c))
  have he (c : Fin L → Fin 2) : (((2*Real.pi+1)/2)*(cutOutNumber c:ℝ)/b)*
      formMass (orderedCutForm p hp ψ c) = (((2*Real.pi+1)/2)/b)*
      ((cutOutNumber c:ℝ)*formMass (orderedCutForm p hp ψ c)) := by ring
  simpa only [Finset.sum_add_distrib,he,←Finset.mul_sum] using hh

end Work_OutRetainedLower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombNeumann

lemma integral_coreSlice_priceExcess {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ t : Spins M, ∫ u, corePriceExcess Z lam (coreSlice ψ t u)) =
      (∑ t : Spins M, ∫ u, formEnergy Z (coreSlice ψ t u)+
        lam*N*formMass (coreSlice ψ t u))-priceEnergy (energy Z) lam*formMass ψ := by
  have he (t : Spins M) : (∫ u, corePriceExcess Z lam (coreSlice ψ t u)) =
      (∫ u, formEnergy Z (coreSlice ψ t u)+lam*N*formMass (coreSlice ψ t u))-
        priceEnergy (energy Z) lam*(∫ u, formMass (coreSlice ψ t u)) := by
    unfold corePriceExcess
    have he := integral_sub ((hψ.coreSlice_energy_integrable Z t).add
      ((hψ.coreSlice_mass_integrable t).const_mul (lam*N)))
      ((hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam))
    simp only [Pi.add_apply,integral_const_mul] at he
    exact he
  simp_rw [he]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,hψ.integral_coreSlice_mass]

lemma priced_core_excess_identity {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    formEnergy Z ψ+lam*(N+M)*formMass ψ-priceEnergy (energy Z) lam*formMass ψ =
      (∑ t : Spins M, ∫ u, corePriceExcess Z lam (coreSlice ψ t u))+
      outKinetic ψ-(∑ t : Spins M, ∫ u, conditionalFieldSum Z lam ψ t u)+outRepulsion ψ := by
  rw [integral_coreSlice_priceExcess hψ Z lam,priced_conditional_energy_identity hψ Z lam]
  ring

theorem integrated_conditional_patch_budget {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (hc : CoreAntisymmetric ψ)
    (ho : CoreAntisymmetric (swapBlocks ψ)) (y : Space) {R : ℝ} (hR : 0 < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hr : IsRadial g)
    (hgs : tsupport g ⊆ ball 0 1) {b : ℝ} (hb : 0 < b)
    (A : Set Space) (hcore : ∀ t u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hsep : Disjoint A (packetRegion (scaledRealPacket b g) (closedBall y R)))
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hcs : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖)
    (S : Spins M → Configuration M → Finset (Fin M))
    (hS : ∀ t i, MeasurableSet {u | i ∈ S t u})
    (hmargin : ∀ t u, ∀ i ∈ S t u, ‖u i-y‖+Real.sqrt 3*b ≤ R)
    (hret_nuc : ∀ t u, ∀ i ∈ S t u, Real.sqrt 3*b ≤ ‖u i‖)
    (hret_core : ∀ t u, ∀ i ∈ S t u, ∀ a ∈ A, Real.sqrt 3*b ≤ ‖a-u i‖) :
    (∑ t : Spins M, ∫ u, weightedPatchGap ψ t Z lam y R hb (S t) u) ≤
      formEnergy Z ψ+lam*(N+M)*formMass ψ-priceEnergy (energy Z) lam*formMass ψ+
        b⁻¹^2*neumannRemainderConstant*((M:ℝ)^(4/3:ℝ)+(M:ℝ))*formMass ψ+
        (((2*Real.pi+1)/2)*(M:ℝ)/b)*formMass ψ+
        (∑ t : Spins M, ∫ u, conditionalFieldSum Z lam ψ t u-
          conditionalRetainedFieldSum Z lam ψ t (S t) u+
          ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass ψ t Z lam y R u) := by
  have hmass (t : Spins M) := weightedPatchMass_integrable hψ t y hR Z lam hb A (hcore t) hnuc hcs
  have hgap (t : Spins M) := weightedPatchGap_integrable hψ hc t y hR hZ hlam hg hcg hgn hr hgs
    hb A (hcore t) hsep hnuc hcs (S t) (hS t) (hmargin t) (hret_nuc t) (hret_core t)
  have hexc (t : Spins M) := coreSlice_priceExcess_integrable hψ t Z lam
  have hpress (t : Spins M) := retained_pressure_weighted_integrable hψ hb t (S t) (hS t)
  have hfield (t : Spins M) := conditionalRetainedFieldSum_integrable hψ Z lam t (S t) (hS t)
  have hdirect (t : Spins M) := retained_direct_weighted_integrable hψ hb t (S t) (hS t)
  have ht (t : Spins M) : (∫ u, weightedPatchGap ψ t Z lam y R hb (S t) u) ≤
      (∫ u, corePriceExcess Z lam (coreSlice ψ t u))+
        tfKinetic*(∫ u, retainedPressure b (S t u) u*formMass (coreSlice ψ t u))-
        (∫ u, conditionalRetainedFieldSum Z lam ψ t (S t) u)+
        (∫ u, retainedDirect b (S t u) u*formMass (coreSlice ψ t u))+
        ((packetDirichlet g/2)*b⁻¹^2)*(∫ u, weightedPatchMass ψ t Z lam y R u) := by
    have h1 := (hexc t).add ((hpress t).const_mul tfKinetic)
    have h2 := h1.sub (hfield t)
    have h3 := h2.add (hdirect t)
    have h4 := (hmass t).const_mul ((packetDirichlet g/2)*b⁻¹^2)
    have ht := integral_mono_ae (hgap t) (h3.add h4)
      (conditionalPatchGap_upper hψ hc t y R hZ hlam hg hcg hgn hr hgs hb A
        (hcore t) hsep hnuc hcs (S t) (hmargin t) (hret_nuc t) (hret_core t))
    have e1 := integral_add (hexc t) ((hpress t).const_mul tfKinetic)
    have e2 := integral_sub h1 (hfield t)
    have e3 := integral_add h2 (hdirect t)
    have e4 := integral_add h3 h4
    simp only [Pi.add_apply,Pi.sub_apply,integral_const_mul] at ht e1 e2 e3 e4
    rwa [e4,e3,e2,e1] at ht
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ => ht t)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hs
  have hk := out_retained_kinetic hψ ho hb S hS
  have hrp := out_retained_repulsion hψ ho hb S hS
  have hid := priced_core_excess_identity hψ Z lam
  have herr (t : Spins M) : (∫ u, conditionalFieldSum Z lam ψ t u-
      conditionalRetainedFieldSum Z lam ψ t (S t) u+
      ((packetDirichlet g/2)*b⁻¹^2)*weightedPatchMass ψ t Z lam y R u) =
      (∫ u, conditionalFieldSum Z lam ψ t u)-
      (∫ u, conditionalRetainedFieldSum Z lam ψ t (S t) u)+
      ((packetDirichlet g/2)*b⁻¹^2)*(∫ u, weightedPatchMass ψ t Z lam y R u) := by
    have e1 := integral_sub (conditionalFieldSum_integrable hψ Z lam t) (hfield t)
    have e2 := integral_add ((conditionalFieldSum_integrable hψ Z lam t).sub (hfield t))
      ((hmass t).const_mul ((packetDirichlet g/2)*b⁻¹^2))
    simp only [Pi.sub_apply,integral_const_mul] at e2
    rw [e2,e1]
  simp_rw [herr]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
  linarith

end CoulombAtom

end

end OAI
