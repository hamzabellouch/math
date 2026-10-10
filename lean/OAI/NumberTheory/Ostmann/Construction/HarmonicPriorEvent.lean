import OAI.NumberTheory.Ostmann.Construction.BroadBandBalance

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

theorem harmonicPrimeSource_event_mean (P : Finset ℕ) (hP : ∀p∈P,p.Prime)
    (hZ : 0<harmonicPrimeMass P) (B : ℕ → Prop) [DecidablePred B] :
    (harmonicPrimeSource P hP hZ).law.mean (fun p => if B (p:ℕ) then 1 else 0)=
      harmonicPrimeMass (P.filter B)/harmonicPrimeMass P := by
  change (∑p:↥P,((1:ℝ)/(p:ℕ))/(∑q:↥P,(1:ℝ)/(q:ℕ))*(if B (p:ℕ) then 1 else 0))=_
  have hsum : (∑q:↥P,(1:ℝ)/(q:ℕ))=harmonicPrimeMass P := by
    simpa only [harmonicPrimeMass] using (Finset.sum_coe_sort P (fun q : ℕ => (1:ℝ)/q))
  rw [hsum]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  have h := Finset.sum_coe_sort P (fun p : ℕ => if B p then (1:ℝ)/p else 0)
  simpa only [harmonicPrimeMass,Finset.sum_filter,mul_ite,mul_one,mul_zero,ite_div,zero_div] using h

theorem broadBand_balanced_prior_eventually (d : Decomposition) {α β : ℝ}
    (hα : 0≤α) (hαβ : α<β) (hβ : β≤(9/10:ℝ)) :
    ∀ᶠ L : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      ∃ hZ : 0<harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E),
        (1/2:ℝ)≤(harmonicPrimeSource (logLogPrimeBand (α*L) (β*L) \ E)
          (fun _p hp => logLogPrimeBand_prime (Finset.mem_sdiff.mp hp).1) hZ).law.mean
          (fun p => balancedPrimeIndicator d p) := by
  classical
  filter_upwards [broadBand_balanced_mass_eventually d hα hαβ hβ] with L hL
  intro E hE
  obtain ⟨hZ,hhalf⟩ := hL E hE
  refine ⟨hZ,?_⟩
  change (1/2:ℝ)≤(harmonicPrimeSource _ _ hZ).law.mean
    (fun p => if Supply.balancedDensity d p then 1 else 0)
  rw [harmonicPrimeSource_event_mean]
  apply (le_div_iff₀ hZ).mpr
  change harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E)/2≤
    harmonicPrimeMass ((logLogPrimeBand (α*L) (β*L) \ E).filter (fun p => Supply.balancedDensity d p)) at hhalf
  linarith

end Ostmann.Construction

end

end OAI
