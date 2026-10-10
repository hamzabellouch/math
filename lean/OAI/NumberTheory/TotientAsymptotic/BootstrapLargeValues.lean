import OAI.NumberTheory.TotientAsymptotic.BootstrapRealGaussian
import OAI.NumberTheory.TotientAsymptotic.SmallValueGaussian

namespace OAI

/-! Outside the explicit Gaussian exception, every preimage has a large head. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem small_head_real_gaussian : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ Ψ : ℕ,Ψ ≤ m x → ∀ Q : Finset ℕ,
    (∀ v ∈ Q,IsTotient v ∧ (v:ℝ) ≤ x ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧ (fordPrime n 0:ℝ) < x^(1/4:ℝ)) →
    (Q.card:ℝ) ≤ C*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := by
  classical
  obtain ⟨A,hA,hcount⟩ := bootstrap_good_real_gaussian
  refine ⟨A+1,by positivity,?_⟩
  filter_upwards [hcount,bootstrap_floor_good_large_head,small_value_gaussian_count]
    with x hc hhead hsmall
  intro Ψ hΨ Q hQ
  let R := Q.filter (fun v => ¬BootstrapGood ⌊x⌋₊ v)
  let T := Q\R
  have hR := hc Ψ hΨ R (by
    intro v hv
    obtain ⟨hv,hr⟩ := Finset.mem_filter.mp hv
    exact ⟨(hQ v hv).1,(hQ v hv).2.1,hr⟩)
  have hT := hsmall Ψ hΨ T (by
    intro v hv
    obtain ⟨hv,hvR⟩ := Finset.mem_sdiff.mp hv
    refine ⟨isTotient_pos (hQ v hv).1,?_⟩
    have hgood : BootstrapGood ⌊x⌋₊ v := by
      by_contra hh
      exact hvR (Finset.mem_filter.mpr ⟨hv,hh⟩)
    by_contra hh
    have hvlarge : x^(3/4:ℝ) < v := lt_of_not_ge hh
    obtain ⟨n,hn,hφ,hbad⟩ := (hQ v hv).2.2
    exact (not_lt_of_ge (hhead v n hgood hvlarge hn hφ)) hbad)
  have hcard : (Q.card:ℝ)=(R.card:ℝ)+(T.card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_eq_card (show R ⊆ Q from Finset.filter_subset _ _)
    exact_mod_cast (show Q.card=R.card+T.card by dsimp [T]; omega)
  rw [hcard]
  calc
    _ ≤ A*(x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4)+
        (x/Real.log x)*G x (m x)*Real.exp (-(Ψ:ℝ)^2/4) := add_le_add hR hT
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
