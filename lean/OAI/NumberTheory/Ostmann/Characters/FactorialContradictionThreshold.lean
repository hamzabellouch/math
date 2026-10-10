import OAI.NumberTheory.Ostmann.Characters.FactorialContradictionRemainders

namespace OAI

noncomputable section
namespace Ostmann.Characters
open Filter
open scoped Topology

theorem exists_factorial_depth_threshold (B BD C ε : ℝ)
    (hε : 60*ε<Real.log 2) :
    ∃N : ℕ,∀n : ℕ,N≤n →
      BD+60*ε*(n+1)+C+2*B+2≤(n:ℝ)*Real.log 2-1 := by
  obtain ⟨N,_,hN⟩ := exists_factorial_depth B BD C ε hε 0
  refine ⟨N,?_⟩
  intro n hn
  have hcast : (N:ℝ)≤n := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_left hcast (sub_nonneg.mpr hε.le)
  nlinarith

theorem exists_threshold_factorial_comparison_with_remainders (B BD C ε : ℝ)
    (hε : 60*ε<Real.log 2) :
    ∃N : ℕ,∀n : ℕ,N≤n → ∀z c α K : ℝ,
      0<z → 0<c → 0<α → 0≤K → ∀R S : ℝ → ℝ,
      Tendsto (fun L => R L/(factorialBulk z L:ℝ)) atTop (𝓝 0) →
      Tendsto (fun L => S L/(factorialBulk z L:ℝ)) atTop (𝓝 0) →
      ∀ᶠ L : ℝ in atTop,
        2*Real.exp ((BD+60*ε*(n+1))*factorialMass n (factorialBulk z L)+R L)*
          (Real.exp (C*factorialMass n (factorialBulk z L)+S L)/
            (factorialCount n (factorialBulk z L):ℝ)+K*Real.exp (-c*Real.exp (α*L))) <
          Real.exp (-2*B*factorialMass n (factorialBulk z L)) := by
  obtain ⟨N,hN⟩ := exists_factorial_depth_threshold B (BD+1) (C+1) ε hε
  refine ⟨N,?_⟩
  intro n hn z c α K hz hc hα hK R S hR hS
  filter_upwards [factorial_comparison_eventually_lt n B (BD+1+60*ε*(n+1)) (C+1) K hz hc hα (hN n hn),
    factorial_remainder_eventually_le_mass n hz R hR,
    factorial_remainder_eventually_le_mass n hz S hS] with L hL hRL hSL
  apply lt_of_le_of_lt _ hL
  have hv : Real.exp ((BD+60*ε*(n+1))*factorialMass n (factorialBulk z L)+R L) ≤
      Real.exp ((BD+1+60*ε*(n+1))*factorialMass n (factorialBulk z L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hd : Real.exp (C*factorialMass n (factorialBulk z L)+S L) ≤
      Real.exp ((C+1)*factorialMass n (factorialBulk z L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  gcongr

theorem finite_depth_factorial_comparison_with_remainders
    (B BD C ε : ℝ) (hε : 60*ε<Real.log 2) :
    ∃N : ℕ,∀ {ι : Type} [Fintype ι] (n : ι → ℕ),
      (∀i,N≤n i) → ∀z c α K : ι → ℝ,
      (∀i,0<z i) → (∀i,0<c i) → (∀i,0<α i) → (∀i,0≤K i) →
      ∀R S : ι → ℝ → ℝ,
      (∀i,Tendsto (fun L => R i L/(factorialBulk (z i) L:ℝ)) atTop (𝓝 0)) →
      (∀i,Tendsto (fun L => S i L/(factorialBulk (z i) L:ℝ)) atTop (𝓝 0)) →
      ∀ᶠ L : ℝ in atTop,∀i,
        2*Real.exp ((BD+60*ε*(n i+1))*factorialMass (n i) (factorialBulk (z i) L)+R i L)*
          (Real.exp (C*factorialMass (n i) (factorialBulk (z i) L)+S i L)/
            (factorialCount (n i) (factorialBulk (z i) L):ℝ)+K i*Real.exp (-c i*Real.exp (α i*L))) <
          Real.exp (-2*B*factorialMass (n i) (factorialBulk (z i) L)) := by
  obtain ⟨N,hN⟩ := exists_threshold_factorial_comparison_with_remainders B BD C ε hε
  refine ⟨N,?_⟩
  intro ι _ n hn z c α K hz hc hα hK R S hR hS
  exact Filter.eventually_all.mpr (fun i =>
    hN (n i) (hn i) (z i) (c i) (α i) (K i) (hz i) (hc i) (hα i) (hK i) (R i) (S i) (hR i) (hS i))

end Ostmann.Characters

end

end OAI
