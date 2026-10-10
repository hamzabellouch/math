import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinNorm

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate HistoryFrequencyLabels
attribute [local instance] Classical.propDecidable

theorem source_nonempty_of_mass_pos {A : ℕ} (E : Finset (PrimeUpTo A))
    (hE : 0<primeShellMass E) : E.Nonempty := by
  by_contra hn
  have he : E=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [he,primeShellMass,Finset.sum_empty] at hE
  exact (lt_irrefl 0) hE

theorem twoPrimeSample_property {I : Type*} [Fintype I] [DecidableEq I] {A : ℕ}
    (p : I→PrimeUpTo A) (L S : I) (q r : PrimeUpTo A) (G : PrimeUpTo A→Prop)
    (hf : ∀i∈frozenVertices L S,G (p i)) (hq : G q) (hr : G r) :
    ∀i,G (twoPrimeSample p L S q r i) := by
  intro i
  by_cases hiS : i=S
  · subst i
    simpa only [twoPrimeSample,Function.update_self] using hr
  · by_cases hiL : i=L
    · subst i
      simpa only [twoPrimeSample,Function.update_of_ne hiS,Function.update_self] using hq
    · simpa only [twoPrimeSample,Function.update_of_ne hiS,Function.update_of_ne hiL] using
        hf i ((mem_frozenVertices L S i).mpr ⟨hiS,hiL⟩)

theorem sourceFactors_norms_on_sources {k A V : ℕ}
    (cfg : SourceConfiguration k) (m j : ℕ) (hj : j<k)
    (σ ρ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (χ : (q:ℕ)→MulChar (ZMod q) ℂ)
    (ζ : PrimeUnitData (schedule k j) (sourceWidth cfg m) A) (hζ : ∀i q,‖ζ i q‖=1)
    (masks : SurvivingPrimeIndex k j (sourceWidth cfg m)→ℕ→ℂ) (hm : ∀i q,‖masks i q‖≤1)
    (p : SurvivingPrimeIndex k j (sourceWidth cfg m)→PrimeUpTo A)
    (L S : SurvivingPrimeIndex k j (sourceWidth cfg m)) (hLS : L≠S)
    (Elong Eshort : Finset (PrimeUpTo A))
    (hElong : 0<primeShellMass Elong) (hEshort : 0<primeShellMass Eshort)
    (hfixed : ∀i∈frozenVertices L S,2<orderOf (χ (p i).val) ∧ V<(p i).val)
    (hlong : ∀q∈Elong,2<orderOf (χ q.val) ∧ V<q.val)
    (hshort : ∀r∈Eshort,2<orderOf (χ r.val) ∧ V<r.val)
    (ranges : List Bool→Finset ℤ)
    (hrange : ∀path f,f∈ranges path→f≠0 ∧ f.natAbs≤V)
    (t u : SupportedHistory ranges j []) (hroot : t.val.1=u.val.1) (P : ℕ+) :
    (∀q∈Elong,‖sourceLongFactor cfg m j hj σ ρ χ ζ masks p L S P t.val.1 t.val.2 u.val.2 q.val‖≤1) ∧
    (∀r∈Eshort,‖sourceShortFactor cfg m j hj σ ρ χ ζ masks p L S P t.val.1 t.val.2 u.val.2 r.val‖≤1) := by
  have hpair (q : PrimeUpTo A) (hq : q∈Elong) (r : PrimeUpTo A) (hr : r∈Eshort) :=
    twoPrimeSample_property p L S q r (fun z=>2<orderOf (χ z.val) ∧ V<z.val)
      hfixed (hlong q hq) (hshort r hr)
  obtain ⟨q₀,hq₀⟩ := source_nonempty_of_mass_pos Elong hElong
  obtain ⟨r₀,hr₀⟩ := source_nonempty_of_mass_pos Eshort hEshort
  constructor
  · intro q hq
    exact (sourceFactors_norms_of_supported cfg m j hj σ ρ χ ζ hζ masks hm p L S hLS q r₀
      (fun i=>(hpair q hq r₀ hr₀ i).1) (fun i=>(hpair q hq r₀ hr₀ i).2)
      ranges hrange t u hroot P).1
  · intro r hr
    exact (sourceFactors_norms_of_supported cfg m j hj σ ρ χ ζ hζ masks hm p L S hLS q₀ r
      (fun i=>(hpair q₀ hq₀ r hr i).1) (fun i=>(hpair q₀ hq₀ r hr i).2)
      ranges hrange t u hroot P).2

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
