import OAI.NumberTheory.TotientAsymptotic.PositiveCount

namespace OAI

noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

/-- Full positive alternative, including uniform positivity, a ratio
asymptotic, and comparison with the number of distinct totients. -/
theorem conditional_companion_positive_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    {d k : ℕ} (hk : 1≤k) (hd : IsTotient d) (hseed : k*d<ell d)
    (hppt : PPTBoundedFiberPropagation d) :
    ∃ cMinus cPlus : ℝ, 0<cMinus ∧ 0<cPlus ∧
      (∀ s∈Set.Ico (0 : ℝ) 1, cMinus≤A (fk k) s ∧ A (fk k) s≤cPlus) ∧
      Tendsto (fun x => N k x/(tupleNormalization x*A (fk k) (theta x))) atTop (nhds 1) ∧
      ∀ᶠ x : ℝ in atTop, (cMinus/cPlus)*V x≤N k x ∧ N k x≤V x := by
  have herr := (conditional_companion_additive hscale hstruct hpnt hbox hren hmertens h26 h51 hconc k hk).2
  obtain ⟨c,hc,hlower⟩ := companion_positive_bound hscale hstruct hpnt hbox hren hmertens h26 h51 hk hd hseed hppt
  obtain ⟨c₀,c₁,_,hscale⟩ := hscale
  let C := |c₁|+1
  have hC : 0<C := by dsimp [C]; positivity
  have hupper : ∀ᶠ x : ℝ in atTop, normalizedCount (N k) x≤C := by
    filter_upwards [hscale,scale_eventually_pos] with x hs hN
    exact (div_le_div_of_nonneg_right (N_le_V k x) hN.le).trans
      (hs.2.trans (by dsimp [C]; linarith [le_abs_self c₁]))
  have hA := coefficient_bounds_of_comparison (fk k) (normalizedCount (N k)) herr c C (hlower.and hupper)
  refine ⟨c,C,hc,hC,hA,?_,?_⟩
  · exact ratio_limit_of_normalized_error (N k) (fk k) c hc (fun s hs => (hA s hs).1) herr
  · filter_upwards [hlower,hscale,scale_eventually_pos] with x hl hs hN
    have hN' : c*tupleNormalization x≤N k x := (le_div_iff₀ hN).mp hl
    have hV : V x≤C*tupleNormalization x := (div_le_iff₀ hN).mp
      (hs.2.trans (by dsimp [C]; linarith [le_abs_self c₁]))
    refine ⟨?_,N_le_V k x⟩
    calc
      (c/C)*V x ≤ (c/C)*(C*tupleNormalization x) :=
        mul_le_mul_of_nonneg_left hV (div_pos hc hC).le
      _ = c*tupleNormalization x := by field_simp
      _ ≤ N k x := hN'

/-- The manuscript's weighted companion theorem, conditional only on the
named published analytic inputs and the published full-fiber propagation. -/
theorem conditional_companion_theorem_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d) (k : ℕ) (hk : 1≤k) :
    TendstoUniformlyOn (fun H => AH H (fk k)) (A (fk k)) atTop (Set.Ico (0 : ℝ) 1) ∧
    Tendsto (fun x => normalizedCount (N k) x-A (fk k) (theta x)) atTop (nhds 0) ∧
    ((∃ d : ℕ, IsTotient d ∧ k*d<ell d) →
      ∃ cMinus cPlus : ℝ, 0<cMinus ∧ 0<cPlus ∧
        (∀ s∈Set.Ico (0 : ℝ) 1, cMinus≤A (fk k) s ∧ A (fk k) s≤cPlus) ∧
        Tendsto (fun x => N k x/(tupleNormalization x*A (fk k) (theta x))) atTop (nhds 1) ∧
        ∀ᶠ x : ℝ in atTop, (cMinus/cPlus)*V x≤N k x ∧ N k x≤V x) ∧
    ((¬∃ d : ℕ, IsTotient d ∧ k*d<ell d) →
      (∀ x : ℝ, 0<x → N k x=0) ∧ (∀ s∈Set.Ico (0 : ℝ) 1, A (fk k) s=0)) := by
  have ha := conditional_companion_additive hscale hstruct hpnt hbox hren hmertens h26 h51 hconc k hk
  refine ⟨ha.1,ha.2,?_,?_⟩
  · rintro ⟨d,hd,hseed⟩
    exact conditional_companion_positive_of_structure hscale hstruct hpnt hbox hren hmertens h26 h51 hconc hk hd hseed (hppt d hd)
  · exact companion_zero_case k (by omega)

/-- The published explicit least-preimage calculation supplies the two
unconditional-in-k positive cases singled out by the manuscript. -/
theorem companion_seeds_one_two
    (hseed : IsTotient (2^18*257)) (hmin : ell (2^18*257)=135268352) :
    ∀ k∈({1,2} : Finset ℕ), ∃ d : ℕ, IsTotient d ∧ k*d<ell d := by
  intro k hk
  have hs := seeds_one_two_of_published_least_preimage hseed hmin
  simp only [Finset.mem_insert,Finset.mem_singleton] at hk
  rcases hk with rfl|rfl
  · exact hs.1
  · exact hs.2

/-- The final assertion for k=1 and k=2, using exactly the published finite
least-preimage calculation cited in `seeds_one_two_of_published_least_preimage`. -/
theorem conditional_companion_one_two_of_structure (hscale : FordScaleBounds)
    (hstruct : ExtractedStructureInput) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d)
    (hseed : IsTotient (2^18*257)) (hmin : ell (2^18*257)=135268352) :
    ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0<c ∧
      ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s := by
  intro k hk
  obtain ⟨d,hd,hkd⟩ := companion_seeds_one_two hseed hmin k hk
  have hk1 : 1≤k := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl <;> omega
  obtain ⟨c,C,hc,_,hA,_,_⟩ := conditional_companion_positive_of_structure hscale hstruct hpnt
    hbox hren hmertens h26 h51 hconc hk1 hd hkd (hppt d hd)
  exact ⟨c,hc,fun s hs => (hA s hs).1⟩


/-- The original published-input interface remains available. -/
theorem conditional_companion_positive (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    {d k : ℕ} (hk : 1≤k) (hd : IsTotient d) (hseed : k*d<ell d)
    (hppt : PPTBoundedFiberPropagation d) :
    ∃ cMinus cPlus : ℝ, 0<cMinus ∧ 0<cPlus ∧
      (∀ s∈Set.Ico (0 : ℝ) 1, cMinus≤A (fk k) s ∧ A (fk k) s≤cPlus) ∧
      Tendsto (fun x => N k x/(tupleNormalization x*A (fk k) (theta x))) atTop (nhds 1) ∧
      ∀ᶠ x : ℝ in atTop, (cMinus/cPlus)*V x≤N k x ∧ N k x≤V x :=
  conditional_companion_positive_of_structure hscale (extractedStructureInput_of_ford hscale h10 h16) hpnt hbox hren hmertens h26 h51 hconc hk hd hseed hppt

theorem conditional_companion_theorem (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d) (k : ℕ) (hk : 1≤k) :
    TendstoUniformlyOn (fun H => AH H (fk k)) (A (fk k)) atTop (Set.Ico (0 : ℝ) 1) ∧
    Tendsto (fun x => normalizedCount (N k) x-A (fk k) (theta x)) atTop (nhds 0) ∧
    ((∃ d : ℕ, IsTotient d ∧ k*d<ell d) →
      ∃ cMinus cPlus : ℝ, 0<cMinus ∧ 0<cPlus ∧
        (∀ s∈Set.Ico (0 : ℝ) 1, cMinus≤A (fk k) s ∧ A (fk k) s≤cPlus) ∧
        Tendsto (fun x => N k x/(tupleNormalization x*A (fk k) (theta x))) atTop (nhds 1) ∧
        ∀ᶠ x : ℝ in atTop, (cMinus/cPlus)*V x≤N k x ∧ N k x≤V x) ∧
    ((¬∃ d : ℕ, IsTotient d ∧ k*d<ell d) →
      (∀ x : ℝ, 0<x → N k x=0) ∧ (∀ s∈Set.Ico (0 : ℝ) 1, A (fk k) s=0)) :=
  conditional_companion_theorem_of_structure hscale (extractedStructureInput_of_ford hscale h10 h16) hpnt hbox hren hmertens h26 h51 hconc hppt k hk

theorem conditional_companion_one_two (hscale : FordScaleBounds)
    (h10 : FordTheorem10Input) (h16 : FordTheorem16Input) (hpnt : PrimeNumberTheoremInput)
    (hbox : FordUnitPrimeBoxInput) (hren : FordRenewalInput) (hmertens : MertensProductInput)
    (h26 : FordLemma26Input) (h51 : FordLemma51Input) (hconc : FordCoordinateConcentrationInput)
    (hppt : ∀ d : ℕ, IsTotient d → PPTBoundedFiberPropagation d)
    (hseed : IsTotient (2^18*257)) (hmin : ell (2^18*257)=135268352) :
    ∀ k∈({1,2} : Finset ℕ), ∃ c : ℝ, 0<c ∧
      ∀ s∈Set.Ico (0 : ℝ) 1, c≤A (fk k) s :=
  conditional_companion_one_two_of_structure hscale (extractedStructureInput_of_ford hscale h10 h16) hpnt hbox hren hmertens h26 h51 hconc hppt hseed hmin

end TotientAsymptotic

end

end OAI
