import OAI.Geometry.LatticeCovering.GaussianPositions

namespace OAI

/-! The unconditional eventual covering bound, using the actual prime-congruence
and local affine Gaussian-position producers. Conditional intermediate interfaces
retain their stated hypotheses and are not used as unproved assumptions here. -/

noncomputable section

namespace SingleLatticeCovering.Assembly
open PrimeKernel SimplexYoung MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal Inputs
open Filter Topology
open scoped BigOperators Pointwise ENNReal




theorem eventual_single_lattice_covering :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ K : Set (Fin n → ℝ),
      IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
        K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
        (volume K).toReal/ZLattice.covolume Λ volume ≤ C*(n : ℝ)*Real.log (n : ℝ) := by
  classical
  obtain ⟨cutoff,hcut,C,k,κ,hC,hk,hκ,hvertical⟩ := vertical_patterns_alphabets
  let CT : ℝ := 301
  have hCT : 0 ≤ CT := by norm_num [CT]
  have hCTeq : 1+CT=302 := by norm_num [CT]
  obtain ⟨Cstar,hstar,hconditions⟩ := FinalRates.final_conditions hC hk
    (show 0 < Real.exp (-1)/8 by positivity) (show 0 ≤ Real.exp 1/8 by positivity)
    hκ (show (1 : ℝ) ≤ 3 by norm_num) hCT
  refine ⟨Real.exp 1*Cstar,by positivity,?_⟩
  filter_upwards [hconditions,FinalRates.eventually_marginal_scales hC (by norm_num : (0:ℝ) < 1)
      (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) < 1) (by norm_num : (0:ℝ) ≤ 0),
    FinalRates.firstSize_tendsto.eventually (eventually_ge_atTop cutoff),
    (FinalRates.localScale_tendsto hC).eventually GaussianNumerics.eventually_local_coordinate_position,
    FinalRates.eventually_localScale_root hC,
      FinalRates.eventually_dimension_small hC,eventually_ge_atTop (540 : ℕ)]
      with n hn hscale hfirst hgaussian hroot hdim hn540
  obtain ⟨B,c,hcb,hcs,hDim,hRad,hAlphabet,hPattern⟩ := hvertical (FinalRates.firstSize n) hfirst
  have hDdim : (c.fullDim : ℝ) ≤ C*((FinalRates.firstSize n : ℝ)+1) := by
    simpa [Chain.fullDim,Nat.cast_add] using hDim
  obtain ⟨hDn,hm,hcap,hload,hcrit,hcount⟩ := hn.2 c.fullDim hDdim
  have hm270 : 270 ≤ n-c.fullDim := by
    have hd := (hdim c.fullDim hDdim).2
    have hnR : (540 : ℝ) ≤ n := by exact_mod_cast hn540
    have hh : (270 : ℝ) ≤ ((n-c.fullDim : ℕ) : ℝ) := by
      rw [Nat.cast_sub hDn]
      linarith
    exact_mod_cast hh
  rw [hCTeq] at hcrit
  obtain ⟨_,_,_,_,_,hSmall⟩ := hscale c.fullDim hDdim
  have hD : 0 < c.fullDim := by
    have hfirstdim := chain_first_le_dim c
    rw [hcb] at hfirstdim
    dsimp [Chain.fullDim]
    omega
  let m := n-c.fullDim
  have hmn : m+c.fullDim=n := Nat.sub_add_cancel hDn
  have hmnle : m ≤ n := Nat.sub_le _ _
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  let ρ := Cstar*(n : ℝ)*Real.log (n : ℝ)
  let ε := Real.exp (-k*(FinalRates.firstSize n : ℝ)^(70/100 : ℝ))
  let R := FinalRates.sectionRadius C n
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrad : c.radiusSq+(B.terminalDim : ℝ) ≤ R^2 :=
    FinalRates.radius_sq_bound hC.le (Nat.cast_nonneg _) hRad
  have step : coversAtBound (m+c.fullDim) ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ)) := by
    intro K hK hc hi
    obtain ⟨e,he⟩ := hgaussian m c.fullDim (FinalRates.dimension_le_localScale hC hDdim)
      (by omega : 0 < m+c.fullDim) (by simpa only [hmn] using hroot) K hK hc hi
    obtain ⟨heK,hec,hei⟩ := affine_body e hK hc hi
    have heV := body_volume_pos heK hei
    have hg : ∀ y : c.FullVec, ‖WithLp.toLp 2 y‖ ≤ 6*(c.fullDim : ℝ)*R →
        (volume (e '' K)).toReal*gamma y/2 ≤ (volume (coordinateFiber (e '' K) y)).toReal := by
      intro y hy
      apply he y
      apply hy.trans
      calc
        6*(c.fullDim:ℝ)*R ≤ 6*(FinalRates.localScale C n:ℝ)*(FinalRates.localScale C n:ℝ) := by
          gcongr
          · exact (FinalRates.sectionRadius_pos hC n).le
          · exact_mod_cast FinalRates.dimension_le_localScale hC hDdim
          · exact FinalRates.sectionRadius_le_localScale C n
        _ = 6*(FinalRates.localScale C n:ℝ)^2 := by ring
    obtain ⟨Λ,hd,hfull,hcover,hbound⟩ := sections_and_circuits_cover c hm270 hD (e '' K) heK hec heV
      (FinalRates.sectionRadius_pos hC n) hrad hSmall hg κ ρ ε (Real.sqrt (m : ℝ))
      (8*(n : ℝ)*Real.log (n : ℝ)) hρ (Real.sqrt_nonneg _) (by positivity)
      (by
        intro y
        obtain ⟨P,hPn,hPb,hPl,hPt,hPw⟩ := hPattern y
        exact ⟨P,hPn,hPb,hPl,hPw⟩)
      (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using hload) hcap hcrit (by
        intro δ s hs
        have hs' : (s.card : ℝ) ≤ (3*(n : ℝ)^2)^c.fullDim := hs.trans (by
          gcongr)
        have ha : ∀ j < c.fullDim, Real.log ((c.alphabetSeq j).card+1 : ℝ) ≤
            Real.log 8+(c.fullDim : ℝ)*Real.log ((c.fullDim : ℝ)+2)+(FinalRates.firstSize n : ℝ)^2 := by
          intro j hj
          simpa only [c.alphabetSeq_fin ⟨j,hj⟩] using hAlphabet ⟨j,hj⟩
        simpa only [Nat.sub_add_cancel hDn] using hcount s c.alphabetSeq hs' ha)
    let := hd
    let := hfull
    have hb : (volume (e '' K)).toReal/ZLattice.covolume Λ volume ≤
        (Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ) := by
      convert hbound using 1 ; dsimp [ρ] ; ring
    exact pull_back_cover e K Λ hcover hb
  change coversAtBound n ((Real.exp 1*Cstar)*(n : ℝ)*Real.log (n : ℝ))
  simpa only [hmn] using step


end SingleLatticeCovering.Assembly


end

end OAI
