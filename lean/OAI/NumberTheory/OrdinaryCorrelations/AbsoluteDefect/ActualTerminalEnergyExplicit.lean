import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ActualWindowMass
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.TerminalBinnedSparseExplicit

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryNarrowGrid OrdinaryDirichletMeanSquare
open OrdinaryFrequencyChain Finset Filter

theorem actual_terminal_energy_explicit :
    ∃ C : ℝ, 0≤C ∧
    ∀ {f : ℕ→ℂ}, OneBounded f → Multiplicative f → UniformlyNonpretentious f →
    ∀ {d : ℕ}, 0<d → ∀ (χ : DirichletCharacter ℂ d) {ε : ℝ}, 0<ε →
    ∀ s J : ℕ, 0<J → 2120/(J:ℝ)≤ε/(1+(C+(s:ℝ)*Real.log 2)^2) →
    let r := 16*(576*J^2+96*J+4)
    ∀ H Kr K B : ℕ,
      16*(4*r)≤2^H → 64*(4*r)≤2^Kr →
      16*((4*r:ℕ):ℝ)*(1+momentCoefficient)≤(2:ℝ)^K →
      H+4*s+2*Kr+K+70≤B → 2*H+s+30≤B →
      ∀D : ℕ,4*2^(F B s 0)≤D →
      ∀ᶠ X : ℕ in atTop,∃j : ℕ,
        (2^(F B s j))^(64*(4*r))≤X ∧ X<(2^(F B s (j+1)))^(64*(4*r)) ∧
        ∀S : Finset ℝ,(S : Set ℝ).Pairwise (fun t u=>1≤|t-u|) →
          (∀t∈S,|t|≤(X:ℝ)/(D:ℝ)) →
          (∑t∈surviving S
            (allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
              (fun _stage index=>primeMellin f χ (primeBin index))
              (fun j i=>threshold H j (binLog B H s j i))) (j+1),
            ‖binnedStage f χ (binQ B H s 0) (binStart B H s 0) (binWidth B s 0) X t‖^2)<ε := by
  classical
  obtain ⟨C,hC,hMass⟩ := actual_window_mass
  refine ⟨C,hC,?_⟩
  intro f hf hm hNP d hd χ ε hε s J hJ hRate
  let L := C+(s:ℝ)*Real.log 2
  have hL : 0≤L := by dsimp [L]; positivity
  let r := 16*(576*J^2+96*J+4)
  have hr : 0<r := by dsimp [r]; positivity
  have ht := terminal_binned_sparse_explicit hf hm hNP hd χ hε hL J hJ hRate
  dsimp only
  intro H Kr K B hH hKr hK hB hB' D hD
  have hB0 : H+10≤B := by omega
  have hDp : 0<D := lt_of_lt_of_le (by positivity : 0<4*2^(F B s 0)) hD
  have hm0 := hMass B H s 0 hB0
  have hm1 : (∑p∈primeWindow (binQ B H s 0) (binStart B H s 0) (binWidth B s 0),(p:ℝ)⁻¹)≤L := by
    have hh := (abs_le.mp hm0).2
    simp only [Nat.add_zero] at hh
    dsimp [L]
    linarith
  have hD' : 4*(binQ B H s 0*2^(binStart B H s 0+binWidth B s 0))≤D := by
    rwa [(window_endpoints B H s 0 hB0).2]
  have he := ht (binQ B H s 0) (binStart B H s 0) (binWidth B s 0)
    (by unfold binQ; positivity) hm1 D hD'
  filter_upwards [he,eventually_ge_atTop ((2^(F B s 0))^(64*(4*r)))] with X hEnergy hX
  obtain ⟨j,hlo,hhi⟩ := terminal_index (B:=B) (s:=s) (R:=4*r) (by omega) hX
  refine ⟨j,hlo,hhi,?_⟩
  intro S hsep hheight
  let good := allBinsGood (fun j=>grid (binQ B H s j) (binStart B H s j) (binWidth B s j))
    (fun j i=>primeMellin f χ (primeBin i)) (fun j i=>threshold H j (binLog B H s j i))
  let T := surviving S good (j+1)
  have hsub : T⊆S := filter_subset _ _
  have hxD : (X:ℝ)/(D:ℝ)≤X := div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hDp)
  have hc := terminal_bad_sparse hf χ hr hH hKr hK hB hB' hlo hhi S hsep
    (fun t ht => (hheight t ht).trans hxD)
  have hbad : T⊆S.filter (fun t=>¬good j t) := by
    intro t ht
    rcases mem_filter.mp ht with ⟨ht,hh⟩
    exact mem_filter.mpr ⟨ht,hh j (by omega)⟩
  have hcard : T.card^(2*r)≤X := (Nat.pow_le_pow_left (Finset.card_le_card hbad) _).trans (by simpa only [good,allBinsGood] using hc)
  exact hEnergy T (hsep.mono (by exact_mod_cast hsub)) (fun t ht=>hheight t (hsub ht)) hcard

end OrdinaryChainScales

end

end OAI
