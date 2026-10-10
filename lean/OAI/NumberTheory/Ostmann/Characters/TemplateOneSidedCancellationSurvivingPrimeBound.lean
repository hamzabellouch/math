import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriorsGridDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingProfiles
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget Arithmetic Preliminaries
open TemplateOneSidedNumericInputs Construction TemplateOneSidedPrior PrimeDyadicCover
attribute [local instance] Classical.propDecidable

theorem exists_surviving_core_prime_bound (k j Cw Cc : ℕ)
    {z a Cmod βHeight : ℝ} (Wp Wl Wc : ℝ)
    (hz : 0 < z) (ha : 0 ≤ a) (hCmod : 0 ≤ Cmod)
    (hβHeight : 0 ≤ βHeight) (hWc : 0 ≤ Wc) :
    ∃ C : ℝ,0 < C ∧ ∀ (L c α β γLong βLong δ : ℝ),
    OriginalPrimePriorBound (Unit ⊕ (Fin (2^j) ⊕ Fin (2^j)))
      C z c 4 α β γLong βLong δ L →
    ∀ {A : ℕ} (Elong Eshort : Finset (PrimeUpTo A))
      (hElong : 0 < primeShellMass Elong) (hEshort : 0 < primeShellMass Eshort)
      (width : Role → ℕ) (N : ℕ)
      (B : ℕ → ℤ) (T : ℕ → ℝ) (J P s v : ℤ)
      (σ π : Equiv.Perm (CopiedConstituent (schedule k j) j width))
      (t u : HistoryReconstruction.Tree j)
      (i : SurvivingPrimeIndex k j width) (x : ↥Eshort → Other i → ℤ)
      (gate : Bool) (X Tc : ℝ)
      (χ : ∀q:↥Eshort,MulChar (ZMod q.val.val) ℂ)
      (U : PrimeUpTo A → ℂ) (V : ↥Eshort → ℂ),
    let m : ℝ := (⌊z*L⌋₊:ℝ)
    let H := rowLogHeight Cmod z βHeight L
    let Q := historyPairResidueModulus k j s (survivingSampledExpressions k j width P σ) t
      v (survivingSampledExpressions k j width P π) u
    1 ≤ m → 1 ≤ X →
    (∀q,width q ≤ N) → N ≤ Cw*(⌊z*L⌋₊+1) →
    Fintype.card (CopiedConstituent (schedule k j) j width) ≤ Cc*(⌊z*L⌋₊+1) →
    RangeSupported (ranges a m j) j [] s t →
    RangeSupported (ranges a m j) j [] v u →
    linearEnvelope a j*m ≤ H → |(P:ℝ)| ≤ Real.exp H →
    (Q:ℝ) ≤ Real.exp (historyPolynomialCost Cmod z 4 L) →
    (∀p∈Elong,∀q:↥Eshort,∀r,
      |((insertCoordinate i (x q) (p.val:ℤ) r:ℤ):ℝ)| ≤ Real.exp H) →
    (∀q,χ q ≠ 1) → (∀p∈Elong,‖U p‖ ≤ 1) → (∀q,‖V q‖ ≤ 1) →
    Real.exp (-c*L) ≤ primeShellMass Elong →
    Real.exp (-c*L) ≤ primeShellMass Eshort →
    (∀p∈Eshort,Real.exp (α*L) ≤ Real.log p.val) →
    (∀p∈Eshort,Real.log p.val ≤ Real.exp (β*L)) →
    (∀p∈Elong,Real.exp (γLong*L) ≤ Real.log p.val) →
    (∀p∈Elong,Real.log p.val ≤ Real.exp (βLong*L)) →
    ‖(primeShellPrior Elong hElong).cmean (fun p=>U p*
      ∑q:↥Eshort,((primeShellPrior Eshort hEshort).mass q.val:ℂ)*V q*
        χ q (p.val:ZMod q.val.val)*
        survivingCorePairAmplitude k j width B (fun l=>(bound a m l:ℤ)) T J
          P s v σ π t u gate X (a*m) Wp Wl Tc Wc
          (insertCoordinate i (x q) (p.val:ℤ)))‖ ≤ Real.exp (-δ*Real.exp (α*L)) := by
  let CD : ℝ := (obstructionSizeFactor k j*(2*Cw+3):ℕ)
  let CM : ℝ := (2*(Cw+Cc+1):ℕ)
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := exists_normalized_source_profile_budget k j
    (𝓕 SchwartzCutoff.psi) Wl Wc hz ha hCmod (show 0≤CD by positivity)
    (show 0≤CM by positivity) hβHeight
  let C := Cprofile+Cmod+1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro L c α β γLong βLong δ hprime A Elong Eshort hElong hEshort width N B T J P s v
    σ π t u i x gate X Tc χ U V
  dsimp only
  intro hm hX hw hN hcard ht hu hfreq hP hQcost hvars hχ hU hV hZlong hZshort
    hshortlo hshorthi hlonglo hlonghi
  let m : ℝ := (⌊z*L⌋₊:ℝ)
  let H := rowLogHeight Cmod z βHeight L
  let Q := historyPairResidueModulus k j s (survivingSampledExpressions k j width P σ) t
    v (survivingSampledExpressions k j width P π) u
  let D := obstructionSizeFactor k j*(2*(N+1)+1)
  let Msyntax := survivingProfileSyntax k j width N
  have hlin := survivingProfile_linear_budgets k j width N ⌊z*L⌋₊ Cw Cc hN hcard
  have hb := hprofile L D Msyntax
    (by simpa only [D,CD,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hlin.1) hlin.2
  have hmono : Real.exp (historyPolynomialCost Cprofile z 4 L) ≤
      Real.exp (historyPolynomialCost C z 4 L) := Real.exp_le_exp.mpr
    (historyPolynomialCost_mono_coefficient (show Cprofile≤C by dsimp [C]; linarith) z L 4)
  have hmodmono : Real.exp (historyPolynomialCost Cmod z 4 L) ≤
      Real.exp (historyPolynomialCost C z 4 L) := Real.exp_le_exp.mpr
    (historyPolynomialCost_mono_coefficient (show Cmod≤C by dsimp [C]; linarith) z L 4)
  have hQ : 0 < Q := historyPairResidueModulus_pos k (fun l=>(bound a m l:ℤ)) j
    s (survivingSampledExpressions k j width P σ) t
    v (survivingSampledExpressions k j width P π) u
    (actual_historyFrequencyBounds a m j j [] (by simp) s t ht)
    (actual_historyFrequencyBounds a m j j [] (by simp) v u hu)
    (fun z=>(survivingSampledExpressions_good k j width P σ (fun _=>0) z).1)
    (fun z=>(survivingSampledExpressions_good k j width P π (fun _=>0) z).1)
  let data := fun (_b : Index (sourceUpper βLong L)) (r : Fin Q) (q : ↥Eshort)=>
    canonicalSourceNormalizedData k B (fun l=>(bound a m l:ℤ)) T J j false true s v
      (survivingSampledExpressions k j width P σ)
      (survivingSampledExpressions k j width P π) t u i (x q) (r.val:ℤ) gate
      X (a*m) Wp Wl H D (survivingCopiedProductExpression k j width) Tc Wc
  let lo := fun (_b : Index (sourceUpper βLong L))=>
    Sum.elim (fun _ : Unit=>-Wc) (fun _ : Fin (2^j) ⊕ Fin (2^j)=>coarseLower D H (a*m) Wl)
  let hi := fun (_b : Index (sourceUpper βLong L))=>
    Sum.elim (fun _ : Unit=>Wc) (fun _ : Fin (2^j) ⊕ Fin (2^j)=> -a*m+Wl)
  let M := fun (_b : Index (sourceUpper βLong L))=>
    max (Real.exp Wc) (Real.exp ((-a*m+Wl)/2)*leafProfileBound (𝓕 SchwartzCutoff.psi))
  apply hprime Elong Eshort hElong hEshort (𝓕 SchwartzCutoff.psi) Q hQ χ hχ U V
    (fun p q=>survivingCorePairAmplitude k j width B (fun l=>(bound a m l:ℤ)) T J
      P s v σ π t u gate X (a*m) Wp Wl Tc Wc (insertCoordinate i (x q) (p.val:ℤ)))
    data lo hi M hZlong hZshort hshortlo hshorthi hlonglo hlonghi hU hV (hQcost.trans hmodmono)
  · intro b _hb
    refine ⟨?_,?_,hb.1.trans hmono,hb.2.2.trans hmono⟩
    · intro r q
      simpa only [data,lo,hi,M,D,neg_mul] using (survivingNormalizedData_ranges_degree k j width B (fun l=>(bound a m l:ℤ))
        T J P s v σ π t u i (x q) (r.val:ℤ) gate (X:=X) (Δ:=a*m) (Wp:=Wp) (Wl:=Wl) (H:=H) (Tc:=Tc) (Wc:=Wc)
        (by linarith) hWc N hw
        (𝓕 SchwartzCutoff.psi)).1
    · intro r q
      have hd := (survivingNormalizedData_ranges_degree k j width B (fun l=>(bound a m l:ℤ))
        T J P s v σ π t u i (x q) (r.val:ℤ) gate (X:=X) (Δ:=a*m) (Wp:=Wp) (Wl:=Wl) (H:=H) (Tc:=Tc) (Wc:=Wc)
        (by linarith) hWc N hw
        (𝓕 SchwartzCutoff.psi)).2
      exact (Nat.cast_le.mpr hd).trans (hb.2.1.trans hmono)
  · intro b p hp _hpblock r n hn q
    have hn' : historyPairResidueModulus k j s (survivingSampledExpressions k j width P σ) t
      v (survivingSampledExpressions k j width P π) u*n+r.val=p.val := hn
    have heq := survivingCorePairAmplitude_eq_data ha hm k j width B T J P s v σ π t u
      ht hu i (x q) gate r.val n (Δ:=a*m) (Wp:=Wp) (Wl:=Wl) (Tc:=Tc) (Wc:=Wc) hX
      (rowLogHeight_ge_log_two Cmod z βHeight L hCmod) hfreq hP N hw
      (by simpa only [hn'] using hvars p hp q)
    simpa only [data,m,H,D,hn,hn'] using heq

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
