import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationPrimePriorsGridDefs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalDataBudget
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsRows

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators SchwartzMap FourierTransform
namespace Ostmann.Characters.TemplateOneSidedCancellation
open SymbolicHistory Template TemplateSupportRemoval TemplateOneSidedBudget
open HistoryFrequencyLabels HistoryFrequencyBudget Arithmetic Preliminaries
open TemplateOneSidedNumericInputs Construction TemplateOneSidedPrior PrimeDyadicCover
open TemplateOneSidedRelabel ParityActions
attribute [local instance] Classical.propDecidable

theorem exists_terminal_core_prime_bound (k n Cw : ℕ)
    {z a Cmod βHeight : ℝ} (Wp Wl : ℝ)
    (hz : 0 < z) (ha : 0 ≤ a) (hCmod : 0 ≤ Cmod) (hβHeight : 0 ≤ βHeight) :
    ∃C : ℝ,0 < C ∧ ∀(L c α β γLong βLong δ : ℝ),
    OriginalPrimePriorBound (Fin (2^(n+1)) ⊕ Fin (2^(n+1)))
      C z c 4 α β γLong βLong δ L →
    ∀{A : ℕ} (Elong Eshort : Finset (PrimeUpTo A))
      (hElong : 0 < primeShellMass Elong) (hEshort : 0 < primeShellMass Eshort)
      (width : Role → ℕ) (N mWord : ℕ) (hmWord : mWord ≤ width .word)
      (B : ℕ → ℤ) (T : ℕ → ℝ) (J s v : ℤ)
      (σ π : Reassignments k n mWord) (t u : HistoryReconstruction.Tree (n+1))
      (i : (schedule k (n+1)).Constituent width) (x : ↥Eshort → Other i → ℤ)
      (gate : Bool) (X : ℝ)
      (χ : ∀q:↥Eshort,MulChar (ZMod q.val.val) ℂ)
      (U : PrimeUpTo A → ℂ) (V : ↥Eshort → ℂ),
    let m : ℝ := (⌊z*L⌋₊:ℝ)
    let H := rowLogHeight Cmod z βHeight L
    let Q := historyPairResidueModulus k (n+1) s (paritySampledExpressions k n width mWord hmWord σ) t
      v (paritySampledExpressions k n width mWord hmWord π) u
    1 ≤ m → 1 ≤ X → (∀q,width q ≤ N) → N ≤ Cw*(⌊z*L⌋₊+1) →
    RangeSupported (ranges a m (n+1)) (n+1) [] s t →
    RangeSupported (ranges a m (n+1)) (n+1) [] v u →
    linearEnvelope a (n+1)*m ≤ H →
    (Q:ℝ) ≤ Real.exp (historyPolynomialCost Cmod z 4 L) →
    (∀p∈Elong,∀q:↥Eshort,∀r,
      |((insertCoordinate i (x q) (p.val:ℤ) r:ℤ):ℝ)| ≤ Real.exp H) →
    (∀q,χ q ≠ 1) → (∀p∈Elong,‖U p‖ ≤ 1) → (∀q,‖V q‖ ≤ 1) →
    Real.exp (-c*L) ≤ primeShellMass Elong → Real.exp (-c*L) ≤ primeShellMass Eshort →
    (∀p∈Eshort,Real.exp (α*L) ≤ Real.log p.val) →
    (∀p∈Eshort,Real.log p.val ≤ Real.exp (β*L)) →
    (∀p∈Elong,Real.exp (γLong*L) ≤ Real.log p.val) →
    (∀p∈Elong,Real.log p.val ≤ Real.exp (βLong*L)) →
    ‖(primeShellPrior Elong hElong).cmean (fun p=>U p*
      ∑q:↥Eshort,((primeShellPrior Eshort hEshort).mass q.val:ℂ)*V q*
        χ q (p.val:ZMod q.val.val)*
        terminalCorePairAmplitude k n width mWord hmWord B (fun l=>(bound a m l:ℤ)) T J
          s v σ π t u gate X (a*m) Wp Wl (insertCoordinate i (x q) (p.val:ℤ)))‖ ≤
      Real.exp (-δ*Real.exp (α*L)) := by
  let CD : ℝ := (obstructionSizeFactor k (n+1)*(2*Cw+3):ℕ)
  let CM : ℝ := (2*(Cw+1):ℕ)
  obtain ⟨Cprofile,hCprofile,hprofile⟩ := exists_terminal_source_profile_budget k (n+1)
    (𝓕 SchwartzCutoff.psi) Wl hz ha hCmod (show 0 ≤ CD by positivity)
    (show 0 ≤ CM by positivity) hβHeight
  let C := Cprofile+Cmod+1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro L c α β γLong βLong δ hprime A Elong Eshort hElong hEshort width N mWord hmWord
    B T J s v σ π t u i x gate X χ U V
  dsimp only
  intro hm hX hw hN ht hu hfreq hQcost hvars hχ hU hV hZlong hZshort
    hshortlo hshorthi hlonglo hlonghi
  let m : ℝ := (⌊z*L⌋₊:ℝ)
  let H := rowLogHeight Cmod z βHeight L
  let e := paritySampledExpressions k n width mWord hmWord σ
  let f := paritySampledExpressions k n width mWord hmWord π
  let Q := historyPairResidueModulus k (n+1) s e t v f u
  let D := obstructionSizeFactor k (n+1)*(2*(N+1)+1)
  let Msyntax := 2*(N+1)
  have hlin := terminalProfile_linear_budgets k (n+1) N ⌊z*L⌋₊ Cw hN
  have hb := hprofile L D Msyntax
    (by simpa only [D,CD,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hlin.1)
    (by simpa only [Msyntax,CM,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hlin.2)
  have hmono : Real.exp (historyPolynomialCost Cprofile z 4 L) ≤
      Real.exp (historyPolynomialCost C z 4 L) := Real.exp_le_exp.mpr
    (historyPolynomialCost_mono_coefficient (show Cprofile ≤ C by dsimp [C]; linarith) z L 4)
  have hmodmono : Real.exp (historyPolynomialCost Cmod z 4 L) ≤
      Real.exp (historyPolynomialCost C z 4 L) := Real.exp_le_exp.mpr
    (historyPolynomialCost_mono_coefficient (show Cmod ≤ C by dsimp [C]; linarith) z L 4)
  have he := terminal_initial_expression_parameters k n width mWord hmWord σ N hw (le_refl (0:ℝ))
  have hf := terminal_initial_expression_parameters k n width mWord hmWord π N hw (le_refl (0:ℝ))
  have hQ : 0 < Q := historyPairResidueModulus_pos k (fun l=>(bound a m l:ℤ)) (n+1)
    s e t v f u (actual_historyFrequencyBounds a m (n+1) (n+1) [] (by simp) s t ht)
    (actual_historyFrequencyBounds a m (n+1) (n+1) [] (by simp) v u hu)
    (fun z=>(he.1 (fun _=>0) z).1) (fun z=>(hf.1 (fun _=>0) z).1)
  let data := fun (_b : Index (sourceUpper βLong L)) (r : Fin Q) (q : ↥Eshort)=>
    canonicalSourcePairData k B (fun l=>(bound a m l:ℤ)) T J (n+1) true false s v e f t u
      i (x q) (r.val:ℤ) gate X (a*m) Wp Wl H D
  let lo := fun (_b : Index (sourceUpper βLong L)) (_t : Fin (2^(n+1)) ⊕ Fin (2^(n+1)))=>
    coarseLower D H (a*m) Wl
  let hi := fun (_b : Index (sourceUpper βLong L)) (_t : Fin (2^(n+1)) ⊕ Fin (2^(n+1)))=>-a*m+Wl
  let M := fun (_b : Index (sourceUpper βLong L))=>
    Real.exp ((-a*m+Wl)/2)*leafProfileBound (𝓕 SchwartzCutoff.psi)
  apply hprime Elong Eshort hElong hEshort (𝓕 SchwartzCutoff.psi) Q hQ χ hχ U V
    (fun p q=>terminalCorePairAmplitude k n width mWord hmWord B (fun l=>(bound a m l:ℤ)) T J
      s v σ π t u gate X (a*m) Wp Wl (insertCoordinate i (x q) (p.val:ℤ)))
    data lo hi M hZlong hZshort hshortlo hshorthi hlonglo hlonghi hU hV (hQcost.trans hmodmono)
  · intro b _hb
    refine ⟨?_,?_,hb.1.trans hmono,hb.2.2.trans hmono⟩
    · intro r q
      simpa only [data,lo,hi,M,D,e,f,neg_mul] using
        (terminalPairData_ranges_degree k n width mWord hmWord B (fun l=>(bound a m l:ℤ))
          T J s v σ π t u i (x q) (r.val:ℤ) gate (X:=X) (Δ:=a*m) (Wp:=Wp) (Wl:=Wl) (H:=H)
          (by linarith) N hw (𝓕 SchwartzCutoff.psi)).1
    · intro r q
      have hd := (terminalPairData_ranges_degree k n width mWord hmWord B (fun l=>(bound a m l:ℤ))
        T J s v σ π t u i (x q) (r.val:ℤ) gate (X:=X) (Δ:=a*m) (Wp:=Wp) (Wl:=Wl) (H:=H)
        (by linarith) N hw (𝓕 SchwartzCutoff.psi)).2
      exact (Nat.cast_le.mpr hd).trans (hb.2.1.trans hmono)
  · intro b p hp _hpblock r l hl q
    have hl' : historyPairResidueModulus k (n+1) s (paritySampledExpressions k n width mWord hmWord σ) t
      v (paritySampledExpressions k n width mWord hmWord π) u*l+r.val=p.val := hl
    have heq := terminalCorePairAmplitude_eq_data ha hm k n width mWord hmWord B T J s v σ π t u
      ht hu i (x q) gate r.val l (Δ:=a*m) (Wp:=Wp) (Wl:=Wl) hX
      (rowLogHeight_ge_log_two Cmod z βHeight L hCmod) hfreq N hw
      (by simpa only [hl'] using hvars p hp q)
    simpa only [data,m,H,D,e,f,hl,hl'] using heq

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
