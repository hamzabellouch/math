import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinRowsBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries TemplateOneSidedPrior PrimeDyadicCover
attribute [local instance] Classical.propDecidable

theorem primeShellPrior_cmean_eq_subtype {A : ℕ} (E : Finset (PrimeUpTo A))
    (hE : 0<primeShellMass E) (f : PrimeUpTo A→ℂ) :
    (primeShellPrior E hE).cmean f = ∑r:↥E,((primeShellPrior E hE).mass r.val:ℂ)*f r.val := by
  unfold FinitePrior.cmean
  rw [Finset.sum_coe_sort E (fun p=>((primeShellPrior E hE).mass p:ℂ)*f p)]
  symm
  apply Finset.sum_subset (Finset.subset_univ E)
  intro p hp hn
  simp only [primeShellPrior_mass,ite_eq_right hn,zero_div,Complex.ofReal_zero,zero_mul]

def sourceShortMass {A : ℕ} (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (r : ↥E) : ℝ := (primeShellPrior E hE).mass r.val

theorem sourceShortMass_nonneg {A : ℕ} (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (r : ↥E) : 0 ≤ sourceShortMass E hE r := (primeShellPrior E hE).mass_nonneg r.val

theorem sourceShortMass_total {A : ℕ} (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E) :
    ∑r:↥E,sourceShortMass E hE r=1 := by
  calc
    _ = ∑p∈E,(primeShellPrior E hE).mass p := Finset.sum_coe_sort E _
    _ = ∑p:PrimeUpTo A,(primeShellPrior E hE).mass p := by
      apply Finset.sum_subset (Finset.subset_univ E)
      intro p hp hn
      simp only [primeShellPrior_mass,ite_eq_right hn,zero_div]
    _ = 1 := (primeShellPrior E hE).mass_total

theorem source_prime_bilinear_cmean_eq_rows {A : ℕ}
    (Q H : ℕ) (hQ : 0<Q) (Elong Eshort : Finset (PrimeUpTo A))
    (hElong : 0<primeShellMass Elong) (hEshort : 0<primeShellMass Eshort)
    (hmin : ∀p∈Elong,Q≤p.val) (hmax : ∀p∈Elong,p.val≤H)
    (χ : ∀r:↥Eshort,MulChar (ZMod r.val.val) ℂ)
    (U : PrimeUpTo A→ℂ) (V : ↥Eshort→ℂ) (F : PrimeUpTo A→↥Eshort→ℂ) :
    (primeShellPrior Elong hElong).cmean (fun p=>U p*
      ∑r:↥Eshort,((primeShellPrior Eshort hEshort).mass r.val:ℂ)*V r*
        χ r (p.val:ZMod r.val.val)*F p r) =
      ∑i:Index H,oneSidedMean (sourceRowMass Q H Elong i) (sourceShortMass Eshort hEshort)
        (fun x=>sourceTest U (rowValue Q (2*lower Q H i+1) x)) V
        (rowCharacterKernel (fun r:↥Eshort=>r.val.val) χ Q (2*lower Q H i+1)
          (fun r:Fin Q=>r.val) (sourceRowAmplitude Q F)) :=
  source_bilinear_cmean_eq_rows Q H hQ Elong hElong hmin hmax
    (fun r:↥Eshort=>r.val.val) χ (sourceShortMass Eshort hEshort) U V F

theorem source_prime_bilinear_cmean_eq_rows_of_log {A : ℕ}
    (Q : ℕ) (hQ : 0<Q) (Elong Eshort : Finset (PrimeUpTo A))
    (hElong : 0<primeShellMass Elong) (hEshort : 0<primeShellMass Eshort)
    {β L : ℝ} (hmin : ∀p∈Elong,Q≤p.val)
    (hmax : ∀p∈Elong,Real.log p.val≤Real.exp (β*L))
    (χ : ∀r:↥Eshort,MulChar (ZMod r.val.val) ℂ)
    (U : PrimeUpTo A→ℂ) (V : ↥Eshort→ℂ) (F : PrimeUpTo A→↥Eshort→ℂ) :
    (primeShellPrior Elong hElong).cmean (fun p=>U p*
      ∑r:↥Eshort,((primeShellPrior Eshort hEshort).mass r.val:ℂ)*V r*
        χ r (p.val:ZMod r.val.val)*F p r) =
      ∑i:Index (sourceUpper β L),
        oneSidedMean (sourceRowMass Q (sourceUpper β L) Elong i) (sourceShortMass Eshort hEshort)
          (fun x=>sourceTest U (rowValue Q (2*lower Q (sourceUpper β L) i+1) x)) V
          (rowCharacterKernel (fun r:↥Eshort=>r.val.val) χ Q
            (2*lower Q (sourceUpper β L) i+1) (fun r:Fin Q=>r.val) (sourceRowAmplitude Q F)) :=
  source_bilinear_cmean_eq_rows_of_log Q hQ Elong hElong hmin hmax
    (fun r:↥Eshort=>r.val.val) χ (sourceShortMass Eshort hEshort) U V F

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
