import OAI.NumberTheory.Ostmann.Construction.DecompositionAmplitude
import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTPoisson
import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTSupport

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

theorem state_normalized_poisson_canonical (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (G : ℝ)
    (a : State) (outside : List ℕ)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime)
    (hnd : (a.values ++ outside).Nodup) (ht : a.TemplateAt 0)
    {X : ℝ} (hX : 0 < X)
    (hV : ((outsideProduct outside*a.product:ℕ):ℝ)/(4*X) ≤ V 0) (B : ℝ) :
    (B:ℂ)*(∑' n : ℤ,statePhysicalProduct d P a outside n *
      SchwartzCutoff.psi ((n:ℝ)/X))/(Real.sqrt X:ℂ) =
    ∑ s : AllowedFrequency V 0,
      regularTransform (residueTransform d) (favorableGiantResidueTransform d P)
        outside (stateAtFrequency a s.val) *
      actualCoefficient sources seed V X G (residueTransform d)
        (fun _ _ => B) outside 0 (stateAtFrequency a s.val) := by
  rw [state_normalized_poisson_base d P a outside hp hnd hX (V 0) hV B]
  rw [Finset.sum_coe_sort (Finset.Icc (-(V 0:ℤ)) (V 0:ℤ)) (fun s : ℤ =>
    regularTransform (residueTransform d) (favorableGiantResidueTransform d P) outside
      (stateAtFrequency a s) * actualCoefficient sources seed V X G (residueTransform d)
        (fun _ _ => B) outside 0 (stateAtFrequency a s))]
  apply Finset.sum_congr rfl
  intro s hs
  have ha : (stateAtFrequency a s).Positive := fun q hq =>
    (hp q (List.mem_append_left outside hq)).pos
  have hsmall : (stateAtFrequency a s).PrimeSmall := by
    intro q hq
    apply hp q.value
    simp only [State.values,List.cons_append,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨q,hq,rfl⟩)))
  have hv : (stateAtFrequency a s).frequency.natAbs ≤ V 0 := by
    have hh : |s| ≤ (V 0:ℤ) := abs_le.mpr (Finset.mem_Icc.mp hs)
    change s.natAbs ≤ V 0
    have hh' : (s.natAbs:ℤ) ≤ (V 0:ℤ) := by simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast hh' 
  exact (regular_mul_actualCoefficient_level_zero d P sources seed V X G
    (fun _ _ => B) outside (stateAtFrequency a s)
    (hp _ (by simp [State.values,stateAtFrequency])) (hp _ (by simp [State.values,stateAtFrequency])) ha hsmall ht
    (state_coprime_of_distinct a outside hp hnd) hv).symm

theorem sourceStateBins_at_frequency (b r : ℕ) (tb td : ℝ)
    (a : State) (outside : List ℕ) (s : ℤ) :
    Arithmetic.sourceStateBins b r tb td outside (stateAtFrequency a s) =
      Arithmetic.sourceStateBins b r tb td outside a := rfl

theorem state_normalized_poisson_sourceBins (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (G : ℝ)
    (b r : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime)
    (hnd : (a.values ++ outside).Nodup) (ht : a.TemplateAt 0)
    {X : ℝ} (hX : 0 < X)
    (hV : Arithmetic.sourceStateBins b r tb td outside a ≠ 0 →
      ((outsideProduct outside*a.product:ℕ):ℝ)/(4*X) ≤ V 0) :
    (Arithmetic.sourceStateBins b r tb td outside a:ℂ)*
      (∑' n : ℤ,statePhysicalProduct d P a outside n *
        SchwartzCutoff.psi ((n:ℝ)/X))/(Real.sqrt X:ℂ) =
    ∑ s : AllowedFrequency V 0,
      regularTransform (residueTransform d) (favorableGiantResidueTransform d P)
        outside (stateAtFrequency a s.val) *
      actualCoefficient sources seed V X G (residueTransform d)
        (Arithmetic.sourceStateBins b r tb td) outside 0 (stateAtFrequency a s.val) := by
  classical
  have hcoef (s : ℤ) :
      actualCoefficient sources seed V X G (residueTransform d)
        (fun _ _ => Arithmetic.sourceStateBins b r tb td outside a) outside 0 (stateAtFrequency a s) =
      actualCoefficient sources seed V X G (residueTransform d)
        (Arithmetic.sourceStateBins b r tb td) outside 0 (stateAtFrequency a s) := by
    simp only [actualCoefficient_level_zero,baseCoefficient,sourceStateBins_at_frequency]
  by_cases hb : Arithmetic.sourceStateBins b r tb td outside a = 0
  · simp only [hb,Complex.ofReal_zero,zero_mul,zero_div]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    rw [← hcoef,actualCoefficient_level_zero]
    simp [baseCoefficient,hb]
  · have hh := state_normalized_poisson_canonical d P sources seed V G a outside hp hnd ht
      hX (hV hb) (Arithmetic.sourceStateBins b r tb td outside a)
    simpa only [hcoef] using hh

end Ostmann.Construction.InitialEta

end

end OAI
