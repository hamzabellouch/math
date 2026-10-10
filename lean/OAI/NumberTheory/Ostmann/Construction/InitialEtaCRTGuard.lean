import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTLeaf

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

theorem prime_pairwise_nodup (l : List ℕ) (hp : ∀ q ∈ l, q.Prime)
    (hc : l.Pairwise Nat.Coprime) : l.Nodup := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨hpl,hl⟩ := List.pairwise_cons.mp hc
    apply List.nodup_cons.mpr
    refine ⟨?_,ih (fun q hq => hp q (List.mem_cons_of_mem _ hq)) hl⟩
    intro hmem
    have he : p=1 := by simpa using hpl p hmem
    exact (hp p (by simp)).ne_one he

theorem actualCoefficient_zero_repeated (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ → ℕ) (X G : ℝ) (g : (p:ℕ) → ZMod p → ℂ)
    (bins : List ℕ → State → ℝ) (outside : List ℕ) (a : State)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime) (hnd : ¬(a.values ++ outside).Nodup) :
    actualCoefficient sources seed V X G g bins outside 0 a = 0 := by
  classical
  rw [actualCoefficient_level_zero]
  split_ifs with hs
  · exact False.elim (hnd (prime_pairwise_nodup _ hp (History.supported_root_coprime hs)))
  · rfl

open Classical in

theorem distinct_state_physical_eq_canonical (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ → ℕ) (G : ℝ)
    (b r : ℕ) (tb td : ℝ) (a : State) (outside : List ℕ)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime) (ht : a.TemplateAt 0)
    {X : ℝ} (hX : 0 < X)
    (hV : (a.values ++ outside).Nodup → Arithmetic.sourceStateBins b r tb td outside a ≠ 0 →
      ((outsideProduct outside*a.product:ℕ):ℝ)/(4*X) ≤ V 0) :
    (if (a.values ++ outside).Nodup then
      (Arithmetic.sourceStateBins b r tb td outside a:ℂ)*
        (∑' n : ℤ,statePhysicalProduct d P a outside n *
          SchwartzCutoff.psi ((n:ℝ)/X))/(Real.sqrt X:ℂ) else 0) =
    ∑ s : AllowedFrequency V 0,
      regularTransform (residueTransform d) (favorableGiantResidueTransform d P)
        outside (stateAtFrequency a s.val) *
      actualCoefficient sources seed V X G (residueTransform d)
        (Arithmetic.sourceStateBins b r tb td) outside 0 (stateAtFrequency a s.val) := by
  classical
  by_cases hd : (a.values ++ outside).Nodup
  · rw [ite_eq_left hd]
    exact state_normalized_poisson_sourceBins d P sources seed V G b r tb td a outside hp hd ht hX (hV hd)
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    rw [actualCoefficient_zero_repeated sources seed V X G (residueTransform d)
      (Arithmetic.sourceStateBins b r tb td) outside (stateAtFrequency a s.val) hp hd,mul_zero]

end Ostmann.Construction.InitialEta

end

end OAI
