import OAI.NumberTheory.Ostmann.Construction.InitialEtaCRTBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Construction.InitialEta

def completeTransform (g giant : (p:ℕ) → ZMod p → ℂ)
    (a : State) (outside : List ℕ) (s : ℤ) : ℂ :=
  let Q := outsideProduct outside*a.product
  giant a.giantPlus (modFraction a.giantPlus s (Q/a.giantPlus)) *
    giant a.giantMinus (modFraction a.giantMinus s (Q/a.giantMinus)) *
    (a.small.map fun q => g q.value (modFraction q.value s (Q/q.value))).prod *
    (outside.map fun q => g q (modFraction q s (Q/q))).prod

theorem stateLocalTest_unitary_product (d : Decomposition) (P : Finset ℕ)
    (a : State) (outside : List ℕ) [∀ i, NeZero (stateModuli a outside i)] (s : ℤ)
    (hp : ∀ q ∈ a.values ++ outside, q.Prime) :
    (∏ i,Supply.unitaryDFT (stateLocalTest d P a outside i)
      (crtFrequency (stateModuli a outside) s i)) =
      completeTransform (residueTransform d) (favorableGiantResidueTransform d P) a outside s := by
  have hpi := stateModuli_prime a outside hp
  have hpplus : a.giantPlus.Prime := hp _ (by simp [State.values])
  have hpminus : a.giantMinus.Prime := hp _ (by simp [State.values])
  let : NeZero a.giantPlus := ⟨hpplus.ne_zero⟩
  let : NeZero a.giantMinus := ⟨hpminus.ne_zero⟩
  let : ∀ i : Fin (crtTail a outside).length, NeZero ((crtTail a outside).get i) :=
    fun i => ⟨(hpi i.succ.succ).ne_zero⟩
  simp_rw [crtFrequency,otherProduct_eq_div _ (fun i => (hpi i).pos),stateModuli_prod]
  rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
  change Supply.unitaryDFT (favorableGiantResidueTest d P a.giantPlus)
      (modFraction a.giantPlus s ((outsideProduct outside*a.product)/a.giantPlus)) *
    (Supply.unitaryDFT (favorableGiantResidueTest d P a.giantMinus)
      (modFraction a.giantMinus s ((outsideProduct outside*a.product)/a.giantMinus)) *
      ∏i : Fin (crtTail a outside).length,
        Supply.unitaryDFT (residueTest d ((crtTail a outside).get i))
          (modFraction ((crtTail a outside).get i) s
            ((outsideProduct outside*a.product)/((crtTail a outside).get i)))) = _
  rw [favorableGiantResidueTest_fourier,favorableGiantResidueTest_fourier]
  have htail : (∏i : Fin (crtTail a outside).length,
      Supply.unitaryDFT (residueTest d ((crtTail a outside).get i))
        (modFraction ((crtTail a outside).get i) s
          ((outsideProduct outside*a.product)/((crtTail a outside).get i)))) =
      ((crtTail a outside).map fun q => residueTransform d q
        (modFraction q s ((outsideProduct outside*a.product)/q))).prod := by
    have he : (∏i : Fin (crtTail a outside).length,
        residueTransform d ((crtTail a outside).get i)
          (modFraction ((crtTail a outside).get i) s
            ((outsideProduct outside*a.product)/((crtTail a outside).get i)))) =
        ((crtTail a outside).map fun q => residueTransform d q
          (modFraction q s ((outsideProduct outside*a.product)/q))).prod := by
      rw [← List.prod_ofFn]
      exact congrArg List.prod (List.ofFn_getElem_eq_map (crtTail a outside)
        (fun q => residueTransform d q (modFraction q s ((outsideProduct outside*a.product)/q))))
    rw [← he]
    apply Finset.prod_congr rfl
    intro i hi
    have hq : ((crtTail a outside).get i).Prime := hp _ (by
      have hh := List.get_mem (crtTail a outside) i
      simpa only [crtTail,State.values,List.cons_append,List.mem_cons] using
        (Or.inr (Or.inr hh) : ((crtTail a outside).get i = a.giantPlus) ∨
          ((crtTail a outside).get i = a.giantMinus) ∨
          (crtTail a outside).get i ∈ crtTail a outside))
    let : NeZero ((crtTail a outside).get i) := ⟨hq.ne_zero⟩
    exact residueTest_fourier _ _ _
  rw [htail]
  simp only [crtTail,List.map_append,List.map_map,List.prod_append,completeTransform,Function.comp_def]
  ring

theorem completeTransform_eq_regular (g giant : (p:ℕ) → ZMod p → ℂ)
    (a : State) (outside : List ℕ) (ha : a.Positive) :
    completeTransform g giant a outside a.frequency =
      regularTransform g giant outside a *
        (outside.map fun q => g q (modFraction q a.frequency
          ((outsideProduct outside/q)*a.product))).prod := by
  have hden (q : ℕ) (hq : q ∈ a.values) :
      outsideProduct outside*a.product/q = outsideProduct outside*(a.product/q) := by
    rw [mul_comm (outsideProduct outside),mul_div_factor q a.product (outsideProduct outside)
      (ha q hq) (List.dvd_prod hq),mul_comm]
  have hp := hden a.giantPlus (by simp [State.values])
  have hm := hden a.giantMinus (by simp [State.values])
  have hs : (a.small.map fun q => g q.value (modFraction q.value a.frequency
      (outsideProduct outside*a.product/q.value))).prod =
      (a.small.map fun q => g q.value (modFraction q.value a.frequency
        (outsideProduct outside*(a.product/q.value)))).prod := by
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [hden q.value (by simp only [State.values,List.mem_cons]; exact Or.inr (Or.inr (List.mem_map.mpr ⟨q,hq,rfl⟩)))]
  have ho : (outside.map fun q => g q (modFraction q a.frequency
      (outsideProduct outside*a.product/q))).prod =
      (outside.map fun q => g q (modFraction q a.frequency
        ((outsideProduct outside/q)*a.product))).prod := by
    congr 1
    apply List.map_congr_left
    intro q hq
    by_cases hzero : q=0
    · simp [hzero]
    · rw [mul_div_factor q (outsideProduct outside) a.product
        (Nat.pos_of_ne_zero hzero) (List.dvd_prod hq)]
  simp only [completeTransform,regularTransform,hp,hm,hs,ho]

theorem completeTransform_scalar_eq_base (g giant : (p:ℕ) → ZMod p → ℂ)
    (X : ℝ) (ψhat : ℝ → ℂ) (bins : List ℕ → State → ℝ)
    (a : State) (outside : List ℕ) (ha : a.Positive) :
    (bins outside a:ℂ)*(Real.sqrt (X/(outsideProduct outside*a.product)):ℂ)*
      (completeTransform g giant a outside a.frequency *
        ψhat (-(a.frequency:ℝ)*X/(outsideProduct outside*a.product))) =
      regularTransform g giant outside a * baseCoefficient X ψhat g bins outside a := by
  rw [completeTransform_eq_regular g giant a outside ha]
  simp only [baseCoefficient, Nat.cast_mul]
  ring

end Ostmann.Construction.InitialEta

end

end OAI
