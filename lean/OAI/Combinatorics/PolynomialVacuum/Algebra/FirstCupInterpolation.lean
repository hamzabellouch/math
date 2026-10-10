import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupPolynomial
import OAI.Combinatorics.PolynomialVacuum.Algebra.FirstCupNodeAssembly

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem update_nat_decidable (Y : ℕ → ℂ) (c : ℕ) (v : ℂ) :
    @Function.update ℕ (fun _ => ℂ) (fun a b => Classical.propDecidable (a=b)) Y c v=
      @Function.update ℕ (fun _ => ℂ) instDecidableEqNat Y c v := by
  funext k
  by_cases h : k=c <;> simp [h]

noncomputable def coordinatePolynomial {n : ℕ} (ψ : State n) (s : ℕ → Spin) :
    MvPolynomial ℕ ℂ := rename Fin.val (ψ (fun j => s j.val))

@[simp] theorem eval_coordinatePolynomial {n : ℕ} (ψ : State n) (s : ℕ → Spin) (X : ℕ → ℂ) :
    eval X (coordinatePolynomial ψ s)=liftState ψ X s := by
  simp [coordinatePolynomial,eval_rename,liftState,liftPolyTensor,Function.comp_def]

theorem coordinatePolynomial_degree {n : ℕ} (ψ : State n) (s : ℕ → Spin) (i : Fin n) :
    (coordinatePolynomial ψ s).degreeOf i.val=(ψ (fun j => s j.val)).degreeOf i := by
  exact degreeOf_rename_of_injective Fin.val_injective _

 

theorem firstCup_of_nodes {n : ℕ} (Ψ : State (n+4)) (ψ : State (n+2))
    (hd : ∀ s, (Ψ s).degreeOf (Fin.last (n+3)) ≤ n+3)
    (hf : ∀ s, s (Fin.last (n+3))=Spin.plus → (Ψ s).degreeOf (Fin.last (n+3)) ≤ n+2)
    (hψd : ∀ s, (ψ s).degreeOf (Fin.last (n+1)) ≤ n+1)
    (hψf : ∀ s, s (Fin.last (n+1))=Spin.plus → (ψ s).degreeOf (Fin.last (n+1)) ≤ n)
    (hnode : ∀ X, X 1=T*X 0 → ∀ i ≤ n+2, X (n+3)=T*X i →
      liftState Ψ X=naturalFusion (n+2) 0 X • cupLinear 0 (liftState ψ (skipTwo 0 X)))
    (hz : ∀ X s, X 1=T*X 0 → X (n+3)=0 → s (n+3)≠Spin.plus →
      liftState Ψ X s=(naturalFusion (n+2) 0 X • cupLinear 0 (liftState ψ (skipTwo 0 X))) s) :
    FirstCupReduction (liftState Ψ) (liftState ψ) (n+2) := by
  classical
  intro X hX
  rw [← lift_firstCupState]
  funext s
  let p := coordinatePolynomial Ψ s
  let r := coordinatePolynomial (firstCupState ψ) s
  have hp : p.degreeOf (n+3) ≤ n+3 := by
    rw [show p.degreeOf (n+3)=(Ψ (fun j => s j.val)).degreeOf (Fin.last (n+3)) from
      coordinatePolynomial_degree Ψ s (Fin.last (n+3))]
    exact hd _
  have hr (d : ℕ) (h : (ψ (fun j => s (j.val+2))).degreeOf (Fin.last (n+1)) ≤ d) :
      r.degreeOf (n+3) ≤ d+2 := by
    rw [show r.degreeOf (n+3)=(firstCupState ψ (fun j => s j.val)).degreeOf (Fin.last (n+3)) from
      coordinatePolynomial_degree (firstCupState ψ) s (Fin.last (n+3))]
    exact firstCupState_last_degree ψ _ _ (by simpa only [Fin.val_succ,Nat.add_assoc,Nat.reduceAdd] using h)
  have hn : ∀ Y, Y 1=T*Y 0 → ∀ i ∈ Finset.range (n+3),
      eval (Function.update Y (n+3) (T*Y i)) p=eval (Function.update Y (n+3) (T*Y i)) r := by
    intro Y hY i hi
    let Z := Function.update Y (n+3) (T*Y i)
    have hZi : Z i=Y i := by simp [Z,Function.update_of_ne (by have:=Finset.mem_range.mp hi; omega : i≠n+3)]
    have he := congrFun (hnode Z (by simpa [Z] using hY) i (by have:=Finset.mem_range.mp hi; omega)
      (by simp [Z,hZi])) s
    simpa only [p,r,eval_coordinatePolynomial,lift_firstCupState,update_nat_decidable] using he
  have he : cupSpecialize 0 1 p=cupSpecialize 0 1 r := by
    by_cases hs : s (n+3)=Spin.plus
    · apply cupSurface_eq_of_nodes 0 1 (n+3) (by omega) (Finset.range (n+3)) p r
      · simpa only [Finset.card_range] using (show p.degreeOf (n+3)<n+3 from by
          have hh := hf (fun j => s j.val) hs
          rw [← coordinatePolynomial_degree Ψ s (Fin.last (n+3))] at hh
          exact hh.trans_lt (by omega))
      · simpa only [Finset.card_range] using (hr n (hψf _ hs)).trans_lt (by omega : n+2<n+3)
      · intro Y hY i hi
        simpa only [update_nat_decidable] using hn Y hY i hi
    · apply cupSurface_eq_of_nodes_zero 0 1 (n+3) (by omega) (Finset.range (n+3)) p r
      · simpa only [Finset.card_range] using hp
      · simpa only [Finset.card_range,show n+1+2=n+3 by omega] using hr (n+1) (hψd _)
      · intro Y hY
        have he := hz (Function.update Y (n+3) 0) s (by simpa using hY) (by simp) hs
        simpa only [p,r,eval_coordinatePolynomial,lift_firstCupState,update_nat_decidable] using he
      · intro Y hY i hi
        simpa only [update_nat_decidable] using hn Y hY i hi
  simpa only [p,r,eval_coordinatePolynomial] using eval_eq_of_cupSurface_eq 0 1 p r he X hX

end PolynomialVacuumAlgebra

end OAI
