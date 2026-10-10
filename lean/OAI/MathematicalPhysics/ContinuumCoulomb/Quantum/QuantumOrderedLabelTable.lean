import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelFamily

namespace OAI

/-! Ordered finite tables and their literal product enumeration. These
identities compare the computed lists with the actual finite Pauli family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open QuantumOrderedLabelData QuantumOrderedLabelFamily
open scoped BigOperators Classical

variable {ι κ : Type} {m n d : ℕ}

def table (e : Fin m ≃ κ) (index : ι → ℕ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ) : List Entry :=
  List.ofFn (fun i => (tag index (xs (e i)) (w (e i)),J (e i)))

def nextTerm (e : Fin m ≃ κ) (d : ℕ) : Fin (m*d) ≃ κ × Fin d :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr e (Equiv.refl _))

def index (q : Fin n ≃ ι) (i : ι) : ℕ := (q.symm i).val

def nextQubit (q : Fin n ≃ ι) (e : Fin m ≃ κ) : Fin (n+m) ≃ ι ⊕ κ :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr q e)

theorem nextQubit_index (q : Fin n ≃ ι) (e : Fin m ≃ κ) :
    index (nextQubit q e) = Sum.elim (index q) (fun a => n+(e.symm a).val) := by
  funext a
  cases a <;> simp [index,nextQubit]

private theorem lookup_ofFn {α : Type} (v : Fin m → α) (fallback : α) (i : Fin m) :
    ((List.ofFn v).drop i.val).headD fallback=v i := by
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.headD_cons,List.getElem_ofFn]

theorem product_table {α : Type} (v : Fin m × Fin d → α) :
    List.ofFn (fun i => v (finProdFinEquiv.symm i)) =
      (List.ofFn (fun a => List.ofFn (fun b => v (a,b)))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext b
  have h : finProdFinEquiv (a,b) =
      (⟨a.val*d+b.val,by nlinarith [a.isLt,b.isLt]⟩ : Fin (m*d)) := by
    apply Fin.ext
    change b.val+d*a.val=a.val*d+b.val
    ac_rfl
  rw [← h,Equiv.symm_apply_apply]

variable [Fintype κ]

theorem radius_table (e : Fin m ≃ κ) (ix : ι → ℕ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ) (N n : ℕ) :
    radius (N,n,table e ix xs w J)=QuantumOrderedSubdivision.scale J N := by
  simp only [radius,weights,table,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    QuantumOrderedWeightProgram.scale,QuantumOrderedSubdivision.scale,
    QuantumOrderedSubdivision.budget]
  rw [e.sum_comp (fun a => (1+|J a|)^2)]

/-- A literal stage is the same product-ordered finite table as its supplied
word and coefficient formulas. The hypotheses are pointwise identities. -/
theorem family_table (e : Fin m ≃ κ) (ix : ι → ℕ) (xs : κ → List ι)
    (w : κ → ι → Fin 4) (J : κ → ℚ) (N n : ℕ)
    (f : ℕ → List Letter → Fin d → List Letter)
    (g : ℚ → ℚ → Fin d → ℚ) :
    family d f g (N,n,table e ix xs w J) =
      List.ofFn (fun i : Fin (m*d) =>
        let p := nextTerm e d i
        (f (n+(e.symm p.1).val) (tag ix (xs p.1) (w p.1)) p.2,
          g (QuantumOrderedSubdivision.scale J N) (J p.1) p.2)) := by
  let v : Fin m → Entry := fun i => (tag ix (xs (e i)) (w (e i)),J (e i))
  have hr := radius_table e ix xs w J N n
  have hrows : (List.range m).map (fun i =>
      block d f g ((n+i,radius (N,n,table e ix xs w J)),((List.ofFn v).drop i).headD ([],0))) =
      List.ofFn (fun a : Fin m => block d f g
        ((n+a.val,QuantumOrderedSubdivision.scale J N),v a)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i < m := by simpa using hi
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
      rw [hr,lookup_ofFn v ([],0) ⟨i,hi'⟩]
  change ((List.range (List.ofFn v).length).map (fun i =>
    block d f g ((n+i,radius (N,n,table e ix xs w J)),((List.ofFn v).drop i).headD ([],0)))).flatten = _
  rw [List.length_ofFn,hrows]
  symm
  convert product_table (fun p : Fin m × Fin d =>
      (f (n+p.1.val) (v p.1).1 p.2,
        g (QuantumOrderedSubdivision.scale J N) (v p.1).2 p.2)) using 1
  · congr 1
    funext i
    simp only [nextTerm,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_fst,Prod.map_snd,
      Equiv.refl_apply,Equiv.symm_apply_apply,v]
  · rfl

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI
