import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackCurrent

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M H : ℕ} [NeZero M]

private theorem stack_up_supported (hH : 0<H) (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (i : ZMod M) (j : ℤ) (s : Fin 3)
    (hu : (Vertex.up i j : Vertex M)∉bandSites M H)
    (hd : neighbor (.up i j) s∉bandSites M H) :
    orientedFlow (stackCurrent v a k) (.up i j,s)=0 := by
  rw [orientedFlow_up]
  simp only [mem_bandSites,InBand,vertexLayer] at hu
  fin_cases s
  · have ht : ¬(0≤j ∧ j<((H+1 : ℕ) : ℤ)) := by
      simp [mem_bandSites,InBand,vertexLayer,neighbor] at hd
      omega
    simp [stackValues,extendSpins_outside v j ht,charge]
  · simp [stackValues,extendSpins_outside k j hu,charge]
  · simp [stackValues,extendSpins_outside a j hu,charge]

theorem stack_supported (hH : 0<H) (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) : SupportedAt (bandSites M H) (stackCurrent v a k) := by
  intro g hg hr
  rcases g with ⟨g,s⟩
  cases g with
  | up i j => exact stack_up_supported hH v a k i j s hg hr
  | down i j =>
    have hz : orientedFlow (stackCurrent v a k) (reverseGerm (.down i j,s))=0 := by
      have hh : neighbor (neighbor (.down i j) s) s∉bandSites M H := by
        simpa only [neighbor_neighbor] using hg
      fin_cases s <;> apply stack_up_supported hH v a k <;>
        simpa only [reverseGerm,neighbor,ite_true,ite_false] using (by assumption)
    rw [orientedFlow_reverse] at hz
    exact neg_eq_zero.mp hz

omit [NeZero M] in
private theorem local_weight_ice [NeZero M] (q : Edge M →₀ ℤ) (v : Vertex M)
    (h : localCurrentWeight q v≠0) : LocalIce q v := by
  have hi : IceTriple (orientedFlow q (v,0)) (orientedFlow q (v,1)) (orientedFlow q (v,2)) := by
    by_contra hh
    exact h (by simp [localCurrentWeight,arrowVertexWeight,hh])
  have ht : ∀j : Fin 3,arrowTriple (orientedFlow q (v,0)) (orientedFlow q (v,1))
      (orientedFlow q (v,2)) j=orientedFlow q (v,j) := by
    intro j
    fin_cases j <;> rfl
  simpa only [IceTriple,ht,LocalIce] using hi

noncomputable def stackLocalWeight (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) : ℂ :=
  ∏j : Fin H,∏i : ZMod M,localCurrentWeight (stackCurrent v a k) (.up i j.val)*
      localCurrentWeight (stackCurrent v a k) (.down i j.val)

theorem stack_ice_of_weight_ne_zero (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (hw : stackLocalWeight v a k≠0) :
    ∀p∈bandSites M H,LocalIce (stackCurrent v a k) p := by
  have hn : ∀j : Fin H,∀i : ZMod M,
      localCurrentWeight (stackCurrent v a k) (.up i j.val)≠0 ∧
      localCurrentWeight (stackCurrent v a k) (.down i j.val)≠0 := by
    intro j i
    exact mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp
      (Finset.prod_ne_zero_iff.mp hw j (Finset.mem_univ _)) i (Finset.mem_univ _))
  intro p hp
  rw [mem_bandSites] at hp
  cases p with
  | up i l =>
    have hl : 0≤l ∧ l<(H : ℤ) := hp
    let j : Fin H:=⟨l.toNat,by omega⟩
    have hj : (j.val : ℤ)=l := by dsimp [j]; omega
    exact hj ▸ local_weight_ice _ _ (hn j i).1
  | down i l =>
    have hl : 0≤l ∧ l<(H : ℤ) := hp
    let j : Fin H:=⟨l.toNat,by omega⟩
    have hj : (j.val : ℤ)=l := by dsimp [j]; omega
    exact hj ▸ local_weight_ice _ _ (hn j i).2

private theorem charge_injective : Function.Injective charge := by
  intro a b h
  cases a <;> cases b <;> simp_all [charge]

 

theorem stackCurrent_injective (v v' : Fin (H+1) → ZMod M → Spin)
    (a k a' k' : Fin H → ZMod M → Spin) (he : stackCurrent v a k=stackCurrent v' a' k') :
    v=v' ∧ a=a' ∧ k=k' := by
  refine ⟨?_,?_,?_⟩
  · funext j i
    apply charge_injective
    have hh:=congrArg (fun q : Edge M →₀ ℤ => q ((i,(j.val : ℤ)),0)) he
    simpa [stackValues] using hh
  · funext j i
    apply charge_injective
    have hh:=congrArg (fun q : Edge M →₀ ℤ => q ((i,(j.val : ℤ)),2)) he
    simpa [stackValues] using hh
  · funext j i
    apply charge_injective
    have hh:=congrArg (fun q : Edge M →₀ ℤ => q ((i,(j.val : ℤ)),1)) he
    simpa [stackValues] using hh

 

theorem nonzero_stack_decomposition (hH : 0<H) (v : Fin (H+1) → ZMod M → Spin)
    (a k : Fin H → ZMod M → Spin) (hw : stackLocalWeight v a k≠0) :
    Nonempty (BoundaryDecomposition (bandSites M H) (stackCurrent v a k)) :=
  boundary_decomposition _ _ (stack_ice_of_weight_ne_zero v a k hw) (stack_supported hH v a k)

end PolynomialVacuumCylinder

end OAI
