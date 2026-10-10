import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathProgram

namespace OAI

/-! Matrix semantics of the literal path-subdivision block. Its fresh labels
are exactly the two ordinary-spin labels in the singlet gadget. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListPathProgram
open Matrix MediatorGraph MediatorListProgram
open scoped BigOperators

def physicalLeft {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) : Fin 3 → Fin (n+r*2) :=
  ![fresh n r i 0,old n r (site 0),old n r (site 1)]

def physicalRight {n r : ℕ} (i : Fin r) (even : Bool) : Fin 3 → Fin (n+r*2) :=
  ![fresh n r i 1,fresh n r i 0,fresh n r i (qmaPathMember even 1)]

private theorem old_value (n r : ℕ) (i : Fin n) : (old n r i).val = i.val := rfl

private theorem fresh_value (n r : ℕ) (i : Fin r) (a : Fin 2) :
    (fresh n r i a).val = n+2*i.val+a.val := by
  change n+(a.val+2*i.val) = _
  omega

theorem bond_eq {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) (even : Bool) (R J : ℚ)
    (k : Fin 3) :
    bond ((n,even,R),i.val,(site 0).val,(site 1).val,J) k =
      ((physicalLeft i site k).val,(physicalRight (n := n) i even k).val,
        QuantumPathCode.coefficients (even,R,J) k.castSucc) := by
  cases even <;> fin_cases k <;>
    simp [bond,left,right,coefficient,physicalLeft,physicalRight,qmaPathMember,fresh_value,old_value]

theorem block_matrix {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) (even : Bool) (R J : ℚ) :
    SourceBondLists.matrix (n+r*2) (block ((n,even,R),i.val,(site 0).val,(site 1).val,J)) =
      ∑ k : Fin 3, (QuantumPathCode.coefficients (even,R,J) k.castSucc:ℂ) •
        sourceHeisenbergMatrix (n+r*2) (physicalLeft i site k) (physicalRight i even k) := by
  simp only [SourceBondLists.matrix,block,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [bond_eq,SourceBondLists.bondMatrix,dite_eq_left
    ⟨(physicalLeft i site k).isLt,(physicalRight i even k).isLt⟩]

theorem offset_cast (n i : ℕ) (site : Fin 2 → ℕ) (even : Bool) (R J : ℚ) :
    (offset ((n,even,R),i,site 0,site 1,J):ℝ) = qmaPathOffset (J:ℝ)+3*(R:ℝ)^2 :=
  QuantumPathCode.coefficients_offset (even,R,J)

theorem indexed_ofFn {m : ℕ} (p : Parameters) (f : Fin m → Bond) (i : Fin m) :
    indexed (i.val,(p,List.ofFn f)) = (p,i.val,f i) := by
  unfold indexed
  rw [List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn,Option.getD_some]

theorem family_ofFn {m : ℕ} (p : Parameters) (f : Fin m → Bond) :
    family (p,List.ofFn f) = (List.ofFn fun i => block (p,i.val,f i)).flatten := by
  have hm (g : ℕ → List Bond) :
      (List.range m).map g = List.ofFn (fun i : Fin m => g i.val) := by
    simpa only [List.length_range,List.getElem_range,Fin.val_cast] using
      (List.ofFn_getElem_eq_map (List.range m) g).symm
  unfold family
  rw [List.length_ofFn,hm]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin m → List Bond => List.ofFn g)
  funext i
  rw [indexed_ofFn]

theorem matrix_flatten (n : ℕ) (xss : List (List Bond)) :
    SourceBondLists.matrix n xss.flatten = (xss.map (SourceBondLists.matrix n)).sum := by
  simp only [SourceBondLists.matrix,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def]
  rfl

theorem family_matrix {n r : ℕ} (site : Fin r → Fin 2 → Fin n) (even : Bool)
    (R : ℚ) (J : Fin r → ℚ) :
    SourceBondLists.matrix (n+r*2)
      (family ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))) =
      ∑ i : Fin r, ∑ k : Fin 3, (QuantumPathCode.coefficients (even,R,J i) k.castSucc:ℂ) •
        sourceHeisenbergMatrix (n+r*2) (physicalLeft i (site i) k) (physicalRight i even k) := by
  rw [family_ofFn,matrix_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact Finset.sum_congr rfl (fun i _ => block_matrix i (site i) even R (J i))

theorem physical_sum {n r : ℕ} (i : Fin r) (site : Fin 2 → Fin n) (even : Bool)
    (R J : ℚ) :
    (∑ k : Fin 3, (QuantumPathCode.coefficients (even,R,J) k.castSucc:ℂ) •
      sourceHeisenbergMatrix (n+r*2) (physicalLeft i site k) (physicalRight i even k)) =
      ((R:ℝ)^2:ℂ) • sourceHeisenbergMatrix (n+r*2) (fresh n r i 0) (fresh n r i 1)+
        ∑ a : Fin 2, (qmaPathAmplitude even (R:ℝ) (J:ℝ) a:ℂ) •
          sourceHeisenbergMatrix (n+r*2) (old n r (site a))
            (fresh n r i (qmaPathMember even a)) := by
  cases even <;> simp [Fin.sum_univ_succ,physicalLeft,physicalRight,
    QuantumPathCode.coefficients,qmaPathAmplitude,qmaPathMember,add_assoc,Complex.ofReal_ratCast] <;>
    ext s t <;>
    simp only [Matrix.add_apply,Matrix.neg_apply,Matrix.smul_apply,smul_eq_mul,
      Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_ratCast]

theorem familyOffset_cast {n r : ℕ} (site : Fin r → Fin 2 → Fin n) (even : Bool)
    (R : ℚ) (J : Fin r → ℚ) :
    (familyOffset ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)):ℝ) =
      (∑ i : Fin r, qmaPathOffset (J i:ℝ))+3*r*(R:ℝ)^2 := by
  simp only [familyOffset,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  calc
    _ = ∑ i : Fin r, (offset ((n,even,R),0,(site i 0).val,(site i 1).val,J i):ℝ) := by
      push_cast
      rfl
    _ = ∑ i : Fin r, (qmaPathOffset (J i:ℝ)+3*(R:ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact offset_cast n 0 (fun a => (site i a).val) even R (J i)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

theorem matrix_ofFn {n m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ) :
    SourceBondLists.matrix n (List.ofFn fun i => ((left i).val,(right i).val,w i)) =
      ∑ i : Fin m, (w i:ℂ) • sourceHeisenbergMatrix n (left i) (right i) := by
  simp only [SourceBondLists.matrix,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [SourceBondLists.bondMatrix,dite_eq_left ⟨(left i).isLt,(right i).isLt⟩]

theorem retained_matrix {n m : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ) (r : ℕ) :
    SourceBondLists.matrix (n+r*2) (List.ofFn fun i => ((left i).val,(right i).val,w i)) =
      ∑ i : Fin m, (w i:ℂ) • sourceHeisenbergMatrix (n+r*2)
        (old n r (left i)) (old n r (right i)) :=
  matrix_ofFn (fun i => old n r (left i)) (fun i => old n r (right i)) w

theorem fixed_step_matrix {n m r : ℕ} (left right : Fin m → Fin n) (w : Fin m → ℚ)
    (site : Fin r → Fin 2 → Fin n) (even : Bool) (R c : ℚ) (J : Fin r → ℚ) :
    let selected := List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)
    SourceBondLists.matrix (n+r*2)
        ((List.ofFn fun i => ((left i).val,(right i).val,w i))++family ((n,even,R),selected))+
      ((c+familyOffset ((n,even,R),selected):ℚ):ℂ) • 1 =
        qmaPathsGraph left right (fun i => (w i:ℝ)) c R site (fun _ => even) (fun i => (J i:ℝ)) := by
  dsimp only
  have hoff :
      ((c+familyOffset ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i)):ℚ):ℂ) =
      ((((c:ℝ)+∑ i : Fin r, qmaPathOffset (J i:ℝ))+3*(r:ℝ)*(R:ℝ)^2:ℝ):ℂ) := by
    calc
      _ = ((c:ℝ)+(familyOffset ((n,even,R),List.ofFn fun i =>
        ((site i 0).val,(site i 1).val,J i)):ℝ):ℂ) := by simp
      _ = _ := by rw [familyOffset_cast]; push_cast; ring
  simp only [SourceBondLists.matrix,List.map_append,List.sum_append]
  change (SourceBondLists.matrix (n+r*2) (List.ofFn fun i =>
      ((left i).val,(right i).val,w i))+SourceBondLists.matrix (n+r*2)
        (family ((n,even,R),List.ofFn fun i => ((site i 0).val,(site i 1).val,J i))))+_ = _
  rw [retained_matrix,family_matrix,hoff]
  simp_rw [physical_sum]
  simp only [qmaPathsGraph,qmaExchangeMatrix,Fintype.sum_sum_type,Fintype.sum_prod_type,
    qmaParallelGraphLeft,qmaParallelGraphRight,qmaParallelGraphWeight,
    Finset.sum_add_distrib,Complex.ofReal_pow,Complex.ofReal_ratCast]

end ContinuumCoulomb.QuantumListPathProgram

end

end OAI
