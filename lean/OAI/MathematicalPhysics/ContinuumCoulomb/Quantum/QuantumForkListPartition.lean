import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListData

namespace OAI

/-! Adjacent pairing partitions the actual port lists without reordering or
dropping the odd final port. These identities connect the list compiler to the
full active-star Hamiltonian. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem pairs_nil : pairs [] = [] := rfl
theorem pairs_singleton (a : Port) : pairs [a] = [] := by simp [pairs]

theorem pairs_cons_cons (a b : Port) (ps : List Port) :
    pairs (a::b::ps) = (a,b)::pairs ps := by
  have hl : (a::b::ps).length/2=ps.length/2+1 := by simp only [List.length_cons]; omega
  unfold pairs
  rw [hl,List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1

theorem unpaired_cons_cons (a b : Port) (ps : List Port) :
    unpaired (a::b::ps)=unpaired ps := by
  have hl : (a::b::ps).length/2=ps.length/2+1 := by simp only [List.length_cons]; omega
  unfold unpaired
  rw [hl]
  have he : 2*(ps.length/2+1)=2*(ps.length/2)+2 := by omega
  rw [he]
  rfl

theorem pairs_partition (ps : List Port) :
    (pairs ps).flatMap (fun p => [p.1,p.2]) ++ unpaired ps=ps := by
  induction ps using List.twoStepInduction with
  | nil => rfl
  | singleton a => simp [pairs,unpaired]
  | cons_cons a b ps ih _ =>
    rw [pairs_cons_cons,unpaired_cons_cons]
    simpa only [List.flatMap_cons,List.append_assoc,List.cons_append,List.nil_append] using
      congrArg (fun xs => a::b::xs) ih

theorem paired_sum {M : Type*} [AddCommMonoid M] (f : Port → M) (ps : List Port) :
    (ps.map f).sum = ((pairs ps).map (fun p => f p.1+f p.2)).sum +
      ((unpaired ps).map f).sum := by
  conv_lhs => rw [← pairs_partition ps]
  simp only [List.map_append,List.sum_append,List.flatMap_def,List.map_flatten,
    List.sum_flatten,List.map_map,Function.comp_def,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero]

theorem catalog_cons (ps : List Port) (gs : Groups) :
    catalog (ps::gs) = (pairs ps).map (fun p => (0,p)) ++
      (catalog gs).map (fun p => (p.1+1,p.2)) := by
  unfold catalog
  simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,
    List.flatten_cons,groupAt_cons_zero,Function.comp_def,groupAt_cons_succ]
  rw [List.map_flatten,List.map_map]
  simp only [List.map_map,Function.comp_def]

end ContinuumCoulomb.QuantumForkList

end

end OAI
