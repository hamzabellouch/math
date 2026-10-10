import OAI.Computability.Scheduling.OptimumCosts

namespace OAI

universe u1 u2 u3

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

theorem time_mapOption_linear {f : ∀ i, α i → β i} (R : Uniform f) (i : I)
    (o : Option (α i)) (C : ℕ)
    (ht : ∀ a ∈ o, R.time i a ≤ C*(volume o+1))
    (hv : ∀ a ∈ o, volume (f i a) ≤ volume o) :
    R.mapOption.time i o ≤ 1000000000*(C+1)*(volume o+1) := by
  let S : Uniform (fun i (a : α i × Unit) => f i a.1) := fst.comp R
  have hm := time_optionMap S i o () ((C+100)*(volume o+1)) (volume o) (by
    intro a ha
    have h := ht a ha
    have h' := volume_option_mem_le ha
    simp only [S,time_comp,time_fst,volume_pair,volume_unit]
    nlinarith) (by intro a ha; exact hv a ha)
  simp only [mapOption,time_congr,time_comp,time_pair,time_id,time_unit,Function.comp_apply,volume_pair,volume_unit]
  dsimp only [S] at hm
  simp only [volume_unit] at hm
  nlinarith [volume_pos o]

theorem time_functionListOption_le (n : ℕ) (o : Option (Fin n → ℕ)) :
    (functionList (α := fun _ => ℕ)).mapOption.time n o ≤ 10000000000*(volume o+1) := by
  have h := time_mapOption_linear (functionList (α := fun _ => ℕ)) n o 3 (by
    intro a ha
    have hv := volume_option_mem_le ha
    change volume a+2 ≤ _
    omega) (by intro a ha; rw [volume_ofFn]; exact volume_option_mem_le ha)
  omega

theorem time_sndFunctionListOption_le (n : ℕ) (o : Option (ℕ × (Fin n → ℕ))) :
    ((snd (α := fun _ : ℕ => ℕ)).comp (functionList (α := fun _ => ℕ))).mapOption.time n o ≤ 100000000000*(volume o+1) := by
  have h := time_mapOption_linear ((snd (α := fun _ : ℕ => ℕ)).comp (functionList (α := fun _ => ℕ))) n o 30 (by
    intro a ha
    have hv := volume_option_mem_le ha
    simp only [time_comp,time_snd]
    change (volume a+2)+(volume a.2+2)+10*(volume a.2+1) ≤ _
    rw [volume_prod] at hv ⊢
    omega) (by
      intro a ha
      have hv := volume_option_mem_le ha
      simp only [Function.comp_apply,volume_ofFn]
      rw [volume_prod] at hv
      omega)
  omega
end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
@[simp] theorem volume_optionFunctionList {n : ℕ} (o : Option (Fin n → ℕ)) :
    volume (o.map List.ofFn) = volume o := by cases o <;> rfl

theorem volume_optionSndFunctionList_le {n : ℕ} (o : Option (ℕ × (Fin n → ℕ))) :
    volume (o.map (fun a => List.ofFn a.2)) ≤ volume o := by
  cases o with
  | none => rfl
  | some a => simp only [Option.map_some,volume_some,volume_ofFn,volume_prod]; omega
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
@[simp] theorem volume_instance {n : ℕ} (G : Instance n) : volume G = volume G.edges := rfl
namespace Poly
variable {J : Type} {s n : J → ℕ} {d e : ℕ}
theorem volumeInstance (G : ∀ j, Instance (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (G j).edges.length) e) : Poly s (fun j => volume (G j)) (e+d) := by
  simp only [volume_instance]
  apply volumeList hl (show Poly s (fun j => 4*n j+3) d from by poly_bound)
  intro j a _ha
  rw [volume_prod,volume_fin,volume_fin]
  have := a.1.isLt; have := a.2.isLt
  omega
end Poly
namespace Costs
theorem edgePairEq : Poly (fun x : Σ n, (Fin n × Fin n) × (Fin n × Fin n) => x.1)
    (fun x => Uniform.edgePairEq.time x.1 x.2) 2 := by poly_auto

theorem edgeAt : Poly (fun x : Σ n, (Fin n × Fin n) × Instance n => x.1+x.2.2.edges.length)
    (fun x => Uniform.edgeAt.time x.1 x.2) 10 := by
  let s (x : Σ n, (Fin n × Fin n) × Instance n) := x.1+x.2.2.edges.length
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hl : Poly s (fun x => x.2.2.edges.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have hv := Poly.volumeInstance (fun x => x.2.2) hn hl
  poly_auto

theorem edgeMatrix : Poly (fun x : Σ n, Universe n × Instance n => x.1+x.2.2.edges.length)
    (fun x => Uniform.edgeMatrix.time x.1 x.2) 20 := by
  let s (x : Σ n, Universe n × Instance n) := x.1+x.2.2.edges.length
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hl : Poly s (fun x => x.2.2.edges.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have hv := Poly.volumeInstance (fun x => x.2.2) hn hl
  poly_auto
end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
theorem nextMatrixCell : Poly
    (fun x : Σ n, (Fin n × Fin n) × (Universe n × (Matrix n × Matrix n)) => x.1)
    (fun x => Uniform.nextMatrixCell.time x.1 x.2) 10 := by poly_auto
theorem nextMatrix : Poly
    (fun x : Σ n, Universe n × (Matrix n × Matrix n) => x.1)
    (fun x => Uniform.nextMatrix.time x.1 x.2) 20 := by poly_auto
theorem closureMatrixStep : Poly
    (fun x : Σ n, (Universe n × Matrix n) × Matrix n => x.1)
    (fun x => Uniform.closureMatrixStep.time x.1 x.2) 20 := by poly_auto

theorem reachMatrix : Poly (fun x : Σ n, Universe n × Instance n => x.1+x.2.2.edges.length)
    (fun x => Uniform.reachMatrix.time x.1 x.2) 30 := by
  let J := Σ n, Universe n × Instance n
  let s (x : J) := x.1+x.2.2.edges.length
  have hn : Poly s (fun x => x.1) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size s)
  have hl : Poly s (fun x => x.2.2.edges.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size s)
  have hv := Poly.volumeInstance (fun x => x.2.2) hn hl
  let a (x : J) : (Universe x.1 × Matrix x.1) × Matrix x.1 :=
    ((x.2.1,fun a b => decide (x.2.2.edge a b)),fun a b => decide (x.2.2.edge a b))
  let f (n : ℕ) (p : (Universe n × Matrix n) × Matrix n) :=
    (p.1,ThreeMachine.StackCompiler.nextMatrix p.1.2 p.2)
  have hN := hn.precomp (Sigma.fst : Poly.IterPool (fun x : J => x.1) → J)
  have hT : Poly (fun p : Poly.IterPool (fun x : J => x.1) => s p.1)
      (fun p => Uniform.closureMatrixStep.time p.1.1 ((f p.1.1)^[p.2.val] (a p.1))) 20 := by poly_auto
  have hV : Poly (fun p : Poly.IterPool (fun x : J => x.1) => s p.1)
      (fun p => volume ((f p.1.1)^[p.2.val] (a p.1))) 2 := by poly_auto
  have hI := Poly.iterateTime Uniform.closureMatrixStep (fun x : J => x.1) (fun x => x.1) a hn hT hV
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
