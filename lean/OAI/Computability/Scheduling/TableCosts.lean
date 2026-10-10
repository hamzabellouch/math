import OAI.Computability.Scheduling.SolverCosts

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
def tableBody {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : α i × γ i) => (f i x).map (fun b => (x.1,b))) :=
  (R.pair fst).comp ((swap : Uniform (fun i (x : β i × α i) => (x.2,x.1))).optionMap)
theorem time_tableBody_le {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (i : I) (a : α i) (e : γ i) :
    (tableBody R).time i (a,e) ≤ 10000000000*(R.time i (a,e)+volume (f i (a,e))+volume a+volume e+1) := by
  have hmem : ∀ b ∈ f i (a,e), volume b ≤ volume (f i (a,e)) := by
    intro b hb
    rw [show f i (a,e) = Option.some b from hb,volume_some]
    omega
  have h := time_optionMap (swap : Uniform (fun i (x : β i × α i) => (x.2,x.1))) i
    (f i (a,e)) a (100*(volume (f i (a,e))+volume a+1))
    (volume (f i (a,e))+volume a+1) (by
      intro b hb
      have := hmem b hb
      simp only [swap,time_pair,time_fst,time_snd,volume_pair]
      omega) (by
      intro b hb
      have := hmem b hb
      simp only [volume_pair]
      omega)
  simp only [tableBody,time_comp,time_pair,time_fst,volume_pair]
  omega
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler
variable {α : Type u5} {β : Type u6} [Coding α] [Coding β]
theorem volume_tableBody (o : Option β) (a : α) :
    volume (o.map (fun b => (a,b))) ≤ volume o+volume a+1 := by
  cases o <;> simp only [Option.map_none,Option.map_some,volume_none,volume_some,volume_pair] <;> omega
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u7} {J : Type u8} {s : J → ℕ} {α : I → Type u9} {β : I → Type u10} {γ : I → Type u11}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
theorem tableOfTime {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f)
    (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))
    {l t v a vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1) (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hv : Poly (fun p : Pool idx xs => s p.1) (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v)
    (ha : Poly (fun p : Pool idx xs => s p.1) (fun p => volume p.2.1) a)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => R.tableOf.time (idx j) (xs j,e j))
      (l+Max.max (Max.max t (Max.max v (Max.max a ve))) (Max.max vx (Max.max ve (l+Max.max v a)))) := by
  have hve := he.precomp (fun p : Pool idx xs => p.1)
  have hT : Poly (fun p : Pool idx xs => s p.1)
      (fun p => (Uniform.tableBody R).time (idx p.1) (p.2.1,e p.1)) (Max.max t (Max.max v (Max.max a ve))) := by
    apply of_le (fun p : Pool idx xs => Uniform.time_tableBody_le R (idx p.1) p.2.1 (e p.1))
    poly_bound
  have hV : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume ((f (idx p.1) (p.2.1,e p.1)).map (fun b => (p.2.1,b)))) (Max.max v a) := by
    apply of_le (fun p : Pool idx xs => volume_tableBody (f (idx p.1) (p.2.1,e p.1)) p.2.1)
    poly_bound
  exact filterMapTime idx xs e (Uniform.tableBody R) hl hT hx he hV
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev eval {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
    {f : ∀ i, α i → β i} (_R : Uniform f) := f
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (ms : ∀ j, Marks (n j)) (v : ∀ j, Algorithm.State (Fin (n j)))

theorem expandBody
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hml : Poly n (fun j => (ms j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly n (fun j => Uniform.expandBody.time (n j) (v j,(U j,(tab j,ms j)))) 90005 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hm
  have hTry := tryAdvance (fun p : Poly.ListPool ms => n p.1) (fun p => U p.1)
    (fun p => tab p.1) (fun p => p.2.1) (fun p => v p.1)
    (hl.precomp Sigma.fst) (fun p => ht p.1) (fun p => hm p.1 _ _ p.2.2)
  have hVolTry := Poly.volumeTryAdvance (fun p : Poly.ListPool ms => tab p.1)
    (fun p => p.2.1) (fun p => v p.1) ((Poly.size n).precomp Sigma.fst)
    (fun p => ht p.1) (fun p => hm p.1 _ _ p.2.2)
  have hLookup := Poly.volumeSmallLookup ms v (Poly.size n) hm
  have hFirst := Poly.volumeFirstResult ms (fun j u => Algorithm.tryAdvance (tab j) u (v j)) hVolTry
  have hpoolB := Poly.volumeSmallBlock (fun p : Poly.ListPool ms => p.2.1.2)
    ((Poly.size n).precomp Sigma.fst) (fun p => hm p.1 _ _ p.2.2)
  poly_auto

theorem expand (sts : ∀ j, List (Algorithm.State (Fin (n j))))
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (hml : Poly n (fun j => (ms j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly n (fun j => Uniform.expand.time (n j) (U j,(tab j,(sts j,ms j)))) 120008 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hm
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hBody := expandBody (fun p : Poly.ListPool sts => n p.1) (fun p => U p.1)
    (fun p => tab p.1) (fun p => ms p.1) (fun p => p.2.1)
    (hl.precomp Sigma.fst) (hml.precomp Sigma.fst) (fun p => ht p.1) (fun p => hm p.1)
  have hVolBody := Poly.volumeExpandBody (fun p : Poly.ListPool sts => tab p.1)
    (fun p => ms p.1) (fun p => p.2.1) ((Poly.size n).precomp Sigma.fst)
    (fun p => ht p.1) (fun p => hm p.1)
  have hVolBodyExact : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume (match Algorithm.lookup (ms p.1) p.2.1 with
        | some b => some b
        | none => Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab p.1) u p.2.1) (ms p.1))) 2 := by
    convert hVolBody using 1 <;> try rfl
    funext p
    cases Algorithm.lookup (ms p.1) p.2.1 <;> rfl
  have hVRun : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume (Uniform.eval Uniform.expandBody (n p.1)
        (p.2.1,(U p.1,(tab p.1,ms p.1))))) 2 := by
    convert hVolBodyExact using 1; try rfl
    funext p
    dsimp only [Uniform.eval]
    cases Algorithm.lookup (ms p.1) p.2.1 <;> rfl
  have hState : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume p.2.1) 2 := by poly_auto
  have he : Poly n (fun j => volume (U j,(tab j,ms j))) 30005 := by poly_auto
  have hTable := Poly.tableOfTime Uniform.expandBody n sts (fun j => (U j,(tab j,ms j)))
    hsl hBody hVRun hState hsv he
  have hExact : Poly n (fun j => Uniform.expandBody.tableOfA.time (n j)
      (sts j,(U j,(tab j,ms j)))) 120008 := hTable
  poly_auto

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}
theorem volumeExpand (tab : ∀ j, Table (n j)) (ms : ∀ j, Marks (n j))
    (sts : ∀ j, List (Algorithm.State (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (sts j).length) l)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly s (fun j => volume (Algorithm.expand (tab j) (sts j) (ms j))) (l+2*d) := by
  have hb := volumeExpandBody (fun p : ListPool sts => tab p.1) (fun p => ms p.1)
    (fun p => p.2.1) (hn.precomp Sigma.fst) (fun p => ht p.1) (fun p => hm p.1)
  have hv : Poly (fun p : ListPool sts => s p.1) (fun p => volume
      (((Algorithm.lookup (ms p.1) p.2.1).or
        (Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab p.1) u p.2.1) (ms p.1))).map
        (fun b => (p.2.1,b)))) (2*d) := by
    have hs : Poly (fun p : ListPool sts => s p.1) (fun p => volume p.2.1) (2*d) :=
      volumeState (hn.precomp (fun p : ListPool sts => p.1)) (fun p => p.2.1)
    apply of_le (fun p : ListPool sts => volume_tableBody _ p.2.1)
    poly_bound
  have h := volumeFilterMap (fun j : J => j) sts (fun j : J => (tab j,ms j))
    (f := fun _ x => ((Algorithm.lookup x.2.2 x.1).or
      (Algorithm.firstResult (fun u => Algorithm.tryAdvance x.2.1 u x.1) x.2.2)).map
      (fun b => (x.1,b))) hl hv
  convert h using 1
  funext j
  congr 1
  apply List.filterMap_congr
  intro a ha
  dsimp only
  cases Algorithm.lookup (ms j) a <;> rfl
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform
def initialMarkBody : Uniform (fun n (x : Algorithm.State (Fin n) × Table n) => Algorithm.lookup x.2 x.1.left) :=
  (snd.pair (fst.comp stateLeft)).comp (lookupA setEq)
theorem time_initialMarks (n : ℕ) (x : Table n × List (Algorithm.State (Fin n))) :
    initialMarks.time n x = (swap.comp initialMarkBody.tableOfA).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (tab : ∀ j, Table (n j))
theorem initialMarkBody (v : ∀ j, Algorithm.State (Fin (n j)))
    (hl : Poly n (fun j => (tab j).length) 30000) (ht : ∀ j, TableSmall (tab j)) :
    Poly n (fun j => Uniform.initialMarkBody.time (n j) (v j,tab j)) 60002 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hv := Poly.volumeSmallLookup tab (fun j => (v j).left) (Poly.size n) ht
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev MarkEnv (n : ℕ) := Universe n × (Table n × List (Algorithm.State (Fin n)))
def markingsStep : Uniform (fun n (x : MarkEnv n × Marks n) =>
    (x.1,Algorithm.expand x.1.2.1 x.1.2.2 x.2)) :=
  fst.pair ((((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
      ((fst.comp (snd.comp snd)).pair snd)))).comp expand)
theorem time_markings (n : ℕ) (x : ℕ × MarkEnv n) :
    markings.time n x =
      ((((fst.pair (snd.pair (snd.comp (snd.comp initialMarks)))).comp markingsStep.iterate).comp snd)).time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

theorem markingsStep_iterate {n : ℕ} (e : Uniform.MarkEnv n) (k : ℕ) :
    (fun p : Uniform.MarkEnv n × Marks n => (p.1,Algorithm.expand p.1.2.1 p.1.2.2 p.2))^[k]
      (e,Algorithm.tableOf e.2.2 (fun v => Algorithm.lookup e.2.1 v.left)) =
      (e,Algorithm.markings e.2.1 e.2.2 k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih]; rfl

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (sts : ∀ j, List (Algorithm.State (Fin (n j))))

theorem initialMarks
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) :
    Poly n (fun j => Uniform.initialMarks.time (n j) (tab j,sts j)) 90005 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hlook : Poly (fun p : Poly.ListPool sts => n p.1)
      (fun p => volume (Algorithm.lookup (tab p.1) p.2.1.left)) 2 :=
    Poly.volumeSmallLookup (fun p : Poly.ListPool sts => tab p.1) (fun p => p.2.1.left)
      ((Poly.size n).precomp Sigma.fst) (fun p => ht p.1)
  have hbody := initialMarkBody (fun p : Poly.ListPool sts => n p.1) (fun p => tab p.1)
    (fun p => p.2.1) (hl.precomp Sigma.fst) (fun p => ht p.1)
  have hA : Poly (fun p : Poly.ListPool sts => n p.1) (fun p => volume p.2.1) 2 := by poly_auto
  have hTable := Poly.tableOfTime Uniform.initialMarkBody n sts tab hsl hbody hlook hA hsv htv
  have hExact : Poly n (fun j => Uniform.initialMarkBody.tableOfA.time (n j) (sts j,tab j)) 90005 := hTable
  poly_auto

theorem markingsStep (ms : ∀ j, Marks (n j))
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (hml : Poly n (fun j => (ms j).length) 30003)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly n (fun j => Uniform.markingsStep.time (n j) ((U j,(tab j,sts j)),ms j)) 120008 := by
  have htv := Poly.volumeTable tab (Poly.size n) hl ht
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hmv := Poly.volumeMarks ms (Poly.size n) hml hm
  have hev := Poly.volumeExpand tab ms sts (Poly.size n) hsl ht hm
  have hel : Poly n (fun j => (Algorithm.expand (tab j) (sts j) (ms j)).length) 30003 :=
    Poly.of_le (fun j => Algorithm.tableOf_length _ _) hsl
  have h := expand n U tab ms sts hl hsl hml ht hm
  poly_auto
end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (sts : ∀ j, List (Algorithm.State (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

theorem markings
    (hl : Poly n (fun j => (tab j).length) 30000)
    (hsl : Poly n (fun j => (sts j).length) 30003)
    (ht : ∀ j, Algorithm.TableGood (matrixRel (M j)) (tab j))
    (hb : ∀ j, Algorithm.TableBounded (tab j))
    (hs : ∀ j u, u ∈ sts j → u.Compatible (matrixRel (M j)) (W j)) :
    Poly n (fun j => Uniform.markings.time (n j) (n j,(U j,(tab j,sts j)))) 120009 := by
  have hts : ∀ j, TableSmall (tab j) := fun j a b h => blockSmall_of_good (ht j a b h) (hb j a b h)
  have htv := Poly.volumeTable tab (Poly.size n) hl hts
  have hsv := Poly.volumeStateList sts (Poly.size n) hsl
  have hInit := initialMarks n tab sts hl hsl hts
  let ms (p : Poly.IterPool n) := Algorithm.markings (tab p.1) (sts p.1) p.2.1
  have hml : Poly (fun p : Poly.IterPool n => n p.1) (fun p => (ms p).length) 30003 :=
    Poly.of_le (fun p => Algorithm.markings_length _ _ _) (hsl.precomp Sigma.fst)
  have hms (p : Poly.IterPool n) : MarksSmall (ms p) := markings_small (matrixRel (M p.1)) (ht p.1) (hb p.1) (hs p.1) _
  have hmv := Poly.volumeMarks ms ((Poly.size n).precomp Sigma.fst) hml hms
  have hStep := markingsStep (fun p : Poly.IterPool n => n p.1) (fun p => U p.1) (fun p => tab p.1)
    (fun p => sts p.1) ms (hl.precomp Sigma.fst) (hsl.precomp Sigma.fst) hml (fun p => hts p.1) hms
  have htIter : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => Uniform.markingsStep.time (n p.1) ((fun q : Uniform.MarkEnv (n p.1) × Marks (n p.1) =>
        (q.1,Algorithm.expand q.1.2.1 q.1.2.2 q.2))^[p.2.1]
        ((U p.1,(tab p.1,sts p.1)),Algorithm.tableOf (sts p.1) (fun v => Algorithm.lookup (tab p.1) v.left)))) 120008 := by
    apply Poly.of_le _ hStep
    intro p
    exact le_of_eq (congrArg (fun q => Uniform.markingsStep.time (n p.1) q)
      (markingsStep_iterate (U p.1,(tab p.1,sts p.1)) p.2.1))
  have hvIter : Poly (fun p : Poly.IterPool n => n p.1)
      (fun p => volume ((fun q : Uniform.MarkEnv (n p.1) × Marks (n p.1) =>
        (q.1,Algorithm.expand q.1.2.1 q.1.2.2 q.2))^[p.2.1]
        ((U p.1,(tab p.1,sts p.1)),Algorithm.tableOf (sts p.1) (fun v => Algorithm.lookup (tab p.1) v.left)))) 30005 := by
    have hpair : Poly (fun p : Poly.IterPool n => n p.1)
        (fun p => volume ((U p.1,(tab p.1,sts p.1)),ms p)) 30005 := by
      have htv' := htv.precomp (fun p : Poly.IterPool n => p.1)
      have hsv' := hsv.precomp (fun p : Poly.IterPool n => p.1)
      poly_auto
    apply Poly.of_le _ hpair
    intro p
    exact le_of_eq (congrArg volume (markingsStep_iterate (U p.1,(tab p.1,sts p.1)) p.2.1))
  have hIter := Poly.iterateTime Uniform.markingsStep n n
    (fun j => ((U j,(tab j,sts j)),Algorithm.tableOf (sts j) (fun v => Algorithm.lookup (tab j) v.left)))
    (Poly.size n) htIter hvIter
  have hmi : Poly n (fun j => volume (Algorithm.tableOf (sts j) (fun v => Algorithm.lookup (tab j) v.left))) 30005 := by
    have hml : Poly n (fun j => (Algorithm.markings (tab j) (sts j) 0).length) 30003 :=
      Poly.of_le (fun j => Algorithm.markings_length _ _ _) hsl
    exact Poly.volumeMarks (d := 1) (l := 30003) (fun j => Algorithm.markings (tab j) (sts j) 0) (Poly.size n) hml
      (fun j => markings_small _ (ht j) (hb j) (hs j) 0)
  have hFinal := hvIter.precomp (fun j : J => (⟨j,⟨n j,by omega⟩⟩ : Poly.IterPool n))
  poly_auto
end ThreeMachine.StackCompiler.Costs
end

end OAI
