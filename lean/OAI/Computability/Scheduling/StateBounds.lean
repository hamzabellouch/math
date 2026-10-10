import OAI.Computability.Scheduling.StateCosts

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.Algorithm

theorem tableOf_length {K V : Type} (ks : List K) (f : K → Option V) :
    (tableOf ks f).length ≤ ks.length := List.length_filterMap_le _ _

theorem states_length {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (fs zs : List (Finset J)) (W : Finset J) :
    (states r fs zs W).length ≤ fs.length*zs.length := by
  calc
    _ ≤ (fs.flatMap (fun F => zs.map (State.candidate W F))).length := List.length_filter_le _ _
    _ = _ := by simp [List.length_flatMap]

theorem markings_length {J : Type} [DecidableEq J]
    (tab : List (Finset J × Block J)) (sts : List (State J)) (k : ℕ) :
    (markings tab sts k).length ≤ sts.length := by
  cases k <;> exact tableOf_length _ _

theorem layers_length {J : Type} [Fintype J] [DecidableEq J]
    (r : J → J → Prop) [DecidableRel r] (fs zs : List (Finset J)) (k : ℕ) :
    (layers r fs zs k).length ≤ fs.length+1 := by
  cases k with
  | zero => simp [layers]
  | succ k => exact (tableOf_length _ _).trans (Nat.le_add_right _ _)

end ThreeMachine.Algorithm

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

def BlockSmall {n : ℕ} (b : Algorithm.Block (Fin n)) : Prop :=
  b.length ≤ n ∧ ∀ v, b.time v ≤ n

def TableSmall {n : ℕ} (tab : Table n) : Prop := ∀ W b, (W,b) ∈ tab → BlockSmall b

def MarksSmall {n : ℕ} (marks : Marks n) : Prop := ∀ u b, (u,b) ∈ marks → BlockSmall b

theorem blockSmall_of_good {n : ℕ} {r : Fin n → Fin n → Prop} {W : Finset (Fin n)}
    {b : Algorithm.Block (Fin n)} (hg : b.Valid r W) (hb : b.Bounded) : BlockSmall b :=
  ⟨hg.length_le,fun v => (hb v).trans hg.length_le⟩

theorem layers_small {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]
    (fs zs : List (Finset (Fin n))) (k : ℕ) : TableSmall (Algorithm.layers r fs zs k) :=
  fun W b h => blockSmall_of_good (Algorithm.layers_good r fs zs k W b h)
    (Algorithm.layers_bounded r fs zs k W b h)

theorem markings_small {n : ℕ} (r : Fin n → Fin n → Prop) [DecidableRel r]
    {tab : Table n} {sts : List (Algorithm.State (Fin n))} {W : Finset (Fin n)}
    (ht : Algorithm.TableGood r tab) (hb : Algorithm.TableBounded tab)
    (hs : ∀ u ∈ sts, u.Compatible r W) (k : ℕ) : MarksSmall (Algorithm.markings tab sts k) :=
  fun u b h => blockSmall_of_good ((Algorithm.markings_good r ht hs k u b h).2)
    (Algorithm.markings_bounded hb k u b h)

theorem volume_table_le {n : ℕ} (tab : Table n) (ht : TableSmall tab) :
    volume tab ≤ 1+tab.length*(30*(n+1)^2+1) := by
  have h := volume_list_le tab (30*(n+1)^2) (by
    rintro ⟨W,b⟩ h
    have hW := volume_finset_le W
    have hb := volume_block_le b (ht W b h).1 (ht W b h).2
    rw [volume_pair]
    have hp : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega)
  omega

theorem volume_marks_le {n : ℕ} (ms : Marks n) (ht : MarksSmall ms) :
    volume ms ≤ 1+ms.length*(30*(n+1)^2+1) := by
  have h := volume_list_le ms (30*(n+1)^2) (by
    rintro ⟨u,b⟩ h
    have hW := volume_state_le u
    have hb := volume_block_le b (ht u b h).1 (ht u b h).2
    rw [volume_pair]
    have hp : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
    omega)
  omega

namespace Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

theorem volumeTable (tab : ∀ j, Table (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (tab j).length) l) (ht : ∀ j, TableSmall (tab j)) :
    Poly s (fun j => volume (tab j)) (l+2*d) := by
  apply of_le (fun j => volume_table_le (tab j) (ht j))
  poly_bound

theorem volumeMarks (ms : ∀ j, Marks (n j)) (hn : Poly s n d)
    (hl : Poly s (fun j => (ms j).length) l) (ht : ∀ j, MarksSmall (ms j)) :
    Poly s (fun j => volume (ms j)) (l+2*d) := by
  apply of_le (fun j => volume_marks_le (ms j) (ht j))
  poly_bound

theorem lengthTriples (hn : Poly s n d) :
    Poly s (fun j => (Structure.tripleList (List.finRange (n j))).length) (3*d) := by
  apply of_le (fun j => Structure.tripleList_length (List.finRange (n j)))
  simp only [List.length_finRange]
  poly_bound

theorem lengthAlphabet (hn : Poly s n d) :
    Poly s (fun j => (Structure.Atomic.alphabet (List.finRange (n j))).length) (3*d) := by
  apply of_le (fun j => Structure.Atomic.alphabet_length (List.finRange (n j)))
  simp only [Fintype.card_fin,List.length_finRange]
  poly_bound

theorem lengthFamily (M : ∀ j, Matrix (n j)) (K : ℕ) (hn : Poly s n d) :
    Poly s (fun j => (Structure.effectiveFamily (matrixRel (M j))
      (Structure.jobRank (matrixRel (M j))) (Structure.reverseJobRank (matrixRel (M j)))
      (List.finRange (n j)) K).length) (3*K*d) := by
  simp only [Structure.effectiveFamily_length]
  have h := (lengthAlphabet hn).pow K
  convert h.mul (const s (Structure.Formula.templates K).length) using 1; ring

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

theorem volume_block_bound {n : ℕ} (b : Block (Fin n)) (B : ℕ)
    (hl : b.length ≤ B) (ht : ∀ v, b.time v ≤ B) :
    volume b ≤ 4*(n+1)*(B+1) := by
  have h := volume_function_le b.time (2*B+1) (by intro v; rw [volume_nat]; have := ht v; omega)
  rw [volume_block,volume_nat]
  nlinarith

theorem volume_advance_le {n : ℕ} (v : Algorithm.State (Fin n)) (b c : Block (Fin n))
    (hb : BlockSmall b) (hc : BlockSmall c) :
    volume (v.advance b c) ≤ 100*(n+2)^2 := by
  have hl : (v.advance b c).length ≤ 2*n+1 := by
    change b.length+1+c.length ≤ _
    have := hb.1; have := hc.1; omega
  have ht (a : Fin n) : (v.advance b c).time a ≤ 2*n+1 := by
    simp only [Algorithm.State.advance,Block.append,Block.triple]
    have := hb.1; have := hb.2 a; have := hc.2 a
    split_ifs <;> omega
  have h := volume_block_bound (v.advance b c) (2*n+1) hl ht
  nlinarith

namespace Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

theorem volumeSmallBlock (b : ∀ j, Block (Fin (n j))) (hn : Poly s n d)
    (hb : ∀ j, BlockSmall (b j)) : Poly s (fun j => volume (b j)) (2*d) := by
  apply of_le (fun j => volume_block_le (b j) (hb j).1 (hb j).2)
  poly_bound

theorem volumeSmallLookup {K : J → Type} [∀ j, Coding (K j)] [∀ j, DecidableEq (K j)]
    (xs : ∀ j, List (K j × Block (Fin (n j)))) (k : ∀ j, K j)
    (hn : Poly s n d) (hb : ∀ j a b, (a,b) ∈ xs j → BlockSmall b) :
    Poly s (fun j => volume (Algorithm.lookup (xs j) (k j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 10*(n j+1)^2) (2*d) from by poly_bound)
  intro j b h
  exact volume_block_le b (hb j (k j) b (Algorithm.lookup_mem h)).1
    (hb j (k j) b (Algorithm.lookup_mem h)).2

theorem volumeAdvance (v : ∀ j, Algorithm.State (Fin (n j))) (b c : ∀ j, Block (Fin (n j)))
    (hn : Poly s n d) (hb : ∀ j, BlockSmall (b j)) (hc : ∀ j, BlockSmall (c j)) :
    Poly s (fun j => volume ((v j).advance (b j) (c j))) (2*d) := by
  apply of_le (fun j => volume_advance_le (v j) (b j) (c j) (hb j) (hc j))
  poly_bound

theorem volumeTryAdvance (tab : ∀ j, Table (n j)) (u : ∀ j, Algorithm.State (Fin (n j)) × Block (Fin (n j)))
    (v : ∀ j, Algorithm.State (Fin (n j))) (hn : Poly s n d)
    (ht : ∀ j, TableSmall (tab j)) (hb : ∀ j, BlockSmall (u j).2) :
    Poly s (fun j => volume (Algorithm.tryAdvance (tab j) (u j) (v j))) (2*d) := by
  apply volumeOption _ (show Poly s (fun j => 100*(n j+2)^2) (2*d) from by poly_bound)
  intro j b h
  simp only [Algorithm.tryAdvance] at h
  split_ifs at h with hp
  · cases hc : Algorithm.lookup (tab j) ((v j).left \ (u j).1.upto) with
    | none => simp [hc] at h
    | some c =>
      have he : (u j).1.advance (u j).2 c = b := by simpa [hc] using h
      subst b
      exact volume_advance_le _ _ _ (hb j) (ht j _ c (Algorithm.lookup_mem hc))
  · simp at h

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace Uniform
variable {I : Type u1} {α : I → Type u2} [∀ i, Coding (α i)]
theorem time_append_le (i : I) (xs ys : List (α i)) :
    append.time i (xs,ys) ≤ 100000*(xs.length+1)*(volume xs+volume ys+1) := by
  have h := time_consFold i xs.reverse ys
  have hr := time_reverse i xs
  simp only [List.length_reverse,volume_reverse] at h
  simp only [append,time_congr,time_comp,time_pair,time_fst,time_snd,volume_prod,Function.comp_apply,volume_reverse]
  nlinarith [volume_pos xs,volume_pos ys]
end Uniform
namespace Realizer
variable {α : Type u3} [Coding α]
theorem time_zero (x : α) : (zero : Realizer (fun _ : α => (0 : ℕ))).time x = 2 := rfl
theorem time_nil (x : α) : (nil : Realizer (fun _ : α => ([] : List α))).time x = 2 := rfl
theorem time_cons (x : α × List α) : cons.time x = volume x+2 := rfl
theorem time_reverse_le (xs : List α) :
    reverse.time xs ≤ 200*(xs.length+1)*(volume xs+1) :=
  Uniform.time_reverse (I := Unit) (α := fun _ => α) () xs

theorem volume_range_le (n : ℕ) : volume (List.range n) ≤ 10*(n+1)^2 := by
  have h := volume_list_le (List.range n) (2*n+1) (by
    intro a ha
    rw [volume_nat]
    have := List.mem_range.mp ha
    omega)
  simp only [List.length_range] at h
  nlinarith

theorem time_rangeStep_le (j n : ℕ) (hj : j ≤ n) :
    rangeStep.time (j,(List.range j).reverse) ≤ 100000*(n+1)^2 := by
  have hv := volume_range_le j
  have ht := time_succ_le j
  simp only [rangeStep,time_pair,time_comp,time_fst,time_cons,volume_prod,volume_nat,
    Function.comp_apply,volume_cons,volume_nat,volume_reverse]
  nlinarith

theorem time_range_le (n : ℕ) : range.time n ≤ 100000000000*(n+1)^3 := by
  have ht := time_iterate_le rangeStep n (0,[]) (100000*(n+1)^2) (20*(n+1)^2)
    (fun j hj => by rw [rangeStep_iterate]; exact time_rangeStep_le j n (by omega))
    (fun j hj => by
      rw [rangeStep_iterate,volume_prod,volume_nat,volume_reverse]
      have := volume_range_le j
      nlinarith)
  have hr := time_reverse_le (List.range n).reverse
  have hv := volume_range_le n
  simp only [List.length_reverse,List.length_range,volume_reverse] at hr
  simp only [range,time_congr,time_comp,time_pair,time_id,time_zero,time_snd,
    Function.comp_apply,rangeStep_iterate,volume_prod,volume_nat,volume_nil,volume_reverse,id_eq]
  have hz : (nil : Realizer (fun _ : ℕ => ([] : List ℕ))).time n = 2 := rfl
  rw [hz]
  nlinarith
end Realizer
namespace Uniform
variable {I : Type u4} {α : I → Type u5} [∀ i, Coding (α i)]
theorem time_orD_le {p q : ∀ i, α i → Prop}
    [∀ i, DecidablePred (p i)] [∀ i, DecidablePred (q i)]
    (P : Uniform (fun i x => decide (p i x))) (Q : Uniform (fun i x => decide (q i x)))
    (i : I) (x : α i) : (P.orD Q).time i x ≤ P.time i x+Q.time i x+20*volume x+11000 := by
  rw [orD,time_congr,time_comp,time_pair,time_uniform]
  have h := Realizer.time_or_le (decide (p i x),decide (q i x))
  have hp := volume_bool (decide (p i x)); have hq := volume_bool (decide (q i x))
  simp only [volume_pair] at *
  omega
end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u6} {J : Type u7} {s : J → ℕ} {α : I → Type u8} [∀ i, Coding (α i)]
abbrev IterPool (m : J → ℕ) := Σ j, Fin (m j+1)
theorem iterateTime {f : ∀ i, α i → α i} (R : Uniform f)
    (idx : J → I) (m : J → ℕ) (a : ∀ j, α (idx j)) {l t v : ℕ}
    (hm : Poly s m l)
    (ht : Poly (fun p : IterPool m => s p.1)
      (fun p => R.time (idx p.1) ((f (idx p.1))^[p.2.1] (a p.1))) t)
    (hv : Poly (fun p : IterPool m => s p.1)
      (fun p => volume ((f (idx p.1))^[p.2.1] (a p.1))) v) :
    Poly s (fun j => R.iterate.time (idx j) (m j,a j)) (l+Max.max t (Max.max v l)) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_iterate_le R (idx j) (m j) (a j)
    (C*(s j+2)^t) (D*(s j+2)^v)
    (fun k hk => hC ⟨j,⟨k,by omega⟩⟩) (fun k hk => hD ⟨j,⟨k,by omega⟩⟩))
  poly_bound
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s : J → ℕ} {d e : ℕ} {α β : J → Type}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]
omit [∀ j, Coding (α j)] in
theorem volumeFirstResult (xs : ∀ j, List (α j)) (f : ∀ j, α j → Option (β j))
    (hv : Poly (fun p : ListPool xs => s p.1) (fun p => volume (f p.1 p.2.1)) d) :
    Poly s (fun j => volume (Algorithm.firstResult (f j) (xs j))) d := by
  obtain ⟨C,hC⟩ := hv
  apply volumeOption _ (powerBase s C d)
  intro j b hb
  obtain ⟨a,ha,h⟩ := Algorithm.firstResult_some hb
  have ht := hC ⟨j,⟨a,ha⟩⟩
  dsimp only at ht
  rw [h,volume_some] at ht
  omega

omit [∀ j, Coding (β j)] in
theorem volumeOptionOr (a b : ∀ j, Option (α j))
    (ha : Poly s (fun j => volume (a j)) d) (hb : Poly s (fun j => volume (b j)) e) :
    Poly s (fun j => volume ((a j).or (b j))) (Max.max d e) := by
  apply of_le (g := fun j => Max.max (volume (a j)) (volume (b j))) _ (ha.max hb)
  intro j
  cases a j <;> simp
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
open Algorithm
variable {J : Type} {s n : J → ℕ} {d l : ℕ}
theorem volumeStateList (sts : ∀ j, List (Algorithm.State (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (sts j).length) l) :
    Poly s (fun j => volume (sts j)) (l+2*d) := by
  apply volumeList hl (show Poly s (fun j => 12*(n j+1)^2) (2*d) from by poly_bound)
  intro j a _ha
  exact volume_state_le a

theorem volumeSetList (xs : ∀ j, List (Finset (Fin (n j))))
    (hn : Poly s n d) (hl : Poly s (fun j => (xs j).length) l) :
    Poly s (fun j => volume (xs j)) (l+2*d) := by
  apply volumeList hl (show Poly s (fun j => 3*(n j+1)^2) (2*d) from by poly_bound)
  intro j a _ha
  exact volume_finset_le a

theorem volumeExpandBody (tab : ∀ j, Table (n j)) (ms : ∀ j, Marks (n j))
    (v : ∀ j, Algorithm.State (Fin (n j))) (hn : Poly s n d)
    (ht : ∀ j, TableSmall (tab j)) (hm : ∀ j, MarksSmall (ms j)) :
    Poly s (fun j => volume ((Algorithm.lookup (ms j) (v j)).or
      (Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab j) u (v j)) (ms j)))) (2*d) := by
  have h₁ := volumeSmallLookup ms v hn hm
  have h₂ : Poly s (fun j => volume (Algorithm.firstResult (fun u => Algorithm.tryAdvance (tab j) u (v j)) (ms j))) (2*d) := by
    apply volumeFirstResult
    exact volumeTryAdvance (fun p : ListPool ms => tab p.1) (fun p => p.2.1) (fun p => v p.1)
      (hn.precomp (fun p : ListPool ms => p.1)) (fun p => ht p.1)
      (fun p => hm p.1 _ _ p.2.2)
  simpa only [Nat.max_self] using volumeOptionOr _ _ h₁ h₂
end ThreeMachine.StackCompiler.Poly
end

end OAI
