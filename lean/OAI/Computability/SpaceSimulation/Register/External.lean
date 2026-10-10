import OAI.Computability.SpaceSimulation.Register.Output
import OAI.Computability.SpaceSimulation.Stack.FromTM

namespace OAI

/-!
TM access interface inside indexed register computations. Charge the
arguments too. Tolerance of a scaled bound containing their lengths
lets us go both directions.
-/
namespace Fifths
variable {I X J K H Y : Type}

namespace Bin
def tuple (f : J → ℕ) : List J → ℕ
  | [] => 0
  | j::l => pair (f j) (tuple f l)
theorem tuple_fits (f : J → ℕ) (l : List J) (j : J) (h : j ∈ l) :
    (f j).size ≤ (tuple f l).size := by
  induction l with
  | nil => simp at h
  | cons k l ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl e => subst j; rw [tuple,pair_size]; omega
    | inr e =>
      exact le_trans (ih e) (by rw [tuple,pair_size]; omega)
end Bin

namespace SM
open Bin Function
variable [DecidableEq K]

def scatter (k t : K) (p : J → K) : List J → SM X H K Unit
  | [] => pure ()
  | j::l => (sendFirst k (p j) t).seq (scatter k t p l)

def spread (p : J → K) (f : J → ℕ) (s : Store H K) (l : List J) : Store H K :=
  l.foldl (fun u j => u.set (p j) (f j).bits) s

@[simp] theorem spread_nil (p : J → K) (f) (s : Store H K) : spread p f s [] = s := rfl
@[simp] theorem spread_cons (p : J → K) (f) (s : Store H K) (j) (l) :
    spread p f s (j::l) = spread p f (s.set (p j) (f j).bits) l := rfl
theorem spread_ro (p : J → K) (f) (s : Store H K) (l) :
    (spread p f s l).ro = s.ro := by
  induction l generalizing s <;> simp [*]

theorem spread_outside (p : J → K) (f) (s : Store H K) (l) (k)
    (o : ∀ j ∈ l, k ≠ p j) :
    (spread p f s l).st k = s.st k := by
  induction l generalizing s with
  | nil => rfl
  | cons j l ih =>
    simp at o
    simp [ih _ o.2,o.1]
theorem spread_inside (p : J ↪ K) (f : J → ℕ) (s : Store H K) (l : List J)
    (j) (e : j ∈ l) :
    (spread p f s l).st (p j) = (f j).bits := by
  classical
  induction l generalizing s with
  | nil => simp at e
  | cons a l ih =>
    rw [spread_cons]
    by_cases h : j ∈ l
    · exact ih _ h
    · simp [h] at e
      have o : ∀ x ∈ l, p j ≠ p x := fun x hx eqn => h (by rwa [p.injective eqn])
      rw [spread_outside _ _ _ _ _ o, e]
      simp

theorem exec_scatter {i : Inputs X H} {s : Store H K} {B}
    (k t : K) (b : t ≠ k) (p : J ↪ K)
    (u : ∀ j, p j ≠ k) (v : ∀ j, p j ≠ t) (f : J → ℕ)
    (l : List J) (n : l.Nodup) (o : s.ok B)
    (e : s.st k = (tuple f l).bits)
    (g : s.st t = []) (q : ∀ j ∈ l, s.st (p j) = []) :
    (scatter k t p l).Exec i B s (spread p f (s.set k []) l) () := by
  induction l generalizing s with
  | nil =>
    simp only [tuple,Nat.zero_bits] at e
    rw [spread_nil,← e,Store.set_self]
    exact exec_pure o
  | cons j l ih =>
    rw [List.nodup_cons] at n
    simp at q
    rw [tuple,pair_bits] at e
    let w := (s.set k (tuple f l).bits).set (p j) (f j).bits
    have h : (sendFirst k (p j) t).Exec i B s w () :=
      exec_sendFirst k (p j) t (u j) b (v j).symm o _ _ e q.1 g
    have r := ih n.2 h.endOk (by simp [w,Ne.symm (u j)])
      (by simp [w,Ne.symm (v j),b,g]) (by
        intro a e
        have x : a ≠ j := fun g => n.1 (g ▸ e)
        simp [w,p.injective.ne x,u,q.2 a e])
    have y : w.set k [] = (s.set k []).set (p j) (f j).bits := by
      unfold w
      rw [Store.set_swap _ (u j).symm]; simp
    rw [y] at r
    exact exec_seq h r
end SM

namespace Comp
open Bin Function
variable {x : I → List X} {S a : I → ℕ}

theorem tuple {f : I → J → ℕ} (l : List J)
    (h : ∀ j, Comp x S a (fun i => f i j)) (g : Fits S a) :
    Comp x S a (fun i => Bin.tuple (f i) l) := by
  induction l with
  | nil => exact Comp.constant g 0
  | cons j l ih => exact (h j).pair ih

/-- A standard binary-argument TM can take part in a computation.
Input word remains the one bounded-read-only-head interface. This is
used for calls to any fixed accessor. -/
theorem call [Fintype J] [Fintype Y] (M : TM X J Y) (code : Y → ℕ)
    (p : Fits S a) {f : I → J → ℕ} (h : ∀ j, Comp x S a (fun i => f i j))
    {y : I → Y} (d : ℕ)
    (r : ∀ i, M.Within (binaryIn (x i) (f i)) (y i) (d*(S i+1))) :
    Comp x S a (fun i => code (y i)) := by
  classical
  let L := (Finset.univ : Finset J).toList
  have l (j : J) : j ∈ L := by simp [L]
  let A i := Bin.tuple (f i) L
  have c : Comp x S a A := Comp.tuple L h p
  refine c.trans ?_
  obtain ⟨e,v⟩ := c.target
  let W := Unit ⊕ M.stkIdx
  let k : Unit ⊕ W := .inl ()
  let t : Unit ⊕ W := .inr (.inl ())
  let q : M.stkIdx ↪ Unit ⊕ W := Embedding.inr.trans Embedding.inr
  let g : J ↪ Unit ⊕ W :=
    { toFun := fun j => q (.inr (j,true))
      inj' := by
        intro a b z
        injection q.injective z with e
        exact congrArg Prod.fst e }
  have w₁ (j : J) : g j ≠ k := by simp [g,q,k]
  have w₂ (j : J) : g j ≠ t := by simp [g,q,t]
  let D : SM X Empty (Unit ⊕ W) Unit := SM.scatter k t g L
  let E := M.subroutine.pad q
  refine Comp.checked
    (D.seq (E.bind fun y => SM.prepend k (code y).bits))
    (d+e+SM.charLength code) (fun i => ?_)
  let B := (d+e+SM.charLength code)*(S i+1)
  let s := singleton W (A i)
  have sb : (A i).size ≤ B :=
    le_trans (v i) (Nat.mul_le_mul_right _ (by omega))
  have o : s.ok B := Store.ok_extra.mpr (file_ok.mpr sb)
  let inputs := binaryIn (x i) (f i)
  have j := SM.exec_scatter (i := files (x i)) k t (by simp [k,t]) g w₁ w₂
    (f i) L (Finset.nodup_toList _) o rfl rfl (fun _ _ => rfl)
  let loaded : Store Empty M.stkIdx := .init (M.loaded inputs.arg)
  let z (k : Unit ⊕ W) := ([] : List Bool)
  let nils : Store Empty (Unit ⊕ W) := .init z
  have n : s.set k [] = nils := by
    refine Store.ext' rfl ?_
    rintro (k|m)
    · cases k
      exact Store.set_same _ _ _
    · change (s.set _ _).st _ = s.st (.inr m)
      simp [k]
  have l₁ : loaded.pad q z = SM.spread g (f i) (s.set k []) L := by
    rw [n]; apply Store.pad_eq
    · rw [SM.spread_ro]; rfl
    · rintro (a | ⟨a,b⟩)
      · rw [SM.spread_outside _ _ _ _ _ (by simp [g,q])]
        rfl
      · cases b with
        | false =>
          rw [SM.spread_outside _ _ _ _ _ (by simp [g,q])]
          rfl
        | true =>
          exact (SM.spread_inside g (f i) nils L a (l a)).symm
    · intro v h
      rw [SM.spread_outside]
      · rfl
      · intro j _ p
        exact h ⟨.inr (j,true),p.symm⟩
  have l₂ : (Store.init (fun _ : M.stkIdx => [])).pad q z = nils :=
    Store.pad_eq _ _ rfl (fun _ => rfl) (fun _ _ => rfl)
  rw [← l₁] at j
  have m := M.subroutine_exec (i := inputs) (TM.Within.mono (r i)
      (show d * (S i+1) ≤ B from Nat.mul_le_mul_right _ (by omega)))
    (fun j => by
      change (f i j).bits.length ≤ B
      exact (Nat.size_eq_bits_len _).le.trans ((Bin.tuple_fits (f i) L j (l j)).trans sb))
  have u := M.subroutine.pad_exec q m (d := z) (fun _ => Nat.zero_le B)
  rw [l₂] at u
  -- write output code on main slot k and restore all others
  have p₀ : ((code (y i)).bits ++ nils.st k).length ≤ B := by
    rw [show nils.st k = [] from rfl,List.append_nil,Nat.size_eq_bits_len]
    exact (SM.char_le code _).trans <|
      le_trans (Nat.le_add_left _ (d+e))
        (Nat.le_mul_of_pos_right _ (show 0 < S i+1 by omega))
  have a := SM.exec_prepend (i := files (x i)) k _ u.endOk p₀
  have b₁ : nils.set k ((code (y i)).bits ++ nils.st k) =
      singleton W (code (y i)) := by
    rw [show nils.st k = [] from rfl,List.append_nil,← n,Store.set_set]
    refine Store.ext' rfl ?_
    rintro (t|w)
    · cases t; exact Store.set_same _ _ _
    · change (s.set _ _).st _ = s.st (.inr w)
      simp [k]
  rw [b₁] at a
  exact SM.exec_seq j (SM.exec_bind _ (fun y => SM.prepend k (code y).bits) u a)

end Comp
end Fifths

end OAI
