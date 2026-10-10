import OAI.Computability.SpaceSimulation.Stack.Edit
import OAI.Computability.SpaceSimulation.Binary

namespace OAI

namespace Fifths.SM
open Bin
variable {X J K : Type} [DecidableEq K]

/-- Copy stack k onto empty y using empty tmp t. -/
def clone (k y t : K) : SM X J K Unit :=
  (spill k t).seq
    (drain t (fun j => onto k j || onto y j) (fun b => [b]))

theorem exec_clone {i : Inputs X J} {s : Store J K} {B}
    (k y t : K) (a : y ≠ k) (b : t ≠ k) (c : t ≠ y)
    (g : s.st y = []) (h : s.st t = [])
    (o : s.ok B) :
    (clone k y t).Exec i B s (s.set y (s.st k)) () := by
  have e := exec_spill (i := i) (s := s) k t b.symm o (by simpa [h] using o k)
  simp only [h,List.append_nil] at e
  let u := (s.set k []).set t (s.st k).reverse
  let d := fun j => onto k j || onto y j
  let f := fun (j : Bool) => [j]
  have r : u.drained t d f = s.set y (s.st k) := by
    refine Store.ext' rfl ?_
    intro j
    by_cases hk : j = k
    · subst j; simp [Store.drained, Store.pre, u, d, onto, a.symm,b.symm,f]
    by_cases hy : j = y
    · subst j; simp [Store.drained, Store.pre, u, d, onto, a,c.symm,f,g]
    by_cases ht : j = t
    · subst j; simp [Store.drained, Store.pre, u, d, onto, b,c,h]
    · simp [Store.drained, Store.pre, u, d, onto, hk,hy,ht]
  unfold clone
  refine exec_seq e ?_
  rw [← r]
  exact exec_drain t d f (by simp [d,onto,b,c]) e.endOk (r.symm ▸ Store.set_ok o (o k))

/-- Two stack words become one prefix pair (on y); work slot t
initially empty and returned empty. -/
def gather (k y t : K) : SM X J K Unit :=
  (spill k t).seq <|
    (prepend y [true]).seq (drain t (onto y) esc)

theorem exec_gather {i : Inputs X J} {s : Store J K} {B}
    (k y t : K) (a : y ≠ k) (b : t ≠ k) (c : t ≠ y)
    (h : s.st t = [])
    (o : s.ok B)
    (p : (frame (s.st k) (s.st y)).length ≤ B) :
    (gather k y t).Exec i B s
      ((s.set k []).set y (frame (s.st k) (s.st y))) () := by
  let v := (s.set k []).set t (s.st k).reverse
  have e₁ : (spill k t).Exec i B s v () := by
    simpa only [h,List.append_nil] using
      exec_spill (i := i) k t b.symm o (by simpa [h] using o k)
  let u := v.set y (true :: s.st y)
  have vy : v.st y = s.st y := by simp [v,c.symm,a]
  have e₂ : (prepend y [true]).Exec i B v u () := by
    have q : ([true] ++ v.st y).length ≤ B := by
      rw [frameLength] at p
      simp only [vy,List.length_append,List.length_cons,List.length_nil]
      omega
    simpa only [u,vy,List.cons_append,List.nil_append] using
      exec_prepend (i := i) y [true] e₁.endOk q
  have r : u.drained t (onto y) esc = (s.set k []).set y (frame (s.st k) (s.st y)) := by
    refine Store.ext' rfl ?_
    intro j
    by_cases hy : j = y
    · subst j; simp [Store.drained,Store.pre, v,u,frame,onto,c,c.symm]
    by_cases ht : j = t
    · subst j; simp [Store.drained,Store.pre, u,v,onto,b,c,h]
    simp [Store.drained,Store.pre,u,v,onto,hy,ht]
  unfold gather
  rw [← r]
  refine exec_seq e₁ (exec_seq e₂ (exec_drain t _ _ (by simp [onto,c]) e₂.endOk ?_))
  rw [r]
  exact Store.set_ok (Store.set_ok o (by simp)) p

def parsePush (t : K) : Option Bool → SM X J K (Option Unit)
  | none => pure (some ())
  | some b => (prepend t [b]).seq (pure none)

def parseNext (k t : K) : Option Bool → SM X J K (Option Unit)
  | some false => (pop k).bind (parsePush t)
  | _ => pure (some ())

/-- Consume frame prefix of k, pushing first component reversed onto t. -/
def crack (k t : K) : SM X J K Unit :=
  ((pop k).bind (parseNext k t)).loop

theorem exec_crack {i : Inputs X J} {s : Store J K} {B}
    (k t : K) (c : t ≠ k) (o : s.ok B)
    (l r : List Bool) (e : s.st k = frame l r)
    (p : l.length + (s.st t).length ≤ B) :
    (crack k t).Exec i B s
      ((s.set k r).set t (l.reverse ++ s.st t)) () := by
  induction l generalizing s with
  | nil =>
    simp only [frame_nil] at e
    have f : (pop k).Exec i B s (s.set k r) (some true) := by
      simpa [e] using exec_pop (i := i) k o
    have h := loop_stop ((pop k).bind (parseNext k t)) (exec_bind _ (parseNext k t) f
      (show (parseNext k t (some true)).Exec i B _ _ (some ()) from exec_pure f.endOk))
    have g : (s.set k r).set t ([].reverse ++ s.st t) = s.set k r := by
      rw [show ([] : List Bool).reverse ++ s.st t = (s.set k r).st t by simp [c]]
      simp
    rw [g]
    exact h
  | cons b l ih =>
    let u := s.set k (b :: frame l r)
    let v := s.set k (frame l r)
    let w := v.set t (b :: s.st t)
    simp only [frame_cons] at e
    have f : (pop k).Exec i B s u (some false) := by
      simpa [u,e] using exec_pop (i := i) k o
    have g : (pop k).Exec i B u v (some b) := by
      simpa [u,v] using exec_pop (i := i) k f.endOk
    have h : (prepend t [b]).Exec i B v w () := by
      have hv : v.st t = s.st t := by simp [v,c]
      simp only [List.length_cons] at p
      have hw : ([b] ++ v.st t).length ≤ B := by simp [hv]; omega
      simpa only [w,hv,List.cons_append,List.nil_append] using
        exec_prepend (i := i) t [b] g.endOk hw
    have h' : ((pop k).bind (parseNext k t)).Exec i B s w none :=
      exec_bind _ _ f <|
        show (parseNext k t (some false)).Exec i B u w none from
          exec_bind _ _ g <|
            show (parsePush t (some b)).Exec i B v w none from exec_seq h (exec_pure h.endOk)
    have j := ih h.endOk (by simp [w,v,c.symm])
      (by simp [w]; simp at p; omega)
    have y : (w.set k r).set t (l.reverse ++ w.st t) =
        (s.set k r).set t ((b :: l).reverse ++ s.st t) := by
      simp only [w,v,Store.set_same,List.reverse_cons]
      rw [Store.set_swap _ c.symm]
      simp
    rw [y] at j
    exact loop_continue _ h' j

/-- Move first component of frame k to empty y normal order, leaving
second on k. -/
def sendFirst (k y t : K) : SM X J K Unit :=
  (crack k t).seq (spill t y)

theorem exec_sendFirst {i : Inputs X J} {s : Store J K} {B}
    (k y t : K) (a : y ≠ k) (b : t ≠ k) (c : t ≠ y)
    (o : s.ok B)
    (l r : List Bool) (e : s.st k = frame l r)
    (f : s.st y = []) (g : s.st t = []) :
    (sendFirst k y t).Exec i B s ((s.set k r).set y l) () := by
  have p : l.length ≤ B := by
    have q := o k
    rw [e,frameLength] at q
    omega
  have h := exec_crack (i := i) k t b o l r e (by simpa [g] using p)
  simp only [g,List.append_nil] at h
  have v := exec_spill (i := i) t y c h.endOk
    (by simpa [c.symm,a,f] using p)
  simp only [Store.set_same, List.reverse_reverse, Store.set_set,
    Store.set_other _ _ c.symm, Store.set_other _ _ a,f,List.append_nil] at v
  have q : (s.set k r).set t [] = s.set k r := by
    rw [show [] = (s.set k r).st t by simp [b,g]]
    simp
  rw [q] at v
  exact exec_seq h v

/-- In-place first or second projection. -/
def projF (k t : K) : SM X J K Unit :=
  (crack k t).seq <| (clear k).seq (spill t k)
def projS (k t : K) : SM X J K Unit :=
  (crack k t).seq (clear t)

theorem exec_projF {i : Inputs X J} {s : Store J K} {B}
    (k t : K) (b : t ≠ k)
    (o : s.ok B)
    (l r : List Bool) (e : s.st k = frame l r)
    (g : s.st t = []) :
    (projF k t).Exec i B s (s.set k l) () := by
  have p : l.length ≤ B := by
    have q := o k
    rw [e,frameLength] at q
    omega
  have h := exec_crack (i := i) k t b o l r e (by simpa [g] using p)
  simp only [g,List.append_nil] at h
  have v := exec_clear (i := i) k h.endOk
  have u := exec_spill (i := i) t k b v.endOk (by simpa [b] using p)
  unfold projF
  refine exec_seq h (exec_seq v ?_)
  convert u using 1 -- store equal
  simp only [Store.set_same, Store.set_other _ _ b, List.reverse_reverse, List.append_nil]
  refine Store.ext' rfl ?_
  intro j
  by_cases hk : j = k
  · subst j; simp
  by_cases ht : j = t
  · subst j; simp [b,g]
  simp [ht,hk]

theorem exec_projS {i : Inputs X J} {s : Store J K} {B}
    (k t : K) (b : t ≠ k)
    (o : s.ok B)
    (l r : List Bool) (e : s.st k = frame l r)
    (g : s.st t = []) :
    (projS k t).Exec i B s (s.set k r) () := by
  have p : l.length ≤ B := by
    have q := o k
    rw [e,frameLength] at q
    omega
  have h := exec_crack (i := i) k t b o l r e (by simpa [g] using p)
  have v := exec_seq h (exec_clear (i := i) t h.endOk)
  have q : (s.set k r).set t [] = s.set k r := by
    rw [show [] = (s.set k r).st t by simp [b,g]]
    simp
  rwa [Store.set_set,q] at v

end Fifths.SM

end OAI
