import OAI.Computability.SpaceSimulation.Register.Ports
import OAI.Computability.SpaceSimulation.Stack.Duo

namespace OAI

/-! Uniform deterministic computation of binary register values.
Inputs in the main work ports are *charged* (only public input x
here besides the port). All pullbacks are mathematical indices;
no index or bound parameter is available to a program unless it is
in a port or provided in the inputs.
-/

namespace Fifths
variable {I X L : Type}

/-- Throughout, binary order LSB to MSB, ordinary canonical bits,
also on any supplied argument tapes. -/
def files (x : List X) : Inputs X Empty :=
  ⟨x, Empty.elim⟩

def file (n : ℕ) : Store Empty Unit := .init (fun _ => n.bits)

theorem file_ok {n B} : (file n).ok B ↔ n.size ≤ B := by
  simp [file,Store.init,Store.ok,Nat.size_eq_bits_len]

def Comp (x : I → List X) (S a b : I → ℕ) : Prop :=
  Works (fun i => files (x i)) S (fun i => file (a i)) (fun i => file (b i))
    (fun _ => ())

namespace Comp
variable {x : I → List X} {S a b c : I → ℕ}
open Function

theorem source (h : Comp x S a b) : Fits S a := by
  obtain ⟨d,r⟩ := Works.source h
  exact ⟨d,fun i => file_ok.mp (r i)⟩
theorem target (h : Comp x S a b) : Fits S b := by
  obtain ⟨d,r⟩ := Works.target h
  exact ⟨d,fun i => file_ok.mp (r i)⟩
theorem pull (h : Comp x S a b) {U : Type} (p : U → I) :
    Comp (fun i => x (p i)) (fun i => S (p i)) (fun i => a (p i)) (fun i => b (p i)) :=
  Works.pull h p
theorem up (h : Comp x S a b) {R} (p : Scaled R S) :
    Comp x R a b :=
  Works.up h p
theorem trans (h : Comp x S a b) (g : Comp x S b c) : Comp x S a c :=
  Works.seq h g
theorem congr (h : Comp x S a b) (g : ∀ i, b i = c i) : Comp x S a c :=
  funext g ▸ h
theorem refl (h : Fits S a) : Comp x S a a := by
  obtain ⟨d,r⟩ := h
  exact Works.direct (SM.pure ()) d (fun i => SM.exec_pure (file_ok.mpr (r i)))

theorem constant (h : Fits S a) (n : ℕ) : Comp x S a (fun _ => n) := by
  obtain ⟨d,r⟩ := h
  unfold Comp
  refine Works.direct ((SM.clear ()).seq (SM.prepend () n.bits)) (d+n.size) (fun i => ?_)
  have o : (file (a i)).ok ((d+n.size)*(S i+1)) := by
    refine file_ok.mpr (le_trans (r i) ?_)
    exact Nat.mul_le_mul_right _ (by omega)
  have e := SM.exec_clear (i := files (x i)) () o
  have l : (n.bits ++ ((file (a i)).set () []).st ()).length ≤ (d+n.size)*(S i+1) := by
    simp only [Store.set_same,List.append_nil,Nat.size_eq_bits_len]
    exact le_trans (by exact Nat.le_add_left n.size d)
      (Nat.le_mul_of_pos_right (d+n.size) (by omega))
  have f := SM.exec_prepend (i := files (x i)) () n.bits e.endOk l
  have g : (((file (a i)).set () []).set ()
      (n.bits ++ ((file (a i)).set () []).st ())) = file n := by
    refine Store.ext' rfl ?_
    intro y; cases y
    simp [file,Store.init]
  rw [g] at f
  exact SM.exec_seq e f

/-- Use one charged port of a larger file. Itself restores readers. -/
theorem onPort [DecidableEq L] (h : Comp x S a b) (k : L)
    (v : I → Store Empty L) (p : FitsStore S v) (o : ∀ i, (v i).ro = .home)
    (q : ∀ i, (v i).st k = (a i).bits) :
    Works (fun i => files (x i)) S v (fun i => (v i).set k (b i).bits) (fun _ => ()) := by
  let e : Unit ↪ L := ⟨fun _ => k, fun _ _ _ => Subsingleton.elim _ _⟩
  refine Works.addPorts h e _ _ p (fun i => ?_) (fun i => ?_) (fun i _ => ?_)
    (fun i _ => ?_) (fun i y l => ?_)
  · exact (o i).symm
  · exact (o i).symm
  · exact (q i).symm
  · exact (Store.set_same (v i) k _).symm
  · exact (Store.set_other (v i) _ (show y ≠ k from
      fun hy => l ⟨(), hy.symm⟩)).symm

section Extra
/-- For programs with dedicated scratch Sq. -/
def singleton (K : Type) (a : ℕ) := (file a).extra K

theorem singleton_set (U : Type) [DecidableEq U] (u v) :
    (singleton U u).set (.inl ()) v.bits = singleton U v := by
  refine Store.ext' rfl ?_
  rintro (k|k)
  · cases k; exact Store.set_same _ _ _
  · exact (Store.set_other _ _ (Sum.inr_ne_inl (a := ()) (b := k)))

theorem extra {U : Type} [Fintype U]
    (h : Works (fun i => files (x i)) S (fun i => singleton U (a i))
      (fun i => singleton U (b i)) (fun _ => ())) :
    Comp x S a b :=
  Works.hide U h

theorem checked {U : Type} [Fintype U] (M : SM X Empty (Unit ⊕ U) Unit) (d : ℕ)
    (r : ∀ i, M.Exec (files (x i)) (d*(S i+1)) (singleton U (a i))
      (singleton U (b i)) ()) : Comp x S a b :=
  ⟨U,inferInstance,M,d,r⟩

theorem checkSized {U : Type} [Fintype U] (M : SM X Empty (Unit ⊕ U) Unit)
    (h : Fits S a)
    (r : ∀ i B, (a i).size + 1 ≤ B → M.Exec (files (x i)) B (singleton U (a i))
      (singleton U (b i)) ()) : Comp x S a b := by
  obtain ⟨d,v⟩ := Scaled.add h (Scaled.const S 1)
  exact checked M d (fun i => r i _ (v i))
end Extra

theorem pair (h : Comp x S a b) (g : Comp x S a c) :
    Comp x S a (fun i => Bin.pair (b i) (c i)) := by
  let K := Unit ⊕ Bool
  let k : K := .inl ()
  let t : K := .inr false
  let y : K := .inr true
  have ak : k ≠ y := by decide +revert
  have bk : t ≠ k := by decide +revert
  have cy : t ≠ y := by decide +revert
  let v := fun i => singleton Bool (a i)
  let w := fun i => (v i).set y (a i).bits
  let d : I → Inputs X Empty := fun i => files (x i)
  have r₁ : Works d S v w (fun _ => ()) := by
    obtain ⟨l,r⟩ := h.source
    apply Works.direct (SM.clone k y t) l (fun i => ?_)
    have o : (v i).ok (l*(S i+1)) := Store.ok_extra.mpr (file_ok.mpr (r i))
    exact SM.exec_clone k y t ak.symm bk cy rfl rfl o
  let v' := fun i => (w i).set y (b i).bits
  have r₂ : Works d S w v' (fun _ => ()) :=
    h.onPort y _ r₁.target (fun _ => rfl) (fun _ => Store.set_same ..)
  let w' := fun i => (v' i).set k (c i).bits
  have r₃ : Works d S v' w' (fun _ => ()) := by
    apply g.onPort k _ r₂.target (fun _ => rfl) (fun i => ?_)
    simp only [v',w,Store.set_other _ _ ak]
    rfl
  let f := fun i => Bin.pair (b i) (c i)
  refine extra (Works.seq r₁ (Works.seq r₂ (Works.seq r₃ ?_)))
  obtain ⟨l,r⟩ := r₃.target
  obtain ⟨u,p⟩ := h.target.pair g.target
  refine Works.direct (SM.gather y k t) (l+u) (fun i => ?_)
  have hx : (w' i).st y = (b i).bits := by simp [w',v',ak.symm]
  have hy : (w' i).st k = (c i).bits := by simp [w']
  have hz : (w' i).st t = [] := by
    simp only [w',v',w,Store.set_other _ _ bk,Store.set_other _ _ cy]
    rfl
  have q : (Bin.frame ((w' i).st y) ((w' i).st k)).length ≤ (l+u)*(S i+1) := by
    rw [hx,hy,← Bin.pair_bits,Nat.size_eq_bits_len]
    exact le_trans (p i) (Nat.mul_le_mul_right _ (by omega))
  have e := SM.exec_gather (i := d i) y k t ak cy bk hz ((r i).mono
    (show l*(S i+1) ≤ (l+u)*(S i+1) from Nat.mul_le_mul_right _ (by omega))) q
  have eqn : (((w' i).set y []).set k (Bin.frame ((w' i).st y) ((w' i).st k))) =
      singleton Bool (f i) := by
    rw [hx,hy,← Bin.pair_bits]
    refine Store.ext' rfl ?_
    rintro (m|m)
    · cases m
      exact Store.set_same _ k _
    · cases m
      · change _ = ([] : List Bool)
        rw [show (Sum.inr false : K) = t from rfl]
        simp [bk,cy,hz]
      · change _ = ([] : List Bool)
        rw [show (Sum.inr true : K) = y from rfl]
        simp [ak.symm]
  rw [eqn] at e
  exact e

theorem projectF (h : Fits S (fun i => Bin.pair (b i) (c i))) :
    Comp x S (fun i => Bin.pair (b i) (c i)) b := by
  let k : Unit ⊕ Unit := .inl ()
  let t : Unit ⊕ Unit := .inr ()
  refine checkSized (SM.projF k t) h (fun i B p => ?_)
  have e : (singleton Unit (Bin.pair (b i) (c i))).ok B :=
    Store.ok_extra.mpr (file_ok.mpr (le_trans (Nat.le_succ _) p))
  have g := SM.exec_projF (i := files (x i)) k t (by decide +revert) e
    (b i).bits (c i).bits (Bin.pair_bits ..) rfl
  rw [show k = Sum.inl () from rfl,singleton_set] at g
  exact g

theorem projectS (h : Fits S (fun i => Bin.pair (b i) (c i))) :
    Comp x S (fun i => Bin.pair (b i) (c i)) c := by
  let k : Unit ⊕ Unit := .inl ()
  let t : Unit ⊕ Unit := .inr ()
  refine checkSized (SM.projS k t) h (fun i B p => ?_)
  have e : (singleton Unit (Bin.pair (b i) (c i))).ok B :=
    Store.ok_extra.mpr (file_ok.mpr (le_trans (Nat.le_succ _) p))
  have g := SM.exec_projS (i := files (x i)) k t (by decide +revert) e
    (b i).bits (c i).bits (Bin.pair_bits ..) rfl
  rw [show k = Sum.inl () from rfl,singleton_set] at g
  exact g

theorem left (h : Comp x S a (fun i => Bin.pair (b i) (c i))) :
    Comp x S a b :=
  h.trans (projectF h.target)
theorem right (h : Comp x S a (fun i => Bin.pair (b i) (c i))) :
    Comp x S a c :=
  h.trans (projectS h.target)
end Comp
end Fifths

end OAI
