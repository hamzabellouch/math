import OAI.Computability.StarHeight.SplitMetadata

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uT uP uC uM uS uK uM2 uM3
universe uM4

namespace ClockAffine

open scoped Classical
open RobustClock

variable {T : Type uT} {P : Type uP} {C : Type uC} {M : Type uM} {S : Type uS} {K : Type uK} [Fintype T] [Fintype P] [Fintype C]
  [Monoid M] [Field K] [AddCommGroup S] [Module K S]

variable (clock : Specification T P C)

def Edge (z : C → RobustClock.Circle) (a b : T) : Prop :=
  ∃ i ∈ clock.I a, ∃ j ∈ clock.J b, i + j = z

noncomputable def offChoice (z : C → RobustClock.Circle) : Option (T × T) :=
  if h : ∃ ab : T × T, ab.1 ≠ ab.2 ∧ Edge clock z ab.1 ab.2 then some h.choose else none

lemma offChoice_some {z : C → RobustClock.Circle} {ab : T × T}
    (he : offChoice clock z = some ab) :
    ab.1 ≠ ab.2 ∧ Edge clock z ab.1 ab.2 ∧
      ∀ a b, Edge clock z a b → a = ab.1 ∧ b = ab.2 := by
  classical
  unfold offChoice at he
  split_ifs at he with hx
  · have hab := Option.some.inj he
    have hh := hab ▸ hx.choose_spec
    refine ⟨hh.1,hh.2,?_⟩
    rcases clock.graph z with hd | ⟨a,b,_,_,hu⟩
    · exact False.elim (hh.1 (hd _ _ hh.2))
    · have ht := hu _ _ hh.2
      intro a' b' he'
      exact ⟨(hu _ _ he').1.trans ht.1.symm,(hu _ _ he').2.trans ht.2.symm⟩

lemma offChoice_none {z : C → RobustClock.Circle} (he : offChoice clock z = none)
    {a b : T} (hab : Edge clock z a b) : a = b := by
  classical
  by_contra hn
  have hx : ∃ ab : T × T, ab.1 ≠ ab.2 ∧ Edge clock z ab.1 ab.2 := ⟨(a,b),hn,hab⟩
  simp only [offChoice,dite_eq_left hx] at he
  cases he

lemma offChoice_of_offedge {z : C → RobustClock.Circle} {a b : T}
    (hn : a ≠ b) (he : Edge clock z a b) : offChoice clock z = some (a,b) := by
  cases hh : offChoice clock z with
  | none => exact False.elim (hn (offChoice_none clock hh he))
  | some ab =>
    have hp := (offChoice_some clock hh).2.2 _ _ he
    rcases ab with ⟨a',b'⟩
    dsimp at hp
    rcases hp with ⟨rfl,rfl⟩
    rfl

lemma edge_add (φ : ℤ →+ (C → RobustClock.Circle)) {q t k : ℤ} {a b : T}
    (hp : φ (k-t) ∈ clock.I a) (hs : φ (q-k) ∈ clock.J b) :
    Edge clock (φ (q-t)) a b := by
  refine ⟨_,hp,_,hs,?_⟩
  rw [← map_add]
  congr 1
  ring

variable (ρ : M → (S →ₗ[K] S))

def productTable {g : ℕ} (A C : M) (d : Fin g → M) : S →ₗ[K] S :=
  ρ (A * (List.ofFn d).prod * C)

structure Factors (M : Type uM2) (g : ℕ) where
  A : M
  entries : Fin g → M
  C : M

structure Snapshot (M : Type uM3) [Monoid M] (g : ℕ) where
  product : M
  boundaries : Option (Factors M g)
  product_eq : ∀ f, boundaries = some f → product = f.A * (List.ofFn f.entries).prod * f.C

variable {g : ℕ}
variable (β : M → M → (Fin g → M) → S) (X Y : T → S)

noncomputable def shift (z : C → RobustClock.Circle) (D : Snapshot M g) : S :=
  match offChoice clock z with
  | some ab => Y ab.2 - ρ D.product (X ab.1)
  | none => match D.boundaries with
    | none => 0
    | some f => β f.A f.C f.entries

noncomputable def update (z : C → RobustClock.Circle) (D : Snapshot M g) (x : S) : S :=
  ρ D.product x + shift clock ρ β X Y z D

lemma update_off {z : C → RobustClock.Circle} {a b : T} (D : Snapshot M g)
    (hn : a ≠ b) (he : Edge clock z a b) :
    update clock ρ β X Y z D (X a) = Y b := by
  simp only [update,shift,offChoice_of_offedge clock hn he]
  abel

lemma update_main {z : C → RobustClock.Circle} {f : Factors M g} (D : Snapshot M g)
    (hc : offChoice clock z = none) (hf : D.boundaries = some f) (x : S) :
    update clock ρ β X Y z D x = productTable ρ f.A f.C f.entries x + β f.A f.C f.entries := by
  simp only [update,shift,hc,hf,productTable,D.product_eq f hf]

lemma update_periodic {z : C → RobustClock.Circle} (D : Snapshot M g)
    (hc : offChoice clock z = none) (hf : D.boundaries = none) (x : S) :
    update clock ρ β X Y z D x = ρ D.product x := by
  simp only [update,shift,hc,hf,add_zero]

lemma independent_pair {z : C → RobustClock.Circle} {a b : T} (D : Snapshot M g)
    (he : Edge clock z a b)
    (hdiag : a = b → offChoice clock z = none →
      ρ D.product (X a) + (match D.boundaries with
        | none => 0
        | some f => β f.A f.C f.entries) = Y b) :
    update clock ρ β X Y z D (X a) = Y b := by
  cases hc : offChoice clock z with
  | none =>
    have hab := offChoice_none clock hc he
    simpa only [update,shift,hc] using hdiag hab hc
  | some ab =>
    have hh := offChoice_some clock hc
    have hab := hh.2.2 _ _ he
    have hn : a ≠ b := fun heq => hh.1 (hab.1.symm.trans (heq.trans hab.2))
    exact update_off clock ρ β X Y D hn he

structure Later (M : Type uM4) [Monoid M] (g : ℕ) where
  tailProduct : M
  boundaries : Option (Factors M g)
  tail_eq : ∀ f, boundaries = some f → tailProduct = f.A * (List.ofFn f.entries).prod * f.C

def Later.substitute (D : Later M g) (m : M) : Snapshot M g where
  product := m * D.tailProduct
  boundaries := D.boundaries.map (fun f => ⟨m * f.A,f.entries,f.C⟩)
  product_eq := by
    intro f hf
    obtain ⟨a,ha,hf⟩ := Option.map_eq_some_iff.mp hf
    subst f
    simp only [D.tail_eq a ha,mul_assoc]

noncomputable def hypothetical (z : C → RobustClock.Circle) (D : Later M g) :
    M → (S × K →ₗ[K] S × K) := fun m =>
  Homogenization.lift (ρ (m * D.tailProduct))
    (shift clock ρ β X Y z (D.substitute m))

lemma hypothetical_at (z : C → RobustClock.Circle) (D : Later M g) (m : M) (x : S) :
    hypothetical clock ρ β X Y z D m (x,1) =
      (update clock ρ β X Y z (D.substitute m) x,1) := by
  simp only [hypothetical,Homogenization.lift_apply_one,update,Later.substitute]

lemma hypothetical_actual (z : C → RobustClock.Circle) (D : Later M g) (m : M) :
    hypothetical clock ρ β X Y z D m =
      Homogenization.lift (ρ (D.substitute m).product)
        (shift clock ρ β X Y z (D.substitute m)) := rfl

end ClockAffine

end GeneralizedStarHeight

end OAI
