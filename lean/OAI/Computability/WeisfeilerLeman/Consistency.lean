import OAI.Computability.WeisfeilerLeman.Frames

namespace OAI

universe uP uE uΛ uT uLabel uL uB uV

namespace WLTime.Compression
variable {P : Type uP} {E : Type uE} {Λ : Type uΛ}

def frameTransition {K : ℕ} (old new : TypeNode K P E → Equiv.Perm Λ)
    (t : TypeNode K P E) : Equiv.Perm Λ := (old t).symm.trans (new t)

theorem frameTransition_link (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (l : TypeLink K E)
    (old new : TypeNode K P E → Equiv.Perm Λ)
    (ho : ∀ a, old (linkLeft K src l) a =
      old (linkRight K dst l) (linkMatch K perm l a))
    (hn : ∀ a, new (linkLeft K src l) a =
      new (linkRight K dst l) (linkMatch K perm l a)) :
    frameTransition old new (linkLeft K src l) =
      frameTransition old new (linkRight K dst l) := by
  ext a
  change new (linkLeft K src l) ((old (linkLeft K src l)).symm a) =
    new (linkRight K dst l) ((old (linkRight K dst l)).symm a)
  rw [hn]
  congr 1
  apply (old (linkRight K dst l)).injective
  rw [← ho, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem frameTransition_walk (K : ℕ) (src dst : E → P)
    (perm : E → Equiv.Perm Λ) (S : Finset (TypeLink K E))
    (old new : TypeNode K P E → Equiv.Perm Λ)
    (ho : ∀ l ∈ S, ∀ a, old (linkLeft K src l) a =
      old (linkRight K dst l) (linkMatch K perm l a))
    (hn : ∀ l ∈ S, ∀ a, new (linkLeft K src l) a =
      new (linkRight K dst l) (linkMatch K perm l a))
    {x y : TypeNode K P E} (w : (typeSupportGraph K src dst S).Walk x y) :
    frameTransition old new x = frameTransition old new y := by
  induction w with
  | nil => rfl
  | @cons x z y hxz w ih =>
    apply Eq.trans (b := frameTransition old new z) _ ih
    obtain ⟨_, l, hl, he | he⟩ := hxz
    · obtain ⟨rfl, rfl⟩ := he
      exact frameTransition_link K src dst perm l old new (ho l hl) (hn l hl)
    · obtain ⟨rfl, rfl⟩ := he
      exact (frameTransition_link K src dst perm l old new (ho l hl) (hn l hl)).symm

end WLTime.Compression

namespace WLTime.Compression

structure ConsistencyData (r m : ℕ) (P : Type uP) (E : Type uE) where
  dim : P → ℕ
  src : E → P
  dst : E → P
  domain : E → Fin r → Finset (Fin m)
  coord : (e : E) → (i : Fin r) → domain e i → Fin m
  coord_inj : ∀ e i, Function.Injective (coord e i)
  linearSrc : (e : E) → (Fin (dim (src e)) → F₂) →ₗ[F₂] F₂
  linearDst : (e : E) → (Fin (dim (dst e)) → F₂) →ₗ[F₂] F₂
  biasSrc : E → F₂
  biasDst : E → F₂

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData r m P E)

abbrev RealValue (p : P) := Fin (I.dim p) → F₂
abbrev Address (_I : ConsistencyData r m P E) := Fin r → Fin m

def Allowed (e : E) (a : I.Address) : Prop := ∀ i, a i ∈ I.domain e i

def transmit (e : E) (a : I.Address) (ha : I.Allowed e a) : I.Address :=
  fun i => I.coord e i ⟨a i, ha i⟩

def affineSrc (e : E) (x : I.RealValue (I.src e)) : F₂ := I.linearSrc e x + I.biasSrc e

def affineDst (e : E) (x : I.RealValue (I.dst e)) : F₂ := I.linearDst e x + I.biasDst e

def ArcConsistent : Prop :=
  ∃ Q : (p : P) → I.Address → Set (I.RealValue p),
    (∀ p a, (Q p a).Nonempty) ∧
    ∀ e a (ha : I.Allowed e a),
      I.affineSrc e '' Q (I.src e) a =
        I.affineDst e '' Q (I.dst e) (I.transmit e a ha)

noncomputable def coordinatePerm (e : E) (i : Fin r) : Equiv.Perm (Fin m) :=
  extendCoordinate (I.domain e i) (I.coord e i) (I.coord_inj e i)

theorem coordinatePerm_apply (e : E) (i : Fin r) (a : I.domain e i) :
    I.coordinatePerm e i a = I.coord e i a :=
  extendCoordinate_apply (I.domain e i) (I.coord e i) (I.coord_inj e i) a

noncomputable def permuteAddress (e : E) (a : I.Address) : I.Address := fun i => I.coordinatePerm e i (a i)

theorem permuteAddress_eq (e : E) (a : I.Address) (ha : I.Allowed e a) :
    I.permuteAddress e a = I.transmit e a ha := by
  funext i
  exact I.coordinatePerm_apply e i ⟨a i, ha i⟩

abbrev Value (K : ℕ) : TypeNode K P E → Type
  | .inl p => I.RealValue p
  | .inr _ => F₂

instance (K : ℕ) (t : TypeNode K P E) : AddCommGroup (I.Value K t) := by
  cases t <;> dsimp [Value] <;> infer_instance

instance (K : ℕ) (t : TypeNode K P E) : Module F₂ (I.Value K t) := by
  cases t <;> dsimp [Value] <;> infer_instance

instance (K : ℕ) (t : TypeNode K P E) : Fintype (I.Value K t) := by
  cases t <;> dsimp [Value] <;> infer_instance

noncomputable def transportForm (K : ℕ) {s t : TypeNode K P E} (hst : s = t)
    (f : I.Value K t →ₗ[F₂] F₂) : I.Value K s →ₗ[F₂] F₂ := hst.symm ▸ f

theorem transportForm_apply (K : ℕ) {s t : TypeNode K P E} (hst : s = t)
    (f : I.Value K t →ₗ[F₂] F₂) (x : (t : TypeNode K P E) → I.Value K t) :
    I.transportForm K hst f (x s) = f (x t) := by
  subst t
  rfl

noncomputable def leftForm (K : ℕ) (l : TypeLink K E) :
    I.Value K (linkLeft K I.src l) →ₗ[F₂] F₂ :=
  if h : l.2.val = 0 then
    I.transportForm K (t := .inl (I.src l.1)) (by simp only [linkLeft, dite_eq_left h]) (I.linearSrc l.1)
  else
    I.transportForm K (show linkLeft K I.src l = Sum.inr
      (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩) by simp only [linkLeft, dite_eq_right h])
      LinearMap.id

noncomputable def rightForm (K : ℕ) (l : TypeLink K E) :
    I.Value K (linkRight K I.dst l) →ₗ[F₂] F₂ :=
  if h : l.2.val = 4 * K then
    I.transportForm K (t := .inl (I.dst l.1)) (by simp only [linkRight, dite_eq_left h]) (I.linearDst l.1)
  else
    I.transportForm K (show linkRight K I.dst l = Sum.inr
      (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩) by simp only [linkRight, dite_eq_right h])
      LinearMap.id

def linkBias (K : ℕ) (l : TypeLink K E) : F₂ :=
  if l.2.val = 0 then I.biasSrc l.1 else
    if l.2.val = 4 * K then I.biasDst l.1 else 0

def ShiftSolves (K : ℕ) (S : Finset (TypeLink K E))
    (h : (t : TypeNode K P E) → I.Value K t) : Prop :=
  ∀ l ∈ S, I.leftForm K l (h (linkLeft K I.src l)) +
    I.rightForm K l (h (linkRight K I.dst l)) = I.linkBias K l

def rootedShift (K : ℕ) (h : (p : P) → I.RealValue p) :
    (t : TypeNode K P E) → I.Value K t
  | .inl p => h p
  | .inr (e, j) => if j.val < 2 * K then I.affineSrc e (h (I.src e))
      else I.affineDst e (h (I.dst e))

theorem rootedShift_link (K : ℕ) (hK : 0 < K) (h : (p : P) → I.RealValue p)
    (l : TypeLink K E) (hmid : l.2.val ≠ 2 * K) :
    I.leftForm K l (I.rootedShift K h (linkLeft K I.src l)) +
      I.rightForm K l (I.rootedShift K h (linkRight K I.dst l)) = I.linkBias K l := by
  have hj := l.2.isLt
  by_cases h0 : l.2.val = 0
  · have h4 : l.2.val ≠ 4 * K := by omega
    simp only [leftForm, rightForm, dite_eq_left h0, dite_eq_right h4]
    rw [transportForm_apply, transportForm_apply]
    simp only [rootedShift, LinearMap.id_coe, id_eq, h0, show 0 < 2 * K by omega, ite_true,
      affineSrc, linkBias]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · by_cases h4 : l.2.val = 4 * K
    · have hhalf : ¬l.2.val - 1 < 2 * K := by omega
      simp only [leftForm, rightForm, dite_eq_right h0, dite_eq_left h4]
      rw [transportForm_apply, transportForm_apply]
      simp only [rootedShift, LinearMap.id_coe, id_eq, ite_eq_right hhalf, affineDst, linkBias,
        ite_eq_right h0, ite_eq_left h4]
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    · have heq : l.2.val - 1 < 2 * K ↔ l.2.val < 2 * K := by omega
      simp only [leftForm, rightForm, dite_eq_right h0, dite_eq_right h4]
      rw [transportForm_apply, transportForm_apply]
      simp only [rootedShift, LinearMap.id_coe, id_eq, linkBias, ite_eq_right h0, ite_eq_right h4,
        heq, CharTwo.add_self_eq_zero]

def interiorShift (K : ℕ) (s : F₂) : (t : TypeNode K P E) → I.Value K t
  | .inl _ => 0
  | .inr _ => s

theorem interiorShift_link (K : ℕ) (s : F₂) (l : TypeLink K E)
    (h0 : l.2.val ≠ 0) (h4 : l.2.val ≠ 4 * K) :
    I.leftForm K l (I.interiorShift K s (linkLeft K I.src l)) +
      I.rightForm K l (I.interiorShift K s (linkRight K I.dst l)) = I.linkBias K l := by
  simp only [leftForm, rightForm, dite_eq_right h0, dite_eq_right h4]
  rw [transportForm_apply, transportForm_apply]
  simp only [interiorShift, LinearMap.id_coe, id_eq, linkBias, ite_eq_right h0, ite_eq_right h4,
    CharTwo.add_self_eq_zero]

theorem leftForm_section_zero (K : ℕ) (l : TypeLink K E) (h0 : l.2.val = 0)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.leftForm K l (h (linkLeft K I.src l)) = I.linearSrc l.1 (h (.inl (I.src l.1))) := by
  simp only [leftForm, dite_eq_left h0]
  exact I.transportForm_apply K _ _ h

theorem leftForm_section_internal (K : ℕ) (l : TypeLink K E) (h0 : l.2.val ≠ 0)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.leftForm K l (h (linkLeft K I.src l)) =
      h (.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)) := by
  simp only [leftForm, dite_eq_right h0]
  exact I.transportForm_apply K _ _ h

theorem rightForm_section_last (K : ℕ) (l : TypeLink K E) (h4 : l.2.val = 4 * K)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.rightForm K l (h (linkRight K I.dst l)) = I.linearDst l.1 (h (.inl (I.dst l.1))) := by
  simp only [rightForm, dite_eq_left h4]
  exact I.transportForm_apply K _ _ h

theorem rightForm_section_internal (K : ℕ) (l : TypeLink K E) (h4 : l.2.val ≠ 4 * K)
    (h : (t : TypeNode K P E) → I.Value K t) :
    I.rightForm K l (h (linkRight K I.dst l)) =
      h (.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩)) := by
  simp only [rightForm, dite_eq_right h4]
  exact I.transportForm_apply K _ _ h

noncomputable def canonicalShift (K : ℕ) (S : Finset (TypeLink K E))
    (x : (p : P) → I.RealValue p) (z : E → F₂) (t : TypeNode K P E) : I.Value K t := by
  classical
  exact if HasReal K I.src I.dst S t then I.rootedShift K x t else
    match t with
    | .inl p => x p
    | .inr (e, _) => z e

theorem canonicalShift_solves [DecidableEq E] (K : ℕ) (hK : 0 < K)
    (S : Finset (TypeLink K E)) (hS : S.card ≤ K)
    (x : (p : P) → I.RealValue p) (z : E → F₂) :
    I.ShiftSolves K S (I.canonicalShift K S x z) := by
  classical
  intro l hl
  have hreach := support_link_reachable K I.src I.dst S hl
  have heq := hasReal_of_reachable K I.src I.dst S hreach
  by_cases hreal : HasReal K I.src I.dst S (linkLeft K I.src l)
  · have hreal' := heq.mp hreal
    simp only [canonicalShift, ite_eq_left hreal, ite_eq_left hreal']
    apply I.rootedShift_link K hK
    intro hmid
    obtain ⟨p, hp⟩ := hreal
    have hd := reachable_real_depth K I.src I.dst hK S hS p hp
    have hm := (link_midpoint_depth K I.src I.dst hK l hmid).1
    omega
  · have hreal' := mt heq.mpr hreal
    have h0 : l.2.val ≠ 0 := by
      intro h
      apply hreal
      simpa only [linkLeft, dite_eq_left h] using hasReal_inl K I.src I.dst S (I.src l.1)
    have h4 : l.2.val ≠ 4 * K := by
      intro h
      apply hreal'
      simpa only [linkRight, dite_eq_left h] using hasReal_inl K I.src I.dst S (I.dst l.1)
    rw [I.leftForm_section_internal K l h0, I.rightForm_section_internal K l h4]
    have hlreal : ¬ HasReal K I.src I.dst S
        (.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)) := by
      simpa only [linkLeft, dite_eq_right h0] using hreal
    have hrreal : ¬ HasReal K I.src I.dst S
        (.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩)) := by
      simpa only [linkRight, dite_eq_right h4] using hreal'
    simp only [canonicalShift, ite_eq_right hlreal, ite_eq_right hrreal, linkBias,
      ite_eq_right h0, ite_eq_right h4, CharTwo.add_self_eq_zero]

theorem rootedShift_congr (K : ℕ) (x y : (p : P) → I.RealValue p)
    (t : TypeNode K P E) (h : x (realRoot K I.src I.dst t) = y (realRoot K I.src I.dst t)) :
    I.rootedShift K x t = I.rootedShift K y t := by
  cases t with
  | inl p => exact h
  | inr ej =>
    rcases ej with ⟨e,j⟩
    dsimp only [rootedShift]
    dsimp only [realRoot] at h
    split_ifs with hj
    · rw [ite_eq_left hj] at h
      rw [h]
    · rw [ite_eq_right hj] at h
      rw [h]

structure ArcWitness where
  sets : (p : P) → I.Address → Set (I.RealValue p)
  nonempty : ∀ p a, (sets p a).Nonempty
  images : ∀ e a (ha : I.Allowed e a),
    I.affineSrc e '' sets (I.src e) a =
      I.affineDst e '' sets (I.dst e) (I.transmit e a ha)

theorem arcConsistent_iff : I.ArcConsistent ↔ Nonempty I.ArcWitness := by
  constructor
  · rintro ⟨Q, hne, hi⟩; exact ⟨⟨Q, hne, hi⟩⟩
  · rintro ⟨Q⟩; exact ⟨Q.sets, Q.nonempty, Q.images⟩

namespace ArcWitness
variable {I} (Q : I.ArcWitness)

def internalSet (e : E) (a : I.Address) : Set F₂ := I.affineSrc e '' Q.sets (I.src e) a

theorem internal_nonempty (e : E) (a : I.Address) : (Q.internalSet e a).Nonempty :=
  (Q.nonempty (I.src e) a).image _

theorem src_preimage (e : E) (a : I.Address) {s : F₂} (hs : s ∈ Q.internalSet e a) :
    ∃ h ∈ Q.sets (I.src e) a, I.affineSrc e h = s := hs

theorem dst_preimage (e : E) (a : I.Address) (ha : I.Allowed e a)
    {s : F₂} (hs : s ∈ Q.internalSet e a) :
    ∃ h ∈ Q.sets (I.dst e) (I.permuteAddress e a), I.affineDst e h = s := by
  rw [I.permuteAddress_eq e a ha]
  change s ∈ I.affineDst e '' Q.sets (I.dst e) (I.transmit e a ha)
  rw [← Q.images e a ha]
  exact hs

theorem src_mem_internal (e : E) (a : I.Address) {h : I.RealValue (I.src e)}
    (hh : h ∈ Q.sets (I.src e) a) : I.affineSrc e h ∈ Q.internalSet e a :=
  ⟨h, hh, rfl⟩

theorem dst_mem_internal (e : E) (a : I.Address) (ha : I.Allowed e a)
    {h : I.RealValue (I.dst e)} (hh : h ∈ Q.sets (I.dst e) (I.permuteAddress e a)) :
    I.affineDst e h ∈ Q.internalSet e a := by
  rw [I.permuteAddress_eq e a ha] at hh
  rw [internalSet, Q.images e a ha]
  exact ⟨h, hh, rfl⟩

end ArcWitness

def scalarOf (K : ℕ) (h : (t : TypeNode K P E) → I.Value K t) : TypeNode K P E → F₂
  | .inl _ => 0
  | .inr ej => h (.inr ej)

theorem scalar_eq_on_internal_link (K : ℕ) (l : TypeLink K E)
    (h : (t : TypeNode K P E) → I.Value K t)
    (hl : I.leftForm K l (h (linkLeft K I.src l)) +
      I.rightForm K l (h (linkRight K I.dst l)) = I.linkBias K l)
    (h0 : l.2.val ≠ 0) (h4 : l.2.val ≠ 4 * K) :
    I.scalarOf K h (linkLeft K I.src l) = I.scalarOf K h (linkRight K I.dst l) := by
  rw [I.leftForm_section_internal K l h0, I.rightForm_section_internal K l h4] at hl
  simp only [linkBias, ite_eq_right h0, ite_eq_right h4] at hl
  simp only [linkLeft, linkRight, dite_eq_right h0, dite_eq_right h4, scalarOf]
  calc
    _ = _ + (h (.inr (l.1, ⟨l.2.val - 1, by have := l.2.isLt; omega⟩)) +
      h (.inr (l.1, ⟨l.2.val, by have := l.2.isLt; omega⟩))) := by rw [hl, add_zero]
    _ = _ := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem scalar_eq_on_internal_edge (K : ℕ) (S : Finset (TypeLink K E))
    (h : (t : TypeNode K P E) → I.Value K t) (hs : I.ShiftSolves K S h)
    {x y : TypeNode K P E} (hxy : (typeSupportGraph K I.src I.dst S).Adj x y)
    (hx : ∀ p, x ≠ Sum.inl p) (hy : ∀ p, y ≠ Sum.inl p) :
    I.scalarOf K h x = I.scalarOf K h y := by
  have aux : ∀ l ∈ S, (∀ p, linkLeft K I.src l ≠ Sum.inl p) →
      (∀ p, linkRight K I.dst l ≠ Sum.inl p) →
      I.scalarOf K h (linkLeft K I.src l) = I.scalarOf K h (linkRight K I.dst l) := by
    intro l hl hleft hright
    apply I.scalar_eq_on_internal_link K l h (hs l hl)
    · intro hz; exact hleft (I.src l.1) (dite_eq_left hz)
    · intro hz; exact hright (I.dst l.1) (dite_eq_left hz)
  obtain ⟨_, l, hl, he | he⟩ := hxy
  · obtain ⟨rfl, rfl⟩ := he; exact aux l hl hx hy
  · obtain ⟨rfl, rfl⟩ := he; exact (aux l hl hy hx).symm

theorem scalar_eq_on_rootfree_walk (K : ℕ) (S : Finset (TypeLink K E))
    (h : (t : TypeNode K P E) → I.Value K t) (hs : I.ShiftSolves K S h)
    {x y : TypeNode K P E} (w : (typeSupportGraph K I.src I.dst S).Walk x y)
    (hreal : ¬HasReal K I.src I.dst S x) : I.scalarOf K h x = I.scalarOf K h y := by
  induction w with
  | nil => rfl
  | @cons x z y hxz w ih =>
    have hz : ¬HasReal K I.src I.dst S z :=
      mt (hasReal_of_reachable K I.src I.dst S hxz.reachable).mpr hreal
    apply (I.scalar_eq_on_internal_edge K S h hs hxz
      (fun p he => hreal (he.symm ▸ hasReal_inl K I.src I.dst S p))
      (fun p he => hz (he.symm ▸ hasReal_inl K I.src I.dst S p))).trans
    exact ih hz

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression

structure Corner (r : ℕ) (T : Type uT) (Label : Type uLabel) where
  boundary : Fin (r + 1)
  type : T
  label : Label
  deriving DecidableEq, Fintype

inductive BlockName (r : ℕ) (T : Type uT) (L : Type uL) (Label : Type uLabel) where
  | site (row : Fin (r + 1)) (type : T) (lowLabel highLabel : Label)
  | square (row : Fin (r + 1)) (link : L) (lowLabel highLabel : Label)
  deriving DecidableEq, Fintype

namespace BlockName
variable {r : ℕ} {T : Type uT} {L : Type uL} {Label : Type uLabel}

def row : BlockName r T L Label → Fin (r + 1)
  | .site i _ _ _ => i
  | .square i _ _ _ => i

def low (left right : L → T) (matchLabel : L → Fin (r + 1) → Equiv.Perm Label) :
    BlockName r T L Label → Bool → Corner r T Label
  | .site i t a _, _ => ⟨i, t, a⟩
  | .square i l a _, false => ⟨i, left l, a⟩
  | .square i l a _, true => ⟨i, right l, matchLabel l i a⟩

def high (left right : L → T) (matchLabel : L → Fin (r + 1) → Equiv.Perm Label) :
    BlockName r T L Label → Bool → Corner r T Label
  | .site i t _ b, _ => ⟨finRotate (r + 1) i, t, b⟩
  | .square i l _ b, false => ⟨finRotate (r + 1) i, left l, b⟩
  | .square i l _ b, true => ⟨finRotate (r + 1) i, right l, matchLabel l (finRotate (r + 1) i) b⟩

def drawing (left right : L → T) (matchLabel : L → Fin (r + 1) → Equiv.Perm Label) :
    BlockDrawing r (BlockName r T L Label) (Corner r T Label) where
  boundary := Corner.boundary
  row := row
  low := low left right matchLabel
  high := high left right matchLabel
  low_boundary := by intro b s; cases b <;> cases s <;> rfl
  high_boundary := by intro b s; cases b <;> cases s <;> rfl

noncomputable def blockLinks [DecidableEq L] : BlockName r T L Label → Finset L
  | .site _ _ _ _ => ∅
  | .square _ l _ _ => {l}

noncomputable def links [DecidableEq L] (U : Finset (BlockName r T L Label)) : Finset L :=
  U.biUnion blockLinks

theorem links_card [DecidableEq L] (U : Finset (BlockName r T L Label)) :
    (links U).card ≤ U.card := by
  calc
    _ ≤ ∑ b ∈ U, (blockLinks b).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ U, 1 := Finset.sum_le_sum (fun b _ => by cases b <;> simp [blockLinks])
    _ = _ := by simp

theorem square_link_mem [DecidableEq L] {U : Finset (BlockName r T L Label)}
    {i : Fin (r + 1)} {l : L} {a b : Label} (h : .square i l a b ∈ U) : l ∈ links U := by
  exact Finset.mem_biUnion.mpr ⟨.square i l a b, h, Finset.mem_singleton_self _⟩

theorem links_mono [DecidableEq L] {U W : Finset (BlockName r T L Label)} (h : U ⊆ W) :
    links U ⊆ links W := by
  intro l hl
  obtain ⟨b, hb, hlb⟩ := Finset.mem_biUnion.mp hl
  exact Finset.mem_biUnion.mpr ⟨b, h hb, hlb⟩

theorem drawing_aligned (left right : L → T)
    (matchLabel : L → Fin (r + 1) → Equiv.Perm Label)
    (frame : T → Fin (r + 1) → Equiv.Perm Label)
    (U : Finset (BlockName r T L Label))
    (hframe : ∀ i l a b, .square i l a b ∈ U → ∀ j p,
      frame (left l) j p = frame (right l) j (matchLabel l j p)) :
    let D := drawing left right matchLabel
    let label := fun c : Corner r T Label => frame c.type c.boundary c.label
    ∀ b ∈ U, label (D.low b false) = label (D.low b true) ∧
      label (D.high b false) = label (D.high b true) := by
  intro D label b hb
  cases b with
  | site i t a b => exact ⟨rfl, rfl⟩
  | square i l a b => exact ⟨hframe i l a b hb i a, hframe i l a b hb _ b⟩

end BlockName

namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} {T : Type uT} (D : BlockDrawing r B V)

def restrict (S : Set B) : BlockDrawing r S V where
  boundary := D.boundary
  row := fun b => D.row b.1
  low := fun b => D.low b.1
  high := fun b => D.high b.1
  low_boundary := fun b => D.low_boundary b.1
  high_boundary := fun b => D.high_boundary b.1

theorem graph_mono {U W : Finset B} (h : U ⊆ W) : D.graph U ≤ D.graph W := by
  rintro x y ⟨hne, b, hb, he⟩
  exact ⟨hne, b, h hb, he⟩

theorem map_reachable (U : Finset B) (H : SimpleGraph T) (f : V → T)
    (hhor : ∀ b ∈ U, ∀ s, f (D.low b s) = f (D.high b s))
    (hlow : ∀ b ∈ U, H.Reachable (f (D.low b false)) (f (D.low b true)))
    (hhigh : ∀ b ∈ U, H.Reachable (f (D.high b false)) (f (D.high b true)))
    {x y : V} (h : (D.graph U).Reachable x y) : H.Reachable (f x) (f y) := by
  have hedge : ∀ b ∈ U, ∀ x y, D.Edge b x y → H.Reachable (f x) (f y) := by
    intro b hb x y he
    rcases he with ⟨s, rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hhor b hb s]
    · exact hlow b hb
    · exact hhigh b hb
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab w ih =>
    obtain ⟨_, d, hd, he | he⟩ := hab
    · exact (hedge d hd a b he).trans ih
    · exact (hedge d hd b a he).symm.trans ih

end BlockDrawing
end WLTime.Compression

end OAI
