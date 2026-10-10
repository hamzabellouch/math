import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorIteration
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ContactGadgetStability

namespace OAI

/-! Explicit labels for the eighteen fresh sites of each three-stage
mediator gadget. These identify the actual iterated graph with the
nineteen-link contact geometry, rather than only matching their counts. -/

namespace ContinuumCoulomb.ContactMediator
open MediatorGraph MediatorIteration

abbrev LocalPath := Fin 2 ⊕ (Fin 2 × Fin 2)
abbrev LocalInternal := Fin 2 ⊕ ((Fin 2 × Fin 2) ⊕ (LocalPath × Fin 2))
abbrev LocalSite := Fin 2 ⊕ LocalInternal

def spokeIndex (r : ℕ) (e : Fin r) (s : Fin 2) : Fin (r * 2) :=
  finProdFinEquiv (e, s)

def pathIndex (r : ℕ) (e : Fin r) : LocalPath → Fin (r * 2 + r * 2 * 2)
  | Sum.inl s => finSumFinEquiv (Sum.inl (spokeIndex r e s))
  | Sum.inr (s, t) => finSumFinEquiv (Sum.inr (spokeIndex (r * 2) (spokeIndex r e s) t))

def decodePath (r : ℕ) (a : Fin (r * 2 + r * 2 * 2)) : Fin r × LocalPath :=
  match finSumFinEquiv.symm a with
  | Sum.inl a =>
      let es := finProdFinEquiv.symm a
      (es.1, Sum.inl es.2)
  | Sum.inr a =>
      let st := finProdFinEquiv.symm a
      let es := finProdFinEquiv.symm st.1
      (es.1, Sum.inr (es.2, st.2))

def pathEquiv (r : ℕ) : Fin r × LocalPath ≃ Fin (r * 2 + r * 2 * 2) where
  toFun x := pathIndex r x.1 x.2
  invFun := decodePath r
  left_inv := by
    rintro ⟨e, s | ⟨s, t⟩⟩ <;> simp [pathIndex, decodePath, spokeIndex]
  right_inv := by
    intro a
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    cases a with
    | inl a =>
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [pathIndex, decodePath, spokeIndex]
    | inr a =>
      obtain ⟨⟨a, t⟩, rfl⟩ := finProdFinEquiv.surjective a
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [pathIndex, decodePath, spokeIndex]

@[simp] theorem decodePath_pathIndex (r : ℕ) (e : Fin r) (p : LocalPath) :
    decodePath r (pathIndex r e p) = (e, p) :=
  (pathEquiv r).symm_apply_apply (e, p)

@[simp] theorem finProd_divNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).divNat = a :=
  congrArg Prod.fst ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm_apply_apply (a, b))

@[simp] theorem finProd_modNat {m n : ℕ} (a : Fin m) (b : Fin n) :
    (finProdFinEquiv (a, b)).modNat = b :=
  congrArg Prod.snd ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm_apply_apply (a, b))

def encodeSite (n r : ℕ) : Fin n ⊕ (Fin r × LocalInternal) →
    Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)
  | Sum.inl i => old _ _ (old _ _ (old n r i))
  | Sum.inr (e, Sum.inl s) => old _ _ (old _ _ (fresh n r e s))
  | Sum.inr (e, Sum.inr (Sum.inl (s, t))) =>
      old _ _ (fresh (n + r * 2) (r * 2) (spokeIndex r e s) t)
  | Sum.inr (e, Sum.inr (Sum.inr (p, t))) =>
      fresh (n + r * 2 + r * 2 * 2) (r * 2 + r * 2 * 2) (pathIndex r e p) t

def decodeSite (n r : ℕ)
    (k : Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)) :
    Fin n ⊕ (Fin r × LocalInternal) :=
  match (vertexEquiv (n + r * 2 + r * 2 * 2) (r * 2 + r * 2 * 2)).symm k with
  | Sum.inl k =>
      match (vertexEquiv (n + r * 2) (r * 2)).symm k with
      | Sum.inl k =>
          match (vertexEquiv n r).symm k with
          | Sum.inl i => Sum.inl i
          | Sum.inr (e, s) => Sum.inr (e, Sum.inl s)
      | Sum.inr (a, t) =>
          let es := finProdFinEquiv.symm a
          Sum.inr (es.1, Sum.inr (Sum.inl (es.2, t)))
  | Sum.inr (a, t) =>
      match finSumFinEquiv.symm a with
      | Sum.inl a =>
          let es := finProdFinEquiv.symm a
          Sum.inr (es.1, Sum.inr (Sum.inr (Sum.inl es.2, t)))
      | Sum.inr a =>
          let st := finProdFinEquiv.symm a
          let es := finProdFinEquiv.symm st.1
          Sum.inr (es.1, Sum.inr (Sum.inr (Sum.inr (es.2, st.2), t)))

theorem decode_encode (n r : ℕ) (x : Fin n ⊕ (Fin r × LocalInternal)) :
    decodeSite n r (encodeSite n r x) = x := by
  rcases x with i | ⟨e, s | (st | ⟨p, t⟩)⟩
  · simp [encodeSite, decodeSite, old]
  · simp [encodeSite, decodeSite, old, fresh]
  · rcases st with ⟨s, t⟩
    simp [encodeSite, decodeSite, old, fresh, spokeIndex]
  · cases p with
    | inl s => simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]
    | inr st =>
      rcases st with ⟨s, u⟩
      simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]

theorem encode_decode (n r : ℕ)
    (k : Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)) :
    encodeSite n r (decodeSite n r k) = k := by
  obtain ⟨k, rfl⟩ := (vertexEquiv (n + r * 2 + r * 2 * 2)
    (r * 2 + r * 2 * 2)).surjective k
  rcases k with k | ⟨a, t⟩
  · obtain ⟨k, rfl⟩ := (vertexEquiv (n + r * 2) (r * 2)).surjective k
    rcases k with k | ⟨a, t⟩
    · obtain ⟨k, rfl⟩ := (vertexEquiv n r).surjective k
      rcases k with i | ⟨e, s⟩
      · simp [encodeSite, decodeSite, old]
      · simp [encodeSite, decodeSite, old, fresh]
    · obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [encodeSite, decodeSite, old, fresh, spokeIndex]
  · obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    cases a with
    | inl a =>
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]
    | inr a =>
      obtain ⟨⟨a, u⟩, rfl⟩ := finProdFinEquiv.surjective a
      obtain ⟨⟨e, s⟩, rfl⟩ := finProdFinEquiv.surjective a
      simp [encodeSite, decodeSite, fresh, pathIndex, spokeIndex]

def siteEquiv (n r : ℕ) : Fin n ⊕ (Fin r × LocalInternal) ≃
    Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) where
  toFun := encodeSite n r
  invFun := decodeSite n r
  left_inv := decode_encode n r
  right_inv := encode_decode n r

def localToContact : LocalSite → ContactGadgetSite
  | Sum.inl s => if s = 0 then Sum.inl 0 else Sum.inr (Sum.inl 8)
  | Sum.inr (Sum.inl s) => if s = 0 then Sum.inl 9 else contactGadgetSide
  | Sum.inr (Sum.inr (Sum.inl (s, t))) =>
      if s = 0 then Sum.inl (if t = 0 then 3 else 6)
      else Sum.inr (Sum.inl (if t = 0 then 5 else 2))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl s, t))) =>
      if s = 0 then Sum.inl (if t = 0 then 4 else 5)
      else Sum.inr (Sum.inl (if t = 0 then 4 else 3))
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (s, u), t))) =>
      if s = 0 then Sum.inl (if u = 0 then (if t = 0 then 1 else 2)
        else (if t = 0 then 8 else 7))
      else Sum.inr (Sum.inl (if u = 0 then (if t = 0 then 7 else 6)
        else (if t = 0 then 0 else 1)))

def localOld (s : Fin 2) : LocalSite := Sum.inl s
def localFirst (s : Fin 2) : LocalSite := Sum.inr (Sum.inl s)
def localSecond (s t : Fin 2) : LocalSite := Sum.inr (Sum.inr (Sum.inl (s, t)))
def localThird (p : LocalPath) (t : Fin 2) : LocalSite :=
  Sum.inr (Sum.inr (Sum.inr (p, t)))

def contactToLocal : ContactGadgetSite → LocalSite
  | Sum.inl i => ![localOld 0,
      localThird (Sum.inr (0, 0)) 0, localThird (Sum.inr (0, 0)) 1,
      localSecond 0 0, localThird (Sum.inl 0) 0, localThird (Sum.inl 0) 1,
      localSecond 0 1, localThird (Sum.inr (0, 1)) 1,
      localThird (Sum.inr (0, 1)) 0, localFirst 0] i
  | Sum.inr (Sum.inl i) => ![localThird (Sum.inr (1, 1)) 0,
      localThird (Sum.inr (1, 1)) 1, localSecond 1 1,
      localThird (Sum.inl 1) 1, localThird (Sum.inl 1) 0,
      localSecond 1 0, localThird (Sum.inr (1, 0)) 1,
      localThird (Sum.inr (1, 0)) 0, localOld 1] i
  | Sum.inr (Sum.inr _) => localFirst 1

theorem contact_local_inverse (x : LocalSite) : contactToLocal (localToContact x) = x := by
  rcases x with s | (s | (⟨s, t⟩ | ⟨p, t⟩))
  · fin_cases s <;> rfl
  · fin_cases s <;> rfl
  · fin_cases s <;> fin_cases t <;> rfl
  · cases p with
    | inl s => fin_cases s <;> fin_cases t <;> rfl
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> fin_cases t <;> rfl

theorem local_contact_inverse (x : ContactGadgetSite) : localToContact (contactToLocal x) = x := by
  rcases x with i | (i | ⟨⟩)
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl
  · rfl

def localContactEquiv : LocalSite ≃ ContactGadgetSite where
  toFun := localToContact
  invFun := contactToLocal
  left_inv := contact_local_inverse
  right_inv := local_contact_inverse

def localVertex {n r : ℕ} (a b : Fin n) (e : Fin r) : LocalSite →
    Fin (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) :=
  fun x => siteEquiv n r (Sum.elim
    (fun s => Sum.inl (if s = 0 then a else b)) (fun u => Sum.inr (e, u)) x)

theorem localVertex_injective {n r : ℕ} (a b : Fin n) (e : Fin r) (hab : a ≠ b) :
    Function.Injective (localVertex a b e) := by
  intro x y h
  have h' := (siteEquiv n r).injective h
  cases x with
  | inl s =>
    cases y with
    | inl t =>
      fin_cases s <;> fin_cases t <;> simp_all [localVertex]
    | inr t => simp at h'
  | inr s =>
    cases y with
    | inl t => simp at h'
    | inr t =>
      exact congrArg Sum.inr (Prod.mk.inj (Sum.inr.inj h')).2

abbrev LocalEdge := Unit ⊕ (LocalPath ⊕ (LocalPath × Fin 2))

def encodeEdge (r : ℕ) (e : Fin r) : LocalEdge →
    Fin (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2))
  | Sum.inl _ => finSumFinEquiv (Sum.inl e)
  | Sum.inr (Sum.inl p) =>
      finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl (pathIndex r e p))))
  | Sum.inr (Sum.inr (p, t)) =>
      finSumFinEquiv (Sum.inr (finSumFinEquiv
        (Sum.inr (spokeIndex (r * 2 + r * 2 * 2) (pathIndex r e p) t))))

def decodeEdge (r : ℕ)
    (a : Fin (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2))) :
    Fin r × LocalEdge :=
  match finSumFinEquiv.symm a with
  | Sum.inl e => (e, Sum.inl ())
  | Sum.inr a =>
      match finSumFinEquiv.symm a with
      | Sum.inl a =>
          let ep := (pathEquiv r).symm a
          (ep.1, Sum.inr (Sum.inl ep.2))
      | Sum.inr a =>
          let pt := finProdFinEquiv.symm a
          let ep := (pathEquiv r).symm pt.1
          (ep.1, Sum.inr (Sum.inr (ep.2, pt.2)))

def edgeEquiv (r : ℕ) : Fin r × LocalEdge ≃
    Fin (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2)) where
  toFun x := encodeEdge r x.1 x.2
  invFun := decodeEdge r
  left_inv := by
    rintro ⟨e, ⟨⟩ | (p | ⟨p, t⟩)⟩
    · simp [encodeEdge, decodeEdge]
    · change decodeEdge r (finSumFinEquiv (Sum.inr
        (finSumFinEquiv (Sum.inl (pathEquiv r (e, p)))))) = _
      simp [decodeEdge]
    · change decodeEdge r (finSumFinEquiv (Sum.inr (finSumFinEquiv
        (Sum.inr (spokeIndex (r * 2 + r * 2 * 2) (pathEquiv r (e, p)) t))))) = _
      simp [decodeEdge, spokeIndex]
  right_inv := by
    intro a
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    cases a with
    | inl e => simp [encodeEdge, decodeEdge]
    | inr a =>
      obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
      cases a with
      | inl a =>
        obtain ⟨⟨e, p⟩, rfl⟩ := (pathEquiv r).surjective a
        simp [encodeEdge, decodeEdge]; rfl
      | inr a =>
        obtain ⟨⟨a, t⟩, rfl⟩ := finProdFinEquiv.surjective a
        obtain ⟨⟨e, p⟩, rfl⟩ := (pathEquiv r).surjective a
        simp [encodeEdge, decodeEdge, spokeIndex]; rfl

def firstAttachment (member : Fin 2) (s : Fin 2) : Fin 2 :=
  if s = 0 then 0 else member

def secondEndpoint (member : Fin 2) (p : LocalPath) (t : Fin 2) : LocalSite :=
  match p with
  | Sum.inl s => localSecond s t
  | Sum.inr (s, u) => if t = 0 then
      (if u = 0 then localOld s else localFirst (firstAttachment member s))
    else localSecond s u

def localLeft (member : Fin 2) : LocalEdge → LocalSite
  | Sum.inl _ => localFirst 0
  | Sum.inr (Sum.inl p) => localThird p 0
  | Sum.inr (Sum.inr (p, t)) => secondEndpoint member p t

def localRight : LocalEdge → LocalSite
  | Sum.inl _ => localFirst 1
  | Sum.inr (Sum.inl p) => localThird p 1
  | Sum.inr (Sum.inr (p, t)) => localThird p t

theorem localEdge_contactLinked (negative : Bool) (e : LocalEdge) :
    contactGadgetLinked negative
      (localToContact (localLeft (if negative then 0 else 1) e))
      (localToContact (localRight e)) := by
  rcases e with ⟨⟩ | (p | ⟨p, t⟩)
  · cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
  · cases p with
    | inl s => fin_cases s <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
  · cases p with
    | inl s => fin_cases s <;> fin_cases t <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> fin_cases t <;> cases negative <;> norm_num [contactGadgetLinked, localToContact, localLeft, localRight,
      secondEndpoint, firstAttachment, localFirst, localSecond, localOld, localThird,
      contactGadgetSide, Nat.dist]

theorem spoke_nonneg (r W G : ℕ) (J : ℚ) : 0 ≤ MediatorParameters.spoke r W G J := by
  unfold MediatorParameters.spoke DyadicRootProgram.value
  positivity

theorem member_spoke (r W G : ℕ) (J : ℚ) :
    member (MediatorParameters.spoke r W G J) = 1 := by
  simp only [member, not_lt.mpr (spoke_nonneg r W G J), ite_false]

theorem member_nat (N : ℕ) : member (N : ℚ) = 1 := by
  simp [member]

theorem member_secondPath {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (p : LocalPath) :
    member ((secondPaths F W G).weight (pathIndex r e p)) = 1 := by
  cases p with
  | inl s =>
    simp [secondPaths, join, secondCentral, central, pathIndex, member_nat]
  | inr st =>
    rcases st with ⟨s, t⟩
    simp [secondPaths, join, secondSpokes, spokes, pathIndex, spokeIndex, member_spoke]

/-- Every left endpoint of the actual three-stage graph has the explicit
local gadget label. This identity retains the original edge index. -/
theorem finalGraph_left {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (a : LocalEdge) :
    (finalGraph F W G).left (encodeEdge r e a) =
      localVertex (F.left e) (F.right e) e (localLeft (member (F.weight e)) a) := by
  rcases a with ⟨⟩ | (p | ⟨p, t⟩)
  · simp [finalGraph, encodeEdge, join, lift, retainedCentral, firstCentral, central,
      localVertex, localLeft, localFirst, siteEquiv, encodeSite]
  · simp [finalGraph, encodeEdge, join, thirdCentral, central,
      localVertex, localLeft, localThird, siteEquiv, encodeSite]
  · cases p with
    | inl s =>
      fin_cases s <;> fin_cases t <;>
        simp [finalGraph, encodeEdge, join, thirdSpokes, spokes, secondPaths, secondCentral,
          central, pathIndex, spokeIndex, localVertex, localLeft, secondEndpoint,
          localSecond, siteEquiv, encodeSite]
    | inr su =>
      rcases su with ⟨s, u⟩
      fin_cases s <;> fin_cases u <;> fin_cases t <;>
        simp [finalGraph, encodeEdge, join, thirdSpokes, spokes, secondPaths, secondSpokes,
          firstSpokes, pathIndex, spokeIndex, member_spoke, localVertex, localLeft,
          secondEndpoint, firstAttachment, localOld, localFirst, localSecond, siteEquiv,
          encodeSite]

/-- The matching right-endpoint identity uses the proved nonnegativity of
the actual rounded spokes, so later subdivisions always use member one. -/
theorem finalGraph_right {n r : ℕ} (F : Bonds n r) (W G : ℕ)
    (e : Fin r) (a : LocalEdge) :
    (finalGraph F W G).right (encodeEdge r e a) =
      localVertex (F.left e) (F.right e) e (localRight a) := by
  rcases a with ⟨⟩ | (p | ⟨p, t⟩)
  · simp [finalGraph, encodeEdge, join, lift, retainedCentral, firstCentral, central,
      localVertex, localRight, localFirst, siteEquiv, encodeSite]
  · simp [finalGraph, encodeEdge, join, thirdCentral, central,
      localVertex, localRight, localThird, siteEquiv, encodeSite]
  · have hm := member_secondPath F W G e p
    fin_cases t <;>
      simp [finalGraph, encodeEdge, join, thirdSpokes, spokes, spokeIndex, hm,
        localVertex, localRight, localThird, siteEquiv, encodeSite]

def edgeNegative {n r : ℕ} (F : Bonds n r) (e : Fin r) : Bool := decide (F.weight e < 0)

theorem member_edgeNegative {n r : ℕ} (F : Bonds n r) (e : Fin r) :
    member (F.weight e) = if edgeNegative F e then 0 else 1 := by
  simp [member, edgeNegative]

/-- The entire actual final edge enumeration, not just a graph with the
same cardinality, is carried to the nineteen physical contact links. -/
theorem finalGraph_contact_links {n r : ℕ} (F : Bonds n r) (_W _G : ℕ)
    (e : Fin r) (a : LocalEdge) :
    contactGadgetLinked (edgeNegative F e)
      (localToContact (localLeft (member (F.weight e)) a))
      (localToContact (localRight a)) := by
  rw [member_edgeNegative]
  exact localEdge_contactLinked (edgeNegative F e) a

end ContinuumCoulomb.ContactMediator

end OAI
