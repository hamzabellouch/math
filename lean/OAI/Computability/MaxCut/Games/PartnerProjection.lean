import Mathlib
import OAI.Computability.MaxCut.Encoding.BinaryCoordinates

namespace OAI

namespace MaxCutGames.Soundness.PartnerProjection

inductive Slot where
  | first | second | third
  deriving DecidableEq, Repr

structure Triple where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq, Repr

def zeroTriple : Triple := ⟨false, false, false⟩

def parity (x : Triple) : Bool := (x.first.xor x.second).xor x.third

def addTriple (x y : Triple) : Triple :=
  ⟨x.first.xor y.first, x.second.xor y.second, x.third.xor y.third⟩

theorem parity_add (x y : Triple) :
    parity (addTriple x y) = (parity x).xor (parity y) := by
  rcases x with ⟨a, b, c⟩
  rcases y with ⟨d, e, f⟩
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem and_xor (b h h' : Bool) :
    (b && h).xor (b && h') = (b && h.xor h') := by
  cases b <;> cases h <;> cases h' <;> decide

def retained (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.first
  | .second => x.second
  | .third => x.third

def freeBit (s : Slot) (x : Triple) : Bool :=
  match s with
  | .first => x.second
  | .second => x.first
  | .third => x.first

theorem retained_add (s : Slot) (x y : Triple) :
    retained s (addTriple x y) = (retained s x).xor (retained s y) := by
  cases s <;> rfl

theorem freeBit_add (s : Slot) (x y : Triple) :
    freeBit s (addTriple x y) = (freeBit s x).xor (freeBit s y) := by
  cases s <;> rfl

/-- Reconstruct a parity-constrained triple from its retained bit and one free bit. -/
def complete (s : Slot) (p r f : Bool) : Triple :=
  match s with
  | .first => ⟨r, f, (p.xor r).xor f⟩
  | .second => ⟨f, r, (p.xor r).xor f⟩
  | .third => ⟨f, (p.xor r).xor f, r⟩

theorem parity_complete (s : Slot) (p r f : Bool) :
    parity (complete s p r f) = p := by
  cases s <;> cases p <;> cases r <;> cases f <;> decide

theorem retained_complete (s : Slot) (p r f : Bool) :
    retained s (complete s p r f) = r := by
  cases s <;> rfl

theorem freeBit_complete (s : Slot) (p r f : Bool) :
    freeBit s (complete s p r f) = f := by
  cases s <;> rfl

theorem complete_coordinates (s : Slot) (x : Triple) :
    complete s (parity x) (retained s x) (freeBit s x) = x := by
  rcases x with ⟨a, b, c⟩
  cases s <;> cases a <;> cases b <;> cases c <;> decide

theorem retained_zero (s : Slot) : retained s zeroTriple = false := by
  cases s <;> rfl

theorem freeBit_zero (s : Slot) : freeBit s zeroTriple = false := by
  cases s <;> rfl

theorem complete_zero (s : Slot) : complete s false false false = zeroTriple := by
  cases s <;> rfl

theorem complete_kernel_add (s : Slot) (a b : Bool) :
    complete s false false (a.xor b) =
      addTriple (complete s false false a) (complete s false false b) := by
  cases s <;> cases a <;> cases b <;> decide

variable {Position : Type} (rhs active : Position → Bool) (slot : Position → Slot)

structure SourcePoint where
  homogeneous : Bool
  coordinates : Position → Triple
  valid : ∀ j, parity (coordinates j) = (rhs j && homogeneous)

structure PartnerPoint where
  homogeneous : Bool
  full : Position → Triple
  single : Position → Bool
  full_zero : ∀ j, active j = true → full j = zeroTriple
  full_valid : ∀ j, active j = false → parity (full j) = (rhs j && homogeneous)
  single_zero : ∀ j, active j = false → single j = false

theorem source_ext {x y : SourcePoint rhs}
    (hh : x.homogeneous = y.homogeneous) (hx : x.coordinates = y.coordinates) : x = y := by
  cases x
  cases y
  cases hh
  cases hx
  rfl

theorem partner_ext {x y : PartnerPoint rhs active}
    (hh : x.homogeneous = y.homogeneous) (hf : x.full = y.full)
    (hs : x.single = y.single) : x = y := by
  cases x
  cases y
  cases hh
  cases hf
  cases hs
  rfl

def project (x : SourcePoint rhs) : PartnerPoint rhs active where
  homogeneous := x.homogeneous
  full := fun j => if active j then zeroTriple else x.coordinates j
  single := fun j => if active j then retained (slot j) (x.coordinates j) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simpa [hj] using x.valid j
  single_zero := by intro j hj; simp [hj]

/-- The constructive preimage used in Lemma 6.1: choose the free bit to be zero. -/
def lift (y : PartnerPoint rhs active) : SourcePoint rhs where
  homogeneous := y.homogeneous
  coordinates := fun j =>
    if active j then complete (slot j) (rhs j && y.homogeneous) (y.single j) false
    else y.full j
  valid := by
    intro j
    cases hj : active j with
    | false => simpa [hj] using y.full_valid j hj
    | true => simp [parity_complete]

theorem project_lift (y : PartnerPoint rhs active) :
    project rhs active slot (lift rhs active slot y) = y := by
  apply partner_ext
  · rfl
  · funext j
    cases hj : active j with
    | false => simp [project, lift, hj]
    | true => simpa [project, hj] using (y.full_zero j hj).symm
  · funext j
    cases hj : active j with
    | false => simpa [project, hj] using (y.single_zero j hj).symm
    | true => simp [project, lift, hj, retained_complete]

theorem project_surjective :
    ∀ y : PartnerPoint rhs active, ∃ x : SourcePoint rhs, project rhs active slot x = y := by
  intro y
  exact ⟨lift rhs active slot y, project_lift rhs active slot y⟩

theorem homogeneous_preserved (x : SourcePoint rhs) :
    (project rhs active slot x).homogeneous = x.homogeneous := rfl

def zeroSource : SourcePoint rhs where
  homogeneous := false
  coordinates := fun _ => zeroTriple
  valid := by intro j; simp [parity, zeroTriple]

def zeroPartner : PartnerPoint rhs active where
  homogeneous := false
  full := fun _ => zeroTriple
  single := fun _ => false
  full_zero := by intros; rfl
  full_valid := by intros; simp [parity, zeroTriple]
  single_zero := by intros; rfl

def addSource (x y : SourcePoint rhs) : SourcePoint rhs where
  homogeneous := x.homogeneous.xor y.homogeneous
  coordinates := fun j => addTriple (x.coordinates j) (y.coordinates j)
  valid := by
    intro j
    rw [parity_add, x.valid, y.valid, and_xor]

def addPartner (x y : PartnerPoint rhs active) : PartnerPoint rhs active where
  homogeneous := x.homogeneous.xor y.homogeneous
  full := fun j => addTriple (x.full j) (y.full j)
  single := fun j => (x.single j).xor (y.single j)
  full_zero := by
    intro j hj
    rw [x.full_zero j hj, y.full_zero j hj]
    rfl
  full_valid := by
    intro j hj
    rw [parity_add, x.full_valid j hj, y.full_valid j hj, and_xor]
  single_zero := by
    intro j hj
    rw [x.single_zero j hj, y.single_zero j hj]
    rfl

/-- The projection preserves F₂ addition, as well as zero. -/
theorem project_add (x y : SourcePoint rhs) :
    project rhs active slot (addSource rhs x y) =
      addPartner rhs active (project rhs active slot x) (project rhs active slot y) := by
  apply partner_ext
  · rfl
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, addTriple, zeroTriple]
  · funext j
    cases hj : active j <;> simp [project, addSource, addPartner, hj, retained_add]

theorem project_zero :
    project rhs active slot (zeroSource rhs) = zeroPartner rhs active := by
  apply partner_ext
  · rfl
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner]
  · funext j
    cases active j <;> simp [project, zeroSource, zeroPartner, retained_zero]

def InKernel (x : SourcePoint rhs) : Prop :=
  project rhs active slot x = zeroPartner rhs active

theorem kernel_characterization (x : SourcePoint rhs) :
    InKernel rhs active slot x ↔
      x.homogeneous = false ∧
      (∀ j, active j = false → x.coordinates j = zeroTriple) ∧
      (∀ j, active j = true → retained (slot j) (x.coordinates j) = false) := by
  constructor
  · intro hx
    refine ⟨congrArg PartnerPoint.homogeneous hx, ?_, ?_⟩
    · intro j hj
      have h := congrArg (fun y : PartnerPoint rhs active => y.full j) hx
      simpa [project, zeroPartner, hj] using h
    · intro j hj
      have h := congrArg (fun y : PartnerPoint rhs active => y.single j) hx
      simpa [project, zeroPartner, hj] using h
  · rintro ⟨hh, hf, hs⟩
    apply partner_ext
    · exact hh
    · funext j
      cases hj : active j with
      | false => simpa [project, zeroPartner, hj] using hf j hj
      | true => simp [project, zeroPartner, hj]
    · funext j
      cases hj : active j with
      | false => simp [project, zeroPartner, hj]
      | true => simpa [project, zeroPartner, hj] using hs j hj

/-- One coefficient bit at every active position; all other coefficients vanish. -/
structure ActiveBits where
  coefficient : Position → Bool
  inactive_zero : ∀ j, active j = false → coefficient j = false

theorem activeBits_ext {a b : ActiveBits active}
    (h : a.coefficient = b.coefficient) : a = b := by
  cases a
  cases b
  cases h
  rfl

def addActiveBits (a b : ActiveBits active) : ActiveBits active where
  coefficient := fun j => (a.coefficient j).xor (b.coefficient j)
  inactive_zero := by
    intro j hj
    rw [a.inactive_zero j hj, b.inactive_zero j hj]
    rfl

def kernelPoint (a : ActiveBits active) : SourcePoint rhs where
  homogeneous := false
  coordinates := fun j => complete (slot j) false false (a.coefficient j)
  valid := by intro j; simp [parity_complete]

theorem kernelPoint_add (a b : ActiveBits active) :
    kernelPoint rhs active slot (addActiveBits active a b) =
      addSource rhs (kernelPoint rhs active slot a) (kernelPoint rhs active slot b) := by
  apply source_ext
  · rfl
  · funext j
    exact complete_kernel_add _ _ _

theorem kernelPoint_mem (a : ActiveBits active) :
    InKernel rhs active slot (kernelPoint rhs active slot a) := by
  apply (kernel_characterization rhs active slot _).2
  refine ⟨rfl, ?_, ?_⟩
  · intro j hj
    simp [kernelPoint, a.inactive_zero j hj, complete_zero]
  · intro j _
    exact retained_complete _ _ _ _

def kernelCoefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    ActiveBits active where
  coefficient := fun j => freeBit (slot j) (x.coordinates j)
  inactive_zero := by
    intro j hj
    have hf := (kernel_characterization rhs active slot x).1 hx |>.2.1 j hj
    rw [hf, freeBit_zero]

theorem kernelPoint_coefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    kernelPoint rhs active slot (kernelCoefficients rhs active slot x hx) = x := by
  have hc := (kernel_characterization rhs active slot x).1 hx
  apply source_ext
  · exact hc.1.symm
  · funext j
    have hp : parity (x.coordinates j) = false := by
      rw [x.valid j, hc.1]
      simp
    have hr : retained (slot j) (x.coordinates j) = false := by
      cases hj : active j with
      | false => rw [hc.2.1 j hj, retained_zero]
      | true => exact hc.2.2 j hj
    simpa [kernelPoint, kernelCoefficients, hp, hr] using
      complete_coordinates (slot j) (x.coordinates j)

theorem coefficients_kernelPoint (a : ActiveBits active) :
    kernelCoefficients rhs active slot (kernelPoint rhs active slot a)
      (kernelPoint_mem rhs active slot a) = a := by
  apply activeBits_ext active
  funext j
  exact freeBit_complete _ _ _ _

theorem kernelPoint_injective (a b : ActiveBits active)
    (h : kernelPoint rhs active slot a = kernelPoint rhs active slot b) : a = b := by
  have hc : a.coefficient = b.coefficient := by
    funext j
    have he := congrArg (fun x : SourcePoint rhs => freeBit (slot j) (x.coordinates j)) h
    simpa [kernelPoint, freeBit_complete] using he
  cases a
  cases b
  cases hc
  rfl

/-- Every kernel vector is uniquely determined by one bit per active position. -/
theorem kernel_unique_coefficients (x : SourcePoint rhs) (hx : InKernel rhs active slot x) :
    ∃ a : ActiveBits active, kernelPoint rhs active slot a = x ∧
      ∀ b : ActiveBits active, kernelPoint rhs active slot b = x → b = a := by
  refine ⟨kernelCoefficients rhs active slot x hx,
    kernelPoint_coefficients rhs active slot x hx, ?_⟩
  intro b hb
  apply kernelPoint_injective rhs active slot
  exact hb.trans (kernelPoint_coefficients rhs active slot x hx).symm

/-- Extend an arbitrary function on the active positions by zero. -/
def extendActive (f : {j : Position // active j = true} → Bool) : ActiveBits active where
  coefficient := fun j => if hj : active j = true then f ⟨j, hj⟩ else false
  inactive_zero := by intro j hj; simp [hj]

theorem kernel_realizes_active
    (f : {j : Position // active j = true} → Bool) :
    ∃ x : SourcePoint rhs, InKernel rhs active slot x ∧
      ∀ j (hj : active j = true), freeBit (slot j) (x.coordinates j) = f ⟨j, hj⟩ := by
  refine ⟨kernelPoint rhs active slot (extendActive active f),
    kernelPoint_mem rhs active slot _, ?_⟩
  intro j hj
  simp [kernelPoint, freeBit_complete, extendActive, hj]

theorem kernel_determined_by_active
    (x y : SourcePoint rhs)
    (hx : InKernel rhs active slot x) (hy : InKernel rhs active slot y)
    (hfree : ∀ j, active j = true →
      freeBit (slot j) (x.coordinates j) = freeBit (slot j) (y.coordinates j)) : x = y := by
  have hc : kernelCoefficients rhs active slot x hx = kernelCoefficients rhs active slot y hy := by
    apply activeBits_ext active
    funext j
    cases hj : active j with
    | false =>
      simp [kernelCoefficients,
        (kernel_characterization rhs active slot x).1 hx |>.2.1 j hj,
        (kernel_characterization rhs active slot y).1 hy |>.2.1 j hj]
    | true => exact hfree j hj
  have hp := congrArg (kernelPoint rhs active slot) hc
  simpa only [kernelPoint_coefficients] using hp

/-- The final assertion of Lemma 6.1, including arbitrary retained indices. -/
theorem disjoint_kernels_intersection_zero
    (active' : Position → Bool) (slot' : Position → Slot)
    (hdisjoint : ∀ j, active j = true → active' j = false)
    (x : SourcePoint rhs)
    (hx : InKernel rhs active slot x)
    (hx' : InKernel rhs active' slot' x) : x = zeroSource rhs := by
  have h := (kernel_characterization rhs active slot x).1 hx
  have h' := (kernel_characterization rhs active' slot' x).1 hx'
  apply source_ext
  · exact h.1
  · funext j
    cases hj : active j with
    | false => exact h.2.1 j hj
    | true => exact h'.2.1 j (hdisjoint j hj)

end MaxCutGames.Soundness.PartnerProjection

/-!
Finite cardinality of the concrete projection kernel. This packages the explicit
bit parametrization of Lemma 6.1 as a genuine equivalence, then counts its points.
No vector-space dimension formula is assumed.
-/

namespace MaxCutGames.Soundness.KernelCardinality

open PartnerProjection

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev Kernel := {x : SourcePoint rhs // InKernel rhs active slot x}

/-- Exactly one freely chosen bit per active position parametrizes the kernel. -/
def kernelEquiv : Kernel rhs active slot ≃ ({j : P // active j = true} → Bool) where
  toFun x j := freeBit (slot j.val) (x.val.coordinates j.val)
  invFun f := ⟨kernelPoint rhs active slot (extendActive active f),
    kernelPoint_mem rhs active slot _⟩
  left_inv x := by
    apply Subtype.ext
    apply kernel_determined_by_active rhs active slot
    · exact kernelPoint_mem rhs active slot _
    · exact x.property
    · intro j hj
      simp [kernelPoint, freeBit_complete, extendActive, hj]
  right_inv f := by
    funext j
    simp [kernelPoint, freeBit_complete, extendActive, j.property]

noncomputable instance kernelFintype [Fintype P] : Fintype (Kernel rhs active slot) := by
  classical
  exact Fintype.ofEquiv ({j : P // active j = true} → Bool) (kernelEquiv rhs active slot).symm

/-- The actual kernel has `2^t` points when there are `t` active positions. -/
theorem kernel_card [Fintype P] :
    Fintype.card (Kernel rhs active slot) = 2 ^ Fintype.card {j : P // active j = true} := by
  classical
  calc
    Fintype.card (Kernel rhs active slot) =
        Fintype.card ({j : P // active j = true} → Bool) :=
      Fintype.card_congr (kernelEquiv rhs active slot)
    _ = _ := by simp

theorem kernel_card_of_active_card [Fintype P] (t : Nat)
    (h : Fintype.card {j : P // active j = true} = t) :
    Fintype.card (Kernel rhs active slot) = 2 ^ t := by
  rw [kernel_card, h]

end MaxCutGames.Soundness.KernelCardinality

/-!
# Exact kernel counts for binary linear maps

The last paragraph of Theorem 3.4 uses the fact that a uniform vector in a
binary vector space lands in the kernel of a rank-k map with probability
2⁻ᵏ. These theorems prove its exact integer-count form from mathlib's
rank-nullity and finite-vector-space cardinality theorems. The target space
does not have to be finite, and no injectivity of any factor map is assumed.
-/

namespace MaxCutGames.Gadget.LinearKernelCount

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

/-- A finite-dimensional binary vector space has `2^dimension` vectors. -/
theorem card_binary_space : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp

/-- Exact cross-multiplied uniform kernel probability: `|ker f| * 2^rank f = |V|`. -/
theorem kernel_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V := by
  rw [card_binary_space (V := f.ker), card_binary_space (V := V), ← pow_add]
  congr 1
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker

/-- The denominator of the uniform vector experiment is positive. -/
theorem card_source_pos : 0 < Nat.card V := by
  rw [card_binary_space]
  exact Nat.pow_pos (by decide)

/-- The kernel size itself is the familiar power of the nullity. -/
theorem kernel_card_eq_pow_sub_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker =
      2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) f.range) := by
  rw [card_binary_space (V := f.ker)]
  congr 1
  have h := f.finrank_range_add_finrank_ker
  omega

/-- The kernel formula expressed directly as the cardinality of the zero event. -/
theorem zero_event_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V :=
  kernel_card_mul_pow_rank f

/-- A rank threshold gives the exact cleared-denominator bound used on a good leaf. -/
theorem zero_event_card_mul_pow_le (f : V →ₗ[ZMod 2] P) (r : Nat)
    (hr : r ≤ Module.finrank (ZMod 2) f.range) :
    Nat.card {x : V // f x = 0} * 2 ^ r ≤ Nat.card V := by
  calc
    Nat.card {x : V // f x = 0} * 2 ^ r ≤
        Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hr)
    _ = Nat.card V := zero_event_card_mul_pow_rank f

/-- The same exact probability identity for a direct count over a finite universe. -/
theorem zero_event_finset_count_mul_pow_rank [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) :
    (Finset.univ.filter (fun x : V => f x = 0)).card *
      2 ^ Module.finrank (ZMod 2) f.range = Fintype.card V := by
  have h := zero_event_card_mul_pow_rank f
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

/-- A rank-r lower bound yields a `2⁻ʳ` bound on the actual finite zero-event count. -/
theorem zero_event_finset_count_mul_pow_le [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) (r : Nat)
    (hr : r ≤ Module.finrank (ZMod 2) f.range) :
    (Finset.univ.filter (fun x : V => f x = 0)).card * 2 ^ r ≤ Fintype.card V := by
  have h := zero_event_card_mul_pow_le f r hr
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

end MaxCutGames.Gadget.LinearKernelCount

namespace MaxCutGames.Soundness.PartnerLinear

open PartnerProjection
open MaxCutGames.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
  toBit_ofBit ofBit_xor)

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev SourceCoordinates (P : Type) := F2 × (P → F2 × F2)
abbrev Active := {j : P // active j = true}
abbrev Inactive := {j : P // active j = false}
abbrev PartnerCoordinates := F2 × ((Inactive active → F2 × F2) × (Active active → F2))

def sourceCoordinates (x : SourcePoint rhs) : SourceCoordinates P :=
  (ofBit x.homogeneous, fun j => (ofBit (x.coordinates j).first, ofBit (x.coordinates j).second))

def sourceFromCoordinates (v : SourceCoordinates P) : SourcePoint rhs where
  homogeneous := toBit v.1
  coordinates := fun j => complete .first (rhs j && toBit v.1)
    (toBit (v.2 j).1) (toBit (v.2 j).2)
  valid := by intro j; exact parity_complete _ _ _ _

def sourceEquiv : SourcePoint rhs ≃ SourceCoordinates P where
  toFun := sourceCoordinates rhs
  invFun := sourceFromCoordinates rhs
  left_inv x := by
    apply source_ext rhs
    · exact toBit_ofBit _
    · funext j
      change complete .first (rhs j && toBit (ofBit x.homogeneous))
        (toBit (ofBit (x.coordinates j).first))
        (toBit (ofBit (x.coordinates j).second)) = x.coordinates j
      simp only [toBit_ofBit, ← x.valid j]
      exact complete_coordinates .first (x.coordinates j)
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · funext j
      apply Prod.ext <;> exact ofBit_toBit _

def partnerCoordinates (y : PartnerPoint rhs active) : PartnerCoordinates active :=
  (ofBit y.homogeneous,
    (fun j => (ofBit (y.full j.val).first, ofBit (y.full j.val).second),
      fun j => ofBit (y.single j.val)))

def partnerFromCoordinates (v : PartnerCoordinates active) : PartnerPoint rhs active where
  homogeneous := toBit v.1
  full := fun j => if hj : active j = false then
    complete .first (rhs j && toBit v.1)
      (toBit (v.2.1 ⟨j, hj⟩).1) (toBit (v.2.1 ⟨j, hj⟩).2)
    else zeroTriple
  single := fun j => if hj : active j = true then toBit (v.2.2 ⟨j, hj⟩) else false
  full_zero := by intro j hj; simp [hj]
  full_valid := by intro j hj; simp only [dite_eq_left hj]; exact parity_complete _ _ _ _
  single_zero := by intro j hj; simp [hj]

def partnerEquiv : PartnerPoint rhs active ≃ PartnerCoordinates active where
  toFun := partnerCoordinates rhs active
  invFun := partnerFromCoordinates rhs active
  left_inv y := by
    apply partner_ext rhs active
    · exact toBit_ofBit _
    · funext j
      cases hj : active j with
      | false =>
        change (if hj' : active j = false then
          complete .first (rhs j && toBit (ofBit y.homogeneous))
            (toBit (ofBit (y.full j).first)) (toBit (ofBit (y.full j).second))
          else zeroTriple) = y.full j
        simp only [dite_eq_left hj, toBit_ofBit, ← y.full_valid j hj]
        exact complete_coordinates .first (y.full j)
      | true => simpa [partnerFromCoordinates, hj] using (y.full_zero j hj).symm
    · funext j
      cases hj : active j with
      | false => simpa [partnerFromCoordinates, hj] using (y.single_zero j hj).symm
      | true => simp [partnerFromCoordinates, partnerCoordinates, hj, toBit_ofBit]
  right_inv v := by
    apply Prod.ext
    · exact ofBit_toBit _
    · apply Prod.ext
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, complete, ofBit_toBit]
      · funext j
        simp [partnerCoordinates, partnerFromCoordinates, j.property, ofBit_toBit]

noncomputable instance sourceAddCommGroup : AddCommGroup (SourcePoint rhs) :=
  (sourceEquiv rhs).addCommGroup

noncomputable instance sourceModule : Module F2 (SourcePoint rhs) :=
  (sourceEquiv rhs).addEquiv.module F2

noncomputable instance partnerAddCommGroup : AddCommGroup (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addCommGroup

noncomputable instance partnerModule : Module F2 (PartnerPoint rhs active) :=
  (partnerEquiv rhs active).addEquiv.module F2

noncomputable def sourceLinearEquiv : SourcePoint rhs ≃ₗ[F2] SourceCoordinates P :=
  (sourceEquiv rhs).addEquiv.linearEquiv F2

noncomputable def partnerLinearEquiv : PartnerPoint rhs active ≃ₗ[F2] PartnerCoordinates active :=
  (partnerEquiv rhs active).addEquiv.linearEquiv F2

noncomputable instance sourceFintype [Fintype P] : Fintype (SourcePoint rhs) := by
  classical
  exact Fintype.ofEquiv (SourceCoordinates P) (sourceEquiv rhs).symm

noncomputable instance partnerFintype [Fintype P] : Fintype (PartnerPoint rhs active) := by
  classical
  exact Fintype.ofEquiv (PartnerCoordinates active) (partnerEquiv rhs active).symm

theorem source_add (x y : SourcePoint rhs) : x + y = addSource rhs x y := by
  apply (sourceEquiv rhs).injective
  change sourceEquiv rhs ((sourceEquiv rhs).symm (sourceEquiv rhs x + sourceEquiv rhs y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · funext j
    apply Prod.ext <;> exact (ofBit_xor _ _).symm

theorem source_zero : (0 : SourcePoint rhs) = zeroSource rhs := by
  apply (sourceEquiv rhs).injective
  change sourceEquiv rhs ((sourceEquiv rhs).symm 0) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem partner_add (x y : PartnerPoint rhs active) : x + y = addPartner rhs active x y := by
  apply (partnerEquiv rhs active).injective
  change partnerEquiv rhs active ((partnerEquiv rhs active).symm
    (partnerEquiv rhs active x + partnerEquiv rhs active y)) = _
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · exact (ofBit_xor _ _).symm
  · apply Prod.ext
    · funext j
      apply Prod.ext <;> exact (ofBit_xor _ _).symm
    · funext j
      exact (ofBit_xor _ _).symm

theorem partner_zero : (0 : PartnerPoint rhs active) = zeroPartner rhs active := by
  apply (partnerEquiv rhs active).injective
  change partnerEquiv rhs active ((partnerEquiv rhs active).symm 0) = _
  rw [Equiv.apply_symm_apply]
  rfl

noncomputable def projection : SourcePoint rhs →ₗ[F2] PartnerPoint rhs active where
  toFun := project rhs active slot
  map_add' x y := by rw [source_add, partner_add]; exact project_add rhs active slot x y
  map_smul' c x := by
    rcases scalar_cases c with rfl | rfl
    · change project rhs active slot ((0 : F2) • x) = (0 : F2) • project rhs active slot x
      rw [zero_smul, zero_smul, source_zero, partner_zero, project_zero]
    · simp

theorem projection_apply (x : SourcePoint rhs) :
    projection rhs active slot x = project rhs active slot x := rfl

theorem projection_surjective : Function.Surjective (projection rhs active slot) :=
  project_surjective rhs active slot

theorem mem_projection_ker (x : SourcePoint rhs) :
    x ∈ (projection rhs active slot).ker ↔ InKernel rhs active slot x := by
  change project rhs active slot x = 0 ↔ _
  rw [partner_zero]
  rfl

noncomputable instance sourceFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (SourcePoint rhs) :=
  (sourceLinearEquiv rhs).symm.finiteDimensional

noncomputable instance partnerFiniteDimensional [Fintype P] :
    FiniteDimensional F2 (PartnerPoint rhs active) :=
  (partnerLinearEquiv rhs active).symm.finiteDimensional

/-- Identifies the actual linear kernel with the previously counted concrete kernel. -/
noncomputable def kernelEquiv :
    (projection rhs active slot).ker ≃ KernelCardinality.Kernel rhs active slot where
  toFun x := ⟨x.val, (mem_projection_ker rhs active slot x.val).1 x.property⟩
  invFun x := ⟨x.val, (mem_projection_ker rhs active slot x.val).2 x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem projection_ker_card [Fintype P] :
    Nat.card (projection rhs active slot).ker = 2 ^ Fintype.card (Active active) := by
  rw [Nat.card_congr (kernelEquiv rhs active slot), Nat.card_eq_fintype_card]
  exact KernelCardinality.kernel_card rhs active slot

theorem projection_ker_finrank [Fintype P] :
    Module.finrank F2 (projection rhs active slot).ker = Fintype.card (Active active) := by
  have h := MaxCutGames.Gadget.LinearKernelCount.card_binary_space
    (V := (projection rhs active slot).ker)
  rw [projection_ker_card] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ (2 : Nat)) h.symm

theorem projection_ker_finrank_of_card [Fintype P] (t : Nat)
    (ht : Fintype.card (Active active) = t) :
    Module.finrank F2 (projection rhs active slot).ker = t := by
  rw [projection_ker_finrank, ht]

theorem source_finrank [Fintype P] :
    Module.finrank F2 (SourcePoint rhs) = 1 + 2 * Fintype.card P := by
  rw [(sourceLinearEquiv rhs).finrank_eq]
  simp [SourceCoordinates, Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm]

/-- Distinct coordinate blocks make disjoint active-set kernels have trivial intersection. -/
theorem disjoint_projection_kernels
    (active' : P → Bool) (slot' : P → Slot)
    (hdisjoint : ∀ j, active j = true → active' j = false) :
    (projection rhs active slot).ker ⊓ (projection rhs active' slot').ker = ⊥ := by
  apply le_antisymm
  · intro x hx
    change x = 0
    rw [source_zero]
    exact disjoint_kernels_intersection_zero rhs active slot active' slot' hdisjoint x
      ((mem_projection_ker rhs active slot x).1 hx.1)
      ((mem_projection_ker rhs active' slot' x).1 hx.2)
  · exact bot_le

noncomputable def sourceTau : SourcePoint rhs →ₗ[F2] F2 :=
  (LinearMap.fst F2 F2 (P → F2 × F2)).comp (sourceLinearEquiv rhs).toLinearMap

noncomputable def partnerTau : PartnerPoint rhs active →ₗ[F2] F2 :=
  (LinearMap.fst F2 F2 ((Inactive active → F2 × F2) × (Active active → F2))).comp
    (partnerLinearEquiv rhs active).toLinearMap

theorem sourceTau_apply (x : SourcePoint rhs) : sourceTau rhs x = ofBit x.homogeneous := rfl
theorem partnerTau_apply (x : PartnerPoint rhs active) :
    partnerTau rhs active x = ofBit x.homogeneous := rfl

theorem tau_comp_projection :
    (partnerTau rhs active).comp (projection rhs active slot) = sourceTau rhs := by
  ext x
  rfl

end MaxCutGames.Soundness.PartnerLinear

end OAI
