import Mathlib
import OAI.Computability.DirectedFeedback.Games.FinishReduction

namespace OAI


namespace DFVSGames.Soundness.KernelCardinality

open PartnerProjection

variable {P : Type} (rhs active : P → Bool) (slot : P → Slot)

abbrev Kernel := {x : SourcePoint rhs // InKernel rhs active slot x}

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

end DFVSGames.Soundness.KernelCardinality


namespace DFVSGames.Gadget.LinearKernelCount

universe u v

variable {V : Type u} {P : Type v}
variable [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
variable [AddCommGroup P] [Module (ZMod 2) P]

theorem card_binary_space : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)]
  simp

theorem kernel_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V := by
  rw [card_binary_space (V := f.ker), card_binary_space (V := V), ← pow_add]
  congr 1
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker

theorem card_source_pos : 0 < Nat.card V := by
  rw [card_binary_space]
  exact Nat.pow_pos (by decide)

theorem kernel_card_eq_pow_sub_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card f.ker =
      2 ^ (Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) f.range) := by
  rw [card_binary_space (V := f.ker)]
  congr 1
  have h := f.finrank_range_add_finrank_ker
  omega

theorem zero_event_card_mul_pow_rank (f : V →ₗ[ZMod 2] P) :
    Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range = Nat.card V :=
  kernel_card_mul_pow_rank f

theorem zero_event_card_mul_pow_le (f : V →ₗ[ZMod 2] P) (r : Nat)
    (hr : r ≤ Module.finrank (ZMod 2) f.range) :
    Nat.card {x : V // f x = 0} * 2 ^ r ≤ Nat.card V := by
  calc
    Nat.card {x : V // f x = 0} * 2 ^ r ≤
        Nat.card {x : V // f x = 0} * 2 ^ Module.finrank (ZMod 2) f.range :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hr)
    _ = Nat.card V := zero_event_card_mul_pow_rank f

theorem zero_event_finset_count_mul_pow_rank [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) :
    (Finset.univ.filter (fun x : V => f x = 0)).card *
      2 ^ Module.finrank (ZMod 2) f.range = Fintype.card V := by
  have h := zero_event_card_mul_pow_rank f
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem zero_event_finset_count_mul_pow_le [Fintype V] [DecidableEq P]
    (f : V →ₗ[ZMod 2] P) (r : Nat)
    (hr : r ≤ Module.finrank (ZMod 2) f.range) :
    (Finset.univ.filter (fun x : V => f x = 0)).card * 2 ^ r ≤ Fintype.card V := by
  have h := zero_event_card_mul_pow_le f r hr
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

end DFVSGames.Gadget.LinearKernelCount


namespace DFVSGames.Soundness.PartnerLinear

open PartnerProjection
open DFVSGames.Integration.BinaryLinear (F2 ofBit toBit scalar_cases ofBit_toBit
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
  have h := DFVSGames.Gadget.LinearKernelCount.card_binary_space
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

end DFVSGames.Soundness.PartnerLinear


namespace DFVSGames.Soundness.ZeroInformation

section Fibres

variable {P X Y : Type} (hidden : P → Bool) (reveal : P → X → Y) (observed : P → Y)

def Fibre := {sample : P → X //
  ∀ j, hidden j = false → reveal j (sample j) = observed j}

def Inside := (j : P) → hidden j = true → X

def Outside := {sample : (j : P) → hidden j = false → X //
  ∀ j hj, reveal j (sample j hj) = observed j}

def fibreInside (sample : Fibre hidden reveal observed) : Inside (X := X) hidden :=
  fun j _ => sample.val j

def fibreOutside (sample : Fibre hidden reveal observed) : Outside hidden reveal observed :=
  ⟨fun j _ => sample.val j, sample.property⟩

def assemble (inside : Inside (X := X) hidden) (outside : Outside hidden reveal observed) :
    Fibre hidden reveal observed :=
  ⟨fun j => if hj : hidden j = true then inside j hj else outside.val j (by
      cases h : hidden j
      · rfl
      · exact False.elim (hj h)), by
    intro j hj
    simp only [hj, Bool.false_eq_true, ↓reduceDIte]
    exact outside.property j hj⟩

@[simp] theorem inside_assemble (inside : Inside (X := X) hidden)
    (outside : Outside hidden reveal observed) :
    fibreInside hidden reveal observed (assemble hidden reveal observed inside outside) = inside := by
  funext j hj
  simp [fibreInside, assemble, hj]

@[simp] theorem outside_assemble (inside : Inside (X := X) hidden)
    (outside : Outside hidden reveal observed) :
    fibreOutside hidden reveal observed (assemble hidden reveal observed inside outside) = outside := by
  apply Subtype.ext
  funext j hj
  simp [fibreOutside, assemble, hj]

@[simp] theorem assemble_split (sample : Fibre hidden reveal observed) :
    assemble hidden reveal observed
      (fibreInside hidden reveal observed sample)
      (fibreOutside hidden reveal observed sample) = sample := by
  apply Subtype.ext
  funext j
  simp only [assemble, fibreInside, fibreOutside]
  split <;> rfl

theorem fibre_product (sample : Fibre hidden reveal observed) :
    ∃ inside : Inside (X := X) hidden, ∃ outside : Outside hidden reveal observed,
      assemble hidden reveal observed inside outside = sample := by
  exact ⟨fibreInside hidden reveal observed sample,
    fibreOutside hidden reveal observed sample,
    assemble_split hidden reveal observed sample⟩

end Fibres

def mass {A : Type} : List A → (A → Nat) → Nat
  | [], _ => 0
  | a :: rest, w => w a + mass rest w

theorem mass_scale {A : Type} (xs : List A) (w : A → Nat) (c : Nat) :
    mass xs (fun x => c * w x) = c * mass xs w := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih => simp only [mass, ih, Nat.mul_add]

theorem rectangular_mass {A B : Type} (outside : List A) (inside : List B)
    (outsideWeight : A → Nat) (insideWeight : B → Nat) :
    mass outside (fun a => mass inside (fun b => outsideWeight a * insideWeight b)) =
      mass outside outsideWeight * mass inside insideWeight := by
  induction outside with
  | nil => simp [mass]
  | cons a outside ih =>
      change mass inside (fun b => outsideWeight a * insideWeight b) +
        mass outside (fun a => mass inside (fun b => outsideWeight a * insideWeight b)) = _
      rw [ih, mass_scale]
      simp only [mass, Nat.add_mul]

theorem conditional_inside_identity {A B : Type} (outside : List A) (inside : List B)
    (outsideWeight : A → Nat) (insideWeight : B → Nat) (event : B → Bool) :
    mass outside (fun a => mass inside (fun b =>
        outsideWeight a * (if event b then insideWeight b else 0))) *
      mass inside insideWeight =
    mass outside (fun a => mass inside (fun b => outsideWeight a * insideWeight b)) *
      mass inside (fun b => if event b then insideWeight b else 0) := by
  rw [rectangular_mass, rectangular_mass]
  simp only [Nat.mul_assoc]
  rw [Nat.mul_comm (mass inside (fun b => if event b then insideWeight b else 0))]

abbrev Bits (R : Type) := R → Bool

def zero {R : Type} : Bits R := fun _ => false

def add {R : Type} (a b : Bits R) : Bits R := fun r => a r ^^ b r

def scale {R : Type} (coefficient : Bits R) (bit : Bool) : Bits R :=
  fun r => coefficient r && bit

@[simp] theorem scale_zero {R : Type} (bit : Bool) :
    scale (zero : Bits R) bit = zero := by
  funext r
  simp [scale, zero]

def rowSum {P R : Type} (positions : List P) (term : P → Bits R) : Bits R :=
  positions.foldr (fun j acc => add (term j) acc) zero

theorem rowSum_congr {P R : Type} (positions : List P) (a b : P → Bits R)
    (h : ∀ j, a j = b j) : rowSum positions a = rowSum positions b := by
  have hab : a = b := funext h
  rw [hab]

def pullbackRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (indices : P → Fin 3) (homogeneous : Bool) (x : P → Fin 3 → Bool) : Bits R :=
  add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (x j (indices j))
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))

theorem pullbackRow_index_independent {P R : Type} (positions : List P)
    (single : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (i i' : P → Fin 3)
    (agrees : ∀ j, single j = true → omega j ≠ zero → i j = i' j)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    pullbackRow positions single zeta0 zeta1 zeta2 omega i homogeneous x =
      pullbackRow positions single zeta0 zeta1 zeta2 omega i' homogeneous x := by
  unfold pullbackRow
  congr 1
  apply rowSum_congr
  intro j
  cases hs : single j
  · simp
  · simp only [↓reduceIte]
    by_cases hz : omega j = zero
    · simp [hz]
    · rw [agrees j hs hz]

theorem pullbackRow_from_outside_names {P R O N : Type} (positions : List P)
    (single : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (i i' : P → Fin 3)
    (sameNames : ∀ j, single j = true → omega j ≠ zero →
      name (occurrences j) (i j) = name (occurrences j) (i' j))
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    pullbackRow positions single zeta0 zeta1 zeta2 omega i homogeneous x =
      pullbackRow positions single zeta0 zeta1 zeta2 omega i' homogeneous x := by
  apply pullbackRow_index_independent
  intro j hj hz
  exact distinct (occurrences j) (i j) (i' j) (sameNames j hj hz)

theorem zero_third_bit {R : Type} (rhs homogeneous x1 x2 : Bool) :
    scale (zero : Bits R) ((rhs && homogeneous) ^^ x1 ^^ x2) = zero := by
  exact scale_zero _

abbrev FirstRow (P R : Type) := Bool → (P → Fin 3 → Bool) → Bits R

abbrev SecondRow (P R : Type) :=
  Bool → (P → Fin 3 → Bool) → (P → Bool) → Bits R

structure FirstInput (P R O : Type) where
  question : P → O
  row : FirstRow P R

structure SecondInput (P R O N : Type) where
  question : P → Sum O N
  row : SecondRow P R

def partnerQuestion {P O N : Type} (single : P → Bool) (occurrences : P → O)
    (names : P → N) : P → Sum O N :=
  fun j => if single j then .inr (names j) else .inl (occurrences j)

def partnerRow {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) : SecondRow P R :=
  fun homogeneous x y => add (scale zeta0 homogeneous) (rowSum positions fun j =>
    if single j then scale (omega j) (y j)
    else add (scale (zeta1 j) (x j 0)) (scale (zeta2 j) (x j 1)))

theorem partnerRow_pullback {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) (indices : P → Fin 3)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    partnerRow positions single zeta0 zeta1 zeta2 omega homogeneous x
        (fun j => x j (indices j)) =
      pullbackRow positions single zeta0 zeta1 zeta2 omega indices homogeneous x := rfl

def firstInput {P R O : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (indices : P → Fin 3) : FirstInput P R O :=
  ⟨occurrences, pullbackRow positions single zeta0 zeta1 zeta2 omega indices⟩

def secondInput {P R O N : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (occurrences : P → O) (names : P → N) : SecondInput P R O N :=
  ⟨partnerQuestion single occurrences names,
    partnerRow positions single zeta0 zeta1 zeta2 omega⟩

noncomputable def decodeIndex {O N : Type} (name : O → Fin 3 → N)
    (occurrence : O) (n : N) : Fin 3 := by
  classical
  exact if h : ∃ i, name occurrence i = n then Classical.choose h else 0

theorem decodeIndex_name {O N : Type} (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i') (o : O) (i : Fin 3) :
    decodeIndex name o (name o i) = i := by
  classical
  unfold decodeIndex
  have he : ∃ i', name o i' = name o i := ⟨i, rfl⟩
  simp only [he, ↓reduceDIte]
  exact distinct o _ i (Classical.choose_spec he)

def reconstructQuestion {P X : Type} (hidden : P → Bool) (inside outside : P → X) : P → X :=
  fun j => if hidden j then inside j else outside j

theorem reconstructQuestion_actual {P X : Type} (hidden : P → Bool)
    (actual outside : P → X) (houtside : ∀ j, hidden j = false → outside j = actual j) :
    reconstructQuestion hidden actual outside = actual := by
  funext j
  cases hj : hidden j
  · simp [reconstructQuestion, hj, houtside j hj]
  · simp [reconstructQuestion, hj]

noncomputable def reconstructFirst {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (name : O → Fin 3 → N) (insideOccurrences outsideOccurrences : P → O)
    (outsideNames : P → N) : FirstInput P R O :=
  firstInput positions single zeta0 zeta1 zeta2 omega
    (reconstructQuestion hidden insideOccurrences outsideOccurrences)
    (fun j => decodeIndex name (outsideOccurrences j) (outsideNames j))

theorem first_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_zero : ∀ j, hidden j = true → omega j = zero)
    (name : O → Fin 3 → N)
    (distinct : ∀ o i i', name o i = name o i' → i = i')
    (occurrences outsideOccurrences : P → O) (indices : P → Fin 3)
    (outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = name (occurrences j) (indices j)) :
    reconstructFirst positions single hidden zeta0 zeta1 zeta2 omega name
        occurrences outsideOccurrences outsideNames =
      firstInput positions single zeta0 zeta1 zeta2 omega occurrences indices := by
  unfold reconstructFirst firstInput
  rw [reconstructQuestion_actual hidden occurrences outsideOccurrences houtsideO]
  congr 1
  funext homogeneous x
  apply pullbackRow_index_independent
  intro j _ hz
  have hj : hidden j = false := by
    cases hh : hidden j
    · rfl
    · exact False.elim (hz (hidden_zero j hh))
  rw [houtsideO j hj, houtsideN j hj]
  exact decodeIndex_name name distinct (occurrences j) (indices j)

def reconstructSecond {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (outsideOccurrences : P → O) (insideNames outsideNames : P → N) : SecondInput P R O N :=
  secondInput positions single zeta0 zeta1 zeta2 omega outsideOccurrences
    (reconstructQuestion hidden insideNames outsideNames)

theorem second_input_reconstruction {P R O N : Type} (positions : List P)
    (single hidden : P → Bool) (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R)
    (hidden_single : ∀ j, hidden j = true → single j = true)
    (occurrences outsideOccurrences : P → O) (names outsideNames : P → N)
    (houtsideO : ∀ j, hidden j = false → outsideOccurrences j = occurrences j)
    (houtsideN : ∀ j, hidden j = false → outsideNames j = names j) :
    reconstructSecond positions single hidden zeta0 zeta1 zeta2 omega
        outsideOccurrences names outsideNames =
      secondInput positions single zeta0 zeta1 zeta2 omega occurrences names := by
  unfold reconstructSecond secondInput
  rw [reconstructQuestion_actual hidden names outsideNames houtsideN]
  congr 1
  funext j
  unfold partnerQuestion
  cases hs : single j
  · have hj : hidden j = false := by
      cases hh : hidden j
      · rfl
      · have contradiction := hidden_single j hh
        rw [hs] at contradiction
        contradiction
    simp [houtsideO j hj]
  · simp

def FirstPoint {P O : Type} (rhs : O → Bool) (question : P → O) :=
  {point : Bool × (P → Fin 3 → Bool) // ∀ j,
    (point.2 j 0 ^^ point.2 j 1 ^^ point.2 j 2) = (rhs (question j) && point.1)}

def SecondPoint {P O N : Type} (rhs : O → Bool) (question : P → Sum O N) :=
  {point : Bool × (P → Fin 3 → Bool) × (P → Bool) // ∀ j,
    match question j with
    | .inl o =>
      (point.2.1 j 0 ^^ point.2.1 j 1 ^^ point.2.1 j 2) = (rhs o && point.1) ∧
      point.2.2 j = false
    | .inr _ => ∀ i, point.2.1 j i = false}

def FirstInput.suppliedMap {P R O : Type} (input : FirstInput P R O) (rhs : O → Bool) :
    FirstPoint rhs input.question → Bits R :=
  fun point => input.row point.val.1 point.val.2

def SecondInput.suppliedMap {P R O N : Type} (input : SecondInput P R O N) (rhs : O → Bool) :
    SecondPoint rhs input.question → Bits R :=
  fun point => input.row point.val.1 point.val.2.1 point.val.2.2

def projectFull {P : Type} (single : P → Bool) (x : P → Fin 3 → Bool) :
    P → Fin 3 → Bool :=
  fun j i => if single j then false else x j i

def projectSingles {P : Type} (single : P → Bool) (indices : P → Fin 3)
    (x : P → Fin 3 → Bool) : P → Bool :=
  fun j => if single j then x j (indices j) else false

def partnerProjection {P O N : Type} (single : P → Bool) (rhs : O → Bool)
    (occurrences : P → O) (names : P → N) (indices : P → Fin 3)
    (point : FirstPoint rhs occurrences) :
    SecondPoint rhs (partnerQuestion single occurrences names) :=
  ⟨(point.val.1, projectFull single point.val.2, projectSingles single indices point.val.2), by
    intro j
    cases hs : single j
    · simp only [partnerQuestion, hs, Bool.false_eq_true, ↓reduceIte,
        projectFull, projectSingles]
      exact ⟨point.property j, True.intro⟩
    · simp [partnerQuestion, hs, projectFull]⟩

theorem partnerRow_project {P R : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) (indices : P → Fin 3)
    (homogeneous : Bool) (x : P → Fin 3 → Bool) :
    partnerRow positions single zeta0 zeta1 zeta2 omega homogeneous
        (projectFull single x) (projectSingles single indices x) =
      pullbackRow positions single zeta0 zeta1 zeta2 omega indices homogeneous x := by
  unfold partnerRow pullbackRow
  congr 1
  apply rowSum_congr
  intro j
  cases hs : single j <;> simp [hs, projectFull, projectSingles]

theorem supplied_map_pullback {P R O N : Type} (positions : List P) (single : P → Bool)
    (zeta0 : Bits R) (zeta1 zeta2 omega : P → Bits R) (rhs : O → Bool)
    (occurrences : P → O) (names : P → N) (indices : P → Fin 3)
    (point : FirstPoint rhs occurrences) :
    (secondInput positions single zeta0 zeta1 zeta2 omega occurrences names).suppliedMap rhs
        (partnerProjection single rhs occurrences names indices point) =
      (firstInput positions single zeta0 zeta1 zeta2 omega occurrences indices).suppliedMap rhs point := by
  exact partnerRow_project positions single zeta0 zeta1 zeta2 omega indices point.val.1 point.val.2

end DFVSGames.Soundness.ZeroInformation

end OAI
