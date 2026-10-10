import OAI.Computability.WeisfeilerLeman.Extension

namespace OAI

universe uB uV uT uL uLabel uP uE

namespace WLTime.Compression

namespace BlockDrawing
variable {r : ℕ} {B : Type uB} {V : Type uV} (D : BlockDrawing r B V)

theorem seam_potential_exists (hr : 2 ≤ r) (U : Finset B) (hw : ¬D.Wraps U) :
    ∃ s : V → F₂, ∀ b ∈ U, ∀ x y, D.Edge b x y →
      s x + s y = D.rowMark (Fin.last r) x y := by
  have hclosed : ∀ v (p : (D.graph U).Walk v v),
      walkWeight (D.rowMark (Fin.last r)) p = 0 := by
    intro v p
    by_contra h
    exact hw ⟨v,p,h⟩
  obtain ⟨s, hs⟩ := exists_seam_potential (D.rowMark (Fin.last r))
    (fun x y _ => D.rowMark_symm _ x y) hclosed
  refine ⟨s, ?_⟩
  intro b hb x y hxy
  by_cases he : x = y
  · subst y
    rw [CharTwo.add_self_eq_zero, D.rowMark_zero_of_boundary_eq (by omega) _ rfl]
  · exact hs x y ⟨he,b,hb,Or.inl hxy⟩

end BlockDrawing

inductive ReadoutName (r : ℕ) (T : Type uT) (L : Type uL) (Label : Type uLabel) where
  | horizontal (row : Fin (r+1)) (type : T) (low high : Label)
  | vertical (boundary : Fin (r+1)) (link : L) (label : Label)
  deriving DecidableEq, Fintype

abbrev RawName {r m : ℕ} {P : Type uP} {E : Type uE} (K : ℕ) :=
  ReadoutName r (TypeNode K P E) (TypeLink K E) (Fin m)

namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

abbrev ReadValue (K : ℕ) : RawName (r := r) (m := m) (P := P) (E := E) K → Type
  | .horizontal _ t _ _ => I.Value K t
  | .vertical _ _ _ => F₂

abbrev Readouts (K : ℕ) := (n : RawName (r := r) (m := m) (P := P) (E := E) K) → I.ReadValue K n
abbrev Potentials (K : ℕ) := (c : RawCorner (r := r) (m := m) (P := P) (E := E) K) → I.Value K c.type

def seam (i : Fin (r+1)) : F₂ := if i = Fin.last r then 1 else 0

noncomputable def footprint (K : ℕ) : RawBlock (r := r) (m := m) (P := P) (E := E) K →
    Finset (RawName (r := r) (m := m) (P := P) (E := E) K) := by
  classical
  exact fun b => match b with
    | .site i t a b => {.horizontal i t a b}
    | .square i l a b => {
        .horizontal i (linkLeft K I.src l) a b,
        .horizontal i (linkRight K I.dst l)
          (linkMatch K (fun e => I.coordinatePerm e i) l a)
          (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b),
        .vertical i l a, .vertical (finRotate (r+1) i) l b}

def AgreeOn (K : ℕ) (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (R S : I.Readouts K) : Prop :=
  ∀ b ∈ U, ∀ n ∈ I.footprint K b, R n = S n

namespace AgreeOn
variable {I} {K : ℕ} {U V : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    {R S T : I.Readouts K}
theorem refl (R : I.Readouts K) : I.AgreeOn K U R R := fun _ _ _ _ => rfl
theorem symm (h : I.AgreeOn K U R S) : I.AgreeOn K U S R := fun b hb n hn => (h b hb n hn).symm
theorem trans (h : I.AgreeOn K U R S) (h' : I.AgreeOn K U S T) : I.AgreeOn K U R T :=
  fun b hb n hn => (h b hb n hn).trans (h' b hb n hn)
theorem mono (h : I.AgreeOn K U R S) (hVU : V ⊆ U) : I.AgreeOn K V R S :=
  fun b hb n hn => h b (hVU hb) n hn
end AgreeOn

noncomputable def fromPotentials (K : ℕ) (M : I.Potentials K)
    (h : (t : TypeNode K P E) → I.Value K t) : I.Readouts K
  | .horizontal i t a b => horizontalReadout (M ⟨i,t,a⟩) (M ⟨finRotate (r+1) i,t,b⟩) (h t) (seam i)
  | .vertical i l a => verticalReadout (I.leftForm K l) (I.rightForm K l)
      (M ⟨i,linkLeft K I.src l,a⟩)
      (M ⟨i,linkRight K I.dst l,linkMatch K (fun e => I.coordinatePerm e i) l a⟩)

noncomputable def adjustPotentials (K : ℕ) (M : I.Potentials K)
    (s : RawCorner (r := r) (m := m) (P := P) (E := E) K → F₂)
    (old new : (t : TypeNode K P E) → I.Value K t) : I.Potentials K :=
  fun c => M c + s c • (old c.type - new c.type)

theorem adjust_horizontal (K : ℕ) (M : I.Potentials K)
    (s : RawCorner (r := r) (m := m) (P := P) (E := E) K → F₂)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (i : Fin (r+1)) (t : TypeNode K P E) (a b : Fin m)
    (hs : s ⟨i,t,a⟩ + s ⟨finRotate (r+1) i,t,b⟩ = seam i) :
    I.fromPotentials K (I.adjustPotentials K M s old new) new (.horizontal i t a b) =
      I.fromPotentials K M old (.horizontal i t a b) :=
  horizontal_adjustment _ _ _ _ _ _ _ hs

theorem adjust_vertical (K : ℕ) (M : I.Potentials K)
    (s : RawCorner (r := r) (m := m) (P := P) (E := E) K → F₂)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (i : Fin (r+1)) (l : TypeLink K E) (a : Fin m)
    (hs : s ⟨i,linkLeft K I.src l,a⟩ =
      s ⟨i,linkRight K I.dst l,linkMatch K (fun e => I.coordinatePerm e i) l a⟩)
    (ho : I.leftForm K l (old (linkLeft K I.src l)) + I.rightForm K l (old (linkRight K I.dst l)) = I.linkBias K l)
    (hn : I.leftForm K l (new (linkLeft K I.src l)) + I.rightForm K l (new (linkRight K I.dst l)) = I.linkBias K l) :
    I.fromPotentials K (I.adjustPotentials K M s old new) new (.vertical i l a) =
      I.fromPotentials K M old (.vertical i l a) := by
  dsimp only [fromPotentials, adjustPotentials]
  rw [hs]
  apply vertical_adjustment
  exact homogeneous_shift_difference _ _ _ _ _ _ _ ho hn

theorem adjust_nonwrapping [DecidableEq E] (K : ℕ) (hr : 2 ≤ r)
    (V : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (hw : ¬(I.drawing K).Wraps V) (M : I.Potentials K)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (ho : I.ShiftSolves K (BlockName.links V) old) (hn : I.ShiftSolves K (BlockName.links V) new) :
    ∃ M' : I.Potentials K, I.AgreeOn K V (I.fromPotentials K M' new) (I.fromPotentials K M old) := by
  classical
  obtain ⟨s, hs⟩ := (I.drawing K).seam_potential_exists hr V hw
  have hhor (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ V) (side : Bool) :
      s ((I.drawing K).low b side) + s ((I.drawing K).high b side) = seam ((I.drawing K).row b) := by
    rw [hs b hb _ _ (Or.inl ⟨side,rfl,rfl⟩), (I.drawing K).rowMark_horizontal hr]
    simp only [seam, eq_comm (a := Fin.last r)]
  have hver (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ V) :
      s ((I.drawing K).low b false) = s ((I.drawing K).low b true) ∧
      s ((I.drawing K).high b false) = s ((I.drawing K).high b true) := by
    constructor
    · apply CharTwo.add_eq_zero.mp
      rw [hs b hb _ _ (Or.inr (Or.inl ⟨rfl,rfl⟩))]
      exact (I.drawing K).rowMark_zero_of_boundary_eq (by omega) _
        (((I.drawing K).low_boundary b false).trans ((I.drawing K).low_boundary b true).symm)
    · apply CharTwo.add_eq_zero.mp
      rw [hs b hb _ _ (Or.inr (Or.inr ⟨rfl,rfl⟩))]
      exact (I.drawing K).rowMark_zero_of_boundary_eq (by omega) _
        (((I.drawing K).high_boundary b false).trans ((I.drawing K).high_boundary b true).symm)
  refine ⟨I.adjustPotentials K M s old new, ?_⟩
  intro b hb n hnmem
  cases b with
  | site i t a b =>
    simp only [footprint, Finset.mem_singleton] at hnmem
    subst n
    exact I.adjust_horizontal K M s old new i t a b (hhor _ hb false)
  | square i l a b =>
    have hl := BlockName.square_link_mem hb
    simp only [footprint, Finset.mem_insert, Finset.mem_singleton] at hnmem
    rcases hnmem with rfl | rfl | rfl | rfl
    · exact I.adjust_horizontal K M s old new i _ _ _ (hhor _ hb false)
    · exact I.adjust_horizontal K M s old new i _ _ _ (hhor _ hb true)
    · exact I.adjust_vertical K M s old new i l a (hver _ hb).1 (ho l hl) (hn l hl)
    · exact I.adjust_vertical K M s old new _ l b (hver _ hb).2 (ho l hl) (hn l hl)

theorem fromPotentials_agree [DecidableEq E] (K : ℕ)
    (V : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (M : I.Potentials K)
    (old new : (t : TypeNode K P E) → I.Value K t)
    (heq : ∀ b ∈ V, ∀ side, old ((I.drawing K).low b side).type = new ((I.drawing K).low b side).type) :
    I.AgreeOn K V (I.fromPotentials K M old) (I.fromPotentials K M new) := by
  classical
  intro b hb n hn
  cases b with
  | site i t a b =>
    simp only [footprint, Finset.mem_singleton] at hn
    subst n
    have ht := heq _ hb false
    change old t = new t at ht
    simp only [fromPotentials, ht]
  | square i l a b =>
    have ht := heq _ hb false
    have hu := heq _ hb true
    change old (linkLeft K I.src l) = new (linkLeft K I.src l) at ht
    change old (linkRight K I.dst l) = new (linkRight K I.dst l) at hu
    simp only [footprint, Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · simp only [fromPotentials, ht]
    · simp only [fromPotentials, hu]
    · rfl
    · rfl

def OffsetFamily [DecidableEq E] (Q : I.ArcWitness) (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (R : I.Readouts K) : Prop :=
  ∃ q : I.ShiftChoice, ∃ M : I.Potentials K,
    q.Admissible Q K U ∧ I.AgreeOn K U R (I.fromPotentials K M (q.values K (BlockName.links U)))

theorem offset_nonempty [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hr : 2 ≤ r)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ r+2) :
    ∃ R, I.OffsetFamily Q K U R := by
  obtain ⟨q, hq⟩ := ShiftChoice.admissible_exists Q K hr U hU
  exact ⟨I.fromPotentials K (fun _ => 0) (q.values K (BlockName.links U)), q, fun _ => 0,
    hq, AgreeOn.refl _⟩

theorem offset_extend [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hUr : U.card ≤ r+2)
    (hvalid : ∀ b ∈ U, I.ValidBlock K b)
    (R : I.Readouts K) (hR : I.OffsetFamily Q K V R) :
    ∃ R', I.OffsetFamily Q K U R' ∧ I.AgreeOn K V R R' := by
  classical
  by_cases he : V = U
  · subst V
    exact ⟨R,hR,AgreeOn.refl R⟩
  have hproper : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hVU,he⟩
  have hVr : V.card ≤ r+1 := by have := Finset.card_lt_card hproper; omega
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  obtain ⟨q,M,hq,hRM⟩ := hR
  by_cases hw : (I.drawing K).Wraps V
  · have hcard : V.card = r+1 := Nat.le_antisymm hVr ((I.drawing K).wraps_card hr V hw)
    obtain ⟨d⟩ := I.wrapData_exists K hK hr V V hVK (Finset.Subset.refl _) hcard hw
    have hd : d.blocks = V := Finset.eq_of_subset_of_card_le d.subset (by rw [d.card]; exact hVr)
    obtain ⟨q',hq',hshift⟩ := q.extend_on_wrapping Q K hK hr hVU hUK hUr d
      (fun b hb => hvalid b (hVU hb)) hq
    let R' := I.fromPotentials K M (q'.values K (BlockName.links U))
    refine ⟨R', ⟨q',M,hq',AgreeOn.refl _⟩, hRM.trans ?_⟩
    apply I.fromPotentials_agree K V M
    intro b hb side
    exact (hshift _ (d.type_reachable hr b (hd.symm ▸ hb) side)).symm
  · obtain ⟨q',hq'⟩ := ShiftChoice.admissible_exists Q K hr U hUr
    obtain ⟨M',hM'⟩ := I.adjust_nonwrapping K hr V hw M
      (q.values K (BlockName.links V)) (q'.values K (BlockName.links U))
      (q.values_solves K hK _ ((BlockName.links_card V).trans hVK))
      (fun l hl => q'.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (BlockName.links_mono hVU hl))
    exact ⟨I.fromPotentials K M' (q'.values K (BlockName.links U)),
      ⟨q',M',hq',AgreeOn.refl _⟩, hRM.trans hM'.symm⟩

theorem offset_restrict [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K) (hr : 2 ≤ r)
    {V U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)}
    (hVU : V ⊆ U) (hUK : U.card ≤ K) (hUr : U.card ≤ r+2)
    (hvalid : ∀ b ∈ U, I.ValidBlock K b)
    (R : I.Readouts K) (hR : I.OffsetFamily Q K U R) : I.OffsetFamily Q K V R := by
  classical
  by_cases he : V = U
  · subst V; exact hR
  have hproper : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨hVU,he⟩
  have hVr : V.card ≤ r+1 := by have := Finset.card_lt_card hproper; omega
  have hVK : V.card ≤ K := (Finset.card_le_card hVU).trans hUK
  have hVr' : V.card ≤ r+2 := by omega
  obtain ⟨q,M,hq,hRM⟩ := hR
  have hRM' := hRM.mono hVU
  by_cases hw : (I.drawing K).Wraps V
  · have hcard : V.card = r+1 := Nat.le_antisymm hVr ((I.drawing K).wraps_card hr V hw)
    obtain ⟨d⟩ := I.wrapData_exists K hK hr V V hVK (Finset.Subset.refl _) hcard hw
    have hd : d.blocks = V := Finset.eq_of_subset_of_card_le d.subset (by rw [d.card]; exact hVr)
    obtain ⟨q',hq',hshift⟩ := q.restrict_on_wrapping Q K hK hr hVU hUK hVr' d
      (fun b hb => hvalid b (hVU hb)) hq
    refine ⟨q',M,hq',hRM'.trans ?_⟩
    apply I.fromPotentials_agree K V M
    intro b hb side
    exact (hshift _ (d.type_reachable hr b (hd.symm ▸ hb) side)).symm
  · obtain ⟨q',hq'⟩ := ShiftChoice.admissible_exists Q K hr V hVr'
    obtain ⟨M',hM'⟩ := I.adjust_nonwrapping K hr V hw M
      (q.values K (BlockName.links U)) (q'.values K (BlockName.links V))
      (fun l hl => q.values_solves K hK _ ((BlockName.links_card U).trans hUK) l (BlockName.links_mono hVU hl))
      (q'.values_solves K hK _ ((BlockName.links_card V).trans hVK))
    exact ⟨q',M',hq',hRM'.trans hM'.symm⟩

end ConsistencyData
end WLTime.Compression

namespace WLTime.Compression
namespace ConsistencyData
variable {r m : ℕ} {P : Type uP} {E : Type uE} (I : ConsistencyData (r+1) m P E)

instance (K : ℕ) (n : RawName (r := r) (m := m) (P := P) (E := E) K) :
    AddCommGroup (I.ReadValue K n) := by cases n <;> dsimp [ReadValue] <;> infer_instance
instance (K : ℕ) (n : RawName (r := r) (m := m) (P := P) (E := E) K) :
    Module F₂ (I.ReadValue K n) := by cases n <;> dsimp [ReadValue] <;> infer_instance
instance (K : ℕ) (n : RawName (r := r) (m := m) (P := P) (E := E) K) :
    Fintype (I.ReadValue K n) := by cases n <;> dsimp [ReadValue] <;> infer_instance

noncomputable def blockForm (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : I.Readouts K →ₗ[F₂] F₂ where
  toFun R := match b with
    | .site _ _ _ _ => 0
    | .square i l a b =>
      I.leftForm K l (R (.horizontal i (linkLeft K I.src l) a b)) +
      I.rightForm K l (R (.horizontal i (linkRight K I.dst l)
        (linkMatch K (fun e => I.coordinatePerm e i) l a)
        (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b))) +
      R (.vertical i l a) + R (.vertical (finRotate (r+1) i) l b)
  map_add' R S := by cases b <;> simp only [Pi.add_apply, map_add] <;> abel
  map_smul' c R := by cases b <;> simp only [Pi.smul_apply, map_smul, smul_add, smul_zero, RingHom.id_apply]

noncomputable def blockBias (K : ℕ) : RawBlock (r := r) (m := m) (P := P) (E := E) K → F₂
  | .site _ _ _ _ => 0
  | .square i l _ _ => seam i * I.linkBias K l

noncomputable def blockSpace (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : Submodule F₂ (I.Readouts K) where
  carrier := {R | ∀ n, n ∉ I.footprint K b → R n = 0}
  zero_mem' := by intro n _; rfl
  add_mem' := by intro R S hR hS n hn; simp only [Pi.add_apply, hR n hn, hS n hn, add_zero]
  smul_mem' := by intro c R hR n hn; simp only [Pi.smul_apply, hR n hn, smul_zero]

noncomputable def atBlock (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R : I.Readouts K) : I.blockSpace K b := by
  classical
  exact ⟨fun n => if n ∈ I.footprint K b then R n else 0,
    fun n hn => ite_eq_right hn⟩

@[simp] theorem atBlock_apply (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R : I.Readouts K)
    (n : RawName (r := r) (m := m) (P := P) (E := E) K) (hn : n ∈ I.footprint K b) :
    (I.atBlock K b R).val n = R n := by
  classical
  exact ite_eq_left hn

theorem blockForm_congr (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R S : I.Readouts K)
    (h : ∀ n ∈ I.footprint K b, R n = S n) : I.blockForm K b R = I.blockForm K b S := by
  classical
  cases b with
  | site => rfl
  | square i l a b =>
    have h₁ := h (.horizontal i (linkLeft K I.src l) a b) (by simp [footprint])
    have h₂ := h (.horizontal i (linkRight K I.dst l)
        (linkMatch K (fun e => I.coordinatePerm e i) l a)
        (linkMatch K (fun e => I.coordinatePerm e (finRotate (r+1) i)) l b)) (by simp [footprint])
    have h₃ := h (.vertical i l a) (by simp [footprint])
    have h₄ := h (.vertical (finRotate (r+1) i) l b) (by simp [footprint])
    simp only [blockForm, LinearMap.coe_mk, AddHom.coe_mk]
    rw [h₁,h₂,h₃,h₄]

@[simp] theorem blockForm_atBlock (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (R : I.Readouts K) :
    I.blockForm K b (I.atBlock K b R).val = I.blockForm K b R :=
  I.blockForm_congr K b _ _ (fun n hn => I.atBlock_apply K b R n hn)

abbrev Legal (K : ℕ) (ε : F₂)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) :=
  {R : I.blockSpace K b // I.blockForm K b R.val = ε * I.blockBias K b}

noncomputable def zeroValuation (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : I.Legal K 0 b :=
  ⟨0, by simp⟩

noncomputable def translate (K : ℕ)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (a : I.Legal K 1 b) :
    I.Legal K 0 b ≃ I.Legal K 1 b where
  toFun z := ⟨z.val + a.val, by simp only [Submodule.coe_add, map_add, z.property,
    a.property, zero_mul, zero_add, one_mul]⟩
  invFun z := ⟨z.val - a.val, by simp only [Submodule.coe_sub, map_sub, z.property,
    a.property, sub_self, zero_mul]⟩
  left_inv z := by apply Subtype.ext; exact add_sub_cancel_right _ _
  right_inv z := by apply Subtype.ext; exact sub_add_cancel _ _

theorem fromPotentials_legal [DecidableEq E] (K : ℕ)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K))
    (M : I.Potentials K) (h : (t : TypeNode K P E) → I.Value K t)
    (hh : I.ShiftSolves K (BlockName.links U) h)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ U) :
    I.blockForm K b (I.fromPotentials K M h) = I.blockBias K b := by
  cases b with
  | site => rfl
  | square i l a b =>
    exact square_readouts_legal _ _ _ _ _ _ _ _ _ _ (hh l (BlockName.square_link_mem hb))

theorem offset_legal [DecidableEq E] [DecidableEq P] (Q : I.ArcWitness)
    (K : ℕ) (hK : 0 < K)
    (U : Finset (RawBlock (r := r) (m := m) (P := P) (E := E) K)) (hU : U.card ≤ K)
    (R : I.Readouts K) (hR : I.OffsetFamily Q K U R)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) (hb : b ∈ U) :
    I.blockForm K b R = I.blockBias K b := by
  obtain ⟨q,M,hq,heq⟩ := hR
  rw [I.blockForm_congr K b R _ (heq b hb)]
  exact I.fromPotentials_legal K U M _
    (q.values_solves K hK _ ((BlockName.links_card U).trans hU)) b hb

theorem legal_nonempty (K : ℕ) (hr : 1 ≤ r) (ε : F₂)
    (b : RawBlock (r := r) (m := m) (P := P) (E := E) K) : Nonempty (I.Legal K ε b) := by
  classical
  cases b with
  | site i t a b => exact ⟨⟨0, by simp [blockForm, blockBias]⟩⟩
  | square i l a b =>
    let n : RawName (r := r) (m := m) (P := P) (E := E) K := .vertical i l a
    let R : I.Readouts K := Function.update (fun _ => 0) n (ε * (seam i * I.linkBias K l))
    refine ⟨⟨I.atBlock K (.square i l a b) R, ?_⟩⟩
    rw [I.blockForm_atBlock]
    have hv : ReadoutName.vertical (finRotate (r+1) i) l b ≠ n := by
      intro h
      have hi := ReadoutName.vertical.inj h
      exact rotate_ne_self hr i hi.1
    simp [blockForm, blockBias, R, n, Function.update_of_ne hv]

end ConsistencyData
end WLTime.Compression

end OAI
