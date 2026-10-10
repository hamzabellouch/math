import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section BoundedRelationCover

variable (α : Type*) (L : ℕ)

def ShortWord := Σ n : Fin (L + 1), Fin n.val → α × Bool

def ShortWord.value (w : ShortWord α L) : FreeGroup α :=
  FreeGroup.mk (List.ofFn w.2)

instance [Finite α] : Finite (ShortWord α L) := by
  unfold ShortWord
  infer_instance

variable {α} {G : Type*} [Group G] (f : α → G)

def shortRelations : Set (FreeGroup α) :=
  Set.range (ShortWord.value α L) ∩ (FreeGroup.lift f).ker

theorem shortRelations_finite [Finite α] : (shortRelations L f).Finite :=
  (Set.finite_range (ShortWord.value α L)).subset Set.inter_subset_left

abbrev BoundedRelationCover := PresentedGroup (shortRelations L f)

instance [Finite α] : Group.IsFinitelyPresented (BoundedRelationCover L f) := by
  have : Finite (shortRelations L f) := (shortRelations_finite L f).to_subtype
  unfold BoundedRelationCover
  infer_instance

def coverMap : BoundedRelationCover L f →* G :=
  PresentedGroup.toGroup (fun _ h => h.2)

@[simp] theorem coverMap_mk (w : FreeGroup α) :
    coverMap L f (PresentedGroup.mk (shortRelations L f) w) = FreeGroup.lift f w := rfl

@[simp] theorem coverMap_of (a : α) :
    coverMap L f (PresentedGroup.of a) = f a := by
  exact FreeGroup.lift_apply_of

theorem coverMap_surjective (hf : Function.Surjective (FreeGroup.lift f)) :
    Function.Surjective (coverMap L f) := by
  intro g
  obtain ⟨w, hw⟩ := hf g
  exact ⟨PresentedGroup.mk (shortRelations L f) w, hw⟩

theorem mem_shortRelations_of_length [DecidableEq α] {L : ℕ} {w : FreeGroup α}
    (hw : FreeGroup.lift f w = 1) (hlen : w.toWord.length ≤ L) :
    w ∈ shortRelations L f := by
  classical
  refine ⟨⟨⟨⟨w.toWord.length,by omega⟩,fun i => w.toWord[i]⟩, ?_⟩,hw⟩
  change FreeGroup.mk (List.ofFn w.toWord.get) = w
  rw [List.ofFn_get]
  exact FreeGroup.mk_toWord

theorem finite_true_relations_bounded {R : Set (FreeGroup α)} (hR : R.Finite)
    (ht : ∀ w ∈ R, FreeGroup.lift f w = 1) :
    ∃ L : ℕ, R ⊆ shortRelations L f := by
  classical
  refine ⟨hR.toFinset.sup (fun w => w.toWord.length), ?_⟩
  intro w hw
  exact mem_shortRelations_of_length f (ht w hw)
    (Finset.le_sup (f := fun w => w.toWord.length) (hR.mem_toFinset.mpr hw))

theorem finite_table_lift {T : Type*} [Group T] [Finite T]
    (φ : T →* G) (w : T → FreeGroup α) (hw : ∀ t, FreeGroup.lift f (w t) = φ t) :
    ∃ (L : ℕ) (ρ : T →* BoundedRelationCover L f),
      (coverMap L f).comp ρ = φ ∧
      ∀ t, ρ t = PresentedGroup.mk (shortRelations L f) (w t) := by
  classical
  let R : Set (FreeGroup α) := {w 1} ∪
    Set.range (fun p : T × T => w p.1 * w p.2 * (w (p.1*p.2))⁻¹)
  have hRf : R.Finite := (Set.finite_singleton _).union (Set.finite_range _)
  obtain ⟨L,hL⟩ := finite_true_relations_bounded f hRf (by
    intro z hz
    rcases hz with hz | ⟨⟨s,t⟩,rfl⟩
    · rcases hz with rfl
      simp [hw]
    · simp [hw])
  let ρ : T →* BoundedRelationCover L f :=
    { toFun := fun t => PresentedGroup.mk (shortRelations L f) (w t)
      map_one' := PresentedGroup.one_of_mem (hL (Set.mem_union_left _ (Set.mem_singleton _)))
      map_mul' := by
        intro s t
        have he := PresentedGroup.one_of_mem (hL (Set.mem_union_right _
          (Set.mem_range.mpr ⟨(s,t),rfl⟩)))
        simp only [map_mul, map_inv, mul_inv_eq_one] at he
        exact he.symm }
  refine ⟨L,ρ,?_,fun _ => rfl⟩
  ext t
  exact hw t

theorem finitelyPresented_of_cover [Finite α]
    (hf : Function.Surjective (FreeGroup.lift f))
    [Group.FG (coverMap L f).ker] : Group.IsFinitelyPresented G :=
  Group.IsFinitelyPresented.of_surjective (coverMap L f) (coverMap_surjective L f hf)
    (Subgroup.IsFinitelyNormallyGenerated.of_FG _)

end BoundedRelationCover

section CoherentBoundedCovers
variable {α G : Type*} [Group G] (f : α → G)

theorem shortRelations_mono {L M : ℕ} (hLM : L ≤ M) :
    shortRelations L f ⊆ shortRelations M f := by
  rintro w ⟨⟨⟨n,v⟩,rfl⟩,he⟩
  exact ⟨⟨⟨⟨n.val,by omega⟩,v⟩,rfl⟩,he⟩

def coverTransition {L M : ℕ} (hLM : L ≤ M) :
    BoundedRelationCover L f →* BoundedRelationCover M f :=
  PresentedGroup.map (MonoidHom.id _) (fun _ h => shortRelations_mono f hLM h)

@[simp] theorem coverTransition_mk {L M : ℕ} (hLM : L ≤ M) (w : FreeGroup α) :
    coverTransition f hLM (PresentedGroup.mk (shortRelations L f) w) =
      PresentedGroup.mk (shortRelations M f) w := rfl

theorem coverTransition_surjective {L M : ℕ} (hLM : L ≤ M) :
    Function.Surjective (coverTransition f hLM) := by
  intro g
  obtain ⟨w,rfl⟩ := PresentedGroup.mk_surjective (shortRelations M f) g
  exact ⟨PresentedGroup.mk (shortRelations L f) w,rfl⟩

theorem coverTransition_projection {L M : ℕ} (hLM : L ≤ M) :
    (coverMap M f).comp (coverTransition f hLM) = coverMap L f := by
  ext a
  simp only [MonoidHom.comp_apply, PresentedGroup.of, coverTransition_mk, coverMap_mk]

theorem finite_table_lift_eventually {T : Type*} [Group T] [Finite T]
    (φ : T →* G) (w : T → FreeGroup α) (hw : ∀ t, FreeGroup.lift f (w t) = φ t) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∃ ρ : T →* BoundedRelationCover M f,
      (coverMap M f).comp ρ = φ ∧
      ∀ t, ρ t = PresentedGroup.mk (shortRelations M f) (w t) := by
  obtain ⟨L,ρ,hρ,hword⟩ := finite_table_lift f φ w hw
  refine ⟨L,fun M hM => ⟨(coverTransition f hM).comp ρ,?_,?_⟩⟩
  · rw [← MonoidHom.comp_assoc,coverTransition_projection,hρ]
  · intro t
    simp only [MonoidHom.comp_apply,hword,coverTransition_mk]

theorem bounded_cover_eventually_perfect [Finite α] [Group.IsPerfect G]
    (hf : Function.Surjective (FreeGroup.lift f)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → Group.IsPerfect (BoundedRelationCover M f) := by
  classical
  have hmap : (commutator (FreeGroup α)).map (FreeGroup.lift f) = ⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf,
      ← commutator_def,Group.IsPerfect.commutator_eq_top]
  have hex (a : α) : ∃ w ∈ commutator (FreeGroup α), FreeGroup.lift f w = f a :=
    Subgroup.mem_map.mp (hmap.symm ▸ Subgroup.mem_top (f a))
  choose w hw hwe using hex
  let R : Set (FreeGroup α) := Set.range (fun a => w a * (FreeGroup.of a)⁻¹)
  obtain ⟨L,hL⟩ := finite_true_relations_bounded f (R := R) (Set.finite_range _) (by
    rintro r ⟨a,rfl⟩
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hwe, mul_inv_cancel])
  refine ⟨L,fun M hM => ?_⟩
  let π := PresentedGroup.mk (shortRelations M f)
  have hgen (a : α) : π (FreeGroup.of a) ∈ commutator (BoundedRelationCover M f) := by
    have he : π (w a) = π (FreeGroup.of a) :=
      PresentedGroup.mk_eq_mk_of_mul_inv_mem
        (shortRelations_mono f hM (hL (Set.mem_range.mpr ⟨a,rfl⟩)))
    rw [← he]
    have hle : (commutator (FreeGroup α)).map π ≤ commutator (BoundedRelationCover M f) := by
      rw [map_commutator_eq,commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hle (Subgroup.mem_map.mpr ⟨w a,hw a,rfl⟩)
  constructor
  apply top_unique
  intro g hg
  clear hg
  obtain ⟨z,rfl⟩ := PresentedGroup.mk_surjective (shortRelations M f) g
  induction z using FreeGroup.induction_on with
  | one => exact (commutator _).one_mem
  | of a => exact hgen a
  | inv_of a ha => exact (commutator _).inv_mem ha
  | mul x y hx hy => exact (commutator _).mul_mem hx hy

theorem finitelyPresented_lift_eventually {T : Type*} [Group T]
    [Group.IsFinitelyPresented T] (φ : T →* G)
    (hf : Function.Surjective (FreeGroup.lift f)) :
    ∃ L : ℕ, ∀ M : ℕ, L ≤ M → ∃ ρ : T →* BoundedRelationCover M f,
      (coverMap M f).comp ρ = φ := by
  classical
  obtain ⟨n,R,hR,⟨e⟩⟩ := Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup (G := T)
  let ψ : PresentedGroup R →* G := φ.comp e.symm.toMonoidHom
  have hex (i : Fin n) : ∃ w : FreeGroup α, FreeGroup.lift f w = ψ (PresentedGroup.of i) :=
    hf _
  choose w hw using hex
  let W : FreeGroup (Fin n) →* FreeGroup α := FreeGroup.lift w
  have hW : (FreeGroup.lift f).comp W = ψ.comp (PresentedGroup.mk R) := by
    ext i
    simpa only [MonoidHom.comp_apply, W, FreeGroup.lift_apply_of, PresentedGroup.of] using hw i
  obtain ⟨L,hL⟩ := finite_true_relations_bounded f (hR.image W) (by
    rintro z ⟨r,hr,rfl⟩
    have he := DFunLike.congr_fun hW r
    simpa only [MonoidHom.comp_apply,PresentedGroup.one_of_mem hr,map_one] using he)
  refine ⟨L,fun M hM => ?_⟩
  let ρ₀ : PresentedGroup R →* BoundedRelationCover M f :=
    PresentedGroup.map W (fun r hr => shortRelations_mono f hM (hL ⟨r,hr,rfl⟩))
  have hρ : (coverMap M f).comp ρ₀ = ψ := by
    ext i
    change coverMap M f (PresentedGroup.mk _ (W (FreeGroup.of i))) = ψ (PresentedGroup.of i)
    rw [coverMap_mk]
    exact DFunLike.congr_fun hW (FreeGroup.of i)
  refine ⟨ρ₀.comp e.toMonoidHom,?_⟩
  rw [← MonoidHom.comp_assoc,hρ]
  ext t
  exact congrArg φ (e.symm_apply_apply t)

end CoherentBoundedCovers

end SimpleAmenable
end
end

end OAI
