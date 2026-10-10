import OAI.Probability.TraceReconstruction.Shapes

namespace OAI

/-!
# Energy

Shaped envelopes, actual coefficient aggregation, role counts, central contributions, and full coefficient energy.
-/

open scoped ENNReal
noncomputable section

open Filter
open scoped Topology


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
namespace OccupiedParityTree

/-- Actual unsigned coefficient envelope on one ordered occupied shape.
No bits are resampled for the additional leaves. -/
def Forced.envelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (x : t.Labels T)
    (bits : WindowAssignments T n g Bool b) (incoming : ℤ) : ℝ :=
  binaryAnchorKernel T n g s center globalShift b (F.labels T x) bits incoming *
    ∏e : F.ExtraLeafEdge, motifIndicator s ((x e.val.val).val-
      sourceTreeAnchors T n g center globalShift b bits incoming (e.val.val.parentPath T x))

def Forced.averagedEnvelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced) (x : t.Labels T)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) : ℝ :=
  (windowPosteriorLaw T n g b d).expect
    (fun bits => F.envelope T n g s center globalShift x bits incoming)

/-- Offsets for all extra leaf constraints, with only their labels replaced
by zero. The location of each constraint is not changed by that replacement. -/
def Forced.extraOffsets (T n g : ℕ → ℕ) (hT : 0<T 0) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (p : BinaryWindowLabels T b) (z : F.InteriorLabels T)
    (bits : WindowAssignments T n g Bool b) (incoming : ℤ) (e : F.ExtraLeafEdge) : ℤ :=
  sourceTreeAnchors T n g center globalShift b bits incoming
    (e.val.val.parentPath T ((F.fullLabelsEquiv T).symm (p,(fun _ => ⟨0,hT⟩),z)))

theorem Forced.averagedEnvelope_split (T n g : ℕ → ℕ) (hT : 0<T 0) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (p : BinaryWindowLabels T b) (h : F.ExtraLeafEdge → Fin (T 0)) (z : F.InteriorLabels T)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) :
    F.averagedEnvelope T n g s center globalShift ((F.fullLabelsEquiv T).symm (p,h,z)) d incoming =
      indexedExtraAverage (windowPosteriorLaw T n g b d) s (T 0)
        (fun bits => binaryAnchorKernel T n g s center globalShift b p bits incoming)
        (fun bits e => F.extraOffsets T n g hT center globalShift p z bits incoming e) h := by
  let x := (F.fullLabelsEquiv T).symm (p,h,z)
  have hx : F.fullLabelsEquiv T x=(p,h,z) := Equiv.apply_symm_apply _ _
  have hp : F.labels T x=p := by rw [←F.fullLabelsEquiv_fst,hx]
  apply congrArg (FiniteLaw.expect (windowPosteriorLaw T n g b d))
  funext bits
  change F.envelope T n g s center globalShift x bits incoming = _
  unfold Forced.envelope
  rw [hp]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  have hv := congrArg (fun a => (a.2.1 e).val) hx
  simp only [Forced.fullLabelsEquiv_leaf_value] at hv
  rw [hv]
  unfold Forced.extraOffsets
  congr 2
  exact congrArg (sourceTreeAnchors T n g center globalShift b bits incoming)
    (F.parentPath_extraLeaf_invariant T p h (fun _ => ⟨0,hT⟩) z e.val.val)

/-- Summing every actual numeric labeling of a fixed shape costs exactly
one l1-squared factor per extra leaf and one factor per extra interior label.
The forced-anchor energy remains a single genuine correlated posterior. -/
theorem Forced.envelope_energy (T n g : ℕ → ℕ) (hT : 0<T 0) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    {b : ℕ} {t : OccupiedParityTree b} (F : t.Forced)
    (R : BinaryWindowLabels T b → Prop) [DecidablePred R]
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) :
    (∑x : t.Labels T, if R (F.labels T x) then
      (F.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0) ≤
      (Fintype.card (F.InteriorLabels T):ℝ) * ((2^s:ℕ):ℝ)^(2*Fintype.card F.ExtraLeafEdge) *
        ∑p : BinaryWindowLabels T b, if R p then
          (binaryAnchorAverage T n g s center globalShift b p d incoming)^2 else 0 := by
  let L := ((2^s:ℕ):ℝ)^(2*Fintype.card F.ExtraLeafEdge)
  have hs := (F.fullLabelsEquiv T).symm.sum_comp (fun x : t.Labels T =>
    if R (F.labels T x) then (F.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0)
  rw [←hs]
  simp only [Fintype.sum_prod_type]
  calc
    _ ≤ ∑p : BinaryWindowLabels T b, ∑z : F.InteriorLabels T,
        if R p then L*(binaryAnchorAverage T n g s center globalShift b p d incoming)^2 else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro z hz
      have he (h : F.ExtraLeafEdge → Fin (T 0)) :
          F.labels T ((F.fullLabelsEquiv T).symm (p,h,z))=p := by
        rw [←F.fullLabelsEquiv_fst,Equiv.apply_symm_apply]
      simp_rw [he]
      by_cases hR : R p
      · simp only [ite_eq_left hR]
        simp_rw [F.averagedEnvelope_split T n g hT s center globalShift]
        exact indexedExtraAverage_energy (windowPosteriorLaw T n g b d) s (T 0)
          (fun bits => binaryAnchorKernel T n g s center globalShift b p bits incoming)
          (fun bits => binaryAnchorKernel_nonneg T n g s center globalShift b p bits incoming)
          (fun bits e => F.extraOffsets T n g hT center globalShift p z bits incoming e)
      · simp only [ite_eq_right hR,Finset.sum_const_zero,le_refl]
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hr : R p <;> simp [hr,L,mul_assoc]
/-- Connected forced-shape coefficient-envelope estimate with the true
common-global/local sibling energy, and no independent-sibling substitute. -/
theorem Forced.envelope_energy_root (T n g : ℕ → ℕ) (hT : 0<T 0) (s : ℕ)
    (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b : ℕ) (t : OccupiedParityTree (b+1)) (F : t.Forced)
    (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d) (incoming : ℤ) :
    (∑x : t.Labels T, if BinaryWindowLabels.allowed T A s (b+1) (F.labels T x) then
      (F.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0) ≤
      ((Fintype.card (F.InteriorLabels T):ℝ) * ((2^s:ℕ):ℝ)^(2*Fintype.card F.ExtraLeafEdge)) *
        ((2*((2^s:ℕ):ℝ)^3*B b) *
          binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b) := by
  apply (F.envelope_energy T n g hT s center globalShift
    (BinaryWindowLabels.allowed T A s (b+1)) d incoming).trans
  exact mul_le_mul_of_nonneg_left
    (binaryAnchorAverage_energy T n g s center globalShift A shift hplat B C hB hC b d hcap incoming)
    (by positivity)

end OccupiedParityTree
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
namespace OccupiedParityTree

/-- The actual full-tree leaf address of a bottom edge, including the edge's
own numeric label. -/
def Edge.bottomAddress (T : ℕ → ℕ) : {b : ℕ} → {t : OccupiedParityTree b} →
    (x : t.Labels T) → (e : t.Edge) → e.height=0 → WindowLeaf T b
  | _, .leaf, _, e, _ => e.elim
  | b+1, .node k children roles, x, Sum.inl i, he => by
      change b=0 at he
      subst b
      exact (x (Sum.inl i),(⟨0,by decide⟩ : Fin 1))
  | b+1, .node k children roles, x, Sum.inr z, he =>
      (x (Sum.inl z.1), Edge.bottomAddress T (x.child T z.1) z.2 he)

theorem Edge.bottomAddress_mem (T : ℕ → ℕ) {b : ℕ} {t : OccupiedParityTree b}
    (x : t.Labels T) (e : t.Edge) (he : e.height=0) :
    e.bottomAddress T x he ∈ t.labelledLeaves T x := by
  induction t with
  | leaf => exact e.elim
  | @node b k children roles ih =>
    cases e with
    | inl i =>
      change b=0 at he
      subst b
      apply Finset.mem_biUnion.mpr
      refine ⟨i,Finset.mem_univ i,?_⟩
      apply Finset.mem_image.mpr
      refine ⟨(⟨0,by decide⟩ : Fin 1),?_,rfl⟩
      have hz (u : OccupiedParityTree 0) (y : u.Labels T) :
          u.labelledLeaves T y = {(⟨0,by decide⟩ : Fin 1)} := by cases u; rfl
      rw [hz]
      exact Finset.mem_singleton_self _
    | inr z =>
      apply Finset.mem_biUnion.mpr
      refine ⟨z.1,Finset.mem_univ _,?_⟩
      exact Finset.mem_image.mpr ⟨z.2.bottomAddress T (x.child T z.1) he, ih z.1 _ _ he,rfl⟩

/-- Leaf constraints read from the real shape label address are exactly the
ones in the genuine complete-tree latent law. -/
theorem Edge.bottomIndicator_eq (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (t : OccupiedParityTree (b+1)) (x : t.Labels T)
    (e : t.Edge) (he : e.height=0)
    (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ) :
    sourceBottomIndicator T n g s center globalShift b bits incoming (e.bottomAddress T x he) =
      motifIndicator s ((x e).val-sourceTreeAnchors T n g center globalShift (b+1) bits incoming
        (e.parentPath T x)) := by
  induction b generalizing incoming with
  | zero =>
    cases t with
    | node k children roles =>
      cases e with
      | inl i =>
        change motifIndicator s _ = motifIndicator s _
        congr 1
        change ((x (Sum.inl i)).val:ℤ)-center 0+(∑i,(bitIndex (bits.1 i):ℤ))+incoming =
          ((x (Sum.inl i)).val:ℤ)-(center 0-(∑i,(bitIndex (bits.1 i):ℤ))-incoming)
        omega
      | inr z => have hh := z.2.height_lt; omega
  | succ b ih =>
    cases t with
    | node k children roles =>
      cases e with
      | inl i => change b+1=0 at he; omega
      | inr z =>
        change sourceBottomIndicator T n g s center globalShift b
          (bits.2.2 (x (Sum.inl z.1))) (globalShift (b+1) bits.2.1 (x (Sum.inl z.1)))
          (z.2.bottomAddress T (x.child T z.1) he) = motifIndicator s ((x.child T z.1 z.2).val-
          sourceTreeAnchors T n g center globalShift (b+1+1) bits incoming
            ((x (Sum.inl z.1)).val::z.2.parentPath T (x.child T z.1)))
        rw [sourceTreeAnchors_child T n g center globalShift (b+1) bits incoming
          (x (Sum.inl z.1)) (z.2.parentPath T (x.child T z.1))]
        exact ih _ _ _ he _ _

end OccupiedParityTree
end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Taking repeated constraints from a zero-one product can only enlarge it.
The map need not be injective. This keeps the real leaf addresses, including
coincident labels in the ambient enlarged summation. -/
theorem product_zero_one_pull_le {α β : Type*} [Fintype β]
    (S : Finset α) (f : α → ℝ) (hf : ∀a∈S,f a=0 ∨ f a=1)
    (g : β → α) (hg : ∀b,g b∈S) : (∏a∈S,f a)≤∏b,f (g b) := by
  rcases prod_zero_one S f hf with hz | ho
  · rw [hz]
    exact Finset.prod_nonneg (fun b _ => by rcases hf (g b) (hg b) with h|h <;> simp [h])
  · have h (b : β) : f (g b)=1 := by
      rcases hf (g b) (hg b) with h|h
      · have hz := Finset.prod_eq_zero (hg b) h
        rw [ho] at hz
        norm_num at hz
      · exact h
    rw [ho]
    simp only [h,Finset.prod_const_one,le_refl]

/-- Every actual role coefficient is bounded by its actual forced shape
and extra-leaf envelope before averaging over the single whole latent law. -/
theorem sourceRoleTerm_envelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleTerm T n g s center globalShift b bits incoming S a|≤
      F.envelope T n g s center globalShift (occupiedTermLabels T b S a) bits incoming := by
  let x := occupiedTermLabels T b S a
  let f := sourceBottomIndicator T n g s center globalShift b bits incoming
  let addr : F.ExtraLeafEdge → WindowLeaf T (b+1) :=
    fun e => e.val.val.bottomAddress T x e.property
  have hm (e : F.ExtraLeafEdge) : addr e∈S := by
    rw [←occupiedTermLabels_leaves T b S a]
    exact e.val.val.bottomAddress_mem T x e.property
  have he (e : F.ExtraLeafEdge) : f (addr e)=motifIndicator s ((x e.val.val).val-
      sourceTreeAnchors T n g center globalShift (b+1) bits incoming (e.val.val.parentPath T x)) :=
    e.val.val.bottomIndicator_eq T n g s center globalShift b _ x e.property bits incoming
  have hle := product_zero_one_pull_le S f (fun v hv =>
    sourceBottomIndicator_zero_one T n g s center globalShift b bits incoming v) addr hm
  simp_rw [he] at hle
  apply le_mul_of_zero_one
    (binaryAnchorKernel_zero_one T n g s center globalShift _ _ bits incoming)
    (prod_zero_one Finset.univ _ (fun e _ => by unfold motifIndicator; split_ifs <;> simp))
  · simpa only [occupiedTermLabels_forced] using
      sourceRoleTerm_forced_anchor T n g s center globalShift b bits incoming S a F
  · exact (sourceRoleTerm_all_leaf_constraints T n g s center globalShift b bits incoming S a).trans hle

/-- The averaged coefficient uses one exact metadata fiber. No fit event,
plateau event or leaf-emission observation is conditioned on here. -/
theorem sourceRoleAverage_envelope (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤
      F.averagedEnvelope T n g s center globalShift (occupiedTermLabels T b S a) d incoming := by
  apply ((windowPosteriorLaw T n g (b+1) d).abs_expect_le _).trans
  exact FiniteLaw.expect_mono _ (fun bits =>
    sourceRoleTerm_envelope T n g s center globalShift b bits incoming S a F)

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
open OccupiedParityTree

theorem occupiedWindowTerm_leafCount (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) :
    (occupiedWindowTerm T b S a).leafCount=S.card := by
  rw [←occupiedWindowTerm_eq T 0 (fun _ => 0) b [] S a]
  exact occupiedWindowShape_leafCount T 0 (fun _ => 0) b [] S _

theorem occupiedWindowTerm_occupied (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S) (hS : S.Nonempty) :
    (occupiedWindowTerm T b S a).occupied := by
  rw [←occupiedWindowTerm_eq T 0 (fun _ => 0) b [] S a]
  exact occupiedWindowShape_occupied T 0 (fun _ => 0) b [] S hS _

/-- Only the unlabeled ordered role shape is selected here; no child label
or hidden orientation enters the forced choice. -/
abbrev DegreeForcedShape (b r : ℕ) :=
  {t : OccupiedParityTree b // t.occupied ∧ t.leafCount=r ∧ Nonempty t.Forced}

instance degreeForcedShapeFinite (b r : ℕ) : Finite (DegreeForcedShape b r) := by
  let := finite_bounded_occupied_shapes b r
  exact Finite.of_injective
    (fun t : DegreeForcedShape b r =>
      (⟨t.val,t.property.1,t.property.2.1.le⟩ : {t : OccupiedParityTree b // t.occupied ∧ t.leafCount≤r}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun q : {t : OccupiedParityTree b // t.occupied ∧ t.leafCount≤r} => q.val) h))

noncomputable instance degreeForcedShapeFintype (b r : ℕ) : Fintype (DegreeForcedShape b r) :=
  Fintype.ofFinite _

def DegreeForcedShape.forced {b r : ℕ} (t : DegreeForcedShape b r) : t.val.Forced :=
  Classical.choice t.property.2.2

theorem card_degreeForcedShape_le (b r : ℕ) :
    Fintype.card (DegreeForcedShape b r) ≤ shapeRoleConstant r b := by
  let f : DegreeForcedShape b r → FiniteRoleShape r b := fun t =>
    Classical.choose (exists_finiteRoleShape t.val r t.property.1 t.property.2.1.le)
  apply Fintype.card_le_of_injective f
  intro t u he
  apply Subtype.ext
  have ht := Classical.choose_spec (exists_finiteRoleShape t.val r t.property.1 t.property.2.1.le)
  have hu := Classical.choose_spec (exists_finiteRoleShape u.val r u.property.1 u.property.2.1.le)
  exact ht.symm.trans ((congrArg (FiniteRoleShape.toTree r b) he).trans hu)

abbrev SourceRoleIndex (T : ℕ → ℕ) (b : ℕ) :=
  (S : Finset (WindowLeaf T (b+1))) × OccupiedWindowChoice T b S

abbrev DegreeForcedRole (T : ℕ → ℕ) (b r : ℕ) :=
  {w : SourceRoleIndex T b // w.1.card=r ∧ Nonempty (occupiedWindowTerm T b w.1 w.2).Forced}

def DegreeForcedRole.shape (T : ℕ → ℕ) (b r : ℕ) (w : DegreeForcedRole T b r) :
    DegreeForcedShape (b+1) r := by
  refine ⟨occupiedWindowTerm T b w.val.1 w.val.2,?_,?_,w.property.2⟩
  · apply occupiedWindowTerm_occupied
    apply Finset.card_pos.mp
    obtain ⟨F⟩ := w.property.2
    have hh := F.leaf_lower
    rw [occupiedWindowTerm_leafCount] at hh
    exact (Nat.pow_pos (by decide : (0:ℕ)<2)).trans_le hh
  · exact (occupiedWindowTerm_leafCount T b w.val.1 w.val.2).trans w.property.1

def DegreeForcedRole.encoding (T : ℕ → ℕ) (b r : ℕ) (w : DegreeForcedRole T b r) :
    (t : DegreeForcedShape (b+1) r) × t.val.Labels T :=
  ⟨w.shape T b r,occupiedTermLabels T b w.val.1 w.val.2⟩

theorem DegreeForcedRole.encoding_injective (T : ℕ → ℕ) (b r : ℕ) :
    Function.Injective (DegreeForcedRole.encoding T b r) := by
  intro w v he
  apply Subtype.ext
  apply occupiedTermEncoding_injective T b
  exact congrArg (fun z : (t : DegreeForcedShape (b+1) r) × t.val.Labels T =>
    (⟨z.1.val,z.2⟩ : (t : OccupiedParityTree (b+1)) × t.Labels T)) he

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw
open OccupiedParityTree

/-- A degree-r sum over the genuine pairs (selected leaves, roles),
restricted only by deterministic allowed forced labels. -/
def degreeForcedRoleEnergy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) : ℝ :=
  ∑w : DegreeForcedRole T b r,
    if BinaryWindowLabels.allowed T A s (b+1)
      ((w.shape T b r).forced.labels T (occupiedTermLabels T b w.val.1 w.val.2)) then
      (sourceRoleAverage T n g s center globalShift b d incoming w.val.1 w.val.2)^2 else 0

/-- The actual coefficient indices inject into shape+numeric-labels. Thus
summing the enlarged envelope really bounds the original coefficient sum,
with no identification of different selected monomials. -/
theorem degreeForcedRoleEnergy_le_envelopes (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    degreeForcedRoleEnergy T n g s center globalShift A b r d incoming ≤
      ∑t : DegreeForcedShape (b+1) r, ∑x : t.val.Labels T,
        if BinaryWindowLabels.allowed T A s (b+1) (t.forced.labels T x) then
          (t.forced.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0 := by
  let f := fun z : (t : DegreeForcedShape (b+1) r) × t.val.Labels T =>
    if BinaryWindowLabels.allowed T A s (b+1) (z.1.forced.labels T z.2) then
      (z.1.forced.averagedEnvelope T n g s center globalShift z.2 d incoming)^2 else 0
  have hf : ∀z,0≤f z := by intro z; dsimp [f]; split_ifs <;> positivity
  calc
    _ ≤ ∑w : DegreeForcedRole T b r,f (w.encoding T b r) := by
      apply Finset.sum_le_sum
      intro w hw
      dsimp only [f,DegreeForcedRole.encoding]
      by_cases h : BinaryWindowLabels.allowed T A s (b+1)
          ((w.shape T b r).forced.labels T (occupiedTermLabels T b w.val.1 w.val.2))
      · simp only [ite_eq_left h]
        have hh := sourceRoleAverage_envelope T n g s center globalShift b d incoming
          w.val.1 w.val.2 (w.shape T b r).forced
        rw [←sq_abs (sourceRoleAverage T n g s center globalShift b d incoming w.val.1 w.val.2)]
        exact (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
      · simp only [ite_eq_right h,le_refl]
    _ ≤ ∑z,f z := by
      simpa only [ite_true] using sum_injective_profile_le
        (DegreeForcedRole.encoding T b r) (DegreeForcedRole.encoding_injective T b r)
        (fun _ => True) (fun _ => trivial) f hf
    _ = _ := Fintype.sum_sigma _

/-- Uniform arithmetic interior-label budget of a degree-r depth-(b+1)
shape. This includes no factor for a bottom label. -/
def interiorLabelBudget (T : ℕ → ℕ) (b r : ℕ) : ℝ :=
  ((∏j : Fin (b+1),if j.val=0 then 1 else T j.val : ℕ):ℝ)^(r-2^(b+1))

theorem degreeForcedRoleEnergy_bound (T n g : ℕ → ℕ) (hT : ∀j,0<T j) (s : ℕ)
    (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (shift : ℕ → ℤ)
    (hplat : HasGlobalPlateau T g A shift globalShift)
    (B C : ℕ → ℝ) (hB : ∀b,0≤B b) (hC : ∀b,0≤C b)
    (b r : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1))
    (hcap : MetadataBinomialCaps T n g B C (b+1) d) (incoming : ℤ) :
    degreeForcedRoleEnergy T n g s center globalShift A b r d incoming ≤
      (shapeRoleConstant r (b+1):ℝ) * interiorLabelBudget T b r *
        ((2^s:ℕ):ℝ)^(2*(r-2^(b+1))) *
        ((2*((2^s:ℕ):ℝ)^3*B b) *
          binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b) := by
  let K := interiorLabelBudget T b r * ((2^s:ℕ):ℝ)^(2*(r-2^(b+1))) *
    ((2*((2^s:ℕ):ℝ)^3*B b) * binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b)
  have hbud : 0≤binaryTreeBudget (fun j => 4*((2^s:ℕ):ℝ)^6*C (j+1)*B j) b := by
    exact binaryTreeBudget_nonneg _ (fun j =>
      mul_nonneg (mul_nonneg (by positivity) (hC (j+1))) (hB j)) b
  have hb := hB b
  have hK : 0≤K := by dsimp [K,interiorLabelBudget]; positivity
  calc
    _ ≤ ∑t : DegreeForcedShape (b+1) r, ∑x : t.val.Labels T,
        if BinaryWindowLabels.allowed T A s (b+1) (t.forced.labels T x) then
          (t.forced.averagedEnvelope T n g s center globalShift x d incoming)^2 else 0 :=
      degreeForcedRoleEnergy_le_envelopes T n g s center globalShift A b r d incoming
    _ ≤ ∑_t : DegreeForcedShape (b+1) r,K := by
      apply Finset.sum_le_sum
      intro t ht
      apply (t.forced.envelope_energy_root T n g (hT 0) s center globalShift A shift hplat
        B C hB hC b t.val d hcap incoming).trans
      have hi := t.forced.card_interiorLabels_le T hT t.property.1
      rw [t.property.2.1] at hi
      have hi' : (Fintype.card (t.forced.InteriorLabels T):ℝ) ≤ interiorLabelBudget T b r := by
        dsimp [interiorLabelBudget]
        exact_mod_cast hi
      rw [t.forced.card_extraLeafEdge,t.property.2.1]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi' (by positivity)) (by positivity)
    _ = (Fintype.card (DegreeForcedShape (b+1) r):ℝ)*K := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ (shapeRoleConstant r (b+1):ℝ)*K := by
      apply mul_le_mul_of_nonneg_right _ hK
      exact_mod_cast card_degreeForcedShape_le (b+1) r
    _ = _ := by dsimp [K]; ring

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical

/-- Total role multiplicity for one actual selected monomial. Every level
has at most the number of selected leaves; no ambient-label factor occurs. -/
theorem occupiedWindowChoice_card_le (T : ℕ → ℕ) (b : ℕ)
    (S : Finset (WindowLeaf T (b+1))) :
    Fintype.card (OccupiedWindowChoice T b S) ≤ 3^((b+1)*S.card) := by
  induction b with
  | zero =>
    change Fintype.card (Fin S.card → Fin 3) ≤ _
    simp
  | succ b ih =>
    change Fintype.card (((i : Fin (selectedChildren S).card) →
      OccupiedWindowChoice T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)) ×
      (Fin (selectedChildren S).card → Fin 3)) ≤ _
    rw [Fintype.card_prod,Fintype.card_pi,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin]
    have hprod := Finset.prod_le_prod (s:=Finset.univ) (fun i _ =>
      ih (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val))
    have hs : (∑i : Fin (selectedChildren S).card,
        (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val).card)=S.card :=
      (selected_sum_index (selectedChildren S) (fun h => (selectedChildLeaves S h).card)).trans
        (selected_children_card S)
    have hc : (selectedChildren S).card≤S.card := Finset.card_image_le
    calc
      _ ≤ (∏i : Fin (selectedChildren S).card,
          3^((b+1)*(selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val).card)) *
          3^(selectedChildren S).card := Nat.mul_le_mul_right _ hprod
      _ = 3^((b+1)*S.card+(selectedChildren S).card) := by
        rw [Finset.prod_pow_eq_pow_sum,←Finset.mul_sum,hs,←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by simp only [Nat.add_mul,Nat.one_mul]; omega)

abbrev DegreeLeafSubset (T : ℕ → ℕ) (b r : ℕ) :=
  {S : Finset (WindowLeaf T (b+1)) // S.card=r}

theorem degreeLeafSubset_card (T : ℕ → ℕ) (b r : ℕ) :
    Fintype.card (DegreeLeafSubset T b r)=(Fintype.card (WindowLeaf T (b+1))).choose r := by
  have h := Finset.card_powersetCard r (Finset.univ : Finset (WindowLeaf T (b+1)))
  have he : (Finset.univ.powersetCard r : Finset (Finset (WindowLeaf T (b+1))))=(Finset.univ.filter (fun S : Finset (WindowLeaf T (b+1)) => S.card=r)) := by
    ext S
    simp only [Finset.mem_powersetCard,Finset.subset_univ,true_and,Finset.mem_filter,Finset.mem_univ]
  rw [he,Finset.card_univ] at h
  rw [Fintype.card_subtype]
  exact h

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- All actual motif support lies in the chosen central interval at every
vertex of the full window tree. This is a predicate of the complete bits,
not an event on which any posterior law is conditioned. -/
def SourceCentral (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) :
    (b : ℕ) → WindowAssignments T n g Bool b → ℤ → Prop
  | 0, _, _ => True
  | b+1, bits, incoming =>
      (∀h : Fin (T b), motifIndicator s ((h.val:ℤ)-center b+
        (∑i,(bitIndex (bits.1 i):ℤ))+incoming)≠0 → h∈A b) ∧
      ∀h, SourceCentral T n g s center globalShift A b (bits.2.2 h) (globalShift b bits.2.1 h)

def BinaryWindowLabels.central (T : ℕ → ℕ) (A : (b : ℕ) → Finset (Fin (T b))) :
    (b : ℕ) → BinaryWindowLabels T b → Prop
  | 0, _ => True
  | b+1, p => p.1∈A b ∧ p.2.1∈A b ∧ central T A b p.2.2.1 ∧ central T A b p.2.2.2

theorem BinaryWindowLabels.allowed_of_central (T : ℕ → ℕ)
    (A : (b : ℕ) → Finset (Fin (T b))) (s b : ℕ) (p : BinaryWindowLabels T b)
    (hc : central T A b p) (hd : distinct T b p) (hs : close T s b p) :
    allowed T A s b p := by
  induction b with
  | zero => trivial
  | succ b ih =>
    exact ⟨⟨hc.1,hc.2.1,hd.1,by simpa only [abs_sub_comm] using hs.1⟩,
      ih _ hc.2.2.1 hd.2.1 hs.2.1,ih _ hc.2.2.2 hd.2.2 hs.2.2⟩

theorem sourceRoleTerm_forced_central (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b)))
    (b : ℕ) (bits : WindowAssignments T n g Bool (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced)
    (hc : SourceCentral T n g s center globalShift A (b+1) bits incoming)
    (hz : sourceRoleTerm T n g s center globalShift b bits incoming S a≠0) :
    BinaryWindowLabels.central T A (b+1) (forcedWindowLabels T b S a F) := by
  induction b generalizing incoming with
  | zero =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_zero] at hz
      change (S.equivFin.symm i).val.1 ∈ A 0 ∧ (S.equivFin.symm j).val.1 ∈ A 0 ∧ True ∧ True
      refine ⟨hc.1 _ ?_,hc.1 _ ?_,trivial,trivial⟩
      · convert nonzero_of_abs_le hz (occupiedRootWeight_bottom_anchor T s S a (center 0-(∑k,(bitIndex (bits.1 k):ℤ))-incoming) i) using 1
        congr 1; ring
      · convert nonzero_of_abs_le hz (occupiedRootWeight_bottom_anchor T s S a (center 0-(∑k,(bitIndex (bits.1 k):ℤ))-incoming) j) using 1
        congr 1; ring
  | succ b ih =>
    cases F with
    | node i j hne hi hj left right =>
      rw [sourceRoleTerm_succ] at hz
      have hm := mul_ne_zero_iff.mp hz
      have hp := Finset.prod_ne_zero_iff.mp hm.2
      change ((selectedChildren S).equivFin.symm i).val ∈ A (b+1) ∧
        ((selectedChildren S).equivFin.symm j).val ∈ A (b+1) ∧
        BinaryWindowLabels.central T A (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm i).val)
            (a.1 i) left) ∧
        BinaryWindowLabels.central T A (b+1)
          (forcedWindowLabels T b (selectedChildLeaves S ((selectedChildren S).equivFin.symm j).val)
            (a.1 j) right)
      refine ⟨hc.1 _ ?_,hc.1 _ ?_,
        ih _ _ _ _ left (hc.2 _) (hp i (Finset.mem_univ i)),
        ih _ _ _ _ right (hc.2 _) (hp j (Finset.mem_univ j))⟩
      · convert nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ i hi) using 1
        congr 1; ring
      · convert nonzero_of_abs_le hm.1 (occupiedRootWeight_internal_anchor T s b S a _ j hj) using 1
        congr 1; ring

/-- The discarded noncentral role contributions are bounded by the actual
conditional probability of a failed full-tree layout. Typical metadata may
bound this mass; the averaging distribution itself remains unconditional. -/
def sourceNoncentralMass (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) : ℝ :=
  (windowPosteriorLaw T n g b d).expect
    (fun bits => if SourceCentral T n g s center globalShift A b bits incoming then 0 else 1)

theorem sourceNoncentralMass_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b : ℕ)
    (d : WindowAssignments T n g (Option Bool) b) (incoming : ℤ) :
    0 ≤ sourceNoncentralMass T n g s center globalShift A b d incoming := by
  exact Finset.sum_nonneg (fun bits _ => mul_nonneg
    ((windowPosteriorLaw T n g b d).nonneg bits) (by dsimp only; split_ifs <;> norm_num))

theorem sourceRoleAverage_not_allowed (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b)))
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (a : OccupiedWindowChoice T b S)
    (F : (occupiedWindowTerm T b S a).Forced)
    (h : ¬BinaryWindowLabels.allowed T A s (b+1) (forcedWindowLabels T b S a F)) :
    |sourceRoleAverage T n g s center globalShift b d incoming S a|≤
      sourceNoncentralMass T n g s center globalShift A (b+1) d incoming := by
  apply ((windowPosteriorLaw T n g (b+1) d).abs_expect_le _).trans
  apply FiniteLaw.expect_mono
  intro bits
  by_cases hc : SourceCentral T n g s center globalShift A (b+1) bits incoming
  · rw [ite_eq_left hc]
    have hz : sourceRoleTerm T n g s center globalShift b bits incoming S a=0 := by
      by_contra hn
      exact h (BinaryWindowLabels.allowed_of_central T A s (b+1) _
        (sourceRoleTerm_forced_central T n g s center globalShift A b bits incoming S a F hc hn)
        (forcedWindowLabels_distinct T b S a F)
        (sourceRoleTerm_forced_close T n g s center globalShift b bits incoming S a F hn))
    rw [hz,abs_zero]
  · rw [ite_eq_right hc]
    exact occupiedWindowWeight_abs_le_one T s _ b [] S a

end TraceReconstruction


noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

/-- Extension by zero commutes with the finite subtype sum, including an
empty subtype and predicates depending on dependent role indices. -/
theorem sum_subtype_zero_extend {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p]
    (f : {x // p x} → ℝ) :
    (∑x, if h : p x then f ⟨x,h⟩ else 0) = ∑x,f x := by
  have h := Fintype.sum_subtype_add_sum_subtype p
    (fun x => if h : p x then f ⟨x,h⟩ else 0)
  calc
    _ = (∑x : {x // p x}, if h : p x.val then f ⟨x.val,h⟩ else 0) +
        ∑x : {x // ¬p x}, if h : p x.val then f ⟨x.val,h⟩ else 0 := h.symm
    _ = (∑x,f x)+0 := congrArg₂ (·+·)
      (Finset.sum_congr rfl (fun x _ => dite_eq_left x.property))
      (Finset.sum_eq_zero (fun x _ => dite_eq_right x.property))
    _ = _ := add_zero _

/-- The coefficient is defined directly from the two literal leaf-type
patterns under the common complete posterior bit tree. -/
def sourceCoefficient (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) : ℝ :=
  (windowPosteriorLaw T n g (b+1) d).expect (fun bits =>
    ∏v∈S,(1-sourceTreeLeafSign T n g s center globalShift (b+1) bits incoming 1 v)/2) -
  (windowPosteriorLaw T n g (b+1) d).expect (fun bits =>
    ∏v∈S,(1-sourceTreeLeafSign T n g s center globalShift (b+1) bits incoming (-1) v)/2)

theorem sourceCoefficient_expansion (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (b : ℕ) (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) :
    sourceCoefficient T n g s center globalShift b d incoming S =
      2*∑a : OccupiedWindowChoice T b S,
        if (occupiedWindowTerm T b S a).isOdd then
          sourceRoleAverage T n g s center globalShift b d incoming S a else 0 := by
  unfold sourceCoefficient
  simp_rw [sourceTreeLeafSign_eq]
  exact occupiedWindow_averaged_difference _ T s _ b [] S

def sourceGoodRoleSquare (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (w : SourceRoleIndex T b) : ℝ :=
  if h : w.1.card=r ∧ Nonempty (occupiedWindowTerm T b w.1 w.2).Forced then
    let u : DegreeForcedRole T b r := ⟨w,h⟩
    if BinaryWindowLabels.allowed T A s (b+1)
      ((u.shape T b r).forced.labels T (occupiedTermLabels T b w.1 w.2)) then
      (sourceRoleAverage T n g s center globalShift b d incoming w.1 w.2)^2 else 0
  else 0

theorem sourceGoodRoleSquare_nonneg (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (w : SourceRoleIndex T b) :
    0 ≤ sourceGoodRoleSquare T n g s center globalShift A b r d incoming w := by
  unfold sourceGoodRoleSquare
  split_ifs <;> positivity

theorem sourceGoodRoleSquare_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    (∑w : SourceRoleIndex T b, sourceGoodRoleSquare T n g s center globalShift A b r d incoming w)=
      degreeForcedRoleEnergy T n g s center globalShift A b r d incoming := by
  unfold sourceGoodRoleSquare degreeForcedRoleEnergy
  exact sum_subtype_zero_extend
    (fun w : SourceRoleIndex T b => w.1.card=r ∧ Nonempty (occupiedWindowTerm T b w.1 w.2).Forced)
    (fun w : DegreeForcedRole T b r => if BinaryWindowLabels.allowed T A s (b+1)
      ((w.shape T b r).forced.labels T (occupiedTermLabels T b w.val.1 w.val.2)) then
      (sourceRoleAverage T n g s center globalShift b d incoming w.val.1 w.val.2)^2 else 0)

/-- Every actual odd role term is either smoothed at an actual singleton,
discarded by the literal central-layout failure event, or retained in the
forced-tree sum. There is no unproved coefficient-bound assumption. -/
theorem sourceRoleSquare_split (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (hS : S.card=r) (a : OccupiedWindowChoice T b S)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d) :
    (if (occupiedWindowTerm T b S a).isOdd then
      sourceRoleAverage T n g s center globalShift b d incoming S a else 0)^2 ≤
      η^2+(sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2+
        sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩ := by
  have hg := sourceGoodRoleSquare_nonneg T n g s center globalShift A b r d incoming ⟨S,a⟩
  by_cases ho : (occupiedWindowTerm T b S a).isOdd
  swap
  · rw [ite_eq_right ho]; nlinarith [sq_nonneg η, sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  rw [ite_eq_left ho]
  by_cases hz : sourceRoleAverage T n g s center globalShift b d incoming S a=0
  · rw [hz]; nlinarith [sq_nonneg η, sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  by_cases hn : (occupiedWindowTerm T b S a).noSingleton
  swap
  · have hs := sourceRoleAverage_singleton T n g s center globalShift b d incoming S a η hcap hn
    have hs2 := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hs)).mpr hs
    rw [sq_abs] at hs2
    nlinarith [sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  have hf := OccupiedParityTree.forced_nonempty (occupiedWindowTerm T b S a)
    (sourceRoleAverage_valid T n g s center globalShift b d incoming S a hz) hn ho
  let w : DegreeForcedRole T b r := ⟨⟨S,a⟩,hS,hf⟩
  let F : (occupiedWindowTerm T b S a).Forced := (w.shape T b r).forced
  change _ ≤ _+ (if h : S.card=r ∧ Nonempty (occupiedWindowTerm T b S a).Forced then _ else 0)
  rw [dite_eq_left ⟨hS,hf⟩]
  change _ ≤ _ + (if BinaryWindowLabels.allowed T A s (b+1)
    (F.labels T (occupiedTermLabels T b S a)) then _ else 0)
  rw [occupiedTermLabels_forced T b S a F]
  by_cases ha : BinaryWindowLabels.allowed T A s (b+1) (forcedWindowLabels T b S a F)
  · rw [ite_eq_left ha]; nlinarith [sq_nonneg η,
      sq_nonneg (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)]
  · rw [ite_eq_right ha]
    have hs := sourceRoleAverage_not_allowed T n g s center globalShift A b d incoming S a F ha
    have hs2 := (sq_le_sq₀ (abs_nonneg _) (sourceNoncentralMass_nonneg T n g s center globalShift A (b+1) d incoming)).mpr hs
    rw [sq_abs] at hs2
    nlinarith [sq_nonneg η]

end TraceReconstruction

noncomputable section
namespace TraceReconstruction
open scoped Classical
open FiniteLaw

theorem sourceGoodRoleSquare_degree_sum (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ) :
    (∑S : DegreeLeafSubset T b r, ∑a : OccupiedWindowChoice T b S.val,
      sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S.val,a⟩)=
      degreeForcedRoleEnergy T n g s center globalShift A b r d incoming := by
  rw [←sourceGoodRoleSquare_sum,Fintype.sum_sigma]
  symm
  calc
    _ = ∑S : Finset (WindowLeaf T (b+1)), if h : S.card=r then
        ∑a : OccupiedWindowChoice T b S,
          sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : S.card=r
      · rw [dite_eq_left h]
      · simp [sourceGoodRoleSquare,h]
    _ = _ := sum_subtype_zero_extend
      (fun S : Finset (WindowLeaf T (b+1)) => S.card=r)
      (fun S : DegreeLeafSubset T b r => ∑a : OccupiedWindowChoice T b S.val,
        sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S.val,a⟩)

theorem sourceCoefficient_square_bound (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (S : Finset (WindowLeaf T (b+1))) (hS : S.card=r)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d) :
    (sourceCoefficient T n g s center globalShift b d incoming S)^2 ≤
      4*(3^((b+1)*r):ℕ)*
        ((3^((b+1)*r):ℕ)*(η^2+
          (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2)+
          ∑a : OccupiedWindowChoice T b S,
            sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩) := by
  let f : OccupiedWindowChoice T b S → ℝ := fun a =>
    if (occupiedWindowTerm T b S a).isOdd then
      sourceRoleAverage T n g s center globalShift b d incoming S a else 0
  let M : ℝ := (3^((b+1)*r):ℕ)
  let E : ℝ := η^2+(sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2
  let G := fun a => sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S,a⟩
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hcard : (Fintype.card (OccupiedWindowChoice T b S):ℝ) ≤ M := by
    dsimp only [M]
    exact_mod_cast (hS ▸ occupiedWindowChoice_card_le T b S)
  have hcs : (∑a,f a)^2 ≤ (Fintype.card (OccupiedWindowChoice T b S):ℝ)*∑a,(f a)^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ)) f
  have hs : (∑a,(f a)^2) ≤ M*E+∑a,G a := by
    calc
      _ ≤ ∑a : OccupiedWindowChoice T b S,(E+G a) :=
        Finset.sum_le_sum (fun a _ => sourceRoleSquare_split T n g s center globalShift A b r d incoming S hS a η hcap)
      _ = (Fintype.card (OccupiedWindowChoice T b S):ℝ)*E+∑a,G a := by simp [Finset.sum_add_distrib]
      _ ≤ M*E+∑a,G a := add_le_add (mul_le_mul_of_nonneg_right hcard hE) le_rfl
  calc
    _ = 4*(∑a,f a)^2 := by rw [sourceCoefficient_expansion]; dsimp only [f]; ring
    _ ≤ 4*((Fintype.card (OccupiedWindowChoice T b S):ℝ)*∑a,(f a)^2) := by linarith
    _ ≤ 4*(M*∑a,(f a)^2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num)
    _ ≤ 4*(M*(M*E+∑a,G a)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hs hM) (by norm_num)
    _ = _ := by dsimp only [M,E,G]; ring

/-- The full degree coefficient sum, including every selected monomial,
singletons, and off-center labels. This is the finite, unabsorbed version
of the manuscript's low-degree coefficient estimate. -/
theorem sourceCoefficient_degree_energy (T n g : ℕ → ℕ) (s : ℕ) (center : ℕ → ℤ)
    (globalShift : (b : ℕ) → (Fin (g b) → Bool) → Fin (T b) → ℤ)
    (A : (b : ℕ) → Finset (Fin (T b))) (b r : ℕ)
    (d : WindowAssignments T n g (Option Bool) (b+1)) (incoming : ℤ)
    (η : ℝ) (hcap : MetadataSmoothingCap T n g s η (b+1) d) :
    (∑S : DegreeLeafSubset T b r,
      (sourceCoefficient T n g s center globalShift b d incoming S.val)^2) ≤
      4*(3^((b+1)*r):ℕ)*
        (((Fintype.card (WindowLeaf T (b+1))).choose r:ℕ)*(3^((b+1)*r):ℕ)*
          (η^2+(sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2)+
          degreeForcedRoleEnergy T n g s center globalShift A b r d incoming) := by
  calc
    _ ≤ ∑S : DegreeLeafSubset T b r,
        4*(3^((b+1)*r):ℕ)*
          ((3^((b+1)*r):ℕ)*(η^2+
            (sourceNoncentralMass T n g s center globalShift A (b+1) d incoming)^2)+
            ∑a : OccupiedWindowChoice T b S.val,
              sourceGoodRoleSquare T n g s center globalShift A b r d incoming ⟨S.val,a⟩) :=
      Finset.sum_le_sum (fun S _ => sourceCoefficient_square_bound T n g s center globalShift A b r d incoming S.val S.property η hcap)
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,sourceGoodRoleSquare_degree_sum]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,degreeLeafSubset_card]
      ring

end TraceReconstruction

end
end
end
end
end
end
end
end
end
end

end OAI
