import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.PencilGeometry

namespace OAI

section
open scoped BigOperators Classical
open Finset

namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma rep_mem_line_iff (p z : Projectivization K V) : p.rep ∈ z.submodule ↔ p = z := by
  rw [Projectivization.submodule_eq,Submodule.mem_span_singleton]
  constructor
  · intro h
    exact p.mk_rep.symm.trans (((Projectivization.mk_eq_mk_iff' K _ _ _ _).mpr h).trans z.mk_rep)
  · intro h
    subst p
    exact ⟨1,one_smul K z.rep⟩

lemma quotient_rep_ne_zero (z p : Projectivization K V) (hp : p ≠ z) :
    z.submodule.mkQ p.rep ≠ 0 := by
  intro h
  have hm : p.rep ∈ LinearMap.ker z.submodule.mkQ := h
  rw [Submodule.ker_mkQ] at hm
  exact hp ((rep_mem_line_iff p z).mp hm)

def project (z : Projectivization K V) (p : {p : Projectivization K V // p ≠ z}) :
    Projectivization K (V ⧸ z.submodule) :=
  Projectivization.mk K (z.submodule.mkQ p.val.rep) (quotient_rep_ne_zero z p.val p.property)

lemma quotient_dimension [FiniteDimensional K V] (z : Projectivization K V) :
    Module.finrank K (V ⧸ z.submodule)+1 = Module.finrank K V := by
  simpa only [Projectivization.finrank_submodule] using z.submodule.finrank_quotient_add_finrank

lemma lift_covector_ne_zero (z : Projectivization K V)
    (t : Projectivization K (Module.Dual K V)) (ht : SharpLogRamsey.Incidence.Incident z t) :
    z.submodule.liftQ t.rep ((incident_iff_submodule z t).mp ht) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : Module.Dual K (V ⧸ z.submodule) => f.comp z.submodule.mkQ) h
  rw [Submodule.liftQ_mkQ] at hc
  exact t.rep_nonzero hc

def projectDual (z : Projectivization K V)
    (t : {t : Projectivization K (Module.Dual K V) // SharpLogRamsey.Incidence.Incident z t}) :
    Projectivization K (Module.Dual K (V ⧸ z.submodule)) :=
  Projectivization.mk K (z.submodule.liftQ t.val.rep
    ((incident_iff_submodule z t.val).mp t.property)) (lift_covector_ne_zero z t.val t.property)

lemma incident_mk_iff (v : V) (hv : v ≠ 0) (f : Module.Dual K V) (hf : f ≠ 0) :
    SharpLogRamsey.Incidence.Incident (Projectivization.mk K v hv) (Projectivization.mk K f hf) ↔ f v = 0 := by
  obtain ⟨a,ha⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  obtain ⟨b,hb⟩ := Projectivization.exists_smul_eq_mk_rep K f hf
  unfold SharpLogRamsey.Incidence.Incident
  rw [← ha,← hb]
  simp [Units.smul_def]

lemma project_incident_iff (z : Projectivization K V)
    (p : {p : Projectivization K V // p ≠ z})
    (t : {t : Projectivization K (Module.Dual K V) // SharpLogRamsey.Incidence.Incident z t}) :
    SharpLogRamsey.Incidence.Incident (project z p) (projectDual z t) ↔ SharpLogRamsey.Incidence.Incident p.val t.val := by
  rw [project,projectDual,incident_mk_iff]
  rfl

lemma projectDual_injective (z : Projectivization K V) : Function.Injective (projectDual z) := by
  intro t u h
  apply Subtype.ext
  have hh := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  obtain ⟨a,ha⟩ := hh
  rw [← t.val.mk_rep,← u.val.mk_rep,Projectivization.mk_eq_mk_iff']
  refine ⟨a,?_⟩
  ext v
  exact congrArg (fun f : Module.Dual K (V ⧸ z.submodule) => f (z.submodule.mkQ v)) ha

lemma collision_center_on_line (z : Projectivization K V)
    (p q : {p : Projectivization K V // p ≠ z})
    (hpq : p.val ≠ q.val) (h : project z p = project z q) :
    z.submodule ≤ p.val.submodule ⊔ q.val.submodule := by
  obtain ⟨a,ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp h
  have hker : p.val.rep-a • q.val.rep ∈ LinearMap.ker z.submodule.mkQ := by
    change z.submodule.mkQ (p.val.rep-a • q.val.rep) = 0
    rw [map_sub,map_smul,ha,sub_self]
  rw [Submodule.ker_mkQ] at hker
  have hne : p.val.rep-a • q.val.rep ≠ 0 := by
    intro he
    apply hpq
    rw [← p.val.mk_rep,← q.val.mk_rep,Projectivization.mk_eq_mk_iff']
    exact ⟨a,(sub_eq_zero.mp he).symm⟩
  let r := Projectivization.mk K (p.val.rep-a • q.val.rep) hne
  have hr : r = z := by
    apply Projectivization.submodule_injective
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
      exact hker
    · simp only [Projectivization.finrank_submodule]
  have hline : r.submodule ≤ p.val.submodule ⊔ q.val.submodule := by
    rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
    apply Submodule.sub_mem
    · apply (le_sup_left : p.val.submodule ≤ p.val.submodule ⊔ q.val.submodule)
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    · apply Submodule.smul_mem
      apply (le_sup_right : q.val.submodule ≤ p.val.submodule ⊔ q.val.submodule)
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
  exact (congrArg Projectivization.submodule hr).symm.le.trans hline

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.Projection
open SharpLogRamsey.Incidence Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma joining_line_finrank (p q : Projectivization K V) (hpq : p ≠ q) :
    Module.finrank K ↥(p.submodule ⊔ q.submodule : Submodule K V) = 2 := by
  have h := finrank_span_eq_card (Projectivization.linearIndependent_pair_iff_ne.mpr hpq)
  rw [Matrix.range_cons_cons_empty] at h
  rw [Submodule.span_insert] at h
  rw [Projectivization.submodule_eq,Projectivization.submodule_eq]
  exact h

lemma joining_line_card [Finite K] (p q : Projectivization K V) (hpq : p ≠ q) :
    Nat.card {z : Projectivization K V // z.submodule ≤ p.submodule ⊔ q.submodule} =
      Nat.card K+1 := by
  rw [← Nat.card_congr (projectiveSubmoduleEquiv (p.submodule ⊔ q.submodule))]
  exact Projectivization.card_of_finrank_two K _ (joining_line_finrank p q hpq)

def Collides (z p q : Projectivization K V) : Prop := ∃ (hp : p ≠ z) (hq : q ≠ z),
    project z ⟨p,hp⟩ = project z ⟨q,hq⟩

lemma collides_on_line (z p q : Projectivization K V) (hpq : p ≠ q) (h : Collides z p q) :
    z.submodule ≤ p.submodule ⊔ q.submodule := by
  obtain ⟨hp,hq,h⟩ := h
  exact collision_center_on_line z ⟨p,hp⟩ ⟨q,hq⟩ hpq h

lemma collision_centers_card [Finite K] [Fintype (Projectivization K V)]
    (p q : Projectivization K V) (hpq : p ≠ q) :
    (univ.filter (fun z => Collides z p q)).card ≤ Nat.card K+1 := by
  have hh := card_le_card (show univ.filter (fun z => Collides z p q) ⊆
      univ.filter (fun z => z.submodule ≤ p.submodule ⊔ q.submodule) from by
    intro z hz
    exact mem_filter.mpr ⟨mem_univ _,collides_on_line z p q hpq (mem_filter.mp hz).2⟩)
  have he := joining_line_card p q hpq
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at he
  exact hh.trans_eq he

def orderedCollisions (A : Finset (Projectivization K V)) (z : Projectivization K V) : ℕ :=
  (A.offDiag.filter (fun pq => Collides z pq.1 pq.2)).card

theorem collision_total [Finite K] [Fintype (Projectivization K V)]
    (A : Finset (Projectivization K V)) :
    ∑ z, orderedCollisions A z ≤ A.card*(A.card-1)*(Nat.card K+1) := by
  unfold orderedCollisions
  simp only [card_eq_sum_ones,sum_filter]
  rw [sum_comm]
  calc
    _ ≤ ∑ pq ∈ A.offDiag, (Nat.card K+1) := by
      apply sum_le_sum
      rintro ⟨p,q⟩ hpq
      have hh := collision_centers_card p q (mem_offDiag.mp hpq).2.2
      simpa only [card_eq_sum_ones,sum_filter] using hh
    _ = _ := by simp [offDiag_card,Nat.mul_sub_left_distrib]

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.FiniteImage
open Finset
open scoped Classical
noncomputable section
variable {α β : Type*}

theorem card_le_image_add_collisions (s : Finset α) (f : α → β) :
    s.card ≤ (s.image f).card+(s.offDiag.filter (fun ab => f ab.1 = f ab.2)).card := by
  let r : (s.image f) → α := fun b => (mem_image.mp b.property).choose
  have hr (b : s.image f) : r b ∈ s ∧ f (r b) = b.val :=
    (mem_image.mp b.property).choose_spec
  let D : Finset α := (s.image f).attach.image r
  let R := s \ D
  let g (a : α) : α := if h : a ∈ s then r ⟨f a,mem_image_of_mem f h⟩ else a
  have hg (a : α) (ha : a ∈ s) : g a ∈ D ∧ g a ∈ s ∧ f (g a) = f a := by
    dsimp only [g]
    rw [dite_eq_left ha]
    exact ⟨mem_image.mpr ⟨⟨f a,mem_image_of_mem f ha⟩,mem_attach _ _,rfl⟩,
      hr ⟨f a,mem_image_of_mem f ha⟩⟩
  have hR : R.card ≤ (s.offDiag.filter (fun ab => f ab.1 = f ab.2)).card := by
    apply card_le_card_of_injOn (fun a => (a,g a))
    · intro a ha
      obtain ⟨ha,hn⟩ := mem_sdiff.mp ha
      obtain ⟨hgd,hgs,hgf⟩ := hg a ha
      have hne : a ≠ g a := by
        intro he
        exact hn (he.symm ▸ hgd)
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨ha,hgs,hne⟩,hgf.symm⟩
    · intro a ha b hb he
      exact congrArg Prod.fst he
  have hD : D.card ≤ (s.image f).card := by
    exact (card_image_le).trans_eq card_attach
  calc
    s.card ≤ (D ∪ R).card := card_le_card (by
      intro a ha
      by_cases hd : a ∈ D
      · exact mem_union_left _ hd
      · exact mem_union_right _ (mem_sdiff.mpr ⟨ha,hd⟩))
    _ ≤ D.card+R.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add hD hR

end
end SharpLogRamsey.FiniteImage

namespace SharpLogRamsey.Projection
open Finset
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def projected (A : Finset (Projectivization K V)) (z : Projectivization K V) :
    Finset (Projectivization K (V ⧸ z.submodule)) :=
  (A.subtype (· ≠ z)).image (project z)

lemma noncentral_collision_le (A : Finset (Projectivization K V)) (z : Projectivization K V) :
    ((A.subtype (· ≠ z)).offDiag.filter (fun pq => project z pq.1 = project z pq.2)).card ≤
      orderedCollisions A z := by
  apply card_le_card_of_injOn (fun pq => (pq.1.val,pq.2.val))
  · intro pq hpq
    obtain ⟨hm,he⟩ := mem_filter.mp hpq
    obtain ⟨hp,hq,hne⟩ := mem_offDiag.mp hm
    apply mem_filter.mpr
    refine ⟨mem_offDiag.mpr ⟨mem_subtype.mp hp,mem_subtype.mp hq,?_⟩,?_⟩
    · exact fun h => hne (Subtype.ext h)
    · exact ⟨pq.1.property,pq.2.property,he⟩
  · intro p hp q hq he
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

theorem projection_loss (A : Finset (Projectivization K V)) (z : Projectivization K V) :
    A.card ≤ (projected A z).card+orderedCollisions A z+1 := by
  have h := FiniteImage.card_le_image_add_collisions (A.subtype (· ≠ z)) (project z)
  have hcol := noncentral_collision_le A z
  have ha : A.card ≤ (A.subtype (· ≠ z)).card+1 := by
    rw [card_subtype]
    have hcount := card_filter_add_card_filter_not (s := A) (p := fun p => p = z)
    have hle : (A.filter (fun p => p = z)).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      exact (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
    simpa only [not_not] using (show A.card ≤ (A.filter (fun p => ¬p = z)).card+1 by omega)
  dsimp only [projected]
  omega

end
end SharpLogRamsey.Projection
namespace SharpLogRamsey.FiniteImage
open Finset
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*}

def collisions (s : Finset α) (f : α → β) : ℕ :=
  (s.offDiag.filter (fun ab => f ab.1 = f ab.2)).card

lemma collisions_fiber_sum (s : Finset α) (f : α → β) :
    collisions s f = ∑ b ∈ s.image f,
      (s.filter (fun a => f a=b)).card*((s.filter (fun a => f a=b)).card-1) := by
  let E := s.offDiag.filter (fun ab => f ab.1 = f ab.2)
  have h : E.card = ∑ b ∈ s.image f, (E.filter (fun ab => f ab.1=b)).card :=
    card_eq_sum_card_fiberwise (f := fun ab => f ab.1) (fun ab hab =>
      mem_image_of_mem f (mem_offDiag.mp (mem_filter.mp hab).1).1)
  change E.card = _
  rw [h]
  apply sum_congr rfl
  intro b hb
  have he : E.filter (fun ab => f ab.1=b) = (s.filter (fun a => f a=b)).offDiag := by
    ext ab
    simp only [E,mem_filter,mem_offDiag]
    aesop
  rw [he,offDiag_card]
  simp [Nat.mul_sub_left_distrib]

lemma image_excess_sq (s : Finset α) (f : α → β) :
    ((s.card:ℝ)-(s.image f).card)^2 ≤ (s.image f).card*collisions s f := by
  let k (b : β) : ℝ := (s.filter (fun a => f a=b)).card
  have hk (b : β) (hb : b ∈ s.image f) : 1 ≤ k b := by
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    have : 0 < (s.filter (fun x => f x=f a)).card :=
      card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,rfl⟩⟩
    dsimp [k]
    exact_mod_cast this
  have hs : ∑ b ∈ s.image f, k b = s.card := by
    simp only [k,← Nat.cast_sum]
    congr 1
    exact (card_eq_sum_card_fiberwise (f := f) (fun a ha => mem_image_of_mem f ha)).symm
  have hc : ∑ b ∈ s.image f, k b*(k b-1) = (collisions s f:ℝ) := by
    rw [collisions_fiber_sum,Nat.cast_sum]
    apply sum_congr rfl
    intro b hb
    have hh : 1 ≤ (s.filter (fun a => f a=b)).card := by
      have hh := hk b hb
      dsimp only [k] at hh
      exact_mod_cast hh
    rw [Nat.cast_mul,Nat.cast_sub hh,Nat.cast_one]
  have hcs := sum_mul_sq_le_sq_mul_sq (s.image f) (fun _ => (1:ℝ)) (fun b => k b-1)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  have he : ∑ b ∈ s.image f, (k b-1)^2 ≤ (collisions s f:ℝ) := by
    rw [← hc]
    apply sum_le_sum
    intro b hb
    nlinarith [hk b hb]
  have ht : ∑ b ∈ s.image f, (k b-1) = (s.card:ℝ)-(s.image f).card := by
    rw [sum_sub_distrib,hs]
    simp
  rw [ht] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left he (by positivity))

theorem image_excess (s : Finset α) (f : α → β) :
    (s.card:ℝ) ≤ (s.image f).card+Real.sqrt ((s.image f).card*collisions s f) := by
  have h := image_excess_sq s f
  have hcard : ((s.image f).card:ℝ) ≤ s.card := by exact_mod_cast card_image_le (s:=s) (f:=f)
  have hh : (s.card:ℝ)-(s.image f).card ≤
      Real.sqrt ((s.image f).card*collisions s f) :=
    (Real.le_sqrt (sub_nonneg.mpr hcard) (by positivity)).mpr h
  linarith

lemma collisions_mono (s t : Finset α) (h : s ⊆ t) (f : α → β) :
    collisions s f ≤ collisions t f := by
  apply card_le_card
  intro ab hab
  obtain ⟨⟨ha,hb,hn⟩,he⟩ := by simpa only [mem_filter,mem_offDiag] using hab
  exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨h ha,h hb,hn⟩,he⟩

theorem cap_contraction (s : Finset α) (f : α → β) (W : Finset β) :
    ((s.filter (fun a => f a ∈ W)).card:ℝ) ≤
      W.card+Real.sqrt (W.card*collisions s f) := by
  let t := s.filter (fun a => f a ∈ W)
  have hi : t.image f ⊆ W := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    exact (mem_filter.mp ha).2
  have hic : ((t.image f).card:ℝ) ≤ W.card := by exact_mod_cast card_le_card hi
  have hc : (collisions t f:ℝ) ≤ collisions s f := by
    exact_mod_cast collisions_mono t s (filter_subset _ _) f
  exact (image_excess t f).trans (add_le_add hic
    (Real.sqrt_le_sqrt (mul_le_mul hic hc (by positivity) (by positivity))))

end
end SharpLogRamsey.FiniteImage
namespace SharpLogRamsey.Projection
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def liftCap (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) : Finset (Projectivization K V) :=
  (((A.subtype (· ≠ z)).filter (fun p => project z p ∈ W)).image Subtype.val)

lemma liftCap_card (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    (liftCap A z W).card = ((A.subtype (· ≠ z)).filter (fun p => project z p ∈ W)).card :=
  card_image_of_injective _ Subtype.val_injective

lemma mem_liftCap (A : Finset (Projectivization K V)) (z p : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    p ∈ liftCap A z W ↔ p ∈ A ∧ ∃ hp : p ≠ z, project z ⟨p,hp⟩ ∈ W := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact ⟨mem_subtype.mp (mem_filter.mp ha).1,a.property,(mem_filter.mp ha).2⟩
  · rintro ⟨hp,hn,hw⟩
    exact mem_image.mpr ⟨⟨p,hn⟩,mem_filter.mpr ⟨mem_subtype.mpr hp,hw⟩,rfl⟩

lemma liftCap_subset (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) : liftCap A z W ⊆ A :=
  fun _ hp => ((mem_liftCap _ _ _ _).mp hp).1

theorem liftCap_contraction (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    ((liftCap A z W).card:ℝ) ≤ W.card+Real.sqrt (W.card*orderedCollisions A z) := by
  rw [liftCap_card]
  apply (FiniteImage.cap_contraction (A.subtype (· ≠ z)) (project z) W).trans
  apply add_le_add le_rfl
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast noncentral_collision_le A z

lemma fiber_on_line (z p q : Projectivization K V) (hp : p ≠ z) (hq : q ≠ z)
    (he : project z ⟨p,hp⟩ = project z ⟨q,hq⟩) :
    q.submodule ≤ z.submodule ⊔ p.submodule := by
  by_cases hpq : p=q
  · subst q
    exact le_sup_right
  have hz := collision_center_on_line z ⟨p,hp⟩ ⟨q,hq⟩ hpq he
  have hsub : z.submodule ⊔ p.submodule ≤ p.submodule ⊔ q.submodule :=
    sup_le hz le_sup_left
  have hEq : z.submodule ⊔ p.submodule = p.submodule ⊔ q.submodule := by
    apply Submodule.eq_of_le_of_finrank_eq hsub
    rw [joining_line_finrank z p hp.symm,joining_line_finrank p q hpq]
  rw [hEq]
  exact le_sup_right

variable [Finite K] [Fintype (Projectivization K V)]

lemma project_fiber_card (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (b : Projectivization K (V ⧸ z.submodule)) :
    ((A.subtype (· ≠ z)).filter (fun p => project z p=b)).card ≤ Nat.card K := by
  let F := (A.subtype (· ≠ z)).filter (fun p => project z p=b)
  by_cases hf : F.Nonempty
  · obtain ⟨p,hp⟩ := hf
    let L : Finset (Projectivization K V) :=
      univ.filter (fun q => q.submodule ≤ z.submodule ⊔ p.val.submodule)
    have hL : L.card = Nat.card K+1 := by
      have h := joining_line_card z p.val p.property.symm
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
      exact h
    have hz : z ∈ L := mem_filter.mpr ⟨mem_univ _,le_sup_left⟩
    have hb : F.card ≤ (L.erase z).card := by
      apply card_le_card_of_injOn Subtype.val
      · intro q hq
        apply mem_erase.mpr
        refine ⟨q.property,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
        exact fiber_on_line z p.val q.val p.property q.property
          ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
      · intro x hx y hy he
        exact Subtype.ext he
    rw [card_erase_of_mem hz,hL] at hb
    simpa using hb
  · have : F=∅ := not_nonempty_iff_eq_empty.mp hf
    change F.card ≤ _
    simp [this]

theorem liftCap_initial (A : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    (liftCap A z W).card ≤ Nat.card K*W.card := by
  rw [liftCap_card]
  apply card_le_mul_card_image_of_maps_to (f := project z)
    (fun p hp => (mem_filter.mp hp).2) (Nat.card K)
  intro b hb
  apply le_trans _ (project_fiber_card A z b)
  apply card_le_card
  intro p hp
  obtain ⟨hp,he⟩ := mem_filter.mp hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1,he⟩

end
end SharpLogRamsey.Projection

end

end OAI
