import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.BoundaryBands
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.BoundaryBand
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Unlike `Perm.toList`, this retains fixed-point boundary circles. -/
def orbitList (σ : Equiv.Perm α) (x : α) : List α :=
  if σ x=x then [x] else σ.toList x

@[simp] theorem mem_orbitList (σ : Equiv.Perm α) (x z : α) :
    z∈orbitList σ x ↔ σ.SameCycle x z := by
  unfold orbitList
  split_ifs with hx
  · simp only [List.mem_singleton]
    exact ⟨fun h => by subst z; exact .rfl,fun h => (h.eq_of_left hx).symm⟩
  · simp [Equiv.Perm.mem_toList_iff,Equiv.Perm.mem_support,hx]

@[simp] theorem orbitList_nodup (σ : Equiv.Perm α) (x : α) :
    (orbitList σ x).Nodup := by
  unfold orbitList
  split_ifs <;> simp [Equiv.Perm.nodup_toList]

@[simp] theorem orbitList_formPerm (σ : Equiv.Perm α) (x : α) :
    (orbitList σ x).formPerm=σ.cycleOf x := by
  unfold orbitList
  split_ifs with hx
  · simp [(Equiv.Perm.cycleOf_eq_one_iff σ).mpr hx]
  · exact Equiv.Perm.formPerm_toList σ x

theorem orbitList_head (σ : Equiv.Perm α) (x : α) :
    ∃ L,orbitList σ x=x::L := by
  unfold orbitList
  split_ifs with hx
  · exact ⟨[],rfl⟩
  · have hp := σ.length_toList_pos_of_mem_support x (Equiv.Perm.mem_support.mpr hx)
    have hh := σ.toList_getElem_zero x (Equiv.Perm.mem_support.mpr hx)
    cases he : σ.toList x with
    | nil => simp [he] at hp
    | cons a L =>
      have ha : a=x := by simpa [he] using hh
      subst a
      exact ⟨L,rfl⟩

/-- Every complete orbit is retained. The residual fixes EACH removed occurrence, not merely its
facet rank or its boundary-component count. -/
structure Exposure (σ : Equiv.Perm α) (x y : α) where
  left : List α
  right : List α
  rest : Equiv.Perm α
  oneCircle : Bool
  nodup : ((x::left)++(y::right)).Nodup
  before : σ=(if oneCircle then ((x::left)++(y::right)).formPerm
    else (x::left).formPerm*(y::right).formPerm)*rest
  fixes : ∀ z∈(x::left)++(y::right),rest z=z
  exhaust : ∀ z,z∈(x::left)++(y::right) ↔ σ.SameCycle x z ∨ σ.SameCycle y z
  one_iff : oneCircle=true ↔ σ.SameCycle x y

/-- Produce the canonical cycle exposure for ANY distinct pair of feet. -/
theorem exposure_exists (σ : Equiv.Perm α) (x y : α) (hxy : x≠y) :
    Nonempty (Exposure σ x y) := by
  obtain ⟨L,hL⟩ := orbitList_head σ x
  by_cases hc : σ.SameCycle x y
  · have hy : y∈L := by
      have hm := (mem_orbitList σ x y).mpr hc
      rw [hL,List.mem_cons] at hm
      exact hm.resolve_left (Ne.symm hxy)
    obtain ⟨A,B,hAB⟩ := List.mem_iff_append.mp hy
    have hwhole : orbitList σ x=(x::A)++(y::B) := by simp only [hL,hAB,List.cons_append]
    have hperm : ((x::A)++(y::B)).formPerm=σ.cycleOf x := by rw [←hwhole,orbitList_formPerm]
    refine ⟨⟨A,B,(σ.cycleOf x)⁻¹*σ,true,?_,?_,?_,?_,?_⟩⟩
    · rw [←hwhole]; exact orbitList_nodup σ x
    · change σ=((x::A)++(y::B)).formPerm*((σ.cycleOf x)⁻¹*σ)
      rw [hperm,mul_inv_cancel_left]
    · intro z hz
      have hz' := (mem_orbitList σ x z).mp (hwhole ▸ hz)
      change (σ.cycleOf x)⁻¹ (σ z)=z
      rw [← hz'.cycleOf_apply]
      exact (σ.cycleOf x).symm_apply_apply z
    · intro z
      rw [←hwhole,mem_orbitList]
      exact ⟨Or.inl,fun h => h.elim id hc.trans⟩
    · simp [hc]
  · obtain ⟨M,hM⟩ := orbitList_head σ y
    have hdis : (x::L).Disjoint (y::M) := by
      intro z hz hz'
      have h1 := (mem_orbitList σ x z).mp (hL ▸ hz)
      have h2 := (mem_orbitList σ y z).mp (hM ▸ hz')
      exact hc (h1.trans h2.symm)
    have hperm : (x::L).formPerm*(y::M).formPerm=σ.cycleOf x*σ.cycleOf y := by
      rw [←hL,←hM,orbitList_formPerm,orbitList_formPerm]
    refine ⟨⟨L,M,(σ.cycleOf x*σ.cycleOf y)⁻¹*σ,false,?_,?_,?_,?_,?_⟩⟩
    · exact List.nodup_append.mpr ⟨hL ▸ orbitList_nodup σ x,hM ▸ orbitList_nodup σ y,fun a ha b hb hab => by subst b; exact hdis ha hb⟩
    · simp [hperm,mul_assoc]
    · intro z hz
      change (σ.cycleOf x*σ.cycleOf y)⁻¹ (σ z)=z
      apply (σ.cycleOf x*σ.cycleOf y).injective
      rw [←Equiv.Perm.mul_apply,mul_inv_cancel,Equiv.Perm.one_apply]
      rcases List.mem_append.mp hz with hz|hz
      · have h1 := (mem_orbitList σ x z).mp (hL ▸ hz)
        have hn : ¬σ.SameCycle y z := fun h => hc (h1.trans h.symm)
        simp only [Equiv.Perm.mul_apply,Equiv.Perm.cycleOf_apply_of_not_sameCycle hn]
        exact h1.cycleOf_apply.symm
      · have h2 := (mem_orbitList σ y z).mp (hM ▸ hz)
        have hn : ¬σ.SameCycle x (σ z) := by
          intro h
          exact hc (h.trans ((Equiv.Perm.sameCycle_apply_right.mpr h2).symm))
        rw [Equiv.Perm.mul_apply,h2.cycleOf_apply,Equiv.Perm.cycleOf_apply_of_not_sameCycle hn]
    · intro z
      simp only [List.mem_append,←hL,←hM,mem_orbitList]
    · simp [hc]

omit [Fintype α] in
/-- Exact successor, including every untouched edge, for the produced exposure. -/
theorem Exposure.after {σ : Equiv.Perm α} {x y : α} (E : Exposure σ x y) :
    incomingSwitch σ x y=(if E.oneCircle then (x::E.left).formPerm*(y::E.right).formPerm
      else ((x::E.left)++(y::E.right)).formPerm)*E.rest := by
  calc
    _=incomingSwitch ((if E.oneCircle then ((x::E.left)++(y::E.right)).formPerm
      else (x::E.left).formPerm*(y::E.right).formPerm)*E.rest) x y :=
        congrArg (fun z => incomingSwitch z x y) E.before
    _=_ := by
      cases E.oneCircle
      · simp only [Bool.false_eq_true,↓reduceIte]
        exact join_cycles x y E.left E.right E.rest E.nodup
      · simp only [↓reduceIte]
        exact split_cycle x y E.left E.right E.rest E.nodup

/-- Agreement on every member of a nodup cyclic list identifies its whole orbit, including a
singleton. This excludes hidden fresh-parent or exterior germs. -/
theorem sameCycle_iff_list (σ : Equiv.Perm α) (L : List α) (hn : L.Nodup)
    (x : α) (hx : x∈L) (ha : ∀ z∈L,σ z=L.formPerm z) (z : α) :
    σ.SameCycle x z ↔ z∈L := by
  have hi (k : ℕ) : (σ^k) x=(L.formPerm^k) x ∧ (σ^k) x∈L := by
    induction k with
    | zero => simpa using (show x=x ∧ x∈L from ⟨rfl,hx⟩)
    | succ k ih =>
      rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply]
      rw [ha _ ih.2]
      exact ⟨congrArg L.formPerm ih.1,List.formPerm_apply_mem_of_mem ih.2⟩
  constructor
  · intro h
    obtain ⟨k,rfl⟩ := h.exists_nat_pow_eq
    exact (hi k).2
  · intro hz
    obtain ⟨k,hk⟩ := (hn.isCycleOn_formPerm.2 hx hz).exists_nat_pow_eq
    exact ⟨(k:ℤ),by simpa only [zpow_natCast,(hi k).1] using hk⟩

/-- The two lists produced in the split case are the COMPLETE new boundary circles, not a compatible
but nonexhaustive list of contacts. -/
theorem Exposure.split_exhaust {σ : Equiv.Perm α} {x y : α} (E : Exposure σ x y)
    (he : E.oneCircle=true) (z : α) :
    (incomingSwitch σ x y).SameCycle x z ↔ z∈x::E.left := by
  apply sameCycle_iff_list _ _ (List.nodup_append.mp E.nodup).1 x (by simp)
  intro a ha
  rw [E.after]
  simp only [he,↓reduceIte,Equiv.Perm.mul_apply]
  rw [E.fixes a (List.mem_append.mpr (.inl ha))]
  have hn : a∉y::E.right := by
    intro hb
    exact (List.nodup_append.mp E.nodup).2.2 a ha a hb rfl
  rw [List.formPerm_apply_of_notMem hn]

theorem Exposure.split_exhaust_right {σ : Equiv.Perm α} {x y : α} (E : Exposure σ x y)
    (he : E.oneCircle=true) (z : α) :
    (incomingSwitch σ x y).SameCycle y z ↔ z∈y::E.right := by
  apply sameCycle_iff_list _ _ (List.nodup_append.mp E.nodup).2.1 y (by simp)
  intro a ha
  rw [E.after]
  simp only [he,↓reduceIte,Equiv.Perm.mul_apply]
  rw [E.fixes a (List.mem_append.mpr (.inr ha))]
  have hm := List.formPerm_apply_mem_of_mem ha
  have hn : (y::E.right).formPerm a∉x::E.left := by
    intro hb
    exact (List.nodup_append.mp E.nodup).2.2 _ hb _ hm rfl
  rw [List.formPerm_apply_of_notMem hn]

/-- The joined cycle retains both old cycles in full, even when one was a single fixed side
occurrence. -/
theorem Exposure.join_exhaust {σ : Equiv.Perm α} {x y : α} (E : Exposure σ x y)
    (he : E.oneCircle=false) (z : α) :
    (incomingSwitch σ x y).SameCycle x z ↔ z∈(x::E.left)++(y::E.right) := by
  apply sameCycle_iff_list _ _ E.nodup x (by simp)
  intro a ha
  rw [E.after]
  simp only [he,Bool.false_eq_true,↓reduceIte,Equiv.Perm.mul_apply]
  rw [E.fixes a ha]


end IntegralCharacterVarieties.BoundaryBand

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence BoundaryBand
variable {F S V : Type} [Fintype S] {arity : S → ℕ} (D : Diagram F S V arity)

/-- The old boundary circle of an occurrence, read from the exhaustive boundarySide equivalence, not
inferred from its rank or its facet color. -/
def sideCircle (a : Side S arity) : D.BoundaryCircle :=
  ⟨(D.boundarySide.symm a).1,(D.boundarySide.symm a).2.1⟩

omit [Fintype S] in
theorem mem_boundarySides_iff (B : D.BoundaryCircle) (a : Side S arity) :
    a∈D.boundarySides B ↔ D.sideCircle a=B := by
  constructor
  · intro h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    unfold sideCircle
    rw [D.boundarySide.symm_apply_apply]
  · intro h
    obtain ⟨⟨f,b,i⟩,rfl⟩ := D.boundarySide.surjective a
    have hb : (⟨f,b⟩ : D.BoundaryCircle)=B := by
      unfold sideCircle at h
      rw [D.boundarySide.symm_apply_apply] at h
      exact h
    rw [←hb]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem boundary_sameCycle_iff (a b : Side S arity) :
    D.ports.vertexAssembly.corners.boundaryNext.SameCycle a b ↔
      D.sideCircle a=D.sideCircle b := by
  have hm : a∈D.boundarySides (D.sideCircle a) :=
    (D.mem_boundarySides_iff _ a).mpr rfl
  rw [sameCycle_iff_list _ _ (D.boundarySides_nodup (D.sideCircle a)) a hm
    (fun z hz => (D.boundarySides_agree (D.sideCircle a) z hz).symm) b,
    D.mem_boundarySides_iff]
  exact eq_comm

/-- Universal exposure used by every chronological band step of a whole-port move. Its branch is
decided by old occurrence circles, not colors. -/
def boundaryBandExposure (a b : Side S arity) (hab : a≠b) :
    Exposure D.ports.vertexAssembly.corners.boundaryNext a b :=
  Classical.choice (exposure_exists _ a b hab)

theorem boundaryBandExposure_one (a b : Side S arity) (hab : a≠b) :
    (D.boundaryBandExposure a b hab).oneCircle=true ↔ D.sideCircle a=D.sideCircle b :=
  (D.boundaryBandExposure a b hab).one_iff.trans (D.boundary_sameCycle_iff a b)

/-- The exact split/join successor and its produced exhaustive witness for ANY band feet of the
original finite Diagram. No genus choice is asserted. -/
theorem actual_boundaryBand_exposure (a b : Side S arity) (hab : a≠b) :
    let E := D.boundaryBandExposure a b hab
    incomingSwitch D.ports.vertexAssembly.corners.boundaryNext a b=
      (if E.oneCircle then (a::E.left).formPerm*(b::E.right).formPerm
        else ((a::E.left)++(b::E.right)).formPerm)*E.rest ∧
    (∀ z,z∈(a::E.left)++(b::E.right) ↔
      D.sideCircle z=D.sideCircle a ∨ D.sideCircle z=D.sideCircle b) := by
  refine ⟨(D.boundaryBandExposure a b hab).after,?_⟩
  intro z
  rw [(D.boundaryBandExposure a b hab).exhaust]
  rw [D.boundary_sameCycle_iff,D.boundary_sameCycle_iff]
  simp only [eq_comm]
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end

end OAI
