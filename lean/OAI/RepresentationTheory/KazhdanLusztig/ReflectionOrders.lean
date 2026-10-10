import OAI.RepresentationTheory.KazhdanLusztig.DyerPaths

namespace OAI

/-!
Finite sweep algebra, wall orders and the full reflection-order path formula.
-/

section

namespace KLInvariance.SchedulePaths
open scoped BigOperators
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable (source target : E → V) [Semiring R]

theorem dispatch_append (T : R) (v : V → R) (p q : List E) :
    dispatch source target T v (p ++ q) =
      dispatch source target T (dispatch source target T v q) p := by
  induction p with
  | nil => rfl
  | cons e p ih => simp only [List.cons_append,dispatch,ih]

theorem dispatch_add (T : R) (v w : V → R) (p : List E) :
    dispatch source target T (v+w) p =
      dispatch source target T v p + dispatch source target T w p := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step,Pi.add_apply]
    split_ifs <;> simp [mul_add,add_assoc,add_left_comm,add_comm]

theorem dispatch_mul_right (T c : R) (v : V → R) (p : List E) :
    dispatch source target T (fun x => v x*c) p =
      fun x => dispatch source target T v p x*c := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp only [step]
    split_ifs <;> simp [add_mul,mul_assoc]

theorem dispatch_zero (T : R) (p : List E) : dispatch source target T (0 : V → R) p = 0 := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    simp only [dispatch,ih]
    funext x
    simp [step]

theorem dispatch_sum {A : Type*} (T : R) (F : Finset A) (v : A → V → R) (p : List E) :
    dispatch source target T (∑ a ∈ F, v a) p =
      ∑ a ∈ F, dispatch source target T (v a) p := by
  induction F using Finset.induction_on with
  | empty => simp [dispatch_zero]
  | @insert a F ha ih => simp only [Finset.sum_insert ha,dispatch_add,ih]

theorem dispatch_eq_sum_entries [Fintype V] (T : R) (v : V → R) (p : List E) (x : V) :
    dispatch source target T v p x =
      ∑ y, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  have hv : v = ∑ y, (fun z => (if z=y then 1 else 0)*v y) := by
    funext z
    simp [Finset.sum_apply]
  conv_lhs => rw [hv]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

theorem dispatch_eq_of_entries [Fintype V] (T : R) (p q : List E)
    (h : ∀ x y, dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x) (v : V → R) :
    dispatch source target T v p = dispatch source target T v q := by
  funext x
  rw [dispatch_eq_sum_entries source target T v p x,
    dispatch_eq_sum_entries source target T v q x]
  exact Finset.sum_congr rfl (fun y _ => congrArg (fun a => a*v y) (h x y))

/-- A finite lower region is closed under every target occurring in its
edge schedule, so values outside that region never enter its product. -/
theorem dispatch_congr_on (T : R) (S : Set V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ S) (v w : V → R)
    (hvw : ∀ x ∈ S, v x=w x) :
    ∀ x ∈ S, dispatch source target T v p x = dispatch source target T w p x := by
  induction p with
  | nil => exact hvw
  | cons e p ih =>
    have htail := ih (fun f hf => htarget f (List.mem_cons_of_mem _ hf))
    intro x hx
    simp only [dispatch,step,htail x hx,htail (target e) (htarget e List.mem_cons_self)]

theorem dispatch_eq_finite_entries (T : R) (F : Finset V) (p : List E)
    (htarget : ∀ e ∈ p, target e ∈ F) (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x =
      ∑ y ∈ F, dispatch source target T (fun z => if z=y then 1 else 0) p x * v y := by
  let w : V → R := ∑ y ∈ F, (fun z => (if z=y then 1 else 0)*v y)
  have hvw : ∀ z ∈ (F : Set V), v z=w z := by
    intro z hz
    simp [w,Finset.sum_apply,show z ∈ F from hz]
  rw [dispatch_congr_on source target T (F : Set V) p htarget v w hvw x hx]
  dsimp only [w]
  rw [dispatch_sum]
  simp only [Finset.sum_apply,dispatch_mul_right]

theorem dispatch_eq_of_entries_on (T : R) (F : Finset V) (p q : List E)
    (hp : ∀ e ∈ p, target e ∈ F) (hq : ∀ e ∈ q, target e ∈ F)
    (h : ∀ x ∈ F, ∀ y ∈ F,
      dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x)
    (v : V → R) (x : V) (hx : x ∈ F) :
    dispatch source target T v p x = dispatch source target T v q x := by
  rw [dispatch_eq_finite_entries source target T F p hp v x hx,
    dispatch_eq_finite_entries source target T F q hq v x hx]
  exact Finset.sum_congr rfl (fun y hy => congrArg (fun a => a*v y) (h x hx y hy))

variable {Λ : Type*} [LinearOrder Λ]

/-- A genuine path in a sorted schedule is determined by its edge set and
strict label order. Arbitrary permutations of repeated reflection labels
therefore have no effect. -/
theorem subpaths_eq_of_sorted (label : E → Λ)
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (p q : List E)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    subpaths source target p x y = subpaths source target q x y := by
  ext s
  simp only [mem_subpaths]
  constructor
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hp.sublist hs)) hq
    exact fun e he => (hmem e).mp (hs.subset he)
  · rintro ⟨hs,hpath⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset label
      (decreasing_of_schedule_path source target label hties hpath (hq.sublist hs)) hp
    exact fun e he => (hmem e).mpr (hs.subset he)

theorem dispatch_eq_of_sorted [Fintype V] (T : R) (label : E → Λ)
    (hties : ∀ e f, label e = label f → target e ≠ source f)
    (p q : List E) (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (v : V → R) :
    dispatch source target T v p = dispatch source target T v q := by
  apply dispatch_eq_of_entries
  intro x y
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source target T q hqnd,
    subpaths_eq_of_sorted source target label hties p q hp hq hmem x y]

/-- Replacing each block by an equal actual operator replaces the product. -/
theorem dispatch_flatMap_eq {A : Type*} (T : R) (blocks : List A) (p q : A → List E)
    (h : ∀ a ∈ blocks, ∀ v, dispatch source target T v (p a) =
      dispatch source target T v (q a)) (v : V → R) :
    dispatch source target T v (blocks.flatMap p) =
      dispatch source target T v (blocks.flatMap q) := by
  induction blocks with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons,dispatch_append]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb)),h a List.mem_cons_self]


variable {V' E' : Type*} (source' target' : E' → V')

theorem IsPath.map_iff (j : V' → V) (hj : Function.Injective j) (J : E' → E)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e)) {x y : V'} {p : List E'} :
    IsPath source target (j x) (j y) (p.map J) ↔ IsPath source' target' x y p := by
  induction p generalizing x with
  | nil => exact hj.eq_iff
  | cons e p ih =>
    change (source (J e)=j x ∧ IsPath source target (target (J e)) (j y) (p.map J)) ↔ _
    rw [hs,ht,ih,hj.eq_iff]
    rfl

theorem exists_list_lift (J : E' → E) (p : List E)
    (h : ∀ e ∈ p, ∃ e', J e'=e) : ∃ p' : List E', p'.map J=p := by
  induction p with
  | nil => exact ⟨[],rfl⟩
  | cons e p ih =>
    obtain ⟨e',he⟩ := h e List.mem_cons_self
    obtain ⟨p',hp⟩ := ih (fun f hf => h f (List.mem_cons_of_mem _ hf))
    exact ⟨e'::p',by simp [he,hp]⟩

/-- If all actual paths between the specified endpoints lie in a full embedded
subgraph, its full sorted product computes the same entry. -/
theorem dispatch_entry_graph_embedding (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (j : V' → V) (hj : Function.Injective j) (J : E' → E) (hJ : Function.Injective J)
    (hs : ∀ e, source (J e)=j (source' e))
    (ht : ∀ e, target (J e)=j (target' e))
    (p : List E) (q : List E') (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label (J f) ≤ label (J e)))
    (hqfull : ∀ e, e ∈ q) (hJmem : ∀ e, J e ∈ p)
    (x y : V')
    (hpath : ∀ r ∈ subpaths source target p (j x) (j y), ∀ e ∈ r, ∃ e', J e'=e) :
    dispatch source target T (fun z => if z=j y then 1 else 0) p (j x) =
      dispatch source' target' T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source' target' T q hqnd]
  symm
  have hties' : ∀ e f, label (J e)=label (J f) → target' e ≠ source' f := by
    intro e f he hf
    apply hties (J e) (J f) he
    rw [ht,hs,hf]
  apply Finset.sum_bij (fun r _ => r.map J)
  · intro r hr
    obtain ⟨hr,hpr⟩ := (mem_subpaths source' target' q x y r).mp hr
    apply (mem_subpaths source target p (j x) (j y) (r.map J)).mpr
    constructor
    · apply sublist_of_decreasing_subset label
      · rw [List.pairwise_map]
        exact decreasing_of_schedule_path source' target' (label ∘ J) hties' hpr (hq.sublist hr)
      · exact hp
      · intro e he
        obtain ⟨f,_,rfl⟩ := List.mem_map.mp he
        exact hJmem f
    · exact hpr.map source' target' source target j J hs ht
  · intro r _ s _ he
    exact List.map_injective_iff.mpr hJ he
  · intro r hr
    obtain ⟨s,he⟩ := exists_list_lift J r (hpath r hr)
    refine ⟨s,?_,he⟩
    obtain ⟨hrsub,hrpath⟩ := (mem_subpaths source target p (j x) (j y) r).mp hr
    have hspath : IsPath source' target' x y s :=
      (IsPath.map_iff source target source' target' j hj J hs ht).mp (he ▸ hrpath)
    apply (mem_subpaths source' target' q x y s).mpr
    refine ⟨?_,hspath⟩
    apply sublist_of_decreasing_subset (label ∘ J)
    · have hstrict := decreasing_of_schedule_path source target label hties hrpath (hp.sublist hrsub)
      rw [← he,List.pairwise_map] at hstrict
      exact hstrict
    · exact hq
    · exact fun e _ => hqfull e
  · intro r _
    simp

end
end KLInvariance.SchedulePaths

end


section

/-! Linear coordinates on the actual normalized root line. These give the
rank-two geometry of finite wall crossings for genuine root schedules. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

@[simp] theorem normalizedRoot_height (a : PositiveRoot M cs) :
    height (normalizedRoot a) = 1 := by
  simp [normalizedRoot,a.height_pos.ne']

@[simp] theorem dual_normalizedRoot (f : Module.Dual ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    f (normalizedRoot a) = f a.val / height a.val := by
  simp [normalizedRoot,div_eq_mul_inv,mul_comm]

@[simp] theorem geometricFunctional_normalizedRoot (a : PositiveRoot M cs) :
    geometricFunctional (M := M) (cs := cs) (normalizedRoot a) = geometricSlope a :=
  dual_normalizedRoot _ a

theorem normalizedRoot_mem_iff (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    normalizedRoot a ∈ P ↔ a.val ∈ P := by
  constructor
  · intro h
    have hh := P.smul_mem (height a.val) h
    simpa [normalizedRoot,smul_smul,a.height_pos.ne'] using hh
  · exact fun h => P.smul_mem _ h

theorem rootPlane_eq_normalized_span (a b : PositiveRoot M cs) :
    rootPlane a b = Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mp (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mp (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · apply Submodule.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (normalizedRoot_mem_iff _ a).mpr (Submodule.subset_span (Set.mem_insert _ _))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (normalizedRoot_mem_iff _ b).mpr (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

/-- The intersection of a root-plane with the height-one hyperplane is the
actual affine line through the two normalized roots. -/
theorem normalizedRoot_affine {a b c : PositiveRoot M cs}
    (hc : c.val ∈ rootPlane a b) :
    ∃ t : ℝ, normalizedRoot c = t • normalizedRoot a + (1-t) • normalizedRoot b := by
  have hcn : normalizedRoot c ∈ Submodule.span ℝ {normalizedRoot a,normalizedRoot b} := by
    rw [← rootPlane_eq_normalized_span]
    exact (normalizedRoot_mem_iff _ _).mpr hc
  obtain ⟨t,s,he⟩ := Submodule.mem_span_pair.mp hcn
  have hh := congrArg (height (I := I)) he
  simp only [map_add,map_smul,normalizedRoot_height,smul_eq_mul,mul_one] at hh
  refine ⟨t,?_⟩
  have hs : s=1-t := by linarith
  exact hs ▸ he.symm

/-- On each genuine root plane, every height-normalized linear functional
is an affine function of the fixed angular slope. -/
theorem exists_affine_rootPlane (f : Module.Dual ℝ (I → ℝ))
    (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  let A := geometricSlope a
  let B := geometricSlope b
  let fa := f (normalizedRoot a)
  let fb := f (normalizedRoot b)
  have hAB : A-B ≠ 0 := sub_ne_zero.mpr (fun h => hab (geometricSlope_injective h))
  let c := (fa-fb)/(A-B)
  let d := fb-c*B
  have ha : fa=c*A+d := by
    dsimp [d,c]
    field_simp
    ring
  have hb : fb=c*B+d := by dsimp [d]; ring
  refine ⟨c,d,fun r hr => ?_⟩
  obtain ⟨t,ht⟩ := normalizedRoot_affine hr
  have hf : f (normalizedRoot r) = t*fa+(1-t)*fb := by
    rw [ht]
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hg : geometricSlope r = t*A+(1-t)*B := by
    rw [← geometricFunctional_normalizedRoot,ht]
    simp only [map_add,map_smul,geometricFunctional_normalizedRoot,smul_eq_mul]
    rfl
  rw [hf,hg,ha,hb]
  ring

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
theorem exists_affine (f : Module.Dual ℝ (I → ℝ)) :
    ∃ c d : ℝ, ∀ r : PositiveRoot M cs, r.val ∈ P →
      f (normalizedRoot r) = c * geometricSlope r + d := by
  simpa only [B.plane_eq] using exists_affine_rootPlane f B.left B.right B.distinct

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Localization of genuine directed paths in a maximal root-plane coset.
The full relative interval is proved to contain every such path. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module SchedulePaths
open AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- All edges of a plane-labelled path lie in the full induced relative
interval between its endpoints, with the original ambient labels. -/
theorem path_coordinates {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (g : planeSubgroup M cs P) {y : W} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) y p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∃ k : planeSubgroup M cs P, y=(k:W)*a₀ ∧ BruhatLE B.system g k ∧
      ∀ e ∈ p, ∃ l r : planeSubgroup M cs P,
        source cs e=(l:W)*a₀ ∧ target cs e=(r:W)*a₀ ∧
        BruhatLE B.system g l ∧ BruhatStep B.system l r ∧ BruhatLE B.system r k := by
  induction p generalizing g with
  | nil => exact ⟨g,hp.symm,.refl,by simp⟩
  | cons e p ih =>
    have hg : source cs e*a₀⁻¹ ∈ planeSubgroup M cs P := by
      rw [hp.1]
      simpa only [mul_assoc,mul_inv_cancel,mul_one] using g.property
    have hh := mem_coset_of_graphRoot e.property hg (hP e List.mem_cons_self)
    let h : planeSubgroup M cs P := ⟨target cs e*a₀⁻¹,hh⟩
    have heqh : target cs e=(h:W)*a₀ := by dsimp [h]; group
    have he : BruhatStep B.system g h := by
      apply (B.coset_step_iff hmin g h).mp
      rw [← hp.1,← heqh]
      exact e.property
    obtain ⟨k,hky,hk,hbody⟩ := ih h (heqh ▸ hp.2)
      (fun f hf => hP f (List.mem_cons_of_mem _ hf))
    refine ⟨k,hky,(show BruhatLE B.system g h from .single he).trans hk,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨g,h,hp.1,heqh,.refl,he,hk⟩
    · obtain ⟨l,r,hl,hr,hhl,hlr,hrk⟩ := hbody f hf
      exact ⟨l,r,hl,hr,(show BruhatLE B.system g h from .single he).trans hhl,hlr,hrk⟩

def intervalToAmbient {a₀ : W} {g k : planeSubgroup M cs P}
    (z : Interval B.system g k) : W := (z.val:W)*a₀

theorem intervalToAmbient_injective {a₀ : W} {g k : planeSubgroup M cs P} :
    Function.Injective (B.intervalToAmbient (a₀ := a₀) (g := g) (k := k)) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (mul_right_cancel h))

def edgeToAmbient {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) : AdaptedDyer.Edge cs :=
  ⟨(B.intervalToAmbient e.val.1, B.intervalToAmbient e.val.2),
    (B.coset_step_iff hmin e.val.1.val e.val.2.val).mpr e.property⟩

@[simp] theorem edgeToAmbient_source {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    source cs (B.edgeToAmbient hmin e) = B.intervalToAmbient (a₀ := a₀) (BruhatGraph.source B.system g k e) := rfl

@[simp] theorem edgeToAmbient_target {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    target cs (B.edgeToAmbient hmin e) = B.intervalToAmbient (a₀ := a₀) (BruhatGraph.target B.system g k e) := rfl

theorem edgeToAmbient_injective {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} :
    Function.Injective (B.edgeToAmbient hmin (g := g) (k := k)) := by
  intro e f h
  have hh := congrArg Subtype.val h
  apply Subtype.ext
  exact Prod.ext (B.intervalToAmbient_injective (congrArg Prod.fst hh))
    (B.intervalToAmbient_injective (congrArg Prod.snd hh))

@[simp] theorem edgeToAmbient_root {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    rootLabel cs (B.edgeToAmbient hmin e) = B.edgeRoot e.property := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change rootRef (rootLabel cs (B.edgeToAmbient hmin e)) = rootRef (B.edgeRoot e.property)
  rw [rootRef_rootLabel]
  have hr : rootRef (B.edgeRoot e.property) = (e.val.2.val:W)*(e.val.1.val:W)⁻¹ :=
    (rootReflection_represents M cs _).reflection_unique
      (graphRoot_represents ((B.bruhatStep_iff _ _).mpr e.property))
  rw [hr]
  change ((e.val.2.val:W)*a₀)*((e.val.1.val:W)*a₀)⁻¹ = _
  group

/-- Edge-by-edge lifting of every plane path into the full relative interval.
It is obtained from actual path connectivity, not from ambient comparability
alone (which would not suffice). -/
theorem path_edges_lift {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} {p : List (AdaptedDyer.Edge cs)}
    (hp : IsPath (source cs) (target cs) ((g:W)*a₀) ((k:W)*a₀) p)
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P) :
    ∀ e ∈ p, ∃ e' : BruhatGraph.Edge B.system g k, B.edgeToAmbient hmin e'=e := by
  obtain ⟨k',he,_,hbody⟩ := B.path_coordinates hmin g hp hP
  have hk : k'=k := Subtype.ext (mul_right_cancel he.symm)
  subst k'
  intro e he
  obtain ⟨l,r,hl,hr,hgl,hlr,hrk⟩ := hbody e he
  let vl : Interval B.system g k := ⟨l,hgl,(show BruhatLE B.system l r from .single hlr).trans hrk⟩
  let vr : Interval B.system g k := ⟨r,hgl.trans (.single hlr),hrk⟩
  refine ⟨⟨(vl,vr),hlr⟩,?_⟩
  apply Subtype.ext
  exact Prod.ext hl.symm hr.symm


include B in
/-- Reversal of a complete angular block of genuine ambient edges preserves
all its endpoint entries. Fullness is with respect to the actual root plane,
not to a rank-two subgroup chosen merely to contain two arbitrary reflections. -/
theorem dispatch_plane_reverse {R : Type*} [Semiring R] (T : R) (b : W)
    (p : List (AdaptedDyer.Edge cs)) (hnd : p.Nodup)
    (hfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hs : p.Pairwise (fun e f => geometricSlope (rootLabel cs f) ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p.reverse x := by
  obtain ⟨a₀,g,hg,hx,hmin⟩ := planeCoset_exists_minimal M cs P x
  let g' : planeSubgroup M cs P := ⟨g,hg⟩
  have hx' : x=(g':W)*a₀ := hx
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e f, L e=L f → target cs e ≠ source cs f := by
    intro e f he
    exact fun hj => rootLabel_ne_of_join cs e f hj (geometricSlope_injective he)
  by_cases hex : ∃ r : List (AdaptedDyer.Edge cs),
      IsPath (source cs) (target cs) x y r ∧ ∀ e ∈ r, (rootLabel cs e).val ∈ P
  · obtain ⟨r,hr,hrP⟩ := hex
    obtain ⟨k,hyk,hgk,_⟩ := B.path_coordinates hmin g' (hx' ▸ hr) hrP
    let lo : Interval B.system g' k := ⟨g',.refl,hgk⟩
    let hi : Interval B.system g' k := ⟨k,hgk,.refl⟩
    let j := B.intervalToAmbient (a₀ := a₀) (g := g') (k := k)
    let J := B.edgeToAmbient hmin (g := g') (k := k)
    have hjlo : j lo=x := hx'.symm
    have hjhi : j hi=y := hyk.symm
    let : Fintype (BruhatGraph.Edge B.system g' k) := Fintype.ofFinite _
    let q : List (BruhatGraph.Edge B.system g' k) :=
      Finset.univ.toList.mergeSort (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e)
    have hqnd : q.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
    have hqfull : ∀ e, e ∈ q := by intro e; simp [q]
    have hqs : q.Pairwise (fun e f => B.intervalEdgeSlope g' k f ≤ B.intervalEdgeSlope g' k e) :=
      List.pairwise_mergeSort' _ _
    have hJroot (e : BruhatGraph.Edge B.system g' k) : L (J e)=B.intervalEdgeSlope g' k e := by
      dsimp [L,J,intervalEdgeSlope]
      rw [B.edgeToAmbient_root]
    have hJmem (e : BruhatGraph.Edge B.system g' k) : J e ∈ p := by
      apply (hfull _).mpr
      constructor
      · dsimp [J]
        rw [B.edgeToAmbient_root]
        exact B.edgeRoot_plane e.property
      · have ht : BruhatLE cs ((e.val.2.val:W)*a₀) ((k:W)*a₀) :=
          B.coset_bruhat hmin e.val.2.property.2
        exact ht.trans (hyk ▸ hy)
    have hlift (s : List (AdaptedDyer.Edge cs))
        (hst : ∀ e ∈ s, e ∈ p)
        (hp : IsPath (source cs) (target cs) (j lo) (j hi) s) :
        ∀ e ∈ s, ∃ e' : BruhatGraph.Edge B.system g' k, J e'=e :=
      B.path_edges_lift hmin hp (fun e he => ((hfull e).mp (hst e he)).1)
    have hleft := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T L hties j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p q hnd hqnd hs (by simpa only [hJroot] using hqs) hqfull hJmem lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => hsub.subset he) hpath)
    have hright := dispatch_entry_graph_embedding (source cs) (target cs)
      (BruhatGraph.source B.system g' k) (BruhatGraph.target B.system g' k)
      T (fun e => -L e) (fun e f he => hties e f (neg_injective he))
      j (B.intervalToAmbient_injective) J (B.edgeToAmbient_injective hmin)
      (B.edgeToAmbient_source hmin) (B.edgeToAmbient_target hmin)
      p.reverse q.reverse (List.nodup_reverse.mpr hnd) (List.nodup_reverse.mpr hqnd)
      (by rw [List.pairwise_reverse]; exact hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hqs.imp (fun he => by simpa only [hJroot] using neg_le_neg he))
      (fun e => List.mem_reverse.mpr (hqfull e))
      (fun e => List.mem_reverse.mpr (hJmem e)) lo hi (by
        intro s hsp
        obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hsp
        exact hlift s (fun e he => List.mem_reverse.mp (hsub.subset he)) hpath)
    rw [hjlo,hjhi] at hleft hright
    rw [hleft,hright]
    exact B.dispatch_reverse_endpoints hgk q hqnd hqfull hqs T
  · have hzero (q : List (AdaptedDyer.Edge cs))
        (hqp : ∀ e ∈ q, e ∈ p) : subpaths (source cs) (target cs) q x y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨hsub,hpath⟩ := (mem_subpaths _ _ _ _ _ _).mp hr
      exact hex ⟨r,hpath,fun e he => ((hfull e).mp (hqp e (hsub.subset he))).1⟩
    rw [dispatch_eq_subpaths_sum _ _ _ _ hnd,
      dispatch_eq_subpaths_sum _ _ _ _ (List.nodup_reverse.mpr hnd),
      hzero p (fun _ he => he),hzero p.reverse (fun _ he => List.mem_reverse.mp he)]

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : DecidableEq E := Classical.decEq E

def sortedSchedule (F : Finset E) (score : E → Λ) : List E :=
  F.toList.mergeSort (fun e f => score f ≤ score e)

@[simp] theorem mem_sortedSchedule (F : Finset E) (score : E → Λ) (e : E) :
    e ∈ sortedSchedule F score ↔ e ∈ F := by simp [sortedSchedule]

theorem sortedSchedule_nodup (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem sortedSchedule_pairwise (F : Finset E) (score : E → Λ) :
    (sortedSchedule F score).Pairwise (fun e f => score f ≤ score e) :=
  List.pairwise_mergeSort' _ _

def blockValues (F : Finset E) (primary : E → A) : List A :=
  (F.image primary).sort (fun a b => b ≤ a)

def scheduleBlock (F : Finset E) (primary : E → A) (score : E → Λ) (a : A) : List E :=
  sortedSchedule (F.filter (fun e => primary e=a)) score

def groupedSchedule (F : Finset E) (primary : E → A) (score : E → Λ) : List E :=
  (blockValues F primary).flatMap (scheduleBlock F primary score)

@[simp] theorem mem_blockValues (F : Finset E) (primary : E → A) (a : A) :
    a ∈ blockValues F primary ↔ ∃ e ∈ F, primary e=a := by
  simp [blockValues]

omit [LinearOrder A] in
@[simp] theorem mem_scheduleBlock (F : Finset E) (primary : E → A) (score : E → Λ)
    (a : A) (e : E) : e ∈ scheduleBlock F primary score a ↔ e ∈ F ∧ primary e=a := by
  simp [scheduleBlock]

@[simp] theorem mem_groupedSchedule (F : Finset E) (primary : E → A) (score : E → Λ)
    (e : E) : e ∈ groupedSchedule F primary score ↔ e ∈ F := by
  constructor
  · intro he
    obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp he
    exact ((mem_scheduleBlock F primary score a e).mp ha).1
  · intro he
    apply List.mem_flatMap.mpr
    exact ⟨primary e,(mem_blockValues F primary _).mpr ⟨e,he,rfl⟩,
      (mem_scheduleBlock F primary score _ _).mpr ⟨he,rfl⟩⟩

theorem blockValues_strict (F : Finset E) (primary : E → A) :
    (blockValues F primary).Pairwise (fun a b => b < a) := by
  have hs := Finset.pairwise_sort (F.image primary) (fun a b => b ≤ a)
  have hn := Finset.sort_nodup (F.image primary) (fun a b => b ≤ a)
  exact (List.pairwise_and_iff.mpr ⟨hs,hn⟩).imp (fun h => lt_of_le_of_ne h.1 h.2.symm)

theorem groupedSchedule_nodup (F : Finset E) (primary : E → A) (score : E → Λ) :
    (groupedSchedule F primary score).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_nodup _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab
    apply List.disjoint_left.mpr
    intro e hea heb
    have ha := ((mem_scheduleBlock F primary score a e).mp hea).2
    have hb := ((mem_scheduleBlock F primary score b e).mp heb).2
    exact hab.ne (hb.symm.trans ha)

theorem groupedSchedule_pairwise (F : Finset E) (primary : E → A) (score : E → Λ)
    (h : ∀ e ∈ F, ∀ f ∈ F, primary f < primary e → score f ≤ score e) :
    (groupedSchedule F primary score).Pairwise (fun e f => score f ≤ score e) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    exact sortedSchedule_pairwise _ _
  · apply (blockValues_strict F primary).imp
    intro a b hab e he f hf
    obtain ⟨he,heq⟩ := (mem_scheduleBlock F primary score a e).mp he
    obtain ⟨hf,hfq⟩ := (mem_scheduleBlock F primary score b f).mp hf
    exact h e he f hf (by simpa only [heq,hfq] using hab)

variable {V : Type*} {R : Type*} [Semiring R] (source target : E → V)

theorem dispatch_entries_eq_of_sorted (T : R) (label : E → Λ)
    (hties : ∀ e f, label e=label f → target e ≠ source f)
    (p q : List E) (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hp : p.Pairwise (fun e f => label f ≤ label e))
    (hq : q.Pairwise (fun e f => label f ≤ label e))
    (hmem : ∀ e, e ∈ p ↔ e ∈ q) (x y : V) :
    dispatch source target T (fun z => if z=y then 1 else 0) p x =
      dispatch source target T (fun z => if z=y then 1 else 0) q x := by
  rw [dispatch_eq_subpaths_sum source target T p hpnd,
    dispatch_eq_subpaths_sum source target T q hqnd,
    subpaths_eq_of_sorted source target label hties p q hp hq hmem x y]

omit [LinearOrder A] in
/-- Replacement on a finite lower region requires no artificial finiteness
assumption on the ambient Coxeter group. -/
theorem dispatch_flatMap_eq_on (T : R) (S : Set V) (blocks : List A) (p q : A → List E)
    (htarget : ∀ a ∈ blocks, ∀ e ∈ p a, target e ∈ S)
    (h : ∀ a ∈ blocks, ∀ v, ∀ x ∈ S,
      dispatch source target T v (p a) x = dispatch source target T v (q a) x)
    (v : V → R) : ∀ x ∈ S,
    dispatch source target T v (blocks.flatMap p) x =
      dispatch source target T v (blocks.flatMap q) x := by
  induction blocks with
  | nil => exact fun _ _ => rfl
  | cons a l ih =>
    intro x hx
    simp only [List.flatMap_cons,dispatch_append]
    rw [dispatch_congr_on source target T S (p a) (htarget a List.mem_cons_self)
      _ _ (ih (fun b hb => htarget b (List.mem_cons_of_mem _ hb))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))) x hx]
    exact h a List.mem_cons_self _ x hx

end
end KLInvariance.SchedulePaths

end


section

/-! The actual rank-two edge product is independent of every linear
functional restricted to that root plane, including a wall tie refinement. -/
namespace KLInvariance.TitsSpace
open Module SchedulePaths AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def lexRootScore (f : Module.Dual ℝ (I → ℝ)) (a : PositiveRoot M cs) : ℝ ×ₗ ℝ :=
  toLex (f (normalizedRoot a),geometricSlope a)

theorem lexRootScore_injective (f : Module.Dual ℝ (I → ℝ)) :
    Function.Injective (lexRootScore (M := M) (cs := cs) f) := by
  intro a b hab
  apply geometricSlope_injective
  exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).2) hab

def lexEdgeScore (f : Module.Dual ℝ (I → ℝ)) (e : AdaptedDyer.Edge cs) : ℝ ×ₗ ℝ :=
  lexRootScore f (rootLabel cs e)

theorem lexEdgeScore_ties (f : Module.Dual ℝ (I → ℝ)) (e e' : AdaptedDyer.Edge cs)
    (he : lexEdgeScore f e=lexEdgeScore f e') : target cs e ≠ source cs e' := by
  intro hj
  exact rootLabel_ne_of_join cs e e' hj (lexRootScore_injective f he)

omit [Fintype I] in
theorem lex_affine_nonneg {c d x y : ℝ} (hc : 0 ≤ c)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : x ≤ y := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : y < x := lt_of_not_ge hn
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hxy.le)]
  · exact h.2

omit [Fintype I] in
theorem lex_affine_neg {c d x y : ℝ} (hc : c < 0)
    (h : (toLex (c*x+d,x) : ℝ ×ₗ ℝ) ≤ toLex (c*y+d,y)) : y ≤ x := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | h
  · by_contra hn
    have hxy : x < y := lt_of_not_ge hn
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc.le (sub_nonneg.mpr hxy.le)]
  · have he : x=y := by nlinarith [h.1]
    exact he.symm.le

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

include B in
/-- Any linearly sorted full plane block is either angularly sorted or
reverse-angularly sorted. This includes tied primary labels refined by the
fixed genuine geometric functional. -/
theorem lex_block_orientation (f : Module.Dual ℝ (I → ℝ))
    (p : List (AdaptedDyer.Edge cs))
    (hP : ∀ e ∈ p, (rootLabel cs e).val ∈ P)
    (hs : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e)) :
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)) ∨
    p.Pairwise (fun e e' => geometricSlope (rootLabel cs e) ≤ geometricSlope (rootLabel cs e')) := by
  obtain ⟨c,d,hf⟩ := B.exists_affine f
  have hv (e : AdaptedDyer.Edge cs) (he : e ∈ p) :
      lexEdgeScore f e=toLex (c*geometricSlope (rootLabel cs e)+d,geometricSlope (rootLabel cs e)) := by
    unfold lexEdgeScore lexRootScore
    rw [hf _ (hP e he)]
  by_cases hc : 0 ≤ c
  · left
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_nonneg hc hee'
  · right
    apply hs.imp_of_mem
    intro e e' he he' hee'
    rw [hv e he,hv e' he'] at hee'
    exact lex_affine_neg (lt_of_not_ge hc) hee'

include B in
/-- A complete plane block, sorted by any functional, has precisely the
same actual path product as its angularly sorted version. -/
theorem dispatch_plane_functional {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (p q : List (AdaptedDyer.Edge cs))
    (hpnd : p.Nodup) (hqnd : q.Nodup)
    (hpfull : ∀ e, e ∈ p ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hqfull : ∀ e, e ∈ q ↔ (rootLabel cs e).val ∈ P ∧ BruhatLE cs (target cs e) b)
    (hp : p.Pairwise (fun e e' => lexEdgeScore f e' ≤ lexEdgeScore f e))
    (hq : q.Pairwise (fun e e' => geometricSlope (rootLabel cs e') ≤ geometricSlope (rootLabel cs e)))
    (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) p x =
      dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) q x := by
  let L : AdaptedDyer.Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
  have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
    intro e e' he hj
    exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
  rcases B.lex_block_orientation f p (fun e he => ((hpfull e).mp he).1) hp with hs|hs
  · exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties
      p q hpnd hqnd hs hq (fun e => (hpfull e).trans (hqfull e).symm) x y
  · have hentry := dispatch_entries_eq_of_sorted (source cs) (target cs) T
      (fun e => -L e) (fun e e' he => hties e e' (neg_injective he))
      p q.reverse hpnd (List.nodup_reverse.mpr hqnd)
      (hs.imp (fun he => neg_le_neg he))
      (by rw [List.pairwise_reverse]; exact hq.imp (fun he => neg_le_neg he))
      (fun e => (hpfull e).trans ((hqfull e).symm.trans List.mem_reverse.symm)) x y
    exact hentry.trans (B.dispatch_plane_reverse T b q hqnd hqfull hq x y hy).symm

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Generic pencils of genuine linear root-label functionals. At a wall all
roots of a tied block belong to one full actual root plane. -/
namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

/-- A countable family of nonzero vectors can be simultaneously avoided. -/
theorem exists_avoiding_functional {A : Type v} [Countable A] (v : A → (I → ℝ)) :
    ∃ f : Module.Dual ℝ (I → ℝ), ∀ a, v a ≠ 0 → f (v a) ≠ 0 := by
  classical
  let P := {a : A // v a ≠ 0}
  have hn (a : P) : coordinatePolynomial (v a.val) ≠ 0 := by
    intro h
    apply a.property
    apply coordinatePolynomial_injective
    simpa [coordinatePolynomial] using h
  let bad : Set ℝ := ⋃ a : P, {t | (coordinatePolynomial (v a.val)).IsRoot t}
  have hb : bad.Countable := Set.countable_iUnion
    (fun a => (Polynomial.finite_setOfPred_isRoot (hn a)).countable)
  obtain ⟨t,ht⟩ : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    have he : bad=Set.univ := Set.eq_univ_of_forall h
    rw [he] at hb
    exact Set.not_countable_univ hb
  refine ⟨momentFunctional t,fun a ha he => ht ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨⟨a,ha⟩,?_⟩
  simpa only [Set.mem_ofPred_eq,Polynomial.IsRoot,coordinatePolynomial_eval] using he

end
end KLInvariance.ReflectionSchedules

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def pencil (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) : Module.Dual ℝ (I → ℝ) :=
  (1-t) • f + t • g

omit [Fintype I] in
@[simp] theorem pencil_zero (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 0=f := by
  simp [pencil]
omit [Fintype I] in
@[simp] theorem pencil_one (f g : Module.Dual ℝ (I → ℝ)) : pencil f g 1=g := by
  simp [pencil]

omit [Fintype I] in
theorem pencil_apply (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) (v : I → ℝ) :
    pencil f g t v=(1-t)*f v+t*g v := rfl

def rootDifference (a b : PositiveRoot M cs) : I → ℝ := normalizedRoot b-normalizedRoot a

def wallVector (f : Module.Dual ℝ (I → ℝ)) (a b c : PositiveRoot M cs) : I → ℝ :=
  f (rootDifference a b) • rootDifference a c -
    f (rootDifference a c) • rootDifference a b

/-- This is an actual genericity condition on linear functionals, not
an assumed path or Hecke identity. -/
def Transverse (f g : Module.Dual ℝ (I → ℝ)) : Prop :=
  ∀ a b c : PositiveRoot M cs, g (wallVector f a b c)=0 → wallVector f a b c=0

theorem pencil_tie_plane (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (t : ℝ)
    (a b : PositiveRoot M cs) (hab : a ≠ b)
    (he : pencil f g t (normalizedRoot a)=pencil f g t (normalizedRoot b)) :
    ∀ c : PositiveRoot M cs,
      pencil f g t (normalizedRoot c)=pencil f g t (normalizedRoot a) ↔
        c.val ∈ rootPlane a b := by
  let v := rootDifference a b
  have hv : f v ≠ 0 := by
    change f (normalizedRoot b-normalizedRoot a) ≠ 0
    rw [map_sub,sub_ne_zero]
    exact fun h => hab (hf h).symm
  have hvt : (1-t)*f v+t*g v=0 := by
    rw [← pencil_apply]
    change pencil f g t (normalizedRoot b-normalizedRoot a)=0
    rw [map_sub,he,sub_self]
  have ht : t ≠ 0 := by
    intro h
    subst t
    simp only [sub_zero,one_mul,zero_mul,add_zero] at hvt
    exact hv hvt
  intro c
  constructor
  · intro hc
    let w := rootDifference a c
    have hwt : (1-t)*f w+t*g w=0 := by
      rw [← pencil_apply]
      change pencil f g t (normalizedRoot c-normalizedRoot a)=0
      rw [map_sub,hc,sub_self]
    have hz : g (wallVector f a b c)=0 := by
      change g (f v • w-f w • v)=0
      rw [map_sub,map_smul,map_smul,smul_eq_mul,smul_eq_mul]
      apply (mul_eq_zero.mp (show t * (f v*g w-f w*g v)=0 by
        calc
          _ = f v*((1-t)*f w+t*g w)-f w*((1-t)*f v+t*g v) := by ring
          _ = 0 := by rw [hwt,hvt]; ring)).resolve_left ht
    have heq : f v • w=f w • v := sub_eq_zero.mp (hg a b c hz)
    let P := rootPlane a b
    have haP : normalizedRoot a ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert _ _))
    have hbP : normalizedRoot b ∈ P := (normalizedRoot_mem_iff _ _).mpr
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hvP : v ∈ P := P.sub_mem hbP haP
    have hwP : w ∈ P := by
      have hh := P.smul_mem (f v)⁻¹ (heq ▸ P.smul_mem (f w) hvP)
      simpa only [smul_smul,inv_mul_cancel₀ hv,one_smul] using hh
    apply (normalizedRoot_mem_iff P c).mp
    have hh := P.add_mem hwP haP
    simpa only [w,rootDifference,sub_add_cancel] using hh
  · intro hc
    obtain ⟨s,hs⟩ := normalizedRoot_affine hc
    rw [hs,map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul,← he]
    ring

/-- One intermediate functional is simultaneously transverse to any two
specified generic endpoints, even with infinitely many positive roots. -/
theorem exists_common_transverse (f h : Module.Dual ℝ (I → ℝ)) :
    ∃ g : Module.Dual ℝ (I → ℝ),
      Function.Injective (fun a : PositiveRoot M cs => g (normalizedRoot a)) ∧
      Transverse (M := M) (cs := cs) f g ∧ Transverse (M := M) (cs := cs) h g := by
  let := countable_Positiveroot M cs
  let E := PositiveRoot M cs
  let A := (E × E) ⊕ (Bool × E × E × E)
  let v : A → (I → ℝ) := fun x => match x with
    | .inl (a,b) => rootDifference a b
    | .inr (i,a,b,c) => wallVector (if i then f else h) a b c
  obtain ⟨g,hg⟩ := ReflectionSchedules.exists_avoiding_functional v
  refine ⟨g,?_,?_,?_⟩
  · intro a b he
    by_contra hab
    have hn : rootDifference a b ≠ 0 := by
      exact fun hz => hab (normalizedRoot_injective (sub_eq_zero.mp hz)).symm
    apply hg (.inl (a,b)) hn
    simp only [v,rootDifference,map_sub,he,sub_self]
  · intro a b c he
    by_contra hz
    exact hg (.inr (true,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)
  · intro a b c he
    by_contra hz
    exact hg (.inr (false,a,b,c)) (by simpa [v] using hz)
      (by simpa [v] using he)

end
end KLInvariance.TitsSpace

end


section

/-! Finite wall crossing for actual reflection-edge path matrices. -/
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
open scoped Topology
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def rootValue (f : Module.Dual ℝ (I → ℝ)) (e : Edge cs) : ℝ :=
  f (normalizedRoot (rootLabel cs e))

def rootPlaneTies (f : Module.Dual ℝ (I → ℝ)) : Prop :=
  ∀ a b : PositiveRoot M cs, a ≠ b → f (normalizedRoot a)=f (normalizedRoot b) →
    ∀ c : PositiveRoot M cs, f (normalizedRoot c)=f (normalizedRoot a) ↔
      c.val ∈ rootPlane a b

def schedule (f : Module.Dual ℝ (I → ℝ)) (b : W) : List (Edge cs) :=
  sortedSchedule (edgeFinset cs b) (lexEdgeScore f)

def entry {R : Type*} [Semiring R] (T : R) (f : Module.Dual ℝ (I → ℝ))
    (b x y : W) : R :=
  dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0) (schedule f b) x

/-- The complete tied block at any genuine simple wall has an actual
operator independent of the linear tie-breaking functional. -/
theorem block_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (a : ℝ) (x y : W) (hy : BruhatLE cs y b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g) a) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h) a) x := by
  let F := (edgeFinset cs b).filter (fun e => rootValue f e=a)
  let p := sortedSchedule F (lexEdgeScore g)
  let q := sortedSchedule F (lexEdgeScore h)
  let r := sortedSchedule F (fun e => geometricSlope (rootLabel cs e))
  change dispatch (source cs) (target cs) T _ p x = dispatch (source cs) (target cs) T _ q x
  have hmem (k : Edge cs) : k ∈ F ↔ BruhatLE cs (target cs k) b ∧ rootValue f k=a := by
    simp only [F,Finset.mem_filter,mem_edgeFinset]
  by_cases hex : ∃ e ∈ F, ∃ e' ∈ F, rootLabel cs e ≠ rootLabel cs e'
  · obtain ⟨e,he,e',he',hne⟩ := hex
    obtain ⟨B⟩ := nonempty_planeBasis (rootLabel cs e) (rootLabel cs e') hne
    have hv := hf (rootLabel cs e) (rootLabel cs e') hne
      (((hmem e).mp he).2.trans ((hmem e').mp he').2.symm)
    have hfull (k : Edge cs) : k ∈ F ↔
        (rootLabel cs k).val ∈ rootPlane (rootLabel cs e) (rootLabel cs e') ∧
        BruhatLE cs (target cs k) b := by
      rw [hmem,← hv,show f (normalizedRoot (rootLabel cs e))=a from ((hmem e).mp he).2]
      exact and_comm
    have hp := B.dispatch_plane_functional T b g p r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    have hq := B.dispatch_plane_functional T b h q r
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _)
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (fun k => (mem_sortedSchedule _ _ k).trans (hfull k))
      (sortedSchedule_pairwise _ _) (sortedSchedule_pairwise _ _) x y hy
    exact hp.trans hq.symm
  · have heq (e : Edge cs) (he : e ∈ F) (e' : Edge cs) (he' : e' ∈ F) :
        rootLabel cs e=rootLabel cs e' := by
      by_contra hn
      exact hex ⟨e,he,e',he',hn⟩
    let L : Edge cs → ℝ := fun e => geometricSlope (rootLabel cs e)
    have hties : ∀ e e', L e=L e' → target cs e ≠ source cs e' := by
      intro e e' he hj
      exact rootLabel_ne_of_join cs e e' hj (geometricSlope_injective he)
    have hs (s : Module.Dual ℝ (I → ℝ)) :
        (sortedSchedule F (lexEdgeScore s)).Pairwise (fun e e' => L e' ≤ L e) := by
      apply (sortedSchedule_pairwise F (lexEdgeScore s)).imp_of_mem
      intro e e' he he' _
      have hr := heq e ((mem_sortedSchedule _ _ _).mp he) e' ((mem_sortedSchedule _ _ _).mp he')
      exact (congrArg geometricSlope hr).symm.le
    exact dispatch_entries_eq_of_sorted (source cs) (target cs) T L hties p q
      (sortedSchedule_nodup _ _) (sortedSchedule_nodup _ _) (hs g) (hs h)
      (fun e => (mem_sortedSchedule _ _ e).trans (mem_sortedSchedule _ _ e).symm) x y

/-- All blocks may be replaced simultaneously on the finite lower region. -/
theorem grouped_entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f : Module.Dual ℝ (I → ℝ)) (hf : rootPlaneTies (M := M) (cs := cs) f)
    (g h : Module.Dual ℝ (I → ℝ)) (x y : W) (hx : BruhatLE cs x b) :
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore h)) x := by
  let K := lowerFinset cs b
  have ht (s : Module.Dual ℝ (I → ℝ)) (a : ℝ) (e : Edge cs)
      (he : e ∈ scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore s) a) :
      target cs e ∈ K := by
    exact (mem_lowerFinset cs b _).mpr ((mem_edgeFinset cs b e).mp
      ((mem_scheduleBlock _ _ _ _ _).mp he).1)
  apply dispatch_flatMap_eq_on (source cs) (target cs) T (K : Set W)
    (blockValues (edgeFinset cs b) (rootValue f))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore g))
    (scheduleBlock (edgeFinset cs b) (rootValue f) (lexEdgeScore h))
    (fun a _ e he => ht g a e he) _ _ x ((mem_lowerFinset cs b x).mpr hx)
  intro a _ v z hz
  apply dispatch_eq_of_entries_on (source cs) (target cs) T K _ _ (ht g a) (ht h a) _ v z hz
  intro l _ k hk
  exact block_entry_independent T b f hf g h a l k ((mem_lowerFinset cs b k).mp hk)

/-- Stable strict primary comparisons identify the genuine sorted schedule
with the corresponding product of tied blocks. -/
theorem entry_eq_grouped {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (h : ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue f e' < rootValue f e → rootValue g e' < rootValue g e)
    (x y : W) :
    entry (cs := cs) T g b x y =
    dispatch (source cs) (target cs) T (fun z => if z=y then 1 else 0)
      (groupedSchedule (edgeFinset cs b) (rootValue f) (lexEdgeScore g)) x := by
  apply dispatch_entries_eq_of_sorted (source cs) (target cs) T (lexEdgeScore g)
    (lexEdgeScore_ties g) _ _ (sortedSchedule_nodup _ _) (groupedSchedule_nodup _ _ _)
    (sortedSchedule_pairwise _ _)
  · apply groupedSchedule_pairwise
    intro e he e' he' hlt
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (h e he e' he' hlt))
  · intro e
    simp only [mem_sortedSchedule,mem_groupedSchedule]

theorem pencil_strict_stable (b : W) (f g : Module.Dual ℝ (I → ℝ)) (t₀ : ℝ) :
    ∀ᶠ t in 𝓝 t₀, ∀ e ∈ edgeFinset cs b, ∀ e' ∈ edgeFinset cs b,
      rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e →
        rootValue (pencil f g t) e' < rootValue (pencil f g t) e := by
  apply (Filter.eventually_all_finset _).mpr
  intro e _
  apply (Filter.eventually_all_finset _).mpr
  intro e' _
  have hc (k : Edge cs) : Continuous (fun t : ℝ => rootValue (pencil f g t) k) := by
    change Continuous (fun t : ℝ => (1-t)*f (normalizedRoot (rootLabel cs k))+
      t*g (normalizedRoot (rootLabel cs k)))
    fun_prop
  by_cases hlt : rootValue (pencil f g t₀) e' < rootValue (pencil f g t₀) e
  · filter_upwards [(isOpen_lt (hc e') (hc e)).mem_nhds hlt] with t ht
    exact fun _ => ht
  · exact Filter.Eventually.of_forall (fun _ h => (hlt h).elim)

/-- Crossing all actual root-plane walls leaves the full path matrix fixed,
not merely a single adapted endpoint column. -/
theorem locally_constant_pencil {R : Type*} [Semiring R] (T : R) (b : W)
    (f g : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hg : Transverse (M := M) (cs := cs) f g) (x y : W) (hx : BruhatLE cs x b) :
    IsLocallyConstant (fun t : ℝ => entry (cs := cs) T (pencil f g t) b x y) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro t₀
  filter_upwards [pencil_strict_stable b f g t₀] with t ht
  have hp : rootPlaneTies (M := M) (cs := cs) (pencil f g t₀) := by
    intro a d had he
    exact pencil_tie_plane f g hf hg t₀ a d had he
  rw [entry_eq_grouped T b (pencil f g t₀) (pencil f g t) ht,
    entry_eq_grouped T b (pencil f g t₀) (pencil f g t₀) (fun _ _ _ _ h => h)]
  exact grouped_entry_independent T b (pencil f g t₀) hp (pencil f g t) (pencil f g t₀) x y hx

/-- Full matrix order independence for genuine finite geometric orders. -/
theorem entry_independent {R : Type*} [Semiring R] (T : R) (b : W)
    (f h : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (hh : Function.Injective (fun a : PositiveRoot M cs => h (normalizedRoot a)))
    (x y : W) (hx : BruhatLE cs x b) : entry (cs := cs) T f b x y=entry (cs := cs) T h b x y := by
  obtain ⟨g,_,hfg,hhg⟩ := exists_common_transverse (M := M) (cs := cs) f h
  have he := (locally_constant_pencil T b f g hf hfg x y hx).apply_eq_of_preconnectedSpace 0 1
  have he' := (locally_constant_pencil T b h g hh hhg x y hx).apply_eq_of_preconnectedSpace 0 1
  simp only [pencil_zero,pencil_one] at he he'
  exact he.trans he'.symm

end
end KLInvariance.WallDyer

end


section

/-! Dyer's full path-matrix identity, for the same geometric schedule in
every endpoint column, with the genuine Hecke-defined normalized R. -/
namespace KLInvariance.WallDyer
open Module SchedulePaths TitsSpace AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem neg_numerator_normalized (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (a : PositiveRoot M cs) :
    (-O.numerator) (normalizedRoot a) = -O.slope a := by
  simp only [LinearMap.neg_apply,dual_normalizedRoot,RatioOrder.slope,hh]

/-- An upper bound larger than the path endpoint creates no extra paths:
every actual directed path stays inside its endpoint interval. -/
theorem subpaths_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    subpaths (source cs) (target cs) (WallDyer.schedule (-O.numerator) b) x y =
      paths O x y := by
  have hscore (e : Edge cs) : rootValue (-O.numerator) e = -score O e :=
    neg_numerator_normalized O hh (rootLabel cs e)
  ext p
  rw [mem_subpaths,mem_paths]
  constructor
  · rintro ⟨hsub,hpath⟩
    refine ⟨hpath,?_⟩
    have hs := (sortedSchedule_pairwise (edgeFinset cs b) (lexEdgeScore (-O.numerator))).sublist hsub
    have hs' : p.Pairwise (fun e e' => score O e ≤ score O e') := by
      apply hs.imp
      intro e e' he
      have hm := Prod.Lex.monotone_fst _ _ he
      change rootValue (-O.numerator) e' ≤ rootValue (-O.numerator) e at hm
      rw [hscore e',hscore e] at hm
      exact neg_le_neg_iff.mp hm
    exact decreasing_of_schedule_path (source cs) (target cs)
      (Λ := OrderDual ℝ) (fun e => (score O e : OrderDual ℝ))
      (fun e e' he => score_ties O e e' he) hpath hs'
  · rintro ⟨hpath,hord⟩
    refine ⟨?_,hpath⟩
    apply sublist_of_decreasing_subset (lexEdgeScore (-O.numerator))
    · apply hord.imp
      intro e e' he
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      change rootValue (-O.numerator) e' < rootValue (-O.numerator) e
      rw [hscore e',hscore e]
      exact neg_lt_neg he
    · exact sortedSchedule_pairwise _ _
    · intro e he
      apply (mem_sortedSchedule _ _ _).mpr
      exact (mem_edgeFinset cs b e).mpr ((path_targets_le cs hpath e he).trans hy)

theorem entry_neg_numerator (O : RatioOrder (M := M) (cs := cs))
    (hh : O.denominator=height) (b x y : W) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (-O.numerator) b x y =
      polynomial O x y := by
  unfold entry
  rw [dispatch_eq_subpaths_sum _ _ _ _ (show (WallDyer.schedule (-O.numerator) b).Nodup from sortedSchedule_nodup _ _),
    subpaths_neg_numerator O hh b x y hy]
  rfl


theorem entry_eq_rTilde (f : Module.Dual ℝ (I → ℝ))
    (hf : Function.Injective (fun a : PositiveRoot M cs => f (normalizedRoot a)))
    (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) f b x y = Hecke.rTilde cs x y := by
  obtain ⟨O,hO,hh⟩ := exists_ratioOrder_chamber_height (M := M) (cs := cs) y
  have hn : Function.Injective (fun a : PositiveRoot M cs => (-O.numerator) (normalizedRoot a)) := by
    intro a b he
    change (-O.numerator) (normalizedRoot a) = (-O.numerator) (normalizedRoot b) at he
    rw [neg_numerator_normalized O hh a,neg_numerator_normalized O hh b] at he
    exact O.slope_injective (neg_injective he)
  rw [entry_independent (Polynomial.X : Polynomial ℤ) b f (-O.numerator) hf hn x y hx,
    entry_neg_numerator O hh b x y hy,polynomial_eq_rTilde O x y hO]

/-- The manuscript's fixed geometric functional provides such a genuine
full Dyer schedule for every finite lower Bruhat region. -/
theorem geometric_entry_eq_rTilde (b x y : W) (hx : BruhatLE cs x b) (hy : BruhatLE cs y b) :
    entry (cs := cs) (Polynomial.X : Polynomial ℤ) (geometricFunctional (M := M) (cs := cs)) b x y =
      Hecke.rTilde cs x y := by
  apply entry_eq_rTilde _ _ b x y hx hy
  simpa only [geometricFunctional_normalizedRoot] using
    (geometricSlope_injective (M := M) (cs := cs))

end
end KLInvariance.WallDyer

end


section


end

end OAI
