import Mathlib

namespace OAI

open Set Function Topology
noncomputable section
open Set Function
open scoped unitInterval
namespace PresentationVanKampen

def intervalPath (a b : I) : Path a b where
  toFun t := ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ),
    (convex_Icc (0 : ℝ) 1) a.property b.property
      (by linarith [t.property.2]) t.property.1 (by ring)⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

@[simp] theorem intervalPath_self (a : I) : intervalPath a a = Path.refl a := by
  ext t
  change (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (a : ℝ) = (a : ℝ)
  ring

@[simp] theorem intervalPath_zero_one : intervalPath 0 1 = Path.id := by
  ext t
  simp [intervalPath]

theorem intervalPath_mem {a b : I} (hab : a ≤ b) (t : I) :
    intervalPath a b t ∈ Icc a b := by
  constructor
  · change (a : ℝ) ≤ (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ)
    have := mul_nonneg t.property.1 (sub_nonneg.mpr hab)
    nlinarith
  · change (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) ≤ (b : ℝ)
    have := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hab)
    nlinarith

variable {X : Type*} [TopologicalSpace X] {x y : X}

def portion (p : Path x y) (a b : I) : Path (p a) (p b) :=
  (intervalPath a b).map p.continuous

@[simp] theorem portion_self (p : Path x y) (a : I) :
    portion p a a = Path.refl (p a) := by
  ext t
  simp [portion]

theorem portion_trans (p : Path x y) (a b c : I) :
    ((portion p a b).trans (portion p b c)).Homotopic (portion p a c) := by
  let : ContractibleSpace I := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  have h := (SimplyConnectedSpace.paths_homotopic
    ((intervalPath a b).trans (intervalPath b c)) (intervalPath a c)).map p.toContinuousMap
  simpa only [portion, Path.map_trans] using h

theorem portion_mem {p : Path x y} {a b : I} (hab : a ≤ b)
    {s : Set X} (h : Icc a b ⊆ p ⁻¹' s) :
    Set.range (portion p a b) ⊆ s := by
  rintro _ ⟨t, rfl⟩
  exact h (intervalPath_mem hab t)

theorem path_induction_open_cover {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (P : ∀ {a b : X}, Path a b → Prop)
    (hrefl : ∀ a, P (Path.refl a))
    (htrans : ∀ {a b c} (p : Path a b) (q : Path b c), P p → P q → P (p.trans q))
    (hhom : ∀ {a b} (p q : Path a b), p.Homotopic q → P p → P q)
    (hlocal : ∀ {a b} (p : Path a b) i, Set.range p ⊆ U i → P p)
    (p : Path x y) : P p := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (by intro a _; simpa only [mem_iUnion, mem_preimage] using hcover (mem_univ (p a)))
  have hall : ∀ j, P (portion p (t 0) (t j)) := by
    intro j
    induction j with
    | zero => simpa only [portion_self] using hrefl (p (t 0))
    | succ j ih =>
      obtain ⟨i, hi⟩ := hsub j
      exact hhom _ _ (portion_trans p _ _ _) (htrans _ _ ih
        (hlocal _ i (portion_mem (hmono (Nat.le_succ j)) hi)))
  have hh := hall n
  rw [ht0, hn n le_rfl] at hh
  have heq : (portion p 0 1).cast p.source.symm p.target.symm = p := by
    ext a
    change p (intervalPath 0 1 a) = p a
    rw [intervalPath_zero_one]
    rfl
  have hcast : ∀ {a b a' b' : X} (q : Path a b) (ha : a' = a) (hb : b' = b),
      P q → P (q.cast ha hb) := by
    intro a b a' b' q ha hb
    subst a'; subst b'
    exact id
  have hh' := hcast _ p.source.symm p.target.symm hh
  rwa [heq] at hh' 

def basedPathClass (b : X) (s : ∀ a : X, Path b a)
    {a c : X} (p : Path a c) : FundamentalGroup X b :=
  (Path.Homotopic.Quotient.mk (s a)).trans
    ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk (s c)).symm)

@[simp] theorem basedPathClass_refl (b : X) (s : ∀ a : X, Path b a) (a : X) :
    basedPathClass b s (Path.refl a) = 1 := by
  simp only [basedPathClass, Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_symm]
  rfl

theorem basedPathClass_trans (b : X) (s : ∀ a : X, Path b a)
    {a c d : X} (p : Path a c) (q : Path c d) :
    basedPathClass b s (p.trans q) = basedPathClass b s q * basedPathClass b s p := by
  simp only [basedPathClass, FundamentalGroup.mul_def, Path.Homotopic.Quotient.mk_trans]
  simp only [Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk (s c)).symm,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

theorem basedPathClass_homotopic (b : X) (s : ∀ a : X, Path b a)
    {a c : X} (p q : Path a c) (h : p.Homotopic q) :
    basedPathClass b s p = basedPathClass b s q := by
  have hh : Path.Homotopic.Quotient.mk p = Path.Homotopic.Quotient.mk q := Quotient.sound h
  simp only [basedPathClass, hh]

theorem basedPathClass_loop (b : X) (s : ∀ a : X, Path b a)
    (hs : (s b).Homotopic (Path.refl b)) (p : Path b b) :
    basedPathClass b s p = Path.Homotopic.Quotient.mk p := by
  have hh : Path.Homotopic.Quotient.mk (s b) = Path.Homotopic.Quotient.refl b :=
    Quotient.sound hs
  simp only [basedPathClass, hh, Path.Homotopic.Quotient.refl_trans]
  have hr : (Path.Homotopic.Quotient.refl b).symm = Path.Homotopic.Quotient.refl b := rfl
  rw [hr, Path.Homotopic.Quotient.trans_refl]

theorem subgroup_eq_top_of_open_cover {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : univ ⊆ ⋃ i, U i)
    (b : X) (s : ∀ a : X, Path b a) (hs : (s b).Homotopic (Path.refl b))
    (H : Subgroup (FundamentalGroup X b))
    (hlocal : ∀ {a c} (p : Path a c) i, Set.range p ⊆ U i → basedPathClass b s p ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  rw [← basedPathClass_loop b s hs p]
  apply path_induction_open_cover U hU hcover (fun p => basedPathClass b s p ∈ H)
    (fun a => by rw [basedPathClass_refl]; exact H.one_mem)
  · intro a c d p q hp hq
    rw [basedPathClass_trans]
    exact H.mul_mem hq hp
  · intro a c p q hpq hp
    rwa [← basedPathClass_homotopic b s p q hpq]
  · exact hlocal

def pathIn {a c : X} (p : Path a c) {U : Set X} (h : Set.range p ⊆ U) :
    Path (⟨a, h p.source_mem_range⟩ : U) ⟨c, h p.target_mem_range⟩ where
  toFun t := ⟨p t, h ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem pathIn_map {a c : X} (p : Path a c) {U : Set X}
    (h : Set.range p ⊆ U) :
    (pathIn p h).map continuous_subtype_val = p := by ext t; rfl

theorem homotopic_in_simplyConnected {U : Set X} [SimplyConnectedSpace U]
    {a c : X} (p q : Path a c) (hp : Set.range p ⊆ U) (hq : Set.range q ⊆ U) :
    p.Homotopic q := by
  have h := (SimplyConnectedSpace.paths_homotopic (pathIn p hp) (pathIn q hq)).map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
  simpa only [pathIn_map] using h

def Replaceable (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} (p : Path a c) : Prop :=
  ∃ q : Path (r a : X) (r c : X), Set.range q ⊆ U ∧
    ((spoke a).trans p).Homotopic (q.trans (spoke c))

theorem replaceable_refl (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    (a : X) : Replaceable U r spoke (Path.refl a) := by
  refine ⟨Path.refl (r a : X), ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩; exact (r a).property
  · exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans _).symm

theorem replaceable_trans (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c d : X} {p : Path a c} {q : Path c d}
    (hp : Replaceable U r spoke p) (hq : Replaceable U r spoke q) :
    Replaceable U r spoke (p.trans q) := by
  obtain ⟨p', hp', hpp'⟩ := hp
  obtain ⟨q', hq', hqq'⟩ := hq
  refine ⟨p'.trans q', ?_, ?_⟩
  · simpa only [Path.trans_range] using union_subset hp' hq'
  · exact (Path.Homotopic.trans_assoc _ _ _).symm |>.trans
      (hpp'.hcomp (Path.Homotopic.refl q)) |>.trans
      (Path.Homotopic.trans_assoc _ _ _) |>.trans
      ((Path.Homotopic.refl p').hcomp hqq') |>.trans
      (Path.Homotopic.trans_assoc _ _ _).symm

theorem replaceable_homotopic (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} {p q : Path a c} (hpq : p.Homotopic q) (hp : Replaceable U r spoke p) :
    Replaceable U r spoke q := by
  obtain ⟨p', hp', hpp'⟩ := hp
  exact ⟨p', hp', ((Path.Homotopic.refl (spoke a)).hcomp hpq).symm.trans hpp'⟩

theorem replaceable_of_range_subset (U : Set X) (r : X → U)
    (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} (p : Path a c) (hp : Set.range p ⊆ U)
    (ha : Set.range (spoke a) ⊆ U) (hc : Set.range (spoke c) ⊆ U) :
    Replaceable U r spoke p := by
  refine ⟨((spoke a).trans p).trans (spoke c).symm, ?_, ?_⟩
  · simpa only [Path.trans_range, Path.symm_range] using union_subset (union_subset ha hp) hc
  · apply Path.Homotopic.symm
    exact (Path.Homotopic.trans_assoc _ _ _).trans
      ((Path.Homotopic.refl _).hcomp (Path.Homotopic.symm_trans _)) |>.trans
      (Path.Homotopic.trans_refl _)

theorem replaceable_of_simplyConnected (U V : Set X) [SimplyConnectedSpace V]
    (hUV : IsPathConnected (U ∩ V)) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    {a c : X} (p : Path a c) (hp : Set.range p ⊆ V)
    (ha : Set.range (spoke a) ⊆ V) (hc : Set.range (spoke c) ⊆ V) :
    Replaceable U r spoke p := by
  have hpath := hUV.joinedIn (r a : X) ⟨(r a).property, ha (spoke a).source_mem_range⟩
    (r c : X) ⟨(r c).property, hc (spoke c).source_mem_range⟩
  refine ⟨hpath.somePath, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩; exact (hpath.somePath_mem t).1
  · apply homotopic_in_simplyConnected (U := V)
    · simpa only [Path.trans_range] using union_subset ha hp
    · rw [Path.trans_range]
      refine union_subset ?_ hc
      rintro _ ⟨t, rfl⟩; exact (hpath.somePath_mem t).2

theorem replaceable_of_open_cover {ι : Type*} (O : ι → Set X)
    (hO : ∀ i, IsOpen (O i)) (hcover : univ ⊆ ⋃ i, O i)
    (U : Set X) (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    (hlocal : ∀ {a c} (p : Path a c) i, Set.range p ⊆ O i → Replaceable U r spoke p)
    {a c : X} (p : Path a c) : Replaceable U r spoke p :=
  path_induction_open_cover O hO hcover (Replaceable U r spoke)
    (replaceable_refl U r spoke) (fun _ _ hp hq => replaceable_trans U r spoke hp hq)
    (fun _ _ hpq hp => replaceable_homotopic U r spoke hpq hp) hlocal p

theorem cancel_spoke {a c ra rc : X} (sa : Path ra a) (sc : Path rc c)
    (p : Path a c) (q : Path ra rc) (h : (sa.trans p).Homotopic (q.trans sc)) :
    p.Homotopic ((sa.symm.trans q).trans sc) := by
  exact (Path.Homotopic.refl_trans p).symm |>.trans
    (((Path.Homotopic.symm_trans sa).hcomp (Path.Homotopic.refl p)).symm) |>.trans
    (Path.Homotopic.trans_assoc _ _ _) |>.trans
    ((Path.Homotopic.refl sa.symm).hcomp h) |>.trans
    (Path.Homotopic.trans_assoc _ _ _).symm

theorem fundamentalGroupMap_surjective_of_open_cover
    {ι : Type*} (U : Set X) (V : ι → Set X)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : U ∪ ⋃ i, V i = univ)
    (hUV : ∀ i, IsPathConnected (U ∩ V i))
    (hsc : ∀ i, SimplyConnectedSpace (V i))
    (r : X → U) (spoke : ∀ a : X, Path (r a : X) a)
    (hspU : ∀ a ∈ U, Set.range (spoke a) ⊆ U)
    (hspV : ∀ i a, a ∈ V i → Set.range (spoke a) ⊆ V i)
    (b : U) : Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) b) := by
  let O : Option ι → Set X := fun i => i.elim U V
  have hO : ∀ i, IsOpen (O i) := by intro i; cases i <;> simp [O, hU, hV]
  have hcov : univ ⊆ ⋃ i, O i := by
    intro x _
    have hx : x ∈ U ∪ ⋃ i, V i := by rw [hcover]; trivial
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · rcases mem_iUnion.mp hx with ⟨i, hi⟩
      exact mem_iUnion.mpr ⟨some i, hi⟩
  have hp : ∀ {a c} (p : Path a c), Replaceable U r spoke p := by
    intro a c p
    apply replaceable_of_open_cover O hO hcov U r spoke _ p
    intro a c p i hi
    cases i with
    | none =>
      exact replaceable_of_range_subset U r spoke p hi
        (hspU a (hi p.source_mem_range)) (hspU c (hi p.target_mem_range))
    | some i =>
      let := hsc i
      exact replaceable_of_simplyConnected U (V i) (hUV i) r spoke p hi
        (hspV i a (hi p.source_mem_range)) (hspV i c (hi p.target_mem_range))
  intro g
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  obtain ⟨q, hq, hh⟩ := hp p
  let p' := ((spoke (b : X)).symm.trans q).trans (spoke (b : X))
  have hp' : Set.range p' ⊆ U := by
    have hs := hspU b b.property
    simpa only [p', Path.trans_range, Path.symm_range] using
      union_subset (union_subset hs hq) hs
  refine ⟨Path.Homotopic.Quotient.mk (pathIn p' hp'), ?_⟩
  change Path.Homotopic.Quotient.mk ((pathIn p' hp').map continuous_subtype_val) =
    Path.Homotopic.Quotient.mk p
  rw [pathIn_map]
  exact Quotient.sound (cancel_spoke _ _ _ _ hh).symm

theorem exists_compatible_spokes {ι : Type*} (U : Set X) (V : ι → Set X)
    (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise (Disjoint on V))
    (hUV : ∀ i, (U ∩ V i).Nonempty)
    (hpc : ∀ i, IsPathConnected (V i)) :
    ∃ (r : X → U) (spoke : ∀ a : X, Path (r a : X) a),
      (∀ a ∈ U, Set.range (spoke a) ⊆ U) ∧
      (∀ i a, a ∈ V i → Set.range (spoke a) ⊆ V i) := by
  classical
  have hpoint : ∀ a : X, ∃ u : U, ∃ p : Path (u : X) a,
      (a ∈ U → Set.range p ⊆ U) ∧
      (∀ i, a ∈ V i → Set.range p ⊆ V i) := by
    intro a
    by_cases ha : a ∈ U
    · refine ⟨⟨a, ha⟩, Path.refl a, ?_, ?_⟩
      · intro _ z hz; obtain ⟨t, rfl⟩ := hz; exact ha
      · intro i hi z hz; obtain ⟨t, rfl⟩ := hz; exact hi
    · have hac : a ∈ U ∪ ⋃ i, V i := by rw [hcover]; trivial
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hac.resolve_left ha)
      obtain ⟨u, huU, huV⟩ := hUV i
      let hpath := (hpc i).joinedIn u huV a hi
      refine ⟨⟨u, huU⟩, hpath.somePath, fun h => False.elim (ha h), ?_⟩
      intro j hj z hz
      have hij : i = j := by
        by_contra hij
        exact Set.disjoint_left.mp (hdisj hij) hi hj
      subst j
      obtain ⟨t, rfl⟩ := hz
      exact hpath.somePath_mem t
  choose r spoke hU hV using hpoint
  exact ⟨r, spoke, hU, fun i a => hV a i⟩

theorem fundamentalGroupMap_surjective_of_disjoint_open_cover
    {ι : Type*} (U : Set X) (V : ι → Set X)
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : U ∪ ⋃ i, V i = univ)
    (hdisj : Pairwise (Disjoint on V))
    (hUV : ∀ i, IsPathConnected (U ∩ V i))
    (hsc : ∀ i, SimplyConnectedSpace (V i)) (b : U) :
    Function.Surjective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) b) := by
  obtain ⟨r, spoke, hsU, hsV⟩ := exists_compatible_spokes U V hcover hdisj
    (fun i => (hUV i).nonempty) (fun i => by
      let := hsc i
      exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance)
  exact fundamentalGroupMap_surjective_of_open_cover U V hU hV hcover hUV hsc
    r spoke hsU hsV b

end PresentationVanKampen

end

end OAI
