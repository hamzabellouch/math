import OAI.Probability.FKMaps.CanonicalBijection

namespace OAI

noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def spanningGraphRelabel (r a s : Perm (Dart n)) (A : Set (Orbit a)) :
    spanningGraph (relabelPerm r a) (relabelPerm r s) ((relabelOrbit r a) ⁻¹' A) ≃g
      spanningGraph a s A where
  toEquiv := relabelOrbit r s
  map_rel_iff' := by
    intro v w
    change (_≠_ ∧ _) ↔ (_≠_ ∧ _)
    constructor
    · rintro ⟨hne,(⟨d,hd,hv,hw⟩|⟨d,hd,hw,hv⟩)⟩
      · refine ⟨fun h => hne (by rw [h]),Or.inl ⟨r.symm d,?_,?_,?_⟩⟩
        · simpa using hd
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hv
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hw
      · refine ⟨fun h => hne (by rw [h]),Or.inr ⟨r.symm d,?_,?_,?_⟩⟩
        · simpa using hd
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hw
        · apply (relabelOrbit r s).injective
          simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hv
    · rintro ⟨hne,(⟨d,hd,hv,hw⟩|⟨d,hd,hw,hv⟩)⟩
      · refine ⟨fun h => hne ((relabelOrbit r s).injective h),Or.inl ⟨r d,hd,?_,?_⟩⟩
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hv
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hw
      · refine ⟨fun h => hne ((relabelOrbit r s).injective h),Or.inr ⟨r d,hd,?_,?_⟩⟩
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hw
        · simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using congrArg (relabelOrbit r s) hv

lemma mapConditions_relabel (M : LabelledMap n) (r : Perm (Dart n)) :
    MapConditions (relabelPerm r M.val.1,relabelPerm r M.val.2) := by
  refine ⟨relabelPerm_involutive r _ M.property.1,relabelPerm_no_fixed r _ M.property.2.1,?_,?_⟩
  · have hi := spanningGraphRelabel r M.val.1 M.val.2 Set.univ
    have hc := hi.symm.connected_iff.mp M.property.2.2.1
    simpa using hc
  · change Nat.card (Orbit (relabelPerm r M.val.2))+
        Nat.card (Orbit (relabelPerm r M.val.2*relabelPerm r M.val.1))=n+3
    rw [← relabelPerm_mul,card_orbit_relabel,card_orbit_relabel]
    exact M.property.2.2.2

def relabelMap (M : LabelledMap n) (r : Perm (Dart n)) : LabelledMap n :=
  ⟨(relabelPerm r M.val.1,relabelPerm r M.val.2),mapConditions_relabel M r⟩

lemma relabelMap_iso (M : LabelledMap n) (r : Perm (Dart n)) (hr : r 0=0) :
    MapIso (relabelMap M r) M := by
  refine ⟨r,hr,?_,?_⟩ <;> intro d <;>
    simp only [relabelMap,relabelPerm_apply,Equiv.apply_symm_apply]

/-- Actual tree tours put every map/tree pair into the rooted normal form. -/
def canonicalizeTree (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) : CanonicalTreeMap n := by
  let t := M.val.2*partialReversal M.val.1 M.property.1 T
  have ht := treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT
  let r := tourNumbering t ht
  refine ⟨relabelPerm r M.val.1,relabelPerm r M.val.2,relabelEdges r M.val.1 T,
    mapConditions_relabel M r,?_⟩
  rw [partialReversal_relabel r M.val.1 M.property.1 T,← relabelPerm_mul,
    tourNumbering_relabel,formPerm_finRange_eq_rotate]

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma sameCycle_intertwine (a b r : Perm (Dart n))
    (hh : ∀ d,b (r d)=r (a d)) (d e : Dart n) :
    a.SameCycle d e ↔ b.SameCycle (r d) (r e) := by
  have hp (k : ℕ) (x : Dart n) : (b^k) (r x)=r ((a^k) x) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ',pow_succ',mul_apply,mul_apply,ih,hh]
  constructor
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    simp only [zpow_natCast,hp,hk]
  · intro h
    obtain ⟨k,hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k:ℤ),?_⟩
    rw [zpow_natCast]
    apply r.injective
    rwa [← hp]

def isoOrbit (a b r : Perm (Dart n)) (hh : ∀ d,b (r d)=r (a d)) : Orbit a ≃ Orbit b :=
  Quotient.congr r (sameCycle_intertwine a b r hh)

@[simp] lemma isoOrbit_apply (a b r : Perm (Dart n)) (hh : ∀ d,b (r d)=r (a d)) (d : Dart n) :
    isoOrbit a b r hh (orbit a d)=orbit b (r d) := rfl

lemma partialReversal_intertwine (a b r : Perm (Dart n))
    (ha : Function.Involutive a) (hb : Function.Involutive b)
    (hh : ∀ d,b (r d)=r (a d)) (A : Finset (Orbit a)) (B : Finset (Orbit b))
    (hAB : ∀ d,orbit a d∈A ↔ orbit b (r d)∈B) (d : Dart n) :
    partialReversal b hb B (r d)=r (partialReversal a ha A d) := by
  simp only [partialReversal_apply]
  by_cases hd : orbit a d∈A
  · rw [ite_eq_left hd,ite_eq_left ((hAB d).mp hd),hh]
  · rw [ite_eq_right hd,ite_eq_right (fun h => hd ((hAB d).mpr h))]

lemma treeExtension_of_tour (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (h : ∀ d e,(M.val.2*partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    A∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ := by
  apply (mem_treeExtensions ..).mpr
  exact ⟨Finset.empty_subset _,by simp,multiforest_of_tour M A h,
    spanningGraph_connected_of_tour M.val.1 M.val.2 M.property.1 A h⟩

def CanonicalTreeMap.toMap (X : CanonicalTreeMap n) : LabelledMap n :=
  ⟨(X.a,X.s),X.valid⟩

lemma CanonicalTreeMap.tour_connected (X : CanonicalTreeMap n) :
    ∀ d e,(X.s*partialReversal X.a X.valid.1 X.A).SameCycle d e := by
  rw [X.tour]
  intro d e
  exact MapCycles.sameCycle_of_list _ (List.nodup_finRange _) (fun _ _ => rfl)
    (List.mem_finRange d) (List.mem_finRange e)

lemma CanonicalTreeMap.tree (X : CanonicalTreeMap n) :
    X.A∈treeExtensions X.a X.s ∅ Finset.univ := treeExtension_of_tour X.toMap X.A X.tour_connected

/-- Normalization respects a literal rooted map/tree isomorphism. The root
condition removes the cyclic seam ambiguity, rather than dividing by it. -/
lemma canonicalizeTree_of_iso (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (X : CanonicalTreeMap n) (r : Perm (Dart n)) (hr : r 0=0)
    (ha : ∀ d,M.val.1 (r d)=r (X.a d)) (hs : ∀ d,M.val.2 (r d)=r (X.s d))
    (hA : ∀ d,orbit X.a d∈X.A ↔ orbit M.val.1 (r d)∈T) :
    canonicalizeTree M T hT=X := by
  let t := M.val.2*partialReversal M.val.1 M.property.1 T
  have ht := treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT
  have hp : ∀ d,t (r d)=r ((X.s*partialReversal X.a X.valid.1 X.A) d) := by
    intro d
    change M.val.2 (partialReversal M.val.1 M.property.1 T (r d))=_
    rw [partialReversal_intertwine X.a M.val.1 r X.valid.1 M.property.1 ha X.A T hA,hs]
    rfl
  have he : r=tourNumbering t ht := by
    apply tourNumbering_unique t ht r hr
    intro i
    rw [hp,X.tour,formPerm_finRange_eq_rotate]
  have hea : relabelPerm r M.val.1=X.a := by
    apply Equiv.ext
    intro d
    simp only [relabelPerm_apply,ha,Equiv.symm_apply_apply]
  have hes : relabelPerm r M.val.2=X.s := by
    apply Equiv.ext
    intro d
    simp only [relabelPerm_apply,hs,Equiv.symm_apply_apply]
  subst r
  cases X with
  | mk a s A hv htX =>
    dsimp only at hea hes hA
    unfold canonicalizeTree
    dsimp only
    cases hea
    cases hes
    congr 1
    apply Finset.ext
    intro e
    induction e using Quotient.inductionOn with
    | _ d =>
      change orbit (relabelPerm (tourNumbering t ht) M.val.1) d∈relabelEdges (tourNumbering t ht) M.val.1 T ↔ orbit (relabelPerm (tourNumbering t ht) M.val.1) d∈A
      rw [mem_relabelEdges,relabelOrbit_apply]
      exact (hA d).symm

/-- Each rooted isomorphism class has its actual spanning trees as the fibre
of the canonical tree representation (existence half). -/
lemma canonical_root_fiber_surjective (M : LabelledMap n) (X : CanonicalTreeMap n)
    (h : MapIso X.toMap M) :
    ∃ (T : Finset (Orbit M.val.1)) (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ),
      canonicalizeTree M T hT=X := by
  obtain ⟨r,hr,ha,hs⟩ := h
  let e := isoOrbit X.a M.val.1 r ha
  let T := X.A.map e.toEmbedding
  have hA (d : Dart n) : orbit X.a d∈X.A ↔ orbit M.val.1 (r d)∈T := by
    change _ ↔ e (orbit X.a d)∈X.A.map e.toEmbedding
    simp
  have hp (d : Dart n) : (M.val.2*partialReversal M.val.1 M.property.1 T) (r d)=
      r ((X.s*partialReversal X.a X.valid.1 X.A) d) := by
    simp only [mul_apply,partialReversal_intertwine X.a M.val.1 r X.valid.1 M.property.1 ha X.A T hA,hs]
    rfl
  have ht : ∀ d e,(M.val.2*partialReversal M.val.1 M.property.1 T).SameCycle d e := by
    intro d f
    simpa using (sameCycle_intertwine _ _ r hp (r.symm d) (r.symm f)).mp
      (X.tour_connected (r.symm d) (r.symm f))
  have hT := treeExtension_of_tour M T ht
  exact ⟨T,hT,canonicalizeTree_of_iso M T hT X r hr ha hs hA⟩

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma canonicalizeTree_iso (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) :
    MapIso (canonicalizeTree M T hT).toMap M := by
  apply relabelMap_iso M _ (tourNumbering_zero _ _)

lemma canonicalizeTree_class (M : RootedMap n) (T : Finset (Edge M))
    (hT : T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ) :
    (Quotient.mk _ (canonicalizeTree M.out T hT).toMap : RootedMap n)=M := by
  calc
    _=Quotient.mk _ M.out := Quotient.sound (Relation.EqvGen.rel _ _ (canonicalizeTree_iso M.out T hT))
    _=M := Quotient.out_eq M

lemma canonicalizeTree_mem (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) (d : Dart n) :
    orbit (canonicalizeTree M T hT).a d∈(canonicalizeTree M T hT).A ↔
      orbit M.val.1 (tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour _ _ _ _ _ _ hT) d)∈T := by
  exact mem_relabelEdges _ _ _ _

lemma canonicalizeTree_injective (M : LabelledMap n)
    {T U : Finset (Orbit M.val.1)}
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (hU : U∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (hh : canonicalizeTree M T hT=canonicalizeTree M U hU) : T=U := by
  let X := canonicalizeTree M T hT
  let Y := canonicalizeTree M U hU
  let r := tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
    (treeExtension_tour _ _ _ _ _ _ hT)
  let s := tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 U)
    (treeExtension_tour _ _ _ _ _ _ hU)
  have hr : r 0=0 := tourNumbering_zero _ _
  have hs : s 0=0 := tourNumbering_zero _ _
  have hra (d) : M.val.1 (r d)=r (X.a d) := by
    change _=r (relabelPerm r M.val.1 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hrs (d) : M.val.2 (r d)=r (X.s d) := by
    change _=r (relabelPerm r M.val.2 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hsa (d) : M.val.1 (s d)=s (X.a d) := by
    change _=s ((canonicalizeTree M T hT).a d)
    rw [hh]
    change _=s (relabelPerm s M.val.1 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hss (d) : M.val.2 (s d)=s (X.s d) := by
    change _=s ((canonicalizeTree M T hT).s d)
    rw [hh]
    change _=s (relabelPerm s M.val.2 d)
    simp only [relabelPerm_apply,Equiv.apply_symm_apply]
  have hrs' : r=s := root_isomorphism_unique (M:=X.toMap) (N:=M) hr hra hrs hs hsa hss
  apply Finset.ext
  intro e
  induction e using Quotient.inductionOn with
  | _ d =>
    have hm := congrArg (fun W : CanonicalTreeMap n => orbit W.a (r.symm d)∈W.A) hh
    have hm' : (orbit M.val.1 (r (r.symm d))∈T) ↔ (orbit M.val.1 (s (r.symm d))∈U) :=
      (canonicalizeTree_mem M T hT _).symm.trans ((Iff.of_eq hm).trans (canonicalizeTree_mem M U hU _))
    rw [← hrs'] at hm'
    change orbit M.val.1 d∈T ↔ orbit M.val.1 d∈U
    simpa only [Equiv.apply_symm_apply] using hm'

abbrev RootedSpanningTree (n : ℕ) :=
  Σ M : RootedMap n,{T : Finset (Edge M) // T∈treeExtensions (reversal M) (rotation M) ∅ Finset.univ}

def rootedTreeNormal (x : RootedSpanningTree n) : CanonicalTreeMap n :=
  canonicalizeTree x.1.out x.2.val x.2.property

lemma rootedTreeNormal_bijective : Function.Bijective (@rootedTreeNormal n) := by
  constructor
  · intro x y h
    have hM : x.1=y.1 := (canonicalizeTree_class x.1 x.2.val x.2.property).symm.trans
      ((congrArg (fun W => (Quotient.mk _ W.toMap : RootedMap n)) h).trans
        (canonicalizeTree_class y.1 y.2.val y.2.property))
    cases x with
    | mk M T =>
      cases y with
      | mk N U =>
        dsimp only at hM
        subst N
        have hh := canonicalizeTree_injective M.out T.property U.property h
        have he : T=U := Subtype.ext hh
        subst U
        rfl
  · intro X
    let M : RootedMap n := Quotient.mk _ X.toMap
    have hi : MapIso X.toMap M.out := by
      apply mapIso_eqvGen.mp
      exact @Quotient.exact _ (Relation.EqvGen.setoid (@MapIso n)) X.toMap M.out (Quotient.out_eq M).symm
    obtain ⟨T,hT,hh⟩ := canonical_root_fiber_surjective M.out X hi
    exact ⟨⟨M,⟨T,hT⟩⟩,hh⟩

/-- Actual root-isomorphism classes with actual spanning trees, not labelled
objects divided by an unproved automorphism factor. -/
def rootedCanonicalEquiv (n : ℕ) : RootedSpanningTree n ≃ CanonicalTreeMap n :=
  Equiv.ofBijective rootedTreeNormal rootedTreeNormal_bijective

/-- Exact finite rooted-map/spanning-tree to identified-word correspondence. -/
def rootedWordEquiv (n : ℕ) : RootedSpanningTree n ≃ SuccessfulWord n :=
  (rootedCanonicalEquiv n).trans (canonicalWordEquiv n)

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma edge_reachable_rep (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Set (Orbit a)) (d : Dart n) :
    (spanningGraph a s A).Reachable (orbit s (orbit a d).out) (orbit s (a (orbit a d).out)) ↔
      (spanningGraph a s A).Reachable (orbit s d) (orbit s (a d)) := by
  rcases (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl with hh|hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh,ha]
    exact ⟨SimpleGraph.Reachable.symm,SimpleGraph.Reachable.symm⟩

lemma relabelEdges_erase (r a : Perm (Dart n)) (A : Finset (Orbit a))
    (e : Orbit (relabelPerm r a)) :
    relabelEdges r a (A.erase (relabelOrbit r a e))=(relabelEdges r a A).erase e := by
  ext f
  simp only [mem_relabelEdges,Finset.mem_erase]
  exact and_congr_left fun _ => not_congr (relabelOrbit r a).injective.eq_iff

lemma fundamentalCross_relabel (r a s : Perm (Dart n)) (ha : Function.Involutive a)
    (T : Finset (Orbit a)) (e f : Orbit (relabelPerm r a)) :
    FundamentalCross (relabelPerm r a) (relabelPerm r s) (relabelEdges r a T) e f ↔
      FundamentalCross a s T (relabelOrbit r a e) (relabelOrbit r a f) := by
  have hr (A : Finset (Orbit a)) (g : Orbit (relabelPerm r a)) :
      (spanningGraph (relabelPerm r a) (relabelPerm r s) (relabelEdges r a A : Set _)).Reachable
        (orbit (relabelPerm r s) g.out) (orbit (relabelPerm r s) (relabelPerm r a g.out)) ↔
      (spanningGraph a s (A : Set _)).Reachable (orbit s (relabelOrbit r a g).out)
        (orbit s (a (relabelOrbit r a g).out)) := by
    induction g using Quotient.inductionOn with
    | _ d =>
      change (spanningGraph (relabelPerm r a) (relabelPerm r s) (relabelEdges r a A : Set _)).Reachable
        (orbit (relabelPerm r s) (orbit (relabelPerm r a) d).out)
        (orbit (relabelPerm r s) (relabelPerm r a (orbit (relabelPerm r a) d).out)) ↔ (spanningGraph a s (A : Set _)).Reachable
        (orbit s (orbit a (r d)).out) (orbit s (a (orbit a (r d)).out))
      rw [edge_reachable_rep (relabelPerm r a) _ (relabelPerm_involutive r a ha),edge_reachable_rep a s ha]
      have he : (relabelEdges r a A : Set _)=(relabelOrbit r a) ⁻¹' (A : Set _) := by ext x; simp
      rw [he]
      have hh := @SimpleGraph.Iso.reachable_iff _ _ _ _ (spanningGraphRelabel r a s (A : Set _))
        (orbit (relabelPerm r s) d) (orbit (relabelPerm r s) (relabelPerm r a d))
      change (spanningGraph a s (A : Set _)).Reachable
        (relabelOrbit r s (orbit (relabelPerm r s) d))
        (relabelOrbit r s (orbit (relabelPerm r s) (relabelPerm r a d))) ↔ _ at hh
      simpa only [relabelOrbit_apply,relabelPerm_apply,Equiv.apply_symm_apply] using hh.symm
  unfold FundamentalCross
  rw [mem_relabelEdges,mem_relabelEdges,← relabelEdges_erase,← relabelEdges_erase,hr,hr]

lemma edgeFirst_rep (a p : Perm (Dart n)) (ha : Function.Involutive a)
    (hp : ∀ d e,p.SameCycle d e) (d : Dart n) :
    edgeFirst a p hp (orbit a d)=min ((tourNumbering p hp).symm d).val
      ((tourNumbering p hp).symm (a d)).val := by
  unfold edgeFirst
  rcases (MapFinite.mk_eq_iff_involution a ha d (orbit a d)).mp rfl with hh|hh
  · conv_rhs => rw [hh]
  · conv_rhs => rw [hh,ha]
    exact min_comm _ _

lemma canonicalizeTree_rank (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ)
    (e : Orbit (canonicalizeTree M T hT).a) :
    edgeFirst (canonicalizeTree M T hT).a
      ((canonicalizeTree M T hT).s*partialReversal _ (canonicalizeTree M T hT).valid.1
        (canonicalizeTree M T hT).A) (canonicalizeTree M T hT).tour_connected e =
    edgeFirst M.val.1 (M.val.2*partialReversal M.val.1 M.property.1 T)
      (treeExtension_tour _ _ _ _ _ _ hT)
      (relabelOrbit (tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour _ _ _ _ _ _ hT)) M.val.1 e) := by
  let p := M.val.2*partialReversal M.val.1 M.property.1 T
  let hp := treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT
  let r := tourNumbering p hp
  let X := canonicalizeTree M T hT
  induction e using Quotient.inductionOn with
  | _ d =>
    have hh := edgeFirst_rep X.a (X.s*partialReversal X.a X.valid.1 X.A)
      X.valid.1 X.tour_connected d
    rw [canonical_tourNumbering _ _ X.tour] at hh
    change edgeFirst X.a (X.s*partialReversal X.a X.valid.1 X.A) X.tour_connected (orbit X.a d)=_
    rw [hh]
    change min d.val ((relabelPerm r M.val.1) d).val = edgeFirst M.val.1 p hp (orbit M.val.1 (r d))
    rw [edgeFirst_rep M.val.1 p M.property.1]
    change min d.val (r.symm (M.val.1 (r d))).val=min (r.symm (r d)).val (r.symm (M.val.1 (r d))).val
    rw [Equiv.symm_apply_apply]

/-- Forced FK exponents are unchanged by the true rooted normal form. -/
theorem canonicalizeTree_activity (M : LabelledMap n) (T : Finset (Orbit M.val.1))
    (hT : T∈treeExtensions M.val.1 M.val.2 ∅ Finset.univ) :
    explorationActivity (canonicalizeTree M T hT).a (canonicalizeTree M T hT).s
      (tourSelector (canonicalizeTree M T hT).a (canonicalizeTree M T hT).s (canonicalizeTree M T hT).valid.1) ∅ Finset.univ
      (canonicalizeTree M T hT).A (Fintype.card (Orbit (canonicalizeTree M T hT).a)) =
    explorationActivity M.val.1 M.val.2 (tourSelector M.val.1 M.val.2 M.property.1) ∅ Finset.univ
      T (Fintype.card (Orbit M.val.1)) := by
  let X := canonicalizeTree M T hT
  let r := tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
    (treeExtension_tour _ _ _ _ _ _ hT)
  rw [tourActivity_eq_card _ _ X.valid.1 _ X.tree,tourActivity_eq_card _ _ M.property.1 _ hT]
  apply Finset.card_equiv (relabelOrbit r M.val.1)
  intro e
  change Orbit X.a at e
  change (e∈Finset.univ.filter (OrderedActive X.a X.s X.A
    (edgeFirst X.a (X.s*partialReversal X.a X.valid.1 X.A) X.tour_connected))) ↔
    ((relabelOrbit r M.val.1 e)∈Finset.univ.filter (OrderedActive M.val.1 M.val.2 T
      (edgeFirst M.val.1 (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT))))
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  unfold OrderedActive
  constructor
  · intro h f hlt
    have hf := h ((relabelOrbit r M.val.1).symm f)
    rw [canonicalizeTree_rank M T hT e] at hf
    have hrr := canonicalizeTree_rank M T hT ((relabelOrbit r M.val.1).symm f)
    rw [hrr] at hf
    have hef : relabelOrbit (tourNumbering (M.val.2*partialReversal M.val.1 M.property.1 T)
        (treeExtension_tour M.val.1 M.val.2 M.property.1 ∅ Finset.univ T hT)) M.val.1
        ((relabelOrbit r M.val.1).symm f)=f := (relabelOrbit r M.val.1).apply_symm_apply f
    rw [hef] at hf
    exact fun hh => hf hlt ((fundamentalCross_relabel r M.val.1 M.val.2 M.property.1 T e _).mpr
      (by simpa only [Equiv.apply_symm_apply] using hh))
  · intro h f hlt
    rw [canonicalizeTree_rank M T hT e,canonicalizeTree_rank M T hT f] at hlt
    exact fun hh => h _ hlt ((fundamentalCross_relabel r M.val.1 M.val.2 M.property.1 T e f).mp hh)

end FKCRT
end

end OAI
