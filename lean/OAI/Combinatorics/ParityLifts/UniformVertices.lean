import OAI.Combinatorics.ParityLifts.UniformData

namespace OAI

namespace ParityWL.Complexity
open Classical

lemma tagCharge_false (t : ℕ) : tagCharge t false=(fun _ => 0) := by
  funext a
  simp [tagCharge,rawCharge]

lemma tagCharge_true (t : ℕ) : tagCharge t true=starParity t := by
  funext a
  cases a with
  | inl i =>
    have he : (∃ j : Fin t, j.val=0 ∧ (Sum.inl i : TemplateVertex t)=.inl j) ↔ i.val=0 := by simp
    simp only [tagCharge,rawCharge,rawRole,Bool.true_and,decide_eq_true_eq,Prod.mk.injEq,
      and_self,starParity,he]
    split <;> simp
  | inr h =>
    have hn : h.1.1.1.1.val≠h.1.1.1.2.val := ne_of_lt h.1.1.2
    have hz : (h.1.1.1.1.val,h.1.1.1.2.val,h.1.2.val)≠(0,0,0) := by
      intro he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg (fun x : RawRole => x.2.1) he
      exact hn (h1.trans h2.symm)
    simp [tagCharge,rawCharge,rawRole,hz,starParity]

lemma bit_eq_iff_one (x y : Bit) : x=y ↔ (x=1 ↔ y=1) := by
  rcases bit_zero_or_one x with hx | hx <;>
    rcases bit_zero_or_one y with hy | hy <;> simp [hx,hy]

def rawTagTest (x y : RawTag) : Bool :=
  rawAdjacent x.1 y.1 && decide ((y.1∈x.2) ↔ (x.1∈y.2))

lemma rawTagTest_encode {t : ℕ} (odd : Bool) (x y : GlobalTag t (tagCharge t odd)) :
    rawTagTest (rawTagEncode odd x) (rawTagEncode odd y)=tagTest (tagCharge t odd) x y := by
  apply Bool.eq_iff_iff.mpr
  change (rawAdjacent (rawRole x.1) (rawRole y.1) &&
    decide ((rawRole y.1∈tagOnes x.1 x.2.val) ↔ (rawRole x.1∈tagOnes y.1 y.2.val)))=true ↔ _
  rw [Bool.and_eq_true,rawAdjacent_iff,decide_eq_true_eq]
  by_cases h : (template t).Adj x.1 y.1
  · have hx := mem_tagOnes x.1 x.2.val ⟨y.1,h⟩
    have hy := mem_tagOnes y.1 y.2.val ⟨x.1,h.symm⟩
    simp only [h,true_and,tagTest,↓reduceDIte,decide_eq_true_eq]
    exact (iff_congr hx hy).trans (bit_eq_iff_one _ _).symm
  · simp only [h,false_and,tagTest,↓reduceDIte,Bool.false_eq_true]

abbrev RawVertex := RawTag × ℕ

def rawVertices (D : RawChoiceData) (tags : List RawTag) : List RawVertex :=
  tags.flatMap (fun z => (List.range (D.roleSize z.1)).map (z,·))

lemma mem_rawVertices (D : RawChoiceData) (tags : List RawTag) (x : RawVertex) :
    x∈rawVertices D tags ↔ x.1∈tags ∧ x.2<D.roleSize x.1.1 := by
  rcases x with ⟨z,d⟩
  simp only [rawVertices,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨y,hy,e,he,hyz,hed⟩
    subst y; subst e
    exact ⟨hy,he⟩
  · rintro ⟨hz,hd⟩
    exact ⟨z,hz,d,hd,rfl,rfl⟩

lemma rawVertices_nodup (D : RawChoiceData) (tags : List RawTag) (hs : tags.Nodup) :
    (rawVertices D tags).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro z _
    exact List.nodup_range.map (fun _ _ h => congrArg Prod.snd h)
  · apply hs.imp
    intro z w hzw x hx hy
    obtain ⟨d,_,he⟩ := List.mem_map.mp hx
    obtain ⟨e,_,hf⟩ := List.mem_map.mp hy
    exact hzw ((congrArg Prod.fst he).trans (congrArg Prod.fst hf).symm)

noncomputable def rawVertexEncode {t : ℕ} (D : ChoiceData t) (odd : Bool)
    (x : (z : GlobalTag t (tagCharge t odd)) × Fin (D.roleSize z.1)) : RawVertex :=
  (rawTagEncode odd x.1,x.2.val)

lemma rawVertexEncode_mem {t : ℕ} (D : ChoiceData t) (odd : Bool)
    (x : (z : GlobalTag t (tagCharge t odd)) × Fin (D.roleSize z.1)) :
    rawVertexEncode D odd x∈rawVertices D.raw (rawTags t odd) := by
  rw [mem_rawVertices]
  refine ⟨rawTagEncode_mem odd x.1,?_⟩
  change x.2.val<D.raw.roleSize (rawRole x.1.1)
  rw [D.raw_roleSize]
  exact x.2.isLt

lemma rawVertexEncode_injective {t : ℕ} (D : ChoiceData t) (odd : Bool) :
    Function.Injective (rawVertexEncode D odd) := by
  rintro ⟨z,d⟩ ⟨w,e⟩ he
  have hzw := rawTagEncode_injective t odd (congrArg Prod.fst he)
  change z=w at hzw
  subst w
  have hde : d=e := Fin.ext (congrArg Prod.snd he)
  cases hde
  rfl

noncomputable def rawVertexEquiv {t : ℕ} (D : ChoiceData t) (odd : Bool) :
    ((z : GlobalTag t (tagCharge t odd)) × Fin (D.roleSize z.1)) ≃
      {x // x∈rawVertices D.raw (rawTags t odd)} :=
  Equiv.ofBijective (fun x => ⟨rawVertexEncode D odd x,rawVertexEncode_mem D odd x⟩) ⟨by
    intro x y h
    exact rawVertexEncode_injective D odd (congrArg Subtype.val h),by
    rintro ⟨⟨z,d⟩,hd⟩
    have hz := (mem_rawVertices D.raw (rawTags t odd) (z,d)).mp hd
    let w := (rawTagEquiv t odd).symm ⟨z,hz.1⟩
    have hw : rawTagEncode odd w=z := congrArg Subtype.val ((rawTagEquiv t odd).apply_symm_apply ⟨z,hz.1⟩)
    have hrole : rawRole w.1=z.1 := congrArg Prod.fst hw
    have hsize : D.roleSize w.1=D.raw.roleSize z.1 := by rw [←D.raw_roleSize,hrole]
    refine ⟨⟨w,⟨d,by rw [hsize]; exact hz.2⟩⟩,?_⟩
    apply Subtype.ext
    change (rawTagEncode odd w,d)=(z,d)
    rw [hw]⟩

noncomputable def rawIndexEquiv {t : ℕ} (D : ChoiceData t) (odd : Bool) :
    Fin (rawVertices D.raw (rawTags t odd)).length ≃
      LiftVertex (template t) (baseGraph D.system) (baseProjection D.system) (tagCharge t odd) :=
  (List.Nodup.getEquiv _ (rawVertices_nodup D.raw _ (rawTags_nodup t odd))).trans
    ((rawVertexEquiv D odd).symm.trans (D.globalLiftEquiv (tagCharge t odd)))

noncomputable def rawIndexedGraph {t : ℕ} (D : ChoiceData t) (odd : Bool) :
    SimpleGraph (Fin (rawVertices D.raw (rawTags t odd)).length) :=
  (liftGraph (template t) (baseGraph D.system) (baseProjection D.system) (tagCharge t odd)).comap
    (rawIndexEquiv D odd)

noncomputable def rawIndexedIso {t : ℕ} (D : ChoiceData t) (odd : Bool) :
    rawIndexedGraph D odd ≃g liftGraph (template t) (baseGraph D.system) (baseProjection D.system) (tagCharge t odd) :=
  SimpleGraph.Iso.comap (rawIndexEquiv D odd) _

def rawEdgeTest (D : RawChoiceData) (x y : RawVertex) : Bool :=
  D.baseTest x.1.1 x.2 y.1.1 y.2 && rawTagTest x.1 y.1

lemma rawEdgeTest_encode {t : ℕ} (D : ChoiceData t) (odd : Bool)
    (x y : (z : GlobalTag t (tagCharge t odd)) × Fin (D.roleSize z.1)) :
    rawEdgeTest D.raw (rawVertexEncode D odd x) (rawVertexEncode D odd y)=true ↔
    (liftGraph (template t) (baseGraph D.system) (baseProjection D.system) (tagCharge t odd)).Adj
      (D.globalLiftEquiv (tagCharge t odd) x) (D.globalLiftEquiv (tagCharge t odd) y) := by
  rw [D.lift_arc_iff]
  obtain ⟨hx,hxi⟩ := D.globalLift_raw (tagCharge t odd) x
  obtain ⟨hy,hyi⟩ := D.globalLift_raw (tagCharge t odd) y
  have hx' := congrArg Sigma.fst hx
  have hy' := congrArg Sigma.fst hy
  have htag := rawTagTest_encode odd x.1 y.1
  dsimp only [rawTagEncode] at htag
  dsimp only at hx' hy'
  simp only [rawEdgeTest,rawVertexEncode,rawTagEncode,D.raw_baseTest,Bool.and_eq_true,
    hx,hy,hx',hy',hxi,hyi,htag]

end ParityWL.Complexity

end OAI
