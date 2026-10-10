import Mathlib
import OAI.Probability.UnimodularPercolation.Subdivision.Graph

namespace OAI

/-! Coupling percolation on a graph with percolation on its subdivision. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


 

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def halfBit (G : BondGraph V E) : SubdivisionEdge G ↪ E × Bool := by
  classical
  refine ⟨fun ev => (ev.val.1,if ev.val.2 = (G ev.val.1).out.1 then false else true),?_⟩
  rintro ⟨⟨e,x⟩,hx⟩ ⟨⟨f,y⟩,hy⟩ h
  have hef : e = f := congrArg Prod.fst h
  subst f
  have hb := congrArg Prod.snd h
  dsimp only at hb
  have he : G e = s((G e).out.1,(G e).out.2) := (G e).out_eq.symm
  have hx' : x = (G e).out.1 ∨ x = (G e).out.2 := by
    apply Sym2.mem_iff.mp
    rw [←he]
    exact hx
  have hy' : y = (G e).out.1 ∨ y = (G e).out.2 := by
    apply Sym2.mem_iff.mp
    rw [←he]
    exact hy
  have hxy : x = y := by
    by_cases h₁ : x = (G e).out.1 <;> by_cases h₂ : y = (G e).out.1
    · exact h₁.trans h₂.symm
    · simp only [ite_eq_left h₁,ite_eq_right h₂,Bool.false_eq_true] at hb
    · simp only [ite_eq_right h₁,ite_eq_left h₂,Bool.true_eq_false] at hb
    · exact (hx'.resolve_left h₁).trans (hy'.resolve_left h₂).symm
  subst y
  rfl

def seriesOpen (ν : Set (E × Bool)) : Set E := {e | ∀ b, (e,b) ∈ ν}

noncomputable def subdivisionOpen (G : BondGraph V E) (ν : Set (E × Bool)) :
    Set (SubdivisionEdge G) := halfBit G ⁻¹' ν

@[simp] theorem halfBit_fst (G : BondGraph V E) (e : SubdivisionEdge G) :
    (halfBit G e).1 = e.val.1 := rfl

 
theorem seriesOpen_of_two_incident (G : BondGraph V E) (ν : Set (E × Bool))
    (e : E) (x y : V) (hx : x ∈ G e) (hy : y ∈ G e) (hne : x ≠ y)
    (hxo : (⟨(e,x),hx⟩ : SubdivisionEdge G) ∈ subdivisionOpen G ν)
    (hyo : (⟨(e,y),hy⟩ : SubdivisionEdge G) ∈ subdivisionOpen G ν) :
    e ∈ seriesOpen ν := by
  have hbits : (halfBit G ⟨(e,x),hx⟩).2 ≠ (halfBit G ⟨(e,y),hy⟩).2 := by
    intro h
    have hh : halfBit G ⟨(e,x),hx⟩ = halfBit G ⟨(e,y),hy⟩ := Prod.ext rfl h
    have he := (halfBit G).injective hh
    exact hne (congrArg (fun z : SubdivisionEdge G => z.val.2) he)
  intro b
  have hb : b = (halfBit G ⟨(e,x),hx⟩).2 ∨ b = (halfBit G ⟨(e,y),hy⟩).2 := by
    generalize (halfBit G ⟨(e,x),hx⟩).2 = c at *
    generalize (halfBit G ⟨(e,y),hy⟩).2 = d at *
    cases b <;> cases c <;> cases d <;> simp_all
  rcases hb with rfl | rfl
  · exact hxo
  · exact hyo

 
theorem subdivision_open_adj_iff (G : BondGraph V E) (ν : Set (E × Bool)) (x : V) (e : E) :
    (∃ d ∈ subdivisionOpen G ν, subdivision G d = s(Sum.inl x, Sum.inr e)) ↔
      ∃ hx : x ∈ G e, (⟨(e,x),hx⟩ : SubdivisionEdge G) ∈ subdivisionOpen G ν := by
  constructor
  · rintro ⟨⟨⟨f,y⟩,hy⟩,ho,he⟩
    simp only [subdivision,Sym2.eq_iff] at he
    rcases he with ⟨hyx,hfe⟩ | ⟨hbad,_⟩
    · have : y = x := Sum.inl.inj hyx
      have : f = e := Sum.inr.inj hfe
      subst y; subst f
      exact ⟨hy,ho⟩
    · cases hbad
  · rintro ⟨hx,ho⟩
    exact ⟨⟨(e,x),hx⟩,ho,rfl⟩

 
theorem conn_subdivision_iff (G : BondGraph V E) (ν : Set (E × Bool)) (x y : V) :
    Conn (subdivision G) (subdivisionOpen G ν) (.inl x) (.inl y) ↔
      Conn G (seriesOpen ν) x y := by
  constructor
  · intro hc
    have reach (z : V ⊕ E) (h : Conn (subdivision G) (subdivisionOpen G ν) (.inl x) z) :
        match z with
        | .inl w => Conn G (seriesOpen ν) x w
        | .inr e => ∃ w : V, ∃ hw : w ∈ G e,
            (⟨(e,w),hw⟩ : SubdivisionEdge G) ∈ subdivisionOpen G ν ∧ Conn G (seriesOpen ν) x w := by
      induction h with
      | refl => exact conn_refl G _ x
      | @tail u v huv hed ih =>
        cases u with
        | inl a =>
          cases v with
          | inl b =>
            obtain ⟨d,_,he⟩ := hed
            exact (subdivision_adj_inl_inl G a b ⟨d,he⟩).elim
          | inr e =>
            obtain ⟨ha,ho⟩ := (subdivision_open_adj_iff G ν a e).mp hed
            exact ⟨a,ha,ho,ih⟩
        | inr e =>
          cases v with
          | inl b =>
            have hed' : ∃ d ∈ subdivisionOpen G ν, subdivision G d = s(Sum.inl b, Sum.inr e) := by
              obtain ⟨d,hd,he⟩ := hed
              exact ⟨d,hd,he.trans (Sym2.eq_swap)⟩
            obtain ⟨hb,hbo⟩ := (subdivision_open_adj_iff G ν b e).mp hed'
            obtain ⟨a,ha,hao,hxa⟩ := ih
            by_cases hab : a = b
            · simpa only [hab] using hxa
            · exact hxa.tail ⟨e,seriesOpen_of_two_incident G ν e a b ha hb hab hao hbo,
                (Sym2.mem_and_mem_iff hab).mp ⟨ha,hb⟩⟩
          | inr f =>
            obtain ⟨d,_,he⟩ := hed
            exact (subdivision_adj_inr_inr G e f ⟨d,he⟩).elim
    exact reach (.inl y) hc
  · intro hc
    induction hc with
    | refl => exact conn_refl _ _ _
    | @tail a b hab hed ih =>
      obtain ⟨e,he,heq⟩ := hed
      have ha : a ∈ G e := by simp [heq]
      have hb : b ∈ G e := by simp [heq]
      have hao : (⟨(e,a),ha⟩ : SubdivisionEdge G) ∈ subdivisionOpen G ν := he _
      have hbo : (⟨(e,b),hb⟩ : SubdivisionEdge G) ∈ subdivisionOpen G ν := he _
      exact (ih.tail ⟨⟨(e,a),ha⟩,hao,rfl⟩).tail ⟨⟨(e,b),hb⟩,hbo,Sym2.eq_swap⟩

 
theorem map_bool_and (q : unitInterval) :
    (Measure.infinitePi (fun _ : Bool => bitLaw q)).map
      (fun f : Bool → Prop => ∀ b, f b) = bitLaw (q^2) := by
  let μ := (Measure.infinitePi (fun _ : Bool => bitLaw q)).map
      (fun f : Bool → Prop => ∀ b, f b)
  have hm : Measurable (fun f : Bool → Prop => ∀ b, f b) := .of_discrete
  have : IsProbabilityMeasure μ := inferInstance
  have ht : μ.real {True} = (q:ℝ)^2 := by
    change ((Measure.infinitePi _).map _).real _ = _
    rw [Measure.real,Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun f : Bool → Prop => ∀ b, f b) ⁻¹' ({True} : Set Prop) =
        ((Finset.univ : Finset Bool) : Set Bool).pi (fun _ => ({True} : Set Prop)) := by
      ext f
      simp [and_comm]
    rw [he,Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
    simp [bitLaw,ENNReal.toReal_mul,pow_two]
  have hf : μ.real {False} = 1-(q:ℝ)^2 := by
    have he : ({False} : Set Prop) = ({True} : Set Prop)ᶜ := by ext b; simp
    rw [he,measureReal_compl (measurableSet_singleton _),probReal_univ,ht]
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (q^2)).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [ht]
    simp [bitLaw,Measure.real]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hf]
    simp [bitLaw,Measure.real]

theorem measurable_seriesOpen : Measurable (seriesOpen : Set (E × Bool) → Set E) := by
  apply measurable_setOfPred.comp
  apply Measurable.of_eval
  intro e
  apply measurableSet_setOfPred.mp
  have he : {ν : Set (E × Bool) | ∀ b, (e,b) ∈ ν} = ⋂ b : Bool, {ν | (e,b) ∈ ν} := by
    ext ν; simp
  rw [he]
  exact MeasurableSet.iInter fun b => measurableSet_setOfPred.mpr
    ((measurable_pi_apply (e,b)).comp MeasurableEquiv.setOfPred.symm.measurable)

 
theorem law_map_seriesOpen (q : unitInterval) :
    (law q : Measure (Set (E × Bool))).map seriesOpen = law (q^2) := by
  let c := MeasurableEquiv.curry E Bool Prop
  let b := fun f : E → Bool → Prop => fun e => ∀ j, f e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : Bool → Prop => ∀ j, f j)).comp
      (measurable_pi_apply e))
  unfold law
  rw [setBernoulli_eq_map,Measure.map_map measurable_seriesOpen measurable_setOfPred]
  simp only [Set.mem_univ]
  have he : seriesOpen ∘ (fun f : E × Bool → Prop => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘ b ∘ c := rfl
  rw [he,←Measure.map_map measurable_setOfPred (hb.comp c.measurable),
    ←Measure.map_map hb c.measurable]
  change ((Measure.infinitePi (fun _ : E × Bool => bitLaw q)).map c |>.map b |>.map
    (fun f : E → Prop => {e | f e})) = _
  rw [Measure.infinitePi_map_curry (fun (_ : E) (_ : Bool) => bitLaw q)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (f := fun _ (g : Bool → Prop) => ∀ j, g j)
    (fun _ => Measurable.of_discrete)]
  rw [map_bool_and q,setBernoulli_eq_map]
  rfl

theorem measurable_subdivisionOpen (G : BondGraph V E) : Measurable (subdivisionOpen G) :=
  measurable_setOfPred.comp (Measurable.of_eval (fun e =>
    (measurable_pi_apply (halfBit G e)).comp MeasurableEquiv.setOfPred.symm.measurable))

theorem law_map_subdivisionOpen (G : BondGraph V E) (q : unitInterval) :
    (law q : Measure (Set (E × Bool))).map (subdivisionOpen G) = law q :=
  law_map_preimage_embedding q (halfBit G)

 

theorem twoPoint_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (q : unitInterval) (x y : V) :
    twoPoint (subdivision G) q (.inl x) (.inl y) = twoPoint G (q^2) x y := by
  unfold twoPoint
  congr 1
  rw [←law_map_subdivisionOpen G q,Measure.map_apply (measurable_subdivisionOpen G)
    (measurableSet_conn (subdivision G) (.inl x) (.inl y))]
  rw [←law_map_seriesOpen q,Measure.map_apply measurable_seriesOpen (measurableSet_conn G x y)]
  congr 1
  ext ν
  exact conn_subdivision_iff G ν x y

 
theorem conn_subdivision_inr (G : BondGraph V E) (ν : Set (E × Bool)) (x : V) (e : E)
    (hc : Conn (subdivision G) (subdivisionOpen G ν) (.inl x) (.inr e)) :
    ∃ y, Conn G (seriesOpen ν) x y ∧ y ∈ G e := by
  rcases hc.cases_tail with h | ⟨z,hxz,hze⟩
  · cases h
  · cases z with
    | inl y =>
      obtain ⟨hy,_⟩ := (subdivision_open_adj_iff G ν y e).mp hze
      exact ⟨y,(conn_subdivision_iff G ν x y).mp hxz,hy⟩
    | inr f =>
      obtain ⟨d,_,hd⟩ := hze
      exact (subdivision_adj_inr_inr G f e ⟨d,hd⟩).elim

 

theorem finite_cluster_subdivision_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (ν : Set (E × Bool)) (x : V) :
    (cluster (subdivision G) (subdivisionOpen G ν) (.inl x)).Finite ↔
      (cluster G (seriesOpen ν) x).Finite := by
  constructor
  · intro hf
    apply Set.Finite.of_finite_image (f := (Sum.inl : V → V ⊕ E))
    · apply hf.subset
      rintro z ⟨y,hy,rfl⟩
      exact (conn_subdivision_iff G ν x y).mpr hy
    · exact Sum.inl_injective.injOn
  · intro hf
    have he : (⋃ y ∈ cluster G (seriesOpen ν) x, {e | y ∈ G e}).Finite :=
      hf.biUnion (fun y _ => hloc y)
    apply ((hf.image (Sum.inl : V → V ⊕ E)).union
      (he.image (Sum.inr : E → V ⊕ E))).subset
    intro z hz
    cases z with
    | inl y => exact Or.inl ⟨y,(conn_subdivision_iff G ν x y).mp hz,rfl⟩
    | inr e =>
      obtain ⟨y,hxy,hy⟩ := conn_subdivision_inr G ν x e hz
      exact Or.inr ⟨e,Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hxy,hy⟩⟩,rfl⟩

 

theorem exists_infinite_cluster_subdivision_iff (G : BondGraph V E)
    (hloc : LocallyFinite G) (ν : Set (E × Bool)) :
    (∃ z, (cluster (subdivision G) (subdivisionOpen G ν) z).Infinite) ↔
      ∃ x, (cluster G (seriesOpen ν) x).Infinite := by
  have hi (x : V) : (cluster (subdivision G) (subdivisionOpen G ν) (.inl x)).Infinite ↔
      (cluster G (seriesOpen ν) x).Infinite := by
    exact not_congr (finite_cluster_subdivision_iff G hloc ν x)
  constructor
  · rintro ⟨z,hz⟩
    cases z with
    | inl x => exact ⟨x,(hi x).mp hz⟩
    | inr e =>
      obtain ⟨w,hw,hne⟩ := hz.exists_notMem_finset {Sum.inr e}
      have hwne : w ≠ Sum.inr e := by simpa using hne
      rcases (show Conn (subdivision G) (subdivisionOpen G ν) (.inr e) w from hw).cases_head
        with h | ⟨z,hez,hzw⟩
      · exact (hwne h.symm).elim
      · cases z with
        | inl y =>
          have hconn : Conn (subdivision G) (subdivisionOpen G ν) (.inr e) (.inl y) :=
            .single hez
          have heq := cluster_eq_of_conn (subdivision G) (subdivisionOpen G ν) hconn
          exact ⟨y,(hi y).mp (heq ▸ hz)⟩
        | inr f =>
          obtain ⟨d,_,hd⟩ := hez
          exact (subdivision_adj_inr_inr G e f ⟨d,hd⟩).elim
  · rintro ⟨x,hx⟩
    exact ⟨.inl x,(hi x).mpr hx⟩

theorem infinite_cluster_probability_subdivision [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval) :
    law q {ω | (infiniteClusters (subdivision G) ω).Nonempty} =
      law (q^2) {ω | (infiniteClusters G ω).Nonempty} := by
  simp only [infiniteClusters_nonempty_iff]
  rw [←law_map_subdivisionOpen G q,Measure.map_apply (measurable_subdivisionOpen G)
    (measurableSet_exists_infinite_cluster _)]
  rw [←law_map_seriesOpen q,Measure.map_apply measurable_seriesOpen
    (measurableSet_exists_infinite_cluster _)]
  congr 1
  ext ν
  exact exists_infinite_cluster_subdivision_iff G hloc ν

 
noncomputable def squareParameter : unitInterval ≃o unitInterval where
  toFun q := q^2
  invFun p := ⟨Real.sqrt p,Real.sqrt_nonneg _,Real.sqrt_le_one.mpr p.2.2⟩
  left_inv q := by
    apply Subtype.ext
    change Real.sqrt ((q:ℝ)^2) = (q:ℝ)
    exact Real.sqrt_sq q.2.1
  right_inv p := by
    apply Subtype.ext
    change Real.sqrt (p:ℝ)^2 = (p:ℝ)
    exact Real.sq_sqrt p.2.1
  map_rel_iff' := by
    intro p q
    change (p:ℝ)^2 ≤ (q:ℝ)^2 ↔ (p:ℝ) ≤ (q:ℝ)
    exact sq_le_sq₀ p.2.1 q.2.1

 

theorem pc_subdivision_sq [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) :
    pc (subdivision G)^2 = pc G := by
  change squareParameter (sInf {q | 0 < law q {ω | (infiniteClusters (subdivision G) ω).Nonempty}}) = _
  rw [squareParameter.map_sInf]
  change (⨅ q, ⨅ (_ : 0 < law q {ω | (infiniteClusters (subdivision G) ω).Nonempty}), q^2) = _
  simp only [infinite_cluster_probability_subdivision G hloc]
  change (⨅ q, ⨅ (_ : 0 < law (squareParameter q) {ω | (infiniteClusters G ω).Nonempty}),
    squareParameter q) = _
  simpa only [pc,sInf_eq_iInf,Set.mem_ofPred_eq] using squareParameter.surjective.iInf_comp
    (g := fun p => ⨅ (_ : 0 < law p {ω | (infiniteClusters G ω).Nonempty}), p)

end Percolation

end OAI
