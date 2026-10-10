import OAI.Geometry.PlaneColoring.AngularBoundary
import OAI.Geometry.PlaneColoring.Moser

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
def triangleEdge (i : Fin 3) : Finset (Fin 5) := if i=0 then {0,1} else if i=1 then {1,2} else {2,0}
lemma triangle_majority_cover : ∀s : Fin 3 → Bool,∃b : Bool,
    ∀j∈({0,1,2} : Finset (Fin 5)),∃i : Fin 3,s i=b ∧ j∈triangleEdge i := by decide
lemma triangle_outsider : ∀s : Fin 3 → Bool,∀b : Bool,
    (∀j∈({0,1,2} : Finset (Fin 5)),∃i : Fin 3,s i=b ∧ j∈triangleEdge i) →
    ∀j : Fin 5,(∀i : Fin 3,s i=b → j∉triangleEdge i) → j=3 ∨ j=4 := by decide
lemma ApproachingContinuum.side_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hn : ⟪e,v⟫≠0) (b : Bool)
    (hs : decide (0<⟪e,v⟫)=b) : ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
      0<r → |r-1|<δ → (if b then 1<r else r<1) → x+(r:ℂ)*e'∈Straddle K := by
  cases b
  · have hneg : ⟪e,v⟫<0 := lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false hs)) hn
    obtain ⟨δ,hδ,hh⟩ := h.inner_strip he hneg
    refine ⟨δ,hδ,fun e' he' hd r hr hab hr1 => hh e' he' hd r hr ?_ hr1⟩
    have := (abs_lt.mp hab).1
    linarith
  · obtain ⟨δ,hδ,hh⟩ := h.outer_strip he (of_decide_eq_true hs)
    refine ⟨δ,hδ,fun e' he' hd r _ hab hr1 => hh e' he' hd r hr1 ?_⟩
    have := (abs_lt.mp hab).2
    linarith
/-- Three interface edges supply an actual outsider-only open strip in every
nonexceptional direction, with the radial side chosen by the majority sign. -/
lemma triangle_outsider_strip {c : ℂ → Fin 5} (hc : Measurable c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ}
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i)))
    {e : ℂ} (he : ‖e‖=1) (hn : ∀i,⟪e,v i⟫≠0) :
    ∃b : Bool,∃δ>0,∃W : Set ℂ,IsOpen W ∧
      (∀ᵐz : ℂ∂volume,z∈W → c z=3 ∨ c z=4) ∧
      ∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
        0<r → |r-1|<δ → (if b then 1<r else r<1) → x+(r:ℂ)*e'∈W := by
  classical
  let s : Fin 3 → Bool := fun i => decide (0<⟪e,v i⟫)
  obtain ⟨b,hb⟩ := triangle_majority_cover s
  let E : Finset (Fin 3) := Finset.univ.filter fun i => s i=b
  have hex (i : E) := (hK i).side_strip he (hn i) b ((Finset.mem_filter.mp i.2).2)
  choose d hd hs using hex
  obtain ⟨δ,hδ,_,hδd⟩ := finite_positive_lower_bound Finset.univ d (fun i _ => hd i)
  let W : Set ℂ := ⋂i : E,Straddle (K i)
  refine ⟨b,δ,hδ,W,isOpen_iInter_of_finite (fun i => straddle_isOpen (K i)),?_,?_⟩
  · filter_upwards [finite_support_exclusion_ae c hc K triangleEdge hH] with z hz hzW
    apply triangle_outsider s b hb (c z)
    intro i hi
    exact hz i (mem_iInter.mp hzW ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
  · intro e' he' heδ r hr hrδ hside
    apply mem_iInter.mpr
    intro i
    exact hs i e' he' (heδ.trans_le (hδd i (Finset.mem_univ _))) r hr
      (hrδ.trans_le (hδd i (Finset.mem_univ _))) hside
/-- Actual local triangle palette rigidity, without terminal angular sectors
or boundary information as hypotheses. -/
lemma triangle_palette_local {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ}
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i)))
    {t : Angles} (hn : ∀i,⟪direction t,v i⟫≠0)
    (hnR : ∀i,⟪direction t*(Circle.exp (Real.pi/3) : ℂ),v i⟫≠0) :
    ∃i : Fin 5,(i=3 ∨ i=4) ∧ ∃A : Set Angles,IsOpen A ∧ t∈A ∧
      ∀ᵐu∂angularMeasure,u∈A → i∈palette c hc x u := by
  obtain ⟨bu,δu,hδu,U,hU,hUc,hsU⟩ := triangle_outsider_strip hc hK hH (direction_norm t) hn
  have hunit : ‖direction t*(Circle.exp (Real.pi/3) : ℂ)‖=1 := by
    rw [norm_mul,direction_norm,Circle.norm_coe,one_mul]
  obtain ⟨bv,δv,hδv,V,hV,hVc,hsV⟩ := triangle_outsider_strip hc hK hH hunit hnR
  apply binary_strip_palette_rigidity c hc hw hU hV hUc hVc (lt_min hδu hδv) bu bv
  · intro e' he' hd r hr hrd hb
    exact hsU e' he' (hd.trans_le (min_le_left _ _)) r hr (hrd.trans_le (min_le_left _ _)) hb
  · intro e' he' hd r hr hrd hb
    exact hsV e' he' (hd.trans_le (min_le_right _ _)) r hr (hrd.trans_le (min_le_right _ _)) hb
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma triangle_binary_from_continua {c : ℂ → Fin 5} (hc : Measurable c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    BinaryCenter c hc x 3 4 := by
  have hh : ∀ᵐt∂angularMeasure,(∀i,⟪direction t,v i⟫≠0) →
      t∈paletteSet c hc x 3 ∨ t∈paletteSet c hc x 4 := by
    apply ae_of_locally_ae angularMeasure
    intro t ht
    obtain ⟨b,δ,hδ,W,hW,hWc,hs⟩ := triangle_outsider_strip hc hK hH (direction_norm t) ht
    have hcols : ∀ᵐz : ℂ∂volume,z∈W → c z∈({3,4} : Finset (Fin 5)) :=
      hWc.mono fun z hz hzw => by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz hzw
    have hex : ∃A : Set Angles,IsOpen A ∧ t∈A ∧
        ∀ᵐu∂angularMeasure,u∈A → (palette c hc x u∩{3,4}).Nonempty := by
      cases b
      · apply inner_strip_trace c hc hδ hW hcols
        intro u hu r hr hrδ hr1
        apply hs (direction u) (direction_norm u) hu r hr _ hr1
        rw [abs_lt]; constructor <;> linarith
      · apply outer_strip_trace c hc hδ hW hcols
        intro u hu r hr1 hrδ
        apply hs (direction u) (direction_norm u) hu r (by linarith) _ hr1
        rw [abs_lt]; constructor <;> linarith
    obtain ⟨A,hA,htA,hae⟩ := hex
    refine ⟨A,hA,htA,hae.mono fun u hu hAu => ?_⟩
    obtain ⟨i,hi⟩ := hu hAu
    rcases Finset.mem_inter.mp hi with ⟨hip,hi⟩
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact Or.inl ((mem_palette c hc x u 3).mp hip)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Or.inr ((mem_palette c hc x u 4).mp hip)
  filter_upwards [hh,ae_all_iff.mpr (fun i => ae_direction_nonorthogonal (hv i))] with t ht hn
  exact ht hn
def triangleState (c : ℂ → Fin 5) (hc : Measurable c) (x : ℂ) (t : Angles) : Bool := by
  classical
  exact if t∈paletteSet c hc x 3 then false else true
lemma triangleState_measurable (c : ℂ → Fin 5) (hc : Measurable c) (x : ℂ) :
    Measurable (triangleState c hc x) := Measurable.ite (paletteSet_measurable c hc x 3) measurable_const measurable_const
lemma triangleState_flip {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c) {x : ℂ}
    (hb : BinaryCenter c hc x 3 4) :
    ∀ᵐt∂angularMeasure,triangleState c hc x (t+(sixty : Angles))= !(triangleState c hc x t) := by
  filter_upwards [binary_alternation c hc hw hb] with t ht
  by_cases hp : t∈paletteSet c hc x 3
  · have hn : t+(sixty : Angles)∉paletteSet c hc x 3 := fun h => (ht.1.mp h) hp
    simp only [triangleState,hp,hn,ite_true,ite_false,Bool.not_false]
  · have hn : t+(sixty : Angles)∈paletteSet c hc x 3 := ht.1.mpr hp
    simp only [triangleState,hp,hn,ite_true,ite_false,Bool.not_true]
lemma triangleState_local {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i)))
    {t : Angles} (hn : ∀i,⟪direction t,v i⟫≠0)
    (hnR : ∀i,⟪direction t*(Circle.exp (Real.pi/3) : ℂ),v i⟫≠0) :
    ∃b,t∈angleEssential (triangleState c hc x) b := by
  obtain ⟨i,hi,A,hA,htA,hae⟩ := triangle_palette_local hc hw hK hH hn hnR
  have hb := binary_alternation c hc hw (triangle_binary_from_continua hc hv hK hH)
  rcases hi with rfl|rfl
  · refine ⟨false,A,hA,htA,hae.mono fun u hu hAu => ?_⟩
    have hp := (mem_palette c hc x u 3).mp (hu hAu)
    simp only [triangleState,hp,ite_true]
  · refine ⟨true,A,hA,htA,?_⟩
    filter_upwards [hae,hb] with u hu hu' hAu
    have hp := hu'.2.mp ((mem_palette c hc x u 4).mp (hu hAu))
    simp only [triangleState,hp,ite_false]
lemma direction_injective : Function.Injective direction := fun _ _ h =>
  AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0) (Subtype.ext h)
lemma direction_plus_sixty (t : Angles) :
    direction (t+(sixty : Angles))=direction t*(Circle.exp (Real.pi/3) : ℂ) := by
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [←AddCircle.coe_add,direction_real,direction_real,Circle.exp_add]
  rfl
lemma triple_orthogonal_cover (v : Fin 3 → ℂ) (hv : ∀i,‖v i‖=1) :
    ∃B : Finset Angles,B.card≤6 ∧ (∀t,t+(Real.pi : Angles)∈B ↔ t∈B) ∧
      ∀t,t∉B → ∀i,⟪direction t,v i⟫≠0 := by
  classical
  have hex (i : Fin 3) : ∃t : Angles,direction t=Complex.I*v i := direction_exists
    (by rw [norm_mul,Complex.norm_I,hv,one_mul])
  choose a ha using hex
  let B : Finset Angles := Finset.univ.biUnion fun i : Fin 3 => {a i,a i+(Real.pi : Angles)}
  have hmem (t : Angles) : t∈B ↔ ∃i : Fin 3,t=a i ∨ t=a i+(Real.pi : Angles) := by
    simp only [B,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  have hdouble (t : Angles) : t+(Real.pi : Angles)+(Real.pi : Angles)=t := by
    apply direction_injective
    simp only [direction_add_pi,neg_neg]
  refine ⟨B,?_,?_,?_⟩
  · calc B.card ≤ ∑i : Fin 3,({a i,a i+(Real.pi : Angles)} : Finset Angles).card := Finset.card_biUnion_le
         _ ≤ ∑_i : Fin 3,2 := Finset.sum_le_sum fun _ _ => by simpa using (Finset.card_insert_le (a _) ({a _+(Real.pi : Angles)} : Finset Angles))
         _ = 6 := by norm_num
  · intro t
    rw [hmem,hmem]
    constructor
    · rintro ⟨i,hi|hi⟩
      · exact ⟨i,Or.inr (by rw [←hi,hdouble])⟩
      · exact ⟨i,Or.inl (add_right_cancel hi)⟩
    · rintro ⟨i,rfl|rfl⟩
      · exact ⟨i,Or.inr rfl⟩
      · exact ⟨i,Or.inl (hdouble _)⟩
  · intro t ht i hinner
    apply ht
    rw [hmem]
    rcases complex_unit_orthogonal (direction_norm t) (hv i) hinner with he|he
    · exact ⟨i,Or.inl (direction_injective (he.trans (ha i).symm))⟩
    · refine ⟨i,Or.inr (direction_injective ?_)⟩
      rw [direction_add_pi,ha,he]
      ring
/-- The actual three-interface data force the source's unique six-position
boundary orbit. This theorem does not assume local rigidity or orbit finiteness. -/
lemma triangle_boundary_one_orbit {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    ∃t,angleBoundary (triangleState c hc x)={u | ∃j : Fin 6,u=t+sixAngle j} := by
  obtain ⟨B,hB,ha,hn⟩ := triple_orthogonal_cover v hv
  apply angleBoundary_one_orbit (triangleState_flip hc hw (triangle_binary_from_continua hc hv hK hH)) B hB ha
  intro t ht htR
  apply triangleState_local hc hw hv hK hH (hn t ht)
  simpa only [direction_plus_sixty] using hn (t+(sixty : Angles)) htR
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma angleEssential_connected {s : Angles → Bool} {U : Set Angles}
    (hU : IsPreconnected U) (hne : U.Nonempty) (hbound : Disjoint U (angleBoundary s)) :
    ∃b,U⊆angleEssential s b := by
  have hcov : U⊆angleEssential s false∪angleEssential s true := by
    intro t ht
    have hn := disjoint_left.mp hbound ht
    simp only [angleBoundary,mem_compl_iff,not_not,mem_iUnion] at hn
    obtain ⟨b,hb⟩ := hn
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  obtain ⟨t,ht⟩ := hne
  rcases hcov ht with hb|hb
  · exact ⟨false,hU.subset_left_of_subset_union (angleEssential_open s false) (angleEssential_open s true)
      (angleEssential_disjoint s (by decide)) hcov ⟨t,ht,hb⟩⟩
  · exact ⟨true,hU.subset_left_of_subset_union (angleEssential_open s true) (angleEssential_open s false)
      (angleEssential_disjoint s (by decide)) (by simpa only [union_comm] using hcov) ⟨t,ht,hb⟩⟩
lemma one_orbit_first_arc {s : Angles → Bool} {φ : ℝ}
    (hboundary : angleBoundary s={u | ∃j : Fin 6,u=(φ : Angles)+sixAngle j}) :
    ∃b,∀t∈Ioo φ (φ+Real.pi/3),(t : Angles)∈angleEssential s b := by
  let U : Set Angles := ((↑) : ℝ → Angles) '' Ioo φ (φ+Real.pi/3)
  have hU : IsPreconnected U := isPreconnected_Ioo.image _ continuous_quotient_mk'.continuousOn
  have hne : U.Nonempty := (nonempty_Ioo.mpr (by linarith [Real.pi_pos] : φ<φ+Real.pi/3)).image _
  have hd : Disjoint U (angleBoundary s) := by
    apply disjoint_left.mpr
    rintro q ⟨t,ht,rfl⟩ hq
    rw [hboundary] at hq
    obtain ⟨j,hj⟩ := hq
    have he : (t : Angles)=((φ+(j.val:ℝ)*(Real.pi/3) : ℝ) : Angles) := by
      have hx : sixAngle j=((j.val:ℝ)*(Real.pi/3) : ℝ) := by
        rw [sixAngle,←AddCircle.coe_nsmul]
        simp only [nsmul_eq_mul,sixty]
      simpa only [hx,AddCircle.coe_add] using hj
    have htI : t∈Ico φ (φ+2*Real.pi) := ⟨ht.1.le,by linarith [Real.pi_pos,ht.2]⟩
    have hjI : φ+(j.val:ℝ)*(Real.pi/3)∈Ico φ (φ+2*Real.pi) := by
      have hj0 : 0≤(j.val:ℝ) := Nat.cast_nonneg _
      have hj6 : (j.val:ℝ)<6 := by exact_mod_cast j.isLt
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    have hv := (AddCircle.coe_eq_coe_iff_of_mem_Ico htI hjI).mp he
    by_cases hz : j.val=0
    · simp only [hz,Nat.cast_zero,zero_mul,add_zero] at hv
      linarith [ht.1]
    · have hj1 : (1:ℝ)≤j.val := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      nlinarith [ht.2,Real.pi_pos]
  obtain ⟨b,hb⟩ := angleEssential_connected hU hne hd
  exact ⟨b,fun t ht => hb ⟨t,ht,rfl⟩⟩
lemma angleEssential_real_periodic {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (b : Bool) :
    Function.Periodic (fun t : ℝ => (t : Angles)∈angleEssential s b) (2*(Real.pi/3)) := by
  intro t
  apply propext
  have hh := angleEssential_shift hf ((t : Angles)+(sixty : Angles)) (!b)
  rw [Bool.not_not] at hh
  have hh' := angleEssential_shift hf (t : Angles) b
  have he : ((t+2*(Real.pi/3) : ℝ) : Angles) = (t : Angles)+(sixty : Angles)+(sixty : Angles) := by
    calc ((t+2*(Real.pi/3) : ℝ) : Angles) = ((t+sixty+sixty : ℝ) : Angles) := by
           congr 1
           dsimp [sixty]
           ring
         _ = _ := by rw [AddCircle.coe_add,AddCircle.coe_add]
  dsimp only
  rw [he]
  exact hh.trans hh'
lemma one_orbit_sectors {s : Angles → Bool} {φ : ℝ}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t))
    (hboundary : angleBoundary s={u | ∃j : Fin 6,u=(φ : Angles)+sixAngle j}) :
    ∃b,(∀t,0<Real.sin (3*(t-φ)) → (t : Angles)∈angleEssential s b) ∧
      (∀t,Real.sin (3*(t-φ))<0 → (t : Angles)∈angleEssential s (!b)) := by
  obtain ⟨b,hb⟩ := one_orbit_first_arc hboundary
  have hb' (t : ℝ) (ht : t∈Ioo (φ+Real.pi/3) (φ+2*(Real.pi/3))) :
      (t : Angles)∈angleEssential s (!b) := by
    have hh := (angleEssential_shift hf ((t-Real.pi/3 : ℝ) : Angles) b).mpr
      (hb (t-Real.pi/3) ⟨by linarith [ht.1],by linarith [ht.2]⟩)
    simpa only [sixty,←AddCircle.coe_add,sub_add_cancel] using hh
  have hreduce (t : ℝ) : ∃r : ℝ,∃n : ℤ,0≤r ∧ r<2*(Real.pi/3) ∧
      t=φ+r+n*(2*(Real.pi/3)) ∧ Real.sin (3*(t-φ))=Real.sin (3*r) := by
    let n : ℤ := ⌊(t-φ)/(2*(Real.pi/3))⌋
    let r : ℝ := (t-φ)-n*(2*(Real.pi/3))
    have he : t=φ+r+n*(2*(Real.pi/3)) := by dsimp [r]; ring
    refine ⟨r,n,Int.sub_floor_div_mul_nonneg _ (by positivity),Int.sub_floor_div_mul_lt _ (by positivity),he,?_⟩
    have he' : 3*(t-φ)=3*r+(n:ℝ)*(2*Real.pi) := by rw [he]; ring
    rw [he',Real.sin_add_int_mul_two_pi]
  refine ⟨b,?_,?_⟩
  · intro t ht
    obtain ⟨r,n,hr0,hrP,he,hsin⟩ := hreduce t
    rw [hsin] at ht
    have hrpos : 0<r := by
      by_contra hn
      have hr : r=0 := le_antisymm (le_of_not_gt hn) hr0
      simp only [hr,mul_zero,Real.sin_zero,lt_self_iff_false] at ht
    have hra : r<Real.pi/3 := by
      by_contra hn
      have hh := Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by linarith : 3*r-2*Real.pi≤0) (by linarith : -Real.pi≤3*r-2*Real.pi)
      rw [Real.sin_sub_two_pi] at hh
      exact (not_lt_of_ge hh) ht
    have hy := hb (φ+r) ⟨by linarith,by linarith⟩
    rw [he]
    exact (angleEssential_real_periodic hf b).int_mul n (φ+r) ▸ hy
  · intro t ht
    obtain ⟨r,n,hr0,hrP,he,hsin⟩ := hreduce t
    rw [hsin] at ht
    have hra : Real.pi/3<r := by
      by_contra hn
      have hh := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith : 0≤3*r) (by linarith : 3*r≤Real.pi)
      exact (not_lt_of_ge hh) ht
    have hy := hb' (φ+r) ⟨by linarith,by linarith⟩
    rw [he]
    exact (angleEssential_real_periodic hf (!b)).int_mul n (φ+r) ▸ hy
end EuclideanFiveColor
end

noncomputable section
open Set MeasureTheory
namespace EuclideanFiveColor
lemma moser_density_impossible {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c) (x v : ℂ) (hv : ‖v‖=1)
    (J : Finset (Fin k)) (hJ : J.card≤3) :
    ¬(∀ i, DensityOne {q | c q∈J} (x+v*placedMoser i)) := by
  intro hD
  obtain ⟨q,hq,hp⟩ := finite_density_realization hc hw (fun i => x+v*placedMoser i)
    (fun _ => J) hD
  have hh : Fintype.card J≤Fintype.card (Fin 3) := by simpa using hJ
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hh
  apply moser_not_three_colorable (fun i => f ⟨c (q+(x+v*placedMoser i)),hq i⟩)
  intro i j hij he
  have hd : ‖(x+v*placedMoser i)-(x+v*placedMoser j)‖=1 := by
    rw [show (x+v*placedMoser i)-(x+v*placedMoser j)=v*(placedMoser i-placedMoser j) by ring,
      norm_mul,hv,placedMoser_edge_unit hij,one_mul]
  exact hp i j hd (congrArg Subtype.val (f.injective he))
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma lineDensityZero_compl_of_mem_nhds {A : Set ℝ} {t : ℝ} (hA : A∈𝓝 t) :
    LineDensityZero Aᶜ t := by
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hA
  apply tendsto_const_nhds.congr'
  filter_upwards [(eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr
  have hempty : Aᶜ∩Metric.closedBall t r=∅ := by
    ext q
    simp only [mem_empty_iff_false,iff_false]
    rintro ⟨hq,hqr⟩
    exact hq (hsub (lt_of_le_of_lt hqr hr))
  simp [hempty]
def positiveSector (φ : ℝ) : Set ℝ := {t | 0<Real.sin (3*(t-φ))}
def negativeSector (φ : ℝ) : Set ℝ := {t | Real.sin (3*(t-φ))<0}
lemma positiveSector_open (φ : ℝ) : IsOpen (positiveSector φ) := by
  apply isOpen_lt <;> fun_prop
lemma negativeSector_open (φ : ℝ) : IsOpen (negativeSector φ) := by
  apply isOpen_lt <;> fun_prop
variable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
lemma polynomial_region_density (hw : WeakColoring k c) {x : ℂ} {a b : Fin k} {φ : ℝ}
    (hpos : RealState hc x (positiveSector φ) {a})
    (hneg : RealState hc x (negativeSector φ) {b})
    {z : ℂ} (hz : ThreeLabelRegion z.re z.im) :
    DensityOne {q | c q∉({a,b} : Finset (Fin k))} (x+(Circle.exp φ:ℂ)*z) := by
  obtain ⟨t,u,hs,hn,ht⟩ := polynomial_region_angles hz
  have hpoint : angularSum x 1 (angleChart (φ+t,φ+u))=x+(Circle.exp φ:ℂ)*z := by
    simp only [angularSum,angleChart,Complex.ofReal_one,one_mul,direction_real,Circle.exp_add,Circle.coe_mul]
    rw [add_assoc,←mul_add,hs]
  have hnon : Real.sin ((φ+u)-(φ+t))≠0 := by
    simpa only [show φ+u-(φ+t)=u-t by ring] using hn
  rcases mul_neg_iff.mp ht with ⟨ht,hu⟩|⟨ht,hu⟩
  · have htm : φ+t∈positiveSector φ := by simpa [positiveSector] using ht
    have hum : φ+u∈negativeSector φ := by simpa [negativeSector] using hu
    have hd := states_densityOne hc hw hpos hneg
      (lineDensityZero_compl_of_mem_nhds ((positiveSector_open φ).mem_nhds htm))
      (lineDensityZero_compl_of_mem_nhds ((negativeSector_open φ).mem_nhds hum)) hnon
    rw [hpoint] at hd
    simpa only [Finset.singleton_union] using hd
  · have htm : φ+t∈negativeSector φ := by simpa [negativeSector] using ht
    have hum : φ+u∈positiveSector φ := by simpa [positiveSector] using hu
    have hd := states_densityOne hc hw hneg hpos
      (lineDensityZero_compl_of_mem_nhds ((negativeSector_open φ).mem_nhds htm))
      (lineDensityZero_compl_of_mem_nhds ((positiveSector_open φ).mem_nhds hum)) hnon
    rw [hpoint] at hd
    simpa only [Finset.singleton_union,Finset.pair_comm b a] using hd
/-- The exact six-sector outcome of triangle rigidity is impossible, for every center and phase. -/
lemma no_alternating_sectors {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {a b : Fin 5} (hab : a≠b) (φ : ℝ)
    (hpos : RealState hc x (positiveSector φ) {a})
    (hneg : RealState hc x (negativeSector φ) {b}) : False := by
  let J : Finset (Fin 5) := {a,b}ᶜ
  have hJ : J.card≤3 := by
    change ({a,b}ᶜ : Finset (Fin 5)).card≤3
    rw [Finset.card_compl,Finset.card_pair hab]
    decide
  apply moser_density_impossible hc hw x (Circle.exp φ) (Circle.norm_coe _) J hJ
  intro i
  simpa only [J,Finset.mem_compl] using polynomial_region_density hc hw hpos hneg
    (seven_point_certificate i)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma triangleState_palette {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} (hb : BinaryCenter c hc x 3 4) (b : Bool) :
    ∀ᵐt∂angularMeasure,triangleState c hc x t=b → t∈paletteSet c hc x (if b then 4 else 3) := by
  classical
  filter_upwards [binary_alternation c hc hw hb] with t ht he
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    by_contra hn
    simp only [triangleState,hn,ite_false] at he
    exact Bool.noConfusion he
  · simp only [ite_true]
    apply ht.2.mpr
    intro hp
    simp only [triangleState,hp,ite_true] at he
    exact Bool.noConfusion he
/-- Complete actual triangle-interface endgame, including boundary rigidity,
sector extraction and the exact seven-point unit-distance certificate. -/
lemma no_triangle_interfaces {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) : False := by
  have hbinary := triangle_binary_from_continua hc hv hK hH
  obtain ⟨q,hq⟩ := triangle_boundary_one_orbit hc hw hv hK hH
  obtain ⟨φ,rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨b,hpos,hneg⟩ := one_orbit_sectors (triangleState_flip hc hw hbinary) hq
  have hstate (d : Bool) (A : Set ℝ) (hA : MeasurableSet A)
      (hAd : ∀t∈A,(t : Angles)∈angleEssential (triangleState c hc x) d) :
      RealState hc x A {if d then 4 else 3} := by
    refine ⟨hA,?_⟩
    intro i hi
    rw [Finset.mem_singleton] at hi
    subst i
    have hh := angleMk_quasiMeasurePreserving.ae
      ((angleEssential_ae (triangleState c hc x) d).and (triangleState_palette hc hw hbinary d))
    filter_upwards [hh] with t ht hAt
    exact ht.2 (ht.1 (hAd t hAt))
  have hp := hstate b (positiveSector φ) (positiveSector_open φ).measurableSet hpos
  have hn := hstate (!b) (negativeSector φ) (negativeSector_open φ).measurableSet hneg
  exact no_alternating_sectors hc hw (by cases b <;> decide) φ hp hn
end EuclideanFiveColor
end

end OAI
