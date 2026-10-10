import Mathlib
import OAI.GroupTheory.FiniteType.FiberCoreMap

namespace OAI

noncomputable section
open Set Topology unitInterval
namespace CoveringCellGeometry
open Set Topology
variable {X E A : Type*} [TopologicalSpace X] [TopologicalSpace E]
  [TopologicalSpace A] {p : E → X} (cov : IsCoveringMap p)
  [ContractibleSpace A] [CompactSpace A] [T2Space X] (f : C(A,X))

theorem characteristicLift_isClosedMap :
    IsClosedMap (fun z : A × (p ⁻¹' {f (contractionPoint A)}) =>
      characteristicLift cov f z.2 z.1) := by
  have hc : IsClosed {z : A × E | p z.2 = f z.1} :=
    isClosed_eq (cov.continuous.comp continuous_snd) (f.continuous.comp continuous_fst)
  exact isClosedMap_snd_of_compactSpace.comp
    (hc.isClosedEmbedding_subtypeVal.isClosedMap.comp (pullbackTrivialization cov f).isClosedMap)

theorem finite_sheets_meeting {K : Set E} (hK : IsCompact K) :
    {j : p ⁻¹' {f (contractionPoint A)} |
      ∃ a : A, characteristicLift cov f j a ∈ K}.Finite := by
  let : DiscreteTopology (p ⁻¹' {f (contractionPoint A)}) :=
    (cov (f (contractionPoint A))).discreteTopology_fiber
  let T : Set (Pullback (p := p) f) := {z | z.1.2 ∈ K}
  have hc : IsClosed {z : A × E | p z.2 = f z.1} :=
    isClosed_eq (cov.continuous.comp continuous_snd) (f.continuous.comp continuous_fst)
  have hT : IsCompact T := by
    rw [Subtype.isCompact_iff]
    have he : Subtype.val '' T = (univ ×ˢ K) ∩ {z : A × E | p z.2 = f z.1} := by
      ext ⟨a,e⟩
      simp only [mem_image,mem_inter_iff,mem_prod,mem_univ,true_and,mem_ofPred_eq,T]
      constructor
      · rintro ⟨⟨⟨a',e'⟩,hp⟩,hz,he⟩
        cases he
        exact ⟨hz,hp⟩
      · rintro ⟨he,hp⟩
        exact ⟨⟨(a,e),hp⟩,he,rfl⟩
    rw [he]
    exact (isCompact_univ.prod hK).inter_right hc
  have he : {j : p ⁻¹' {f (contractionPoint A)} |
      ∃ a : A, characteristicLift cov f j a ∈ K} = sheet cov f '' T := by
    ext j
    constructor
    · rintro ⟨a,ha⟩
      exact ⟨⟨(a,characteristicLift cov f j a),characteristicLift_proj cov f j a⟩,
        ha,sheet_characteristicLift cov f j a⟩
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.1.1,by simpa only [characteristicLift_sheet] using (show z.1.2 ∈ K from hz)⟩
  rw [he]
  exact (hT.image (sheet cov f).continuous).finite_of_discrete

theorem isClosed_discrete_slices {B J : Type*} [TopologicalSpace B]
    [TopologicalSpace J] [DiscreteTopology J] {S : Set (B × J)}
    (hS : ∀ j, IsClosed ((fun b : B => (b,j)) ⁻¹' S)) : IsClosed S := by
  rw [← isOpen_compl_iff]
  have he : Sᶜ = ⋃ j : J, ((fun b : B => (b,j)) ⁻¹' S)ᶜ ×ˢ {j} := by
    ext ⟨b,j⟩
    simp
  rw [he]
  exact isOpen_iUnion fun j => (hS j).isOpen_compl.prod (isOpen_discrete _)

end CoveringCellGeometry

namespace CoveringCW
section
open Set Topology Metric CoveringCellGeometry
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
  [CWComplex (univ : Set X)] {p : E → X} (cov : IsCoveringMap p)

abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1
instance disk_contractible (n : ℕ) : ContractibleSpace (Disk n) :=
  Metric.contractibleSpace_closedBall (by norm_num)

abbrev BaseCell (n : ℕ) := RelCWComplex.cell (univ : Set X) n

def baseChar (n : ℕ) (i : BaseCell (X := X) n) : C(Disk n,X) :=
  ⟨fun v => RelCWComplex.map n i v, continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)⟩

abbrev Fiber (n : ℕ) (i : BaseCell (X := X) n) :=
  p ⁻¹' {baseChar n i (contractionPoint (Disk n))}

abbrev Cell (n : ℕ) := Σ i : BaseCell (X := X) n, Fiber (p := p) n i

def characteristic (n : ℕ) (c : Cell (p := p) n) (v : Fin n → ℝ) : E := by
  classical
  exact if h : v ∈ closedBall 0 1 then characteristicLift cov (baseChar n c.1) c.2 ⟨v,h⟩ else c.2.1

@[simp] theorem characteristic_on_disk (n : ℕ) (c : Cell (p := p) n) (v : Disk n) :
    characteristic cov n c v = characteristicLift cov (baseChar n c.1) c.2 v := by
  simp only [characteristic,dite_eq_left v.2]

theorem characteristic_proj (n : ℕ) (c : Cell (p := p) n)
    {v : Fin n → ℝ} (hv : v ∈ closedBall 0 1) :
    p (characteristic cov n c v) = RelCWComplex.map n c.1 v := by
  rw [show characteristic cov n c v = characteristicLift cov (baseChar n c.1) c.2 ⟨v,hv⟩ from
    characteristic_on_disk cov n c ⟨v,hv⟩]
  exact characteristicLift_proj cov (baseChar n c.1) c.2 ⟨v,hv⟩

theorem characteristic_continuousOn (n : ℕ) (c : Cell (p := p) n) :
    ContinuousOn (characteristic cov n c) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun v : Disk n => characteristic cov n c v)
  have he : (fun v : Disk n => characteristic cov n c v) =
      characteristicLift cov (baseChar n c.1) c.2 := by
    funext v
    exact characteristic_on_disk cov n c v
  rw [he]
  exact (characteristicLift cov (baseChar n c.1) c.2).continuous

theorem characteristic_injOn (n : ℕ) (c : Cell (p := p) n) :
    InjOn (characteristic cov n c) (ball 0 1) := by
  intro v hv w hw he
  apply (RelCWComplex.map n c.1).injOn
  · simpa only [RelCWComplex.source_eq] using hv
  · simpa only [RelCWComplex.source_eq] using hw
  · simpa only [characteristic_proj cov n c (ball_subset_closedBall hv),
      characteristic_proj cov n c (ball_subset_closedBall hw)] using congrArg p he

def chart (n : ℕ) (c : Cell (p := p) n) : PartialEquiv (Fin n → ℝ) E :=
  (characteristic_injOn cov n c).toPartialEquiv (characteristic cov n c) (ball 0 1)

@[simp] theorem chart_coe (n : ℕ) (c : Cell (p := p) n) :
    ⇑(chart cov n c) = characteristic cov n c := rfl
@[simp] theorem chart_source (n : ℕ) (c : Cell (p := p) n) :
    (chart cov n c).source = ball 0 1 := rfl
@[simp] theorem chart_target (n : ℕ) (c : Cell (p := p) n) :
    (chart cov n c).target = chart cov n c '' ball 0 1 := rfl

theorem chart_proj (n : ℕ) (c : Cell (p := p) n)
    {v : Fin n → ℝ} (hv : v ∈ closedBall 0 1) :
    p (chart cov n c v) = RelCWComplex.map n c.1 v := characteristic_proj cov n c hv

theorem chart_continuousOn (n : ℕ) (c : Cell (p := p) n) :
    ContinuousOn (chart cov n c) (closedBall 0 1) := characteristic_continuousOn cov n c

theorem chart_symm_eq (n : ℕ) (c : Cell (p := p) n) {e : E} (he : e ∈ (chart cov n c).target) :
    (chart cov n c).symm e = (RelCWComplex.map n c.1).symm (p e) := by
  rcases he with ⟨v,hv,rfl⟩
  rw [characteristic_proj cov n c (ball_subset_closedBall hv)]
  have hs : v ∈ (RelCWComplex.map n c.1).source := by
    simpa only [RelCWComplex.source_eq] using hv
  exact (chart cov n c).left_inv hv |>.trans ((RelCWComplex.map n c.1).left_inv hs).symm

theorem chart_continuousOn_symm (n : ℕ) (c : Cell (p := p) n) :
    ContinuousOn (chart cov n c).symm (chart cov n c).target := by
  apply ContinuousOn.congr ((RelCWComplex.continuousOn_symm n c.1).comp
    cov.continuous.continuousOn ?_) (fun e he => chart_symm_eq cov n c he)
  rintro e ⟨v,hv,rfl⟩
  rw [characteristic_proj cov n c (ball_subset_closedBall hv)]
  exact (RelCWComplex.map n c.1).map_source (by simpa only [RelCWComplex.source_eq] using hv)

theorem chart_cell_eq {n m : ℕ} (c : Cell (p := p) n) (d : Cell (p := p) m)
    {v : Fin n → ℝ} {w : Fin m → ℝ} (hv : v ∈ ball 0 1) (hw : w ∈ ball 0 1)
    (he : chart cov n c v = chart cov m d w) : (⟨n,c⟩ : Σ n,Cell (p := p) n) = ⟨m,d⟩ := by
  classical
  have hp : RelCWComplex.map n c.1 v = RelCWComplex.map m d.1 w := by
    simpa only [chart_proj cov n c (ball_subset_closedBall hv),
      chart_proj cov m d (ball_subset_closedBall hw)] using congrArg p he
  by_cases hbase : (⟨n,c.1⟩ : Σ n,BaseCell (X := X) n) = ⟨m,d.1⟩
  · rcases c with ⟨i,j⟩
    rcases d with ⟨i',j'⟩
    cases hbase
    have hvw : v = w := (RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using hv)
      (by simpa only [RelCWComplex.source_eq] using hw) hp
    subst w
    have hj : j = j' := characteristicLift_fiber_injective cov (baseChar n i)
      (⟨v,ball_subset_closedBall hv⟩ : Disk n) (by
        exact (characteristic_on_disk cov n ⟨i,j⟩ ⟨v,ball_subset_closedBall hv⟩).symm.trans
          (he.trans (characteristic_on_disk cov n ⟨i,j'⟩ ⟨v,ball_subset_closedBall hv⟩)))
    subst j'
    rfl
  · exact False.elim (Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne hbase)
      ⟨v,hv,rfl⟩ ⟨w,hw,hp.symm⟩)

theorem chart_pairwiseDisjoint :
    (univ : Set (Σ n,Cell (p := p) n)).PairwiseDisjoint
      (fun ni => chart cov ni.1 ni.2 '' ball 0 1) := by
  rintro ⟨n,c⟩ _ ⟨m,d⟩ _ hne
  apply Set.disjoint_left.mpr
  rintro e ⟨v,hv,rfl⟩ ⟨w,hw,he⟩
  exact hne (chart_cell_eq cov c d hv hw he.symm)

theorem chart_union :
    (⋃ n, ⋃ c : Cell (p := p) n, chart cov n c '' closedBall 0 1) = univ := by
  apply eq_univ_of_forall
  intro e
  have hp : p e ∈ ⋃ n, ⋃ i : BaseCell (X := X) n, RelCWComplex.closedCell n i := by
    rw [CWComplex.union]
    trivial
  simp only [mem_iUnion,RelCWComplex.closedCell,mem_image] at hp
  rcases hp with ⟨n,i,v,hv,he⟩
  let z : Pullback (p := p) (baseChar n i) := ⟨(⟨v,hv⟩,e),he.symm⟩
  simp only [mem_iUnion,mem_image]
  refine ⟨n,⟨i,sheet cov (baseChar n i) z⟩,v,hv,?_⟩
  exact (characteristic_on_disk cov n _ ⟨v,hv⟩).trans (characteristicLift_sheet cov (baseChar n i) z)

end

open Set Topology Metric CoveringCellGeometry
universe u
variable {X E : Type u} [TopologicalSpace X] [TopologicalSpace E]
  [CWComplex (univ : Set X)] [T2Space X] {p : E → X} (cov : IsCoveringMap p)

omit [T2Space X] in
theorem chart_closedCell_eq_range (n : ℕ) (c : Cell (p := p) n) :
    chart cov n c '' closedBall 0 1 = range (characteristicLift cov (baseChar n c.1) c.2) := by
  ext e
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨⟨v,hv⟩,(characteristic_on_disk cov n c ⟨v,hv⟩).symm⟩
  · rintro ⟨v,rfl⟩
    exact ⟨v,v.2,characteristic_on_disk cov n c v⟩

omit [T2Space X] in
theorem chart_isCompact (n : ℕ) (c : Cell (p := p) n) :
    IsCompact (chart cov n c '' closedBall 0 1) := by
  rw [chart_closedCell_eq_range]
  exact isCompact_range (characteristicLift cov (baseChar n c.1) c.2).continuous

section FiniteType
variable [RelCWComplex.FiniteType (univ : Set X)]

def meetingCells (K : Set E) (hK : IsCompact K) (n : ℕ) : Finset (Cell (p := p) n) := by
  classical
  letI : Finite (BaseCell (X := X) n) := RelCWComplex.FiniteType.finite_cell n
  letI := Fintype.ofFinite (BaseCell (X := X) n)
  exact Finset.univ.sigma (fun i => (finite_sheets_meeting cov (baseChar n i) hK).toFinset)

@[simp] theorem mem_meetingCells (K : Set E) (hK : IsCompact K) (n : ℕ) (c : Cell (p := p) n) :
    c ∈ meetingCells cov K hK n ↔
      ∃ a : Disk n, characteristicLift cov (baseChar n c.1) c.2 a ∈ K := by
  classical
  simp only [meetingCells,Finset.mem_sigma,Finset.mem_univ,true_and,Set.Finite.mem_toFinset,
    mem_ofPred_eq]

theorem chart_mapsTo (n : ℕ) (c : Cell (p := p) n) :
    ∃ J : Π m, Finset (Cell (p := p) m),
      MapsTo (chart cov n c) (sphere 0 1)
        (⋃ (m < n) (d ∈ J m), chart cov m d '' closedBall 0 1) := by
  classical
  let K := chart cov n c '' closedBall 0 1
  have hK : IsCompact K := chart_isCompact cov n c
  refine ⟨meetingCells cov K hK,?_⟩
  intro v hv
  obtain ⟨J0,hI⟩ := CWComplex.mapsTo n c.1
  have hp := hI hv
  simp only [mem_iUnion,mem_image] at hp
  rcases hp with ⟨m,hm,i,hi,w,hw,he⟩
  let e := chart cov n c v
  have hpe : p e = baseChar m i ⟨w,hw⟩ :=
    (chart_proj cov n c (sphere_subset_closedBall hv)).trans he.symm
  let z : Pullback (p := p) (baseChar m i) := ⟨(⟨w,hw⟩,e),hpe⟩
  let d : Cell (p := p) m := ⟨i,sheet cov (baseChar m i) z⟩
  have hd : chart cov m d w = e :=
    (characteristic_on_disk cov m d ⟨w,hw⟩).trans (characteristicLift_sheet cov (baseChar m i) z)
  have hdJ : d ∈ meetingCells cov K hK m := by
    rw [mem_meetingCells]
    refine ⟨⟨w,hw⟩,?_⟩
    change characteristicLift cov (baseChar m i) (sheet cov (baseChar m i) z) z.1.1 ∈ K
    rw [characteristicLift_sheet]
    exact ⟨v,sphere_subset_closedBall hv,rfl⟩
  simp only [mem_iUnion,mem_image]
  exact ⟨m,hm,d,hdJ,w,hw,hd⟩

end FiniteType

theorem closed_over_cell (S : Set E) (n : ℕ) (i : BaseCell (X := X) n)
    (hS : ∀ j : Fiber (p := p) n i,
      IsClosed (S ∩ chart cov n ⟨i,j⟩ '' closedBall 0 1)) :
    IsClosed (S ∩ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1)) := by
  let : DiscreteTopology (Fiber (p := p) n i) :=
    (cov (baseChar n i (contractionPoint (Disk n)))).discreteTopology_fiber
  let F : Disk n × Fiber (p := p) n i → E := fun z => characteristicLift cov (baseChar n i) z.2 z.1
  have hpre : IsClosed (F ⁻¹' S) := by
    apply isClosed_discrete_slices
    intro j
    have h := (hS j).preimage (characteristicLift cov (baseChar n i) j).continuous
    have he : (fun a : Disk n => F (a,j)) ⁻¹' S =
        (characteristicLift cov (baseChar n i) j) ⁻¹' (S ∩ chart cov n ⟨i,j⟩ '' closedBall 0 1) := by
      ext a
      simp only [mem_preimage,mem_inter_iff,F]
      exact ⟨fun ha => ⟨ha,⟨a,a.2,characteristic_on_disk cov n ⟨i,j⟩ a⟩⟩,And.left⟩
    exact he ▸ h
  have hclosed := characteristicLift_isClosedMap cov (baseChar n i) _ hpre
  have he : F '' (F ⁻¹' S) = S ∩ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1) := by
    ext e
    constructor
    · rintro ⟨⟨a,j⟩,ha,rfl⟩
      refine ⟨ha,?_⟩
      exact ⟨a,a.2,(characteristicLift_proj cov (baseChar n i) j a).symm⟩
    · rintro ⟨heS,v,hv,hve⟩
      let z : Pullback (p := p) (baseChar n i) := ⟨(⟨v,hv⟩,e),hve.symm⟩
      have hz : F (⟨v,hv⟩,sheet cov (baseChar n i) z) = e :=
        characteristicLift_sheet cov (baseChar n i) z
      exact ⟨(⟨v,hv⟩,sheet cov (baseChar n i) z),by simpa only [mem_preimage,hz] using heS,hz⟩
  exact he ▸ hclosed

theorem base_isOpen_of_cells (O : Set X)
    (hO : ∀ n (i : BaseCell (X := X) n), IsOpen (baseChar n i ⁻¹' O)) : IsOpen O := by
  rw [← isClosed_compl_iff]
  apply (CWComplex.closed (univ : Set X) _ (subset_univ _)).mpr
  intro n i
  have hk : IsCompact (baseChar n i ⁻¹' Oᶜ) := (by
    simpa only [preimage_compl] using (hO n i).isClosed_compl :
      IsClosed (baseChar n i ⁻¹' Oᶜ)).isCompact
  have he : Oᶜ ∩ RelCWComplex.closedCell n i =
      baseChar n i '' (baseChar n i ⁻¹' Oᶜ) := by
    ext x
    constructor
    · rintro ⟨hx,v,hv,hvx⟩
      exact ⟨⟨v,hv⟩,by change RelCWComplex.map n i v ∈ Oᶜ; rwa [hvx],hvx⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨hv,v,v.2,rfl⟩
  rw [he]
  exact (hk.image (baseChar n i).continuous).isClosed

theorem chart_closed_general (S : Set E)
    (hS : ∀ n (c : Cell (p := p) n), IsClosed (S ∩ chart cov n c '' closedBall 0 1)) :
    IsClosed S := by
  rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
  intro e he
  obtain ⟨t,hte,hpt⟩ := cov.isLocalHomeomorph e
  let O : Set X := t.target ∩ t.symm ⁻¹' Sᶜ
  have hO : IsOpen O := by
    apply base_isOpen_of_cells
    intro n i
    let F := S ∩ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1)
    have hF : IsClosed F := closed_over_cell cov S n i (fun j => hS n ⟨i,j⟩)
    have hcont : ContinuousOn (t.symm ∘ baseChar n i) (baseChar n i ⁻¹' t.target) :=
      t.continuousOn_invFun.comp (baseChar n i).continuous.continuousOn (fun _ hx => hx)
    have hopen := hcont.isOpen_inter_preimage
      (t.open_target.preimage (baseChar n i).continuous) hF.isOpen_compl
    have heq : baseChar n i ⁻¹' O =
        (baseChar n i ⁻¹' t.target) ∩ (t.symm ∘ baseChar n i) ⁻¹' Fᶜ := by
      ext v
      simp only [O,preimage_inter,mem_inter_iff,mem_preimage,Function.comp_apply]
      apply and_congr_right
      intro hv
      have hp : p (t.symm (baseChar n i v)) = baseChar n i v := by
        rw [hpt]
        exact t.right_inv hv
      have hc : t.symm (baseChar n i v) ∈ p ⁻¹' (RelCWComplex.map n i '' closedBall 0 1) :=
        ⟨v,v.2,hp.symm⟩
      simp only [F,mem_compl_iff,mem_inter_iff,hc,and_true]
    exact heq ▸ hopen
  have hV : IsOpen (t.symm '' O) := t.isOpen_image_symm_of_subset_target hO (inter_subset_left)
  have heV : e ∈ t.symm '' O := by
    refine ⟨t e,⟨t.map_source hte,?_⟩,t.left_inv hte⟩
    change t.symm (t e) ∈ Sᶜ
    rwa [t.left_inv hte]
  exact Filter.mem_of_superset (hV.mem_nhds heV) (by
    rintro _ ⟨x,hx,rfl⟩
    exact hx.2)

def meetingCellsOver (K : Set E) (hK : IsCompact K) (n : ℕ)
    (J : Finset (BaseCell (X := X) n)) : Finset (Cell (p := p) n) := by
  classical
  exact J.sigma (fun i => (finite_sheets_meeting cov (baseChar n i) hK).toFinset)

 theorem chart_mapsTo_general (n : ℕ) (c : Cell (p := p) n) :
    ∃ J : Π m, Finset (Cell (p := p) m),
      MapsTo (chart cov n c) (sphere 0 1)
        (⋃ (m < n) (d ∈ J m), chart cov m d '' closedBall 0 1) := by
  classical
  let K := chart cov n c '' closedBall 0 1
  have hK : IsCompact K := chart_isCompact cov n c
  obtain ⟨J0,hI⟩ := CWComplex.mapsTo n c.1
  refine ⟨fun m => meetingCellsOver cov K hK m (J0 m),?_⟩
  intro v hv
  have hp := hI hv
  simp only [mem_iUnion,mem_image] at hp
  rcases hp with ⟨m,hm,i,hi,w,hw,he⟩
  let e := chart cov n c v
  have hpe : p e = baseChar m i ⟨w,hw⟩ :=
    (chart_proj cov n c (sphere_subset_closedBall hv)).trans he.symm
  let z : Pullback (p := p) (baseChar m i) := ⟨(⟨w,hw⟩,e),hpe⟩
  let d : Cell (p := p) m := ⟨i,sheet cov (baseChar m i) z⟩
  have hd : chart cov m d w = e :=
    (characteristic_on_disk cov m d ⟨w,hw⟩).trans (characteristicLift_sheet cov (baseChar m i) z)
  have hdJ : d ∈ meetingCellsOver cov K hK m (J0 m) := by
    simp only [meetingCellsOver,Finset.mem_sigma,Set.Finite.mem_toFinset,mem_ofPred_eq]
    refine ⟨hi,⟨⟨w,hw⟩,?_⟩⟩
    change characteristicLift cov (baseChar m i) (sheet cov (baseChar m i) z) z.1.1 ∈ K
    rw [characteristicLift_sheet]
    exact ⟨v,sphere_subset_closedBall hv,rfl⟩
  simp only [mem_iUnion,mem_image]
  exact ⟨m,hm,d,hdJ,w,hw,hd⟩

@[instance_reducible] def cwComplex_general : CWComplex (univ : Set E) where
  cell := Cell (p := p)
  map := chart cov
  source_eq := chart_source cov
  continuousOn := chart_continuousOn cov
  continuousOn_symm := chart_continuousOn_symm cov
  pairwiseDisjoint' := chart_pairwiseDisjoint cov
  mapsTo' := chart_mapsTo_general cov
  closed' S _ := chart_closed_general cov S
  union' := chart_union cov

end CoveringCW

end

end OAI
