import OAI.Dynamics.SmoothObstruction.DensityBounds

namespace OAI

section

open MeasureTheory Filter Topology TopologicalSpace Set Finset
open scoped ENNReal NNReal BoundedContinuousFunction
open Finset MeasureTheory Filter Topology
open scoped BigOperators
open Finset Matrix
open scoped Matrix.Norms.L2Operator
open Matrix

namespace SmoothObstruction.GridMargin
open Set MeasureTheory

/-- The deleted street for one of N translated grids of the same mesh Nδ. -/
def street (δ : ℝ) (N : ℕ) (k : Fin N) : Set ℝ :=
  {x | ∃ j : ℤ, |x-δ*((N:ℝ)*j+k.val)|≤δ/4}

lemma street_measurable (δ : ℝ) (N : ℕ) (k : Fin N) : MeasurableSet (street δ N k) := by
  have he : street δ N k=⋃ j : ℤ,{x : ℝ | |x-δ*((N:ℝ)*j+k.val)|≤δ/4} := by
    ext x; simp [street]
  rw [he]
  exact MeasurableSet.iUnion fun _ => measurableSet_le (by fun_prop) measurable_const

lemma centers_lt_eq {a b : ℤ} {δ : ℝ} (hδ : 0<δ)
    (hab : |δ*((a:ℝ)-b)|≤δ/2) : a=b := by
  have hd : |(a:ℝ)-b|<1 := by
    rw [abs_mul,abs_of_pos hδ] at hab
    nlinarith [abs_nonneg ((a:ℝ)-b)]
  have hdi : |a-b|<1 := by exact_mod_cast hd
  have he : a-b=0 := by
    have hh := abs_lt.mp hdi
    omega
  omega

lemma street_disjoint {δ : ℝ} (hδ : 0<δ) (N : ℕ) :
    Pairwise (fun k l : Fin N => Disjoint (street δ N k) (street δ N l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j,hj⟩ := hx
  obtain ⟨m,hm⟩ := hy
  have h := (abs_sub_le (δ*((N:ℝ)*j+k.val)) x (δ*((N:ℝ)*m+l.val)))
  rw [abs_sub_comm (δ*((N:ℝ)*j+k.val)) x] at h
  have hab : |δ*((((N:ℤ)*j+k.val : ℤ):ℝ)-(((N:ℤ)*m+l.val : ℤ):ℝ))|≤δ/2 := by
    push_cast
    calc
      _ = |δ*((N:ℝ)*j+k.val)-δ*((N:ℝ)*m+l.val)| := by congr 1; ring
      _ ≤ _ := h.trans (by linarith)
  have he := centers_lt_eq hδ hab
  have hmod := congrArg (fun z : ℤ => z%(N:ℤ)) he
  have hk : (k.val:ℤ)%(N:ℤ)=k.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast k.isLt)
  have hl : (l.val:ℤ)%(N:ℤ)=l.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast l.isLt)
  simp only [Int.add_emod,Int.mul_emod_right,zero_add,hk,hl] at hmod
  exact hkl (Fin.ext (by exact_mod_cast hmod))

/-- A translated regular grid with a quantitative margin for an arbitrary
probability law; no replacement of the law by a conditioned one. -/
theorem exists_small_street (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ k : Fin N,μ.real (street δ N k)≤(N:ℝ)⁻¹ := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hs : (∑ k : Fin N,μ.real (street δ N k))≤1 := by
    have h := sum_measureReal_le_measureReal_univ (μ:=μ) (s:=Finset.univ)
      (fun k _ => street_measurable δ N k)
      (fun k _ l _ hkl => street_disjoint hδ N hkl)
    simpa using h
  by_contra hh
  push Not at hh
  have hl := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty
    (fun k _ => hh k)
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hv : (∑ _k : Fin N,(N:ℝ)⁻¹)=1 := by simp [hn]
  rw [hv] at hl
  linarith

/-- Within a retained scalar cell, a perturbation less than the full margin
cannot change the integer cell index. -/
lemma floor_stable {r a x y ε : ℝ} (hr : 0<r)
    (hx : ∀ j : ℤ,ε < |x-(a+r*j)|) (hxy : |y-x|≤ε) :
    ⌊(y-a)/r⌋=⌊(x-a)/r⌋ := by
  let j : ℤ := ⌊(x-a)/r⌋
  have hj₁ := Int.floor_le ((x-a)/r)
  have hj₂ := Int.lt_floor_add_one ((x-a)/r)
  have hlo : a+r*j≤x := by nlinarith [(le_div_iff₀ hr).mp hj₁]
  have hhi : x<a+r*(j+1) := by nlinarith [(div_lt_iff₀ hr).mp hj₂]
  have hleft := hx j
  have hright := hx (j+1)
  rw [abs_of_nonneg (by linarith)] at hleft
  rw [abs_of_nonpos (by push_cast; linarith)] at hright
  have hy := abs_le.mp hxy
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hr).mpr
    dsimp [j] at *
    nlinarith
  · apply (div_lt_iff₀ hr).mpr
    push_cast at hright
    dsimp [j] at *
    nlinarith
end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridMargin
open Set MeasureTheory
variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

/-- Simultaneous product-coordinate margins for the original probability,
with no conditioning on a good set. Each coordinate gets one translation. -/
theorem exists_product_margins (μ : Measure X) [IsProbabilityMeasure μ]
    (c : X → ι → ℝ) (hc : ∀ i,Measurable (fun x =>  c x i))
    {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N) :
    ∃ k : ι → Fin N,
      μ.real (⋃ i,(fun x =>  c x i) ⁻¹' street δ N (k i)) ≤ (Fintype.card ι:ℝ)/N := by
  have hchoice (i : ι) : ∃ k : Fin N,
      μ.real ((fun x =>  c x i) ⁻¹' street δ N k) ≤ (N:ℝ)⁻¹ := by
    let ν := μ.map (fun x =>  c x i)
    have : IsProbabilityMeasure ν := inferInstance
    obtain ⟨k,hk⟩ := exists_small_street ν hδ hN
    refine ⟨k,?_⟩
    simpa only [ν,Measure.real,Measure.map_apply (hc i) (street_measurable δ N k)] using hk
  choose k hk using hchoice
  refine ⟨k,?_⟩
  calc
    _  ≤  ∑ i,μ.real ((fun x =>  c x i) ⁻¹' street δ N (k i)) := measureReal_iUnion_fintype_le _
    _  ≤  ∑ _i : ι,(N:ℝ)⁻¹ := Finset.sum_le_sum fun i _ =>  hk i
    _ = _ := by simp [div_eq_mul_inv]

/-- The precise regular translated-grid label. -/
noncomputable def gridIndex (δ : ℝ) (N : ℕ) (k : Fin N) (x : ℝ) : ℤ :=
  ⌊(x-δ*k.val)/(δ*N)⌋

lemma measurable_gridIndex (δ : ℝ) (N : ℕ) (k : Fin N) :
    Measurable (gridIndex δ N k) := by unfold gridIndex; fun_prop

lemma gridIndex_stable {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N)
    (k : Fin N) {x y : ℝ} (hx : x∉street δ N k) (hxy : |y-x| ≤ δ/4) :
    gridIndex δ N k y=gridIndex δ N k x := by
  apply floor_stable (mul_pos hδ (by exact_mod_cast hN)) _ hxy
  intro j
  have hj : ¬ |x-δ*((N:ℝ)*j+k.val)| ≤ δ/4 := fun h => hx ⟨j,h⟩
  have he : δ*k.val+(δ*N)*j=δ*((N:ℝ)*j+k.val) := by ring
  rw [he]
  exact lt_of_not_ge hj

/-- Bounded integer labels are encoded without enlarging the physical cells. -/
def boundedLabel (m : ℕ) (j : ℤ) : Fin (2*m+1) :=
  ⟨(max 0 (min (2*m : ℤ) (j+m))).toNat,by omega⟩

lemma boundedLabel_inj {m : ℕ} {i j : ℤ}
    (hi : -(m:ℤ) ≤ i  ∧  i ≤ m) (hj : -(m:ℤ) ≤ j  ∧  j ≤ m)
    (he : boundedLabel m i=boundedLabel m j) : i=j := by
  have hv := congrArg Fin.val he
  simp only [boundedLabel] at hv
  omega

lemma floor_bounds {x : ℝ} {m : ℕ} (hx : |x| ≤ (m:ℝ)) :
    -(m:ℤ) ≤ ⌊x⌋  ∧  ⌊x⌋ ≤ m := by
  constructor
  · apply Int.le_floor.mpr
    push_cast
    exact (abs_le.mp hx).1
  · exact_mod_cast (Int.floor_le x).trans (abs_le.mp hx).2

/-- Arbitrary bounded coordinates give a genuine finite measurable partition,
with exactly this finite alphabet, rather than an assumed cardinal bound. -/
noncomputable def productLabel (m : ℕ) (δ : ℝ) (N : ℕ) (k : ι → Fin N)
    (c : X → ι → ℝ) (x : X) : ι → Fin (2*m+1) :=
  fun i =>  boundedLabel m (gridIndex δ N (k i) (c x i))

omit [Fintype ι] in
lemma measurable_productLabel (m : ℕ) (δ : ℝ) (N : ℕ) (k : ι → Fin N)
    (c : X → ι → ℝ) (hc : ∀ i,Measurable (fun x =>  c x i)) :
    Measurable (productLabel m δ N k c) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_of_countable (boundedLabel m)).comp ((measurable_gridIndex δ N (k i)).comp (hc i))

omit [MeasurableSpace X] [Fintype ι] in
lemma productLabel_stable (m : ℕ) {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N)
    (k : ι → Fin N) (c : X → ι → ℝ) {x y : X}
    (hx : x∉⋃ i,(fun x =>  c x i) ⁻¹' street δ N (k i))
    (hxy : ∀ i,|c y i-c x i| ≤ δ/4) :
    productLabel m δ N k c y=productLabel m δ N k c x := by
  funext i
  apply congrArg (boundedLabel m)
  apply gridIndex_stable hδ hN _ _ (hxy i)
  exact fun h =>  hx (mem_iUnion.mpr ⟨i,h⟩)

lemma same_cell_coord {r a x y : ℝ} (hr : 0 < r)
    (he : ⌊(x-a)/r⌋=⌊(y-a)/r⌋) : |y-x| < r := by
  have hx₁ := Int.floor_le ((x-a)/r)
  have hx₂ := Int.lt_floor_add_one ((x-a)/r)
  have hy₁ := Int.floor_le ((y-a)/r)
  have hy₂ := Int.lt_floor_add_one ((y-a)/r)
  rw [←he] at hy₁ hy₂
  apply abs_lt.mpr
  constructor  <;>  nlinarith [(le_div_iff₀ hr).mp hx₁,(le_div_iff₀ hr).mp hy₁,
    (div_lt_iff₀ hr).mp hx₂,(div_lt_iff₀ hr).mp hy₂]

omit [MeasurableSpace X] [Fintype ι] in
lemma productLabel_diameter (m : ℕ) {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N)
    (k : ι → Fin N) (c : X → ι → ℝ) {x y : X}
    (hx : ∀ i,|(c x i-δ*(k i).val)/(δ*N)| ≤ m)
    (hy : ∀ i,|(c y i-δ*(k i).val)/(δ*N)| ≤ m)
    (he : productLabel m δ N k c x=productLabel m δ N k c y) :
    ∀ i,|c y i-c x i| < δ*N := by
  intro i
  apply same_cell_coord (mul_pos hδ (by exact_mod_cast hN))
  apply boundedLabel_inj (floor_bounds (hx i)) (floor_bounds (hy i))
  exact congrFun he i

lemma productLabel_card (m : ℕ) :
    Nat.card (ι → Fin (2*m+1))=(2*m+1)^Fintype.card ι := by
  classical
  simp [Nat.card_eq_fintype_card]
end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridMargin
open Set MeasureTheory

/-- Each finite original measure admits the same translated-street estimate,
scaled by its original total mass. This is used on partition fibres without
changing the final pair law. -/
theorem exists_small_street_finite (μ : Measure ℝ) [IsFiniteMeasure μ]
    {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ k : Fin N,μ.real (street δ N k)≤μ.real univ/(N:ℝ) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hs : (∑ k : Fin N,μ.real (street δ N k))≤μ.real univ :=
    sum_measureReal_le_measureReal_univ (μ:=μ) (s:=Finset.univ)
      (fun k _ => street_measurable δ N k)
      (fun k _ l _ hkl => street_disjoint hδ N hkl)
  by_contra hh
  push Not at hh
  have hl := Finset.sum_lt_sum_of_nonempty (s:=Finset.univ) Finset.univ_nonempty
    (fun k _ => hh k)
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have hv : (∑ _k : Fin N,μ.real univ/(N:ℝ))=μ.real univ := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  rw [hv] at hl
  linarith

variable {X ι C : Type*} [MeasurableSpace X] [Fintype ι]

/-- Simultaneous margins for a finite, not necessarily probability, law. -/
theorem exists_product_margins_finite (μ : Measure X) [IsFiniteMeasure μ]
    (c : X → ι → ℝ) (hc : ∀ i,Measurable (fun x => c x i))
    {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ k : ι → Fin N,
      μ.real (⋃ i,(fun x => c x i) ⁻¹' street δ N (k i)) ≤
        (Fintype.card ι:ℝ)*μ.real univ/N := by
  have hchoice (i : ι) : ∃ k : Fin N,
      μ.real ((fun x => c x i) ⁻¹' street δ N k) ≤ μ.real univ/(N:ℝ) := by
    obtain ⟨k,hk⟩ := exists_small_street_finite (μ.map (fun x => c x i)) hδ hN
    refine ⟨k,?_⟩
    simpa only [Measure.real,Measure.map_apply (hc i) (street_measurable δ N k),
      Measure.map_apply (hc i) MeasurableSet.univ,preimage_univ] using hk
  choose k hk using hchoice
  refine ⟨k,?_⟩
  calc
    _ ≤ ∑ i,μ.real ((fun x => c x i) ⁻¹' street δ N (k i)) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι,μ.real univ/(N:ℝ) := Finset.sum_le_sum fun i _ => hk i
    _ = _ := by simp [mul_div_assoc]

variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]

/-- Independently translated grids in each fibre of a finite measurable
partition retain the same original total-mass budget. The number of fibres
does not multiply the loss. -/
theorem fibrewise_margins (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (c : C → X → ι → ℝ)
    (hc : ∀ a i,Measurable (fun x => c a x i))
    {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ k : C → ι → Fin N,
      μ.real (⋃ a,(P ⁻¹' {a}) ∩ ⋃ i,(fun x => c a x i) ⁻¹' street δ N (k a i)) ≤
        (Fintype.card ι:ℝ)/N := by
  have hchoice (a : C) := exists_product_margins_finite (μ.restrict (P ⁻¹' {a}))
    (c a) (hc a) hδ hN
  choose k hk using hchoice
  let D (a : C) := ⋃ i,(fun x => c a x i) ⁻¹' street δ N (k a i)
  have hD (a : C) : MeasurableSet (D a) :=
    MeasurableSet.iUnion (fun i => (hc a i) (street_measurable δ N _))
  have hQ (a : C) : MeasurableSet (P ⁻¹' {a}) := hP (measurableSet_singleton a)
  have hs : (∑ a,μ.real (P ⁻¹' {a}))=1 := by
    have hd : Pairwise (fun i j : C => Disjoint (P ⁻¹' {i}) (P ⁻¹' {j})) := by
      intro i j hij
      exact (Set.disjoint_singleton.mpr hij).preimage P
    rw [←measureReal_iUnion_fintype (μ:=μ) hd hQ]
    have he : (⋃ a,P ⁻¹' {a})=univ := by ext x; simp
    rw [he]
    simp
  refine ⟨k,?_⟩
  calc
    _ ≤ ∑ a,μ.real ((P ⁻¹' {a})∩D a) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ a,(Fintype.card ι:ℝ)*μ.real (P ⁻¹' {a})/N := by
      apply Finset.sum_le_sum
      intro a _
      have h := hk a
      rw [Measure.real,Measure.restrict_apply (hD a),Measure.real,
        Measure.restrict_apply MeasurableSet.univ,univ_inter] at h
      simpa only [Measure.real,inter_comm] using h
    _ = (Fintype.card ι:ℝ)/N := by
      rw [←Finset.sum_div,←Finset.mul_sum,hs,mul_one]
end SmoothObstruction.GridMargin

namespace SmoothObstruction.GridRefinement
open Set MeasureTheory
open SmoothObstruction.GridMargin
variable {X C ι : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [Fintype ι] [DecidableEq ι]

noncomputable def label (P : X → C) (c : C → X → ι → ℝ)
    (m : ℕ) (δ : ℝ) (N : ℕ) (k : C → ι → Fin N) (x : X) :
    C × (ι → Fin (2*m+1)) :=
  (P x,productLabel m δ N (k (P x)) (c (P x)) x)

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_label (P : X → C) (hP : Measurable P)
    (c : C → X → ι → ℝ) (hc : ∀ a i,Measurable (fun x => c a x i))
    (m : ℕ) (δ : ℝ) (N : ℕ) (k : C → ι → Fin N) :
    Measurable (label P c m δ N k) := by
  have h : Measurable (fun p : C × X => productLabel m δ N (k p.1) (c p.1) p.2) :=
    measurable_from_prod_countable_right (fun a => measurable_productLabel m δ N (k a) (c a) (hc a))
  change Measurable (fun x => (P x,productLabel m δ N (k (P x)) (c (P x)) x))
  have hg : Measurable (fun x : X => (P x,x)) := hP.prodMk measurable_id
  have hq := h.comp hg
  exact hP.prodMk hq

/-- A genuine finite coordinate-grid refinement, with original-measure loss
independent of the number of base fibres. Stability is quantitative and the
cardinality is the actual finite alphabet cardinality. -/
theorem exists_refinement (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (c : C → X → ι → ℝ)
    (hc : ∀ a i,Measurable (fun x => c a x i))
    (m : ℕ) {δ : ℝ} (hδ : 0<δ) {N : ℕ} (hN : 0<N) :
    ∃ (k : C → ι → Fin N) (W : Set X),
      MeasurableSet W ∧ μ.real W≤(Fintype.card ι:ℝ)/N ∧
      Measurable (label P c m δ N k) ∧
      (∀ x y,x∉W → P y=P x →
        (∀ i,|c (P x) y i-c (P x) x i|≤δ/4) →
        label P c m δ N k y=label P c m δ N k x) ∧
      (∀ x y,label P c m δ N k x=label P c m δ N k y →
        (∀ i,|((c (P x) x i-δ*(k (P x) i).val)/(δ*N))|≤(m:ℝ)) →
        (∀ i,|((c (P x) y i-δ*(k (P x) i).val)/(δ*N))|≤(m:ℝ)) →
        ∀ i,gridIndex δ N (k (P x) i) (c (P x) x i)=
          gridIndex δ N (k (P x) i) (c (P x) y i)) ∧
      Fintype.card (C × (ι → Fin (2*m+1)))=
        Fintype.card C*(2*m+1)^Fintype.card ι := by
  classical
  obtain ⟨k,hk⟩ := fibrewise_margins μ P hP c hc hδ hN
  let W := ⋃ a,(P ⁻¹' {a}) ∩ ⋃ i,(fun x => c a x i) ⁻¹' street δ N (k a i)
  have hW : MeasurableSet W := MeasurableSet.iUnion (fun a =>
    (hP (measurableSet_singleton a)).inter
      (MeasurableSet.iUnion (fun i => (hc a i) (street_measurable δ N _))))
  refine ⟨k,W,hW,hk,measurable_label P hP c hc m δ N k,?_,?_,?_⟩
  · intro x y hx he hdist
    have hx' : x∉⋃ i,(fun u => c (P x) u i) ⁻¹' street δ N (k (P x) i) := by
      intro hh
      exact hx (mem_iUnion.mpr ⟨P x,by exact ⟨rfl,hh⟩⟩)
    dsimp [label]
    rw [he]
    exact Prod.ext rfl (productLabel_stable m hδ hN _ _ hx' hdist)
  · intro x y he hx hy i
    have hPxy := congrArg Prod.fst he
    have he' := congrArg (fun p : C × (ι → Fin (2*m+1)) => p.2 i) he
    change P x=P y at hPxy
    change boundedLabel m (gridIndex δ N (k (P x) i) (c (P x) x i))=
      boundedLabel m (gridIndex δ N (k (P y) i) (c (P y) y i)) at he'
    rw [←hPxy] at he'
    exact boundedLabel_inj (floor_bounds (hx i)) (floor_bounds (hy i)) he'
  · simp
end SmoothObstruction.GridRefinement

namespace SmoothObstruction.GridRefinement
open Set MeasureTheory
open SmoothObstruction.GridMargin
variable {X C ι : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The retained product margins survive a complementary coordinate mix.
Each output coordinate may follow either retained input, so this applies
simultaneously to both actual orbit joins. Mass is still the original law. -/
theorem exists_mixing_refinement (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (c : C → X → ι → ℝ)
    (hc : ∀ a i,Measurable (fun x => c a x i))
    (m : ℕ) {δ : ℝ} (hδ : 0 < δ) {N : ℕ} (hN : 0 < N) :
    ∃ (k : C → ι → Fin N) (W : Set X),
      MeasurableSet W ∧ μ.real W ≤ (Fintype.card ι:ℝ)/N ∧
      Measurable (label P c m δ N k) ∧
      (∀ x y z,x∉W → y∉W →
        label P c m δ N k x=label P c m δ N k y → P z=P x →
        (∀ i,|c (P x) z i-c (P x) x i| ≤ δ/4 ∨
          |c (P x) z i-c (P x) y i| ≤ δ/4) →
        label P c m δ N k z=label P c m δ N k x) ∧
      (∀ x y,label P c m δ N k x=label P c m δ N k y →
        (∀ i,|(c (P x) x i-δ*(k (P x) i).val)/(δ*N)| ≤ (m:ℝ)) →
        (∀ i,|(c (P x) y i-δ*(k (P x) i).val)/(δ*N)| ≤ (m:ℝ)) →
        ∀ i,|c (P x) x i-c (P x) y i| < δ*N) := by
  classical
  obtain ⟨k,hk⟩ := fibrewise_margins μ P hP c hc hδ hN
  let W := ⋃ a,(P ⁻¹' {a}) ∩ ⋃ i,(fun x => c a x i) ⁻¹' street δ N (k a i)
  have hW : MeasurableSet W := MeasurableSet.iUnion (fun a =>
    (hP (measurableSet_singleton a)).inter
      (MeasurableSet.iUnion (fun i => (hc a i) (street_measurable δ N _))))
  have hout (x : X) (hx : x∉W) (i : ι) : c (P x) x i∉street δ N (k (P x) i) := by
    intro hi
    exact hx (mem_iUnion.mpr ⟨P x,rfl,mem_iUnion.mpr ⟨i,hi⟩⟩)
  refine ⟨k,W,hW,hk,measurable_label P hP c hc m δ N k,?_,?_⟩
  · intro x y z hx hy he hp hm
    have hxy : P x=P y := congrArg Prod.fst he
    apply Prod.ext hp
    change productLabel m δ N (k (P z)) (c (P z)) z=
      productLabel m δ N (k (P x)) (c (P x)) x
    rw [hp]
    funext i
    rcases hm i with hi | hi
    · exact congrArg (boundedLabel m) (gridIndex_stable hδ hN _ (hout x hx i) hi)
    · have hy' : c (P x) y i∉street δ N (k (P x) i) := by
        simpa only [hxy] using hout y hy i
      have he' := congrArg (fun p : C × (ι → Fin (2*m+1)) => p.2 i) he
      change boundedLabel m (gridIndex δ N (k (P x) i) (c (P x) x i))=
        boundedLabel m (gridIndex δ N (k (P y) i) (c (P y) y i)) at he'
      rw [←hxy] at he'
      exact (congrArg (boundedLabel m) (gridIndex_stable hδ hN _ hy' hi)).trans he'.symm
  · intro x y he hx hy i
    have hxy : P x=P y := congrArg Prod.fst he
    have he' := congrArg (fun p : C × (ι → Fin (2*m+1)) => p.2 i) he
    change boundedLabel m (gridIndex δ N (k (P x) i) (c (P x) x i))=
      boundedLabel m (gridIndex δ N (k (P y) i) (c (P y) y i)) at he'
    rw [←hxy] at he'
    have hidx := boundedLabel_inj (floor_bounds (hx i)) (floor_bounds (hy i)) he'
    exact same_cell_coord (mul_pos hδ (by exact_mod_cast hN)) hidx.symm
end SmoothObstruction.GridRefinement

namespace SmoothObstruction.ProductCells
open Set MeasureTheory
open SmoothObstruction.GridMargin SmoothObstruction.GridRefinement
variable {X C : Type*} [MeasurableSpace X] [Fintype C]
  [MeasurableSpace C] [MeasurableSingletonClass C] {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

lemma norm_le_coords {u : E} {h : ℝ} (hh : 0≤h) (hu : ∀ i,|u i|≤h) :
    ‖u‖≤((d:ℝ)+1)*h := by
  have hs : ‖u‖^2≤(d:ℝ)*h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin d,h^2 := Finset.sum_le_sum (fun i _ => by
        have hi := hu i
        nlinarith [sq_abs (u i),abs_nonneg (u i)])
      _ = _ := by simp
  have hd : 0≤(d:ℝ) := Nat.cast_nonneg _
  have hp : 0≤((d:ℝ)+1)*h := by positivity
  have hsq : (d:ℝ)*h^2≤(((d:ℝ)+1)*h)^2 := by
    nlinarith [sq_nonneg ((d:ℝ)*h),mul_nonneg hd (sq_nonneg h)]
  nlinarith [norm_nonneg u]

lemma grid_range {δ D H : ℝ} (hδ : 0<δ) (hD : 0≤D) (hH : 0≤H)
    {N : ℕ} (hN : 0<N) (k : Fin N) {v : ℝ} (hv : |v|≤H*D) :
    |(v-δ*k.val)/(δ*N)|≤(⌈H*D/(δ*N)+1⌉₊:ℝ) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hk : (k.val:ℝ)≤N := by exact_mod_cast k.isLt.le
  have hi : 0≤δ*(k.val:ℝ) := by positivity
  have hab : |v-δ*k.val|≤H*D+δ*N := by
    calc
      _ ≤ |v|+|δ*k.val| := abs_sub _ _
      _ ≤ H*D+δ*N := by rw [abs_of_nonneg hi]; nlinarith
  rw [abs_div,abs_of_pos (mul_pos hδ hn)]
  calc
    _ ≤ (H*D+δ*N)/(δ*N) := div_le_div_of_nonneg_right hab (by positivity)
    _ = H*D/(δ*N)+1 := by field_simp
    _ ≤ _ := Nat.le_ceil _

/-- Finite product cells for arbitrary measurable geometric coordinates.
The original probability law loses at most d/N near product streets. The
number of cells is exactly the finite grid alphabet; no rank or orbit code
is counted. Stability is stated in the physical coordinates needed for joins. -/
theorem exists_cells (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (φ : C → X → E)
    (hφ : ∀ c,Measurable (φ c)) (A : C → E ≃L[ℝ] E)
    {D H F δ : ℝ} (hD : 0≤D) (hH : 0≤H) (hF : 0≤F) (hδ : 0<δ)
    (hbound : ∀ x,‖φ (P x) x‖≤D)
    (hAi : ∀ c,‖(A c).symm.toContinuousLinearMap‖≤H)
    (hA : ∀ c,‖(A c).toContinuousLinearMap‖≤F)
    {N : ℕ} (hN : 0<N) :
    let m := ⌈H*D/(δ*N)+1⌉₊
    ∃ (L : X → C × (Fin d → Fin (2*m+1))) (W : Set X),
      Measurable L ∧ MeasurableSet W ∧ μ.real W≤(d:ℝ)/N ∧
      (∀ x,(L x).1=P x) ∧
      (∀ x y,L x=L y → ‖φ (P x) x-φ (P x) y‖≤F*((d:ℝ)+1)*(δ*N)) ∧
      (∀ x y z,L x=L y → x∉W → y∉W → P z=P x →
        (∀ i,|((A (P x)).symm (φ (P x) z)) i-
          ((A (P x)).symm (φ (P x) x)) i|≤δ/4 ∨
          |((A (P x)).symm (φ (P x) z)) i-
          ((A (P x)).symm (φ (P x) y)) i|≤δ/4) → L z=L x) ∧
      Fintype.card (C × (Fin d → Fin (2*m+1)))=Fintype.card C*(2*m+1)^d := by
  classical
  dsimp only
  let m := ⌈H*D/(δ*N)+1⌉₊
  let c (a : C) (x : X) (i : Fin d) := ((A a).symm (φ a x)) i
  have hc (a : C) (i : Fin d) : Measurable (fun x => c a x i) :=
    (show Measurable (fun u : E => u i) by fun_prop).comp
      ((A a).symm.continuous.measurable.comp (hφ a))
  obtain ⟨k,W,hW,hm,hL,hstable,hdiam⟩ :=
    exists_mixing_refinement μ P hP c hc m hδ hN
  let L := label P c m δ N k
  have hrange (x : X) (i : Fin d) :
      |(c (P x) x i-δ*(k (P x) i).val)/(δ*N)|≤(m:ℝ) := by
    apply grid_range hδ hD hH hN
    calc
      _ = ‖((A (P x)).symm (φ (P x) x)) i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖(A (P x)).symm (φ (P x) x)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖(A (P x)).symm.toContinuousLinearMap‖*‖φ (P x) x‖ :=
        (A (P x)).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ H*D := mul_le_mul (hAi _) (hbound x) (norm_nonneg _) hH
  refine ⟨L,W,hL,hW,by simpa using hm,fun _ => rfl,?_,?_,by simp⟩
  · intro x y he
    have hxy : P x=P y := congrArg Prod.fst he
    have hh := hdiam x y he (hrange x) (by simpa only [hxy] using hrange y)
    have hb : ‖(A (P x)).symm (φ (P x) x)-(A (P x)).symm (φ (P x) y)‖≤
        ((d:ℝ)+1)*(δ*N) := by
      apply norm_le_coords (by positivity)
      intro i
      exact (hh i).le
    calc
      _ = ‖A (P x) ((A (P x)).symm (φ (P x) x)-(A (P x)).symm (φ (P x) y))‖ := by
        rw [map_sub]; simp
      _ ≤ ‖(A (P x)).toContinuousLinearMap‖*
          ‖(A (P x)).symm (φ (P x) x)-(A (P x)).symm (φ (P x) y)‖ :=
        (A (P x)).toContinuousLinearMap.le_opNorm _
      _ ≤ F*(((d:ℝ)+1)*(δ*N)) := mul_le_mul (hA _) hb (norm_nonneg _) hF
      _ = _ := by ring
  · intro x y z he hx hy hp hh
    exact hstable x y z hx hy he hp hh
end SmoothObstruction.ProductCells

namespace SmoothObstruction.ChartDensity
open Set MeasureTheory
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] in
/-- A uniform selected-coordinate bound follows from the compact atlas,
without any regularity assumption on the selection itself. -/
theorem selected_coordinate_bound (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (q : M → ι) (hqK : ∀ x,x∈K (q x)) :
    ∃ D : ℝ,1≤D ∧ ∀ x,‖coordinates I (a (q x)) x‖≤D := by
  classical
  have hex (i : ι) : ∃ R : ℝ,∀ x∈K i,‖(extChartAt I (a i)) x‖≤R := by
    have hc := (hK i).image_of_continuousOn
      ((continuousOn_extChartAt (I:=I) (a i)).mono
        (by simpa only [extChartAt_source] using hKU i))
    obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
    exact ⟨R,fun x hx => hR _ ⟨x,hx,rfl⟩⟩
  choose R hR using hex
  let D := 1+∑ i,|R i|
  have hp : 0≤∑ i,|R i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨D,by dsimp [D]; linarith,fun x => ?_⟩
  rw [coordinates_eq I _ _ (by simpa only [extChartAt_source] using hKU _ (hqK x))]
  calc
    _ ≤ R (q x) := hR _ _ (hqK x)
    _ ≤ |R (q x)| := le_abs_self _
    _ ≤ ∑ i,|R i| := Finset.single_le_sum (fun i _ => abs_nonneg (R i)) (Finset.mem_univ _)
    _ ≤ D := by dsimp [D]; linarith

omit [T2Space M] in
/-- Genuine finite coarse bins in a compact atlas. Their translated margins
are estimated using the ORIGINAL measure, with no assumptions about its
interaction with the good gauge set. Only the selected starting chart is
part of the finite alphabet. -/
theorem exists_coarse_cells [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (q : M → ι) (hq : Measurable q) (hqK : ∀ x,x∈K (q x)) :
    ∃ D : ℝ,1≤D ∧ ∀ {δ : ℝ},0<δ → ∀ {N : ℕ},0<N →
      let m := ⌈D/(δ*N)+1⌉₊
      ∃ (P : M → ι × (Fin d → Fin (2*m+1))) (W : Set M),
        Measurable P ∧ MeasurableSet W ∧ μ.real W≤(d:ℝ)/N ∧
        (∀ x,(P x).1=q x) ∧
        (∀ x y,P x=P y →
          ‖coordinates I (a (q x)) x-coordinates I (a (q x)) y‖≤((d:ℝ)+1)*(δ*N)) ∧
        (∀ x z,x∉W → q z=q x →
          ‖coordinates I (a (q x)) z-coordinates I (a (q x)) x‖≤δ/4 → P z=P x) ∧
        Fintype.card (ι × (Fin d → Fin (2*m+1)))=Fintype.card ι*(2*m+1)^d := by
  obtain ⟨D,hD,hbound⟩ := selected_coordinate_bound I a K hK hKU q hqK
  refine ⟨D,hD,?_⟩
  intro δ hδ N hN
  have hh := ProductCells.exists_cells μ q hq (fun i => coordinates I (a i))
      (fun i => measurable_coordinates I (a i))
      (fun _ => ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin d)))
      (D:=D) (H:=1) (F:=1) (by linarith) (by norm_num) (by norm_num) hδ hbound
      (fun _ => ContinuousLinearMap.norm_id_le) (fun _ => ContinuousLinearMap.norm_id_le) hN
  dsimp only at hh
  rw [one_mul] at hh
  simp only [one_mul] at hh
  obtain ⟨P,W,hP,hW,hm,hqP,hd,hs,hcard⟩ := hh
  refine ⟨P,W,hP,hW,hm,hqP,hd,?_,hcard⟩
  intro x z hx hqz hz
  apply hs x x z rfl hx hx hqz
  intro i
  left
  exact (PiLp.norm_apply_le
    (coordinates I (a (q x)) z-coordinates I (a (q x)) x) i).trans hz
end SmoothObstruction.ChartDensity

end

end OAI
