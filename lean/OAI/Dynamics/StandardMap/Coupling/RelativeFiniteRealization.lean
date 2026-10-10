import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Towers.ScaledFiniteCoupling

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma finite_map_eq_of_mass (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (h : ∀ a,mass μ p a=mass ν q a) :
    μ.map p=ν.map q := by
  apply Measure.ext_of_singleton
  intro a
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [Measure.map_apply hp (measurableSet_singleton a),Measure.map_apply hq (measurableSet_singleton a)]
  exact h a

omit [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A] in
lemma mass_eq_of_map_eq (μ : Measure X) (ν : Measure Y) (p : X → A) (q : Y → A)
    (hp : Measurable p) (hq : Measurable q) (h : μ.map p=ν.map q) (a : A) :
    mass μ p a=mass ν q a := by
  have hh := congrArg (fun ξ : Measure A => (ξ {a}).toReal) h
  simpa only [Measure.map_apply hp (measurableSet_singleton a),
    Measure.map_apply hq (measurableSet_singleton a),mass] using hh

omit [StandardBorelSpace X] in
lemma relative_finite_realization (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (p : X → A) (α : X → B) (q : Y → A)
    (hp : Measurable p) (hα : Measurable α) (hq : Measurable q)
    (hfirst : μ.map p=ν.map q) :
    ∃ b : Y → B,Measurable b ∧
      ν.map (fun y => (q y,b y))=μ.map (fun x => (p x,α x)) := by
  let S := MatrixCoupling.observations μ p α hp hα
  let R : MatrixCoupling (mass ν q) (mass μ α) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun a => (S.row a).trans (mass_eq_of_map_eq μ ν p q hp hq hfirst a)
    col := S.col }
  obtain ⟨b,hb,hR⟩ := realize_finite_coupling_finite ν q hq (mass μ α) R
  refine ⟨b,hb,finite_map_eq_of_mass ν μ _ _ (hq.prodMk hb) (hp.prodMk hα) ?_⟩
  rintro ⟨a,c⟩
  exact hR a c

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma map_restrict_factor (μ : Measure X) (ν : Measure Y)
    (π : X → Y) (hπ : MeasurePreserving π μ ν) {U : Set Y} (hU : MeasurableSet U) :
    (μ.restrict (π ⁻¹' U)).map π=ν.restrict U := by
  rw [←hπ.map_eq,Measure.restrict_map hπ.measurable hU]

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] in
lemma factor_iterate (e : X → X) (f : Y → Y) (π : X → Y)
    (h : ∀ x,π (e x)=f (π x)) (i : ℕ) (x : X) : π (e^[i] x)=f^[i] (π x) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',h,ih,Function.iterate_succ_apply']

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] in
lemma factor_word (e : X → X) (f : Y → Y) (π : X → Y)
    (h : ∀ x,π (e x)=f (π x)) (p : Y → A) (n : ℕ) :
    word e (p ∘ π) n=word f p n ∘ π := by
  funext x j
  exact congrArg p (factor_iterate e f π h j.val x)

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma factor_tower_level (e : X ≃ᵐ X) (f : Y ≃ᵐ Y) (π : X → Y)
    (h : ∀ x,π (e x)=f (π x)) (U : Set Y) (i : ℕ) :
    (e^[i]) '' (π ⁻¹' U)=π ⁻¹' ((f^[i]) '' U) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨π z,hz,(factor_iterate e f π h i z).symm⟩
  · rintro ⟨y,hy,hxy⟩
    let z := (iterateEquiv e i).symm x
    have hzx : e^[i] z=x := (iterateEquiv e i).apply_symm_apply x
    refine ⟨z,?_,hzx⟩
    have hh : f^[i] (π z)=f^[i] y := by rw [←factor_iterate e f π h,hzx,hxy]
    have hz := (iterateEquiv f i).injective hh
    change π z∈U
    rwa [hz]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [StandardBorelSpace X] in
lemma relative_tower_base_copy (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (e : X ≃ᵐ X) (f : Y ≃ᵐ Y) (π : X → Y) (hπ : MeasurePreserving π μ ν)
    (hcomm : ∀ x,π (e x)=f (π x))
    (p : Y → A) (α : X → B) (hp : Measurable p) (hα : Measurable α)
    {U : Set Y} (hU : MeasurableSet U) (N : ℕ)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((f^[i.val]) '' U) ((f^[j.val]) '' U))) :
    ∃ b : Y → B,Measurable b ∧
      (ν.restrict U).map (word f (fun y => (p y,b y)) N)=
      (μ.restrict (π ⁻¹' U)).map (word e (fun x => (p (π x),α x)) N) := by
  let V := π ⁻¹' U
  have hV : MeasurableSet V := hπ.measurable hU
  have hP : Measurable (word e (p ∘ π) N) :=
    word_measurable e e.measurable _ (hp.comp hπ.measurable) N
  have hQ : Measurable (word f p N) := word_measurable f f.measurable p hp N
  have hA : Measurable (word e α N) := word_measurable e e.measurable α hα N
  have hfirst : (μ.restrict V).map (word e (p ∘ π) N)=(ν.restrict U).map (word f p N) := by
    rw [factor_word e f π hcomm p N,←Measure.map_map hQ hπ.measurable,map_restrict_factor μ ν π hπ hU]
  obtain ⟨C,hC,hjoint⟩ := relative_finite_realization (μ.restrict V) (ν.restrict U)
    (word e (p ∘ π) N) (word e α N) (word f p N) hP hA hQ hfirst
  let b := paintTower f U N C (fun _ => Classical.arbitrary B)
  have hb : Measurable b := measurable_paintTower f hU N hd hC measurable_const
  refine ⟨b,hb,?_⟩
  let zip : (Fin N → A) × (Fin N → B) → (Fin N → A×B) := fun ab i => (ab.1 i,ab.2 i)
  have hzip : Measurable zip := measurable_of_finite zip
  have heq : (ν.restrict U).map (word f (fun y => (p y,b y)) N)=
      (ν.restrict U).map (zip ∘ fun y => (word f p N y,C y)) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hU] with y hy
    have hh : word f b N y=C y := paintTower_word f U N hd C _ hy
    funext i
    exact congrArg (fun c => (p (f^[i.val] y),c i)) hh
  rw [heq,←Measure.map_map hzip (hQ.prodMk hC),hjoint,
    Measure.map_map hzip (hP.prodMk hA)]
  rfl

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma equal_base_level_laws (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y ≃ᵐ Y) (hf : MeasurePreserving f ν ν)
    (V : Set X) (U : Set Y) (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {N m : ℕ} (hbase : (μ.restrict V).map (word e p N)=(ν.restrict U).map (word f q N))
    (i : ℕ) (hi : i+m≤N) :
    (μ.restrict ((e^[i]) '' V)).map (word e p m)=
      (ν.restrict ((f^[i]) '' U)).map (word f q m) := by
  have heI : MeasurePreserving (iterateEquiv e i) μ μ := by
    simpa only [funext (iterateEquiv_apply e i)] using he.iterate i
  have hfI : MeasurePreserving (iterateEquiv f i) ν ν := by
    simpa only [funext (iterateEquiv_apply f i)] using hf.iterate i
  have hpw := word_measurable e e.measurable p hp m
  have hqw := word_measurable f f.measurable q hq m
  change (μ.restrict ((iterateEquiv e i) '' V)).map (word e p m)=
    (ν.restrict ((iterateEquiv f i) '' U)).map (word f q m)
  rw [map_restrict_image_equiv μ (iterateEquiv e i) heI V _ hpw,
    map_restrict_image_equiv ν (iterateEquiv f i) hfI U _ hqw]
  have hcomp (g : X ≃ᵐ X) : word g p m ∘ iterateEquiv g i=wordWindow i hi ∘ word g p N := by
    funext x
    exact (wordWindow_word g p i hi x).symm
  rw [hcomp e]
  have hcomp' : word f q m ∘ iterateEquiv f i=wordWindow i hi ∘ word f q N := by
    funext y
    exact (wordWindow_word f q i hi y).symm
  rw [hcomp',←Measure.map_map (measurable_of_countable (wordWindow (A:=A) i hi))
    (word_measurable e e.measurable p hp N),hbase,
    Measure.map_map (measurable_of_countable (wordWindow (A:=A) i hi))
    (word_measurable f f.measurable q hq N)]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A] [MeasurableSingletonClass A] in
lemma lawClose_of_common_restriction (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    {V : Set X} {U : Set Y} (_ : MeasurableSet V) (_ : MeasurableSet U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (hc : (μ.restrict V).map p=(ν.restrict U).map q) :
    LawClose (μ.map p) (ν.map q) (μ.real Vᶜ+ν.real Uᶜ) := by
  intro D hD
  rw [map_measureReal_apply hp hD,map_measureReal_apply hq hD]
  have hcommon := congrArg (fun ξ : Measure A => (ξ D).toReal) hc
  simp only [Measure.map_apply hp hD,Measure.map_apply hq hD,
    Measure.restrict_apply (hp hD),Measure.restrict_apply (hq hD)] at hcommon
  change μ.real ((p ⁻¹' D)∩V)=ν.real ((q ⁻¹' D)∩U) at hcommon
  have hp₀ : μ.real ((p ⁻¹' D)∩V)≤μ.real (p ⁻¹' D) := measureReal_mono inter_subset_left
  have hq₀ : ν.real ((q ⁻¹' D)∩U)≤ν.real (q ⁻¹' D) := measureReal_mono inter_subset_left
  have hp₁ : μ.real (p ⁻¹' D)≤μ.real ((p ⁻¹' D)∩V)+μ.real Vᶜ := by
    apply (measureReal_mono (μ:=μ) (show p ⁻¹' D⊆((p ⁻¹' D)∩V)∪Vᶜ by
      intro x hx; by_cases hv : x∈V
      · exact Or.inl ⟨hx,hv⟩
      · exact Or.inr hv)).trans
    exact measureReal_union_le _ _
  have hq₁ : ν.real (q ⁻¹' D)≤ν.real ((q ⁻¹' D)∩U)+ν.real Uᶜ := by
    apply (measureReal_mono (μ:=ν) (show q ⁻¹' D⊆((q ⁻¹' D)∩U)∪Uᶜ by
      intro x hx; by_cases hu : x∈U
      · exact Or.inl ⟨hx,hu⟩
      · exact Or.inr hu)).trans
    exact measureReal_union_le _ _
  rw [abs_le]
  constructor <;> linarith [measureReal_nonneg (μ:=μ) (s:=Vᶜ),measureReal_nonneg (μ:=ν) (s:=Uᶜ)]

omit [StandardBorelSpace X] in
lemma tower_disjoint_mono (e : X ≃ᵐ X) (V : Set X) {N M : ℕ} (hm : M≤N)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V))) :
    Pairwise (fun i j : Fin M => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) := by
  intro i j hij
  apply hd (i:=⟨i.val,i.isLt.trans_le hm⟩) (j:=⟨j.val,j.isLt.trans_le hm⟩)
  intro hh
  exact hij (Fin.ext (congrArg (fun z : Fin N => z.val) hh))

omit [StandardBorelSpace X] [StandardBorelSpace Y] in
lemma equal_base_interior_laws (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y ≃ᵐ Y) (hf : MeasurePreserving f ν ν)
    {V : Set X} {U : Set Y} (hV : MeasurableSet V) (hU : MeasurableSet U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {N m : ℕ}
    (hdV : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)))
    (hdU : Pairwise (fun i j : Fin N => Disjoint ((f^[i.val]) '' U) ((f^[j.val]) '' U)))
    (hbase : (μ.restrict V).map (word e p N)=(ν.restrict U).map (word f q N)) :
    (μ.restrict (⋃ i : Fin (N-m),(e^[i.val]) '' V)).map (word e p m)=
    (ν.restrict (⋃ i : Fin (N-m),(f^[i.val]) '' U)).map (word f q m) := by
  rw [map_restrict_finite_iUnion μ (fun i : Fin (N-m) => (e^[i.val]) '' V) (fun i => measurableSet_iterate_image e hV i.val)
    (tower_disjoint_mono e V (Nat.sub_le N m) hdV) _ (word_measurable e e.measurable p hp m),
    map_restrict_finite_iUnion ν (fun i : Fin (N-m) => (f^[i.val]) '' U) (fun i => measurableSet_iterate_image f hU i.val)
    (tower_disjoint_mono f U (Nat.sub_le N m) hdU) _ (word_measurable f f.measurable q hq m)]
  apply Finset.sum_congr rfl
  intro i _
  exact equal_base_level_laws μ ν e he f hf V U p q hp hq hbase i.val (by omega)

omit [StandardBorelSpace X] in
lemma tower_interior_compl_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) {U : Set X} (hU : MeasurableSet U)
    {N m : ℕ} (hN : 0<N) (hm : m≤N)
    (hd : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U))) :
    μ.real (⋃ i : Fin (N-m),(e^[i.val]) '' U)ᶜ≤
      μ.real (⋃ i : Fin N,(e^[i.val]) '' U)ᶜ+(m : ℝ)/(N : ℝ) := by
  have hc := congrArg ENNReal.toReal (tower_measure μ e he hU (N-m)
    (tower_disjoint_mono e U (Nat.sub_le N m) hd))
  have ht := congrArg ENNReal.toReal (tower_measure μ e he hU N hd)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_sub hm] at hc ht
  change μ.real (⋃ i : Fin (N-m),(e^[i.val]) '' U)=((N : ℝ)-m)*μ.real U at hc
  change μ.real (⋃ i : Fin N,(e^[i.val]) '' U)=(N : ℝ)*μ.real U at ht
  have hC := measureReal_add_measureReal_compl (μ:=μ)
    (MeasurableSet.iUnion (fun i : Fin (N-m) => measurableSet_iterate_image e hU i.val))
  have hT := measureReal_add_measureReal_compl (μ:=μ)
    (MeasurableSet.iUnion (fun i : Fin N => measurableSet_iterate_image e hU i.val))
  have hu : μ.real univ=1 := by simp [Measure.real]
  rw [hu,hc] at hC
  rw [hu,ht] at hT
  have hmass : (N : ℝ)*μ.real U≤1 := by
    linarith [measureReal_nonneg (μ:=μ) (s:=(⋃ i : Fin N,(e^[i.val]) '' U)ᶜ)]
  have hbound : (m : ℝ)*μ.real U≤(m : ℝ)/(N : ℝ) := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg m)]
  linarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
  [TopologicalSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

omit [StandardBorelSpace X] in
theorem relative_measurable_graph_approx (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] [NullSingletonClass ν] [ν.OuterRegular]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (f : Y ≃ᵐ Y) (hf : Ergodic f ν)
    (π : X → Y) (hπ : MeasurePreserving π μ ν) (hcomm : ∀ x,π (e x)=f (π x))
    (p : Y → A) (α : X → B) (hp : Measurable p) (hα : Measurable α)
    (m : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ b : Y → B,Measurable b ∧
      LawClose (μ.map (word e (fun x => (p (π x),α x)) m))
        (ν.map (word f (fun y => (p y,b y)) m)) ε := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max (m : ℝ) (4*(m : ℝ)/ε)+1)
  have hNm : m<N := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) (by linarith : max (m : ℝ) (4*(m : ℝ)/ε)<N))
  have hNp : 0<N := lt_of_le_of_lt (Nat.zero_le m) hNm
  have hfrac : (m : ℝ)/(N : ℝ)<ε/4 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hNp)).mpr
    have hh : 4*(m : ℝ)/ε<(N : ℝ) := by linarith [le_max_right (m : ℝ) (4*(m : ℝ)/ε)]
    have hh' := (div_lt_iff₀ hε).mp hh
    linarith
  obtain ⟨U,hU,hdU,hcover⟩ := exists_rohlin_tower ν f hf hNp (show 0<ε/4 by positivity)
  let V := π ⁻¹' U
  have hV : MeasurableSet V := hπ.measurable hU
  have hlevels (i : ℕ) : (e^[i]) '' V=π ⁻¹' ((f^[i]) '' U) := factor_tower_level e f π hcomm U i
  have hdV : Pairwise (fun i j : Fin N => Disjoint ((e^[i.val]) '' V) ((e^[j.val]) '' V)) := by
    intro i j hij
    rw [hlevels,hlevels]
    exact (hdU i j hij).preimage π
  obtain ⟨b,hb,hbase⟩ := relative_tower_base_copy μ ν e f π hπ hcomm p α hp hα hU N hdU
  refine ⟨b,hb,?_⟩
  have hi := equal_base_interior_laws μ ν e he f hf.toMeasurePreserving hV hU
    (fun x => (p (π x),α x)) (fun y => (p y,b y)) ((hp.comp hπ.measurable).prodMk hα)
    (hp.prodMk hb) (m:=m) hdV hdU hbase.symm
  have hc := lawClose_of_common_restriction μ ν
    (MeasurableSet.iUnion (fun i : Fin (N-m) => measurableSet_iterate_image e hV i.val))
    (MeasurableSet.iUnion (fun i : Fin (N-m) => measurableSet_iterate_image f hU i.val))
    _ _ (word_measurable e e.measurable _ ((hp.comp hπ.measurable).prodMk hα) m)
    (word_measurable f f.measurable _ (hp.prodMk hb) m) hi
  have hcU : ν.real (⋃ i : Fin N,(f^[i.val]) '' U)ᶜ<ε/4 := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hcover
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hunion : (⋃ i : Fin N,(e^[i.val]) '' V)=π ⁻¹' (⋃ i : Fin N,(f^[i.val]) '' U) := by
    simp only [hlevels,preimage_iUnion]
  have hcV : μ.real (⋃ i : Fin N,(e^[i.val]) '' V)ᶜ=ν.real (⋃ i : Fin N,(f^[i.val]) '' U)ᶜ := by
    rw [hunion,←preimage_compl]
    exact congrArg ENNReal.toReal (hπ.measure_preimage
      (MeasurableSet.iUnion (fun i : Fin N => measurableSet_iterate_image f hU i.val)).compl.nullMeasurableSet)
  have h₁ := tower_interior_compl_bound μ e he hV hNp hNm.le hdV
  have h₂ := tower_interior_compl_bound ν f hf.toMeasurePreserving hU hNp hNm.le hdU
  exact hc.mono (by linarith)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators symmDiff
variable {X : Type*} [mX : MeasurableSpace X]

lemma finite_sigma_set_approx (μ : Measure X) [IsFiniteMeasure μ]
    (m : ℕ → MeasurableSpace X) (hm : Monotone m) (hgen : ‹MeasurableSpace X›=⨆ n,m n)
    {s : Set X} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0<ε) :
    ∃ n : ℕ,∃ t : Set X,MeasurableSet[m n] t ∧ μ (t ∆ s)<ε := by
  let C : Set (Set X) := {t | ∃ n,MeasurableSet[m n] t}
  have hC : IsSetRing C := {
    empty_mem := ⟨0,@MeasurableSet.empty X (m 0)⟩
    union_mem := by
      rintro s t ⟨i,hi⟩ ⟨j,hj⟩
      exact ⟨max i j,((hm (le_max_left _ _)) _ hi).union ((hm (le_max_right _ _)) _ hj)⟩
    sdiff_mem := by
      rintro s t ⟨i,hi⟩ ⟨j,hj⟩
      exact ⟨max i j,((hm (le_max_left _ _)) _ hi).diff ((hm (le_max_right _ _)) _ hj)⟩ }
  have he : (⨆ n,m n)=MeasurableSpace.generateFrom C := by
    apply le_antisymm
    · apply iSup_le
      intro n t ht
      exact MeasurableSpace.measurableSet_generateFrom ⟨n,ht⟩
    · apply MeasurableSpace.generateFrom_le
      rintro t ⟨n,ht⟩
      exact (le_iSup m n) _ ht
  have hc : ∃ D : Set (Set X),D.Countable ∧ D⊆C ∧ μ (⋃₀ D)ᶜ=0 := by
    refine ⟨{univ},countable_singleton _,?_,?_⟩
    · intro t ht
      rcases mem_singleton_iff.mp ht with rfl
      exact ⟨0,@MeasurableSet.univ X (m 0)⟩
    · simp
  obtain ⟨t,⟨n,hn⟩,ht⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hc
    (hgen.trans he) hs hε
  exact ⟨n,t,hn,ht⟩

theorem finite_factor_approx (μ : Measure X) [IsProbabilityMeasure μ]
    (F : ℕ → Type*) [∀ n,Fintype (F n)] [∀ n,MeasurableSpace (F n)]
    [∀ n,MeasurableSingletonClass (F n)] (f : (n : ℕ) → X → F n)
    (hm : Monotone (fun n => MeasurableSpace.comap (f n) inferInstance))
    (hgen : ‹MeasurableSpace X›=⨆ n,MeasurableSpace.comap (f n) inferInstance)
    {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,∃ D : F N → A,μ.real {x | D (f N x)≠p x}<ε := by
  classical
  let δ := ε/((Fintype.card A : ℝ)+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  have ha (a : A) := finite_sigma_set_approx μ
    (fun n => MeasurableSpace.comap (f n) inferInstance) hm hgen
    (hp (measurableSet_singleton a)) (ENNReal.ofReal_pos.mpr hδ)
  choose n t ht hclose using ha
  let N := Finset.univ.sup n
  have hn (a : A) : n a≤N := Finset.le_sup (Finset.mem_univ a)
  have ht' (a : A) : MeasurableSet[MeasurableSpace.comap (f N) inferInstance] (t a) :=
    (hm (hn a)) _ (ht a)
  have hu (a : A) := MeasurableSpace.measurableSet_comap.mp (ht' a)
  choose U hUm hUt using hu
  let D : F N → A := fun y => if h : ∃ a,y∈U a then h.choose else Classical.ofNonempty
  have hbad : {x | D (f N x)≠p x}⊆⋃ a : A,t a ∆ (p ⁻¹' {a}) := by
    intro x hx
    by_contra hn
    have hnot (a : A) : x∉t a ∆ (p ⁻¹' {a}) := by
      intro ha
      exact hn (mem_iUnion.mpr ⟨a,ha⟩)
    have he (a : A) : f N x∈U a ↔ p x=a := by
      have hiff : x∈t a ↔ x∈p ⁻¹' {a} := by
        have hh := hnot a
        simp only [mem_symmDiff] at hh
        tauto
      rw [←hUt a] at hiff
      exact hiff
    have hex : ∃ a,f N x∈U a := ⟨p x,(he _).mpr rfl⟩
    exact hx (by simpa only [D,dite_eq_left hex] using ((he hex.choose).mp hex.choose_spec).symm)
  have hc (a : A) : μ.real (t a ∆ (p ⁻¹' {a}))≤δ := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr (hclose a)
    rw [ENNReal.toReal_ofReal hδ.le] at hh
    exact hh.le
  refine ⟨N,D,lt_of_le_of_lt ((measureReal_mono hbad).trans
    ((measureReal_iUnion_fintype_le _).trans (Finset.sum_le_sum (fun a _ => hc a)))) ?_⟩
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have he : ((Fintype.card A : ℝ)+1)*δ=ε := mul_div_cancel₀ ε (ne_of_gt (by positivity))
  nlinarith

omit mX in
lemma joinedBinary_comap_monotone (α : ℕ → ℕ → X → Bool) :
    Monotone (fun N => MeasurableSpace.comap (joinedBinary α N) inferInstance) := by
  intro i j hij
  let r : ((Fin j×Fin j) → Bool) → ((Fin i×Fin i) → Bool) :=
    fun w p => w (p.1.castLE hij,p.2.castLE hij)
  have hF : Measurable[MeasurableSpace.comap (joinedBinary α j) inferInstance]
      (joinedBinary α j) := measurable_iff_comap_le.mpr le_rfl
  have hr := (measurable_of_countable r).comp hF
  exact measurable_iff_comap_le.mp hr

lemma joinedBinary_generates [StandardBorelSpace X]
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x)) :
    ‹MeasurableSpace X›=⨆ N,MeasurableSpace.comap (joinedBinary α N) inferInstance := by
  let F : X → ℕ → ℕ → Bool := fun x i j => α i j x
  have hF : Measurable F := Measurable.of_eval (fun index => Measurable.of_eval (hα index))
  have hFE : MeasurableEmbedding F := hF.measurableEmbedding hsep
  have heq : MeasurableSpace.comap F inferInstance = mX := hFE.comap_eq
  have hupper : (⨆ N,MeasurableSpace.comap (joinedBinary α N) inferInstance) ≤ mX := by
    apply iSup_le
    intro N
    exact measurable_iff_comap_le.mp (measurable_joinedBinary hα N)
  let m : MeasurableSpace X := ⨆ N,MeasurableSpace.comap (joinedBinary α N) inferInstance
  have hlarge (i j : ℕ) : @Measurable X Bool m inferInstance (α i j) := by
    let N := max i j+1
    let a : Fin N×Fin N := (⟨i,by dsimp [N]; omega⟩,⟨j,by dsimp [N]; omega⟩)
    have hN : @Measurable X ((Fin N×Fin N) → Bool) m inferInstance (joinedBinary α N) :=
      measurable_iff_comap_le.mpr
        (le_iSup (fun n => MeasurableSpace.comap (joinedBinary α n) inferInstance) N)
    exact (measurable_pi_apply a).comp hN
  have hsup : @Measurable X (ℕ → ℕ → Bool) m inferInstance F :=
    Measurable.of_eval (fun index => Measurable.of_eval (hlarge index))
  apply le_antisymm
  · have hle : MeasurableSpace.comap F inferInstance ≤ m := measurable_iff_comap_le.mp hsup
    exact (le_of_eq heq.symm).trans hle
  · exact hupper

theorem joinedBinary_approximates [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    {A : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,∃ D : ((Fin N×Fin N) → Bool) → A,
      μ.real {x | D (joinedBinary α N x)≠p x}<ε :=
  finite_factor_approx μ (fun N => (Fin N×Fin N) → Bool) (joinedBinary α)
    (joinedBinary_comap_monotone α) (joinedBinary_generates α hα hsep) p hp hε
end HyperbolicCoding

end

end OAI
