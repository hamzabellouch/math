import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.ConditionalRefinementInformation
import OAI.Dynamics.StandardMap.Towers.PhaseAveraging

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [Fintype A] [Fintype B]

omit [Fintype A] in
lemma mass_smul_measure (μ : Measure X) (c : ℝ≥0∞) (p : X → A) (a : A) :
    mass (c • μ) p a=c.toReal*mass μ p a := by
  simp only [mass,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul]

omit [Fintype A] in
lemma normalize_mass_cancel (μ : Measure X) [IsFiniteMeasure μ] {U : Set X}
    (hU : 0<μ U) (p : X → A) (a : A) :
    μ.real U*mass ((μ U)⁻¹ • μ.restrict U) p a=mass (μ.restrict U) p a := by
  rw [Measure.real,mass_smul_measure,ENNReal.toReal_inv,←mul_assoc]
  rw [mul_inv_cancel₀ (ENNReal.toReal_pos hU.ne' (measure_ne_top _ _)).ne',one_mul]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}
noncomputable def scale (R : MatrixCoupling p q) (c : ℝ) (hc : 0≤c) :
    MatrixCoupling (fun a => c*p a) (fun b => c*q b) where
  weight a b := c*R.weight a b
  nonneg a b := mul_nonneg hc (R.nonneg a b)
  row a := by rw [←Finset.mul_sum,R.row]
  col b := by rw [←Finset.mul_sum,R.col]
lemma scale_cost (R : MatrixCoupling p q) (c : ℝ) (hc : 0≤c) (d : A → B → ℝ) :
    (R.scale c hc).cost d=c*R.cost d := by
  simp only [cost,scale,mul_assoc,←Finset.mul_sum]
lemma cost_nonneg (R : MatrixCoupling p q) (d : A → B → ℝ) (hd : ∀ a b,0≤d a b) :
    0≤R.cost d :=
  Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => mul_nonneg (R.nonneg a b) (hd a b)))
lemma cost_mul (R : MatrixCoupling p q) (c : ℝ) (d : A → B → ℝ) :
    R.cost (fun a b => c*d a b)=c*R.cost d := by
  simp only [cost]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring
end MatrixCoupling

lemma nameCost_nonneg {E : Type*} {n : ℕ} (a b : Fin n → E) : 0≤nameCost a b :=
  Finset.sum_nonneg (fun _ _ => symbolCost_nonneg _ _)
lemma nameCost_le_symbolCost {E : Type*} {n : ℕ} (a b : Fin n → E) :
    nameCost a b≤(n : ℝ)*symbolCost a b := by
  classical
  by_cases hab : a=b
  · subst b; simp [nameCost_self,symbolCost_self]
  · rw [symbolCost,ite_eq_right hab,mul_one]
    calc
      nameCost a b≤∑ _ : Fin n,(1 : ℝ) := Finset.sum_le_sum (fun i _ => by
        unfold symbolCost; split <;> norm_num)
      _=(n : ℝ) := by simp
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

omit [StandardBorelSpace X] in
lemma normalized_restriction_probability (μ : Measure X) [IsFiniteMeasure μ]
    {U : Set X} (hU : 0<μ U) : IsProbabilityMeasure ((μ U)⁻¹ • μ.restrict U) := by
  constructor
  rw [Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hU.ne' (measure_ne_top _ _)

theorem lift_ambient_word_transport [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    {n : ℕ} (hn : 0<n) (p : X → A) (hp : Measurable p)
    (t : (Fin n → A) → ℝ) (R : MatrixCoupling (mass μ (word e p n)) t)
    {η ε : ℝ} (hη : 0≤η) (hε : 0<ε) (hR : R.cost nameCost≤(n : ℝ)*η) :
    ∃ (U : Set X) (q : X → A),MeasurableSet U ∧ 0<μ U ∧ Measurable q ∧
      Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) ∧
      μ.real (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ<ε ∧
      (∀ b,mass (μ.restrict U) (word e q n) b=μ.real U*t b) ∧
      μ.real {x | p x≠q x}≤η+ε ∧
      ∀ x,x∉⋃ i : Fin n,(e^[i.val]) '' U → q x=p x := by
  have hw := word_measurable e e.measurable p hp n
  obtain ⟨U,hU,hUp,hd,hcover,hclose⟩ := exists_unbiased_rohlin_tower μ e he hn (word e p n) hw hε
  let ν := (μ U)⁻¹ • μ.restrict U
  have : IsProbabilityMeasure ν := normalized_restriction_probability μ hUp
  obtain ⟨S,hS⟩ := coupling_of_observation_lawClose ν μ (word e p n) (word e p n) hw hw hclose
  have hSn : S.cost nameCost≤(n : ℝ)*ε := by
    have hh := S.cost_mono nameCost (fun a b => (n : ℝ)*symbolCost a b) (nameCost_le_symbolCost (n:=n))
    rw [S.cost_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg n))
  have hc : 0≤μ.real U := ENNReal.toReal_nonneg
  let W := (S.comp R).scale (μ.real U) hc
  let W' : MatrixCoupling (mass (μ.restrict U) (word e p n)) (fun b => μ.real U*t b) := {
    weight := W.weight
    nonneg := W.nonneg
    row := fun a => (W.row a).trans (normalize_mass_cancel μ hUp (word e p n) a)
    col := W.col }
  have hW : W'.cost nameCost≤μ.real U*((n : ℝ)*(ε+η)) := by
    change W.cost nameCost≤_
    dsimp only [W]
    rw [MatrixCoupling.scale_cost]
    apply mul_le_mul_of_nonneg_left _ hc
    have hh := S.comp_cost_le R nameCost nameCost nameCost nameCost_triangle
    nlinarith
  obtain ⟨q,hq,_hjoint,hbase,hcost,hoff⟩ := realize_tower_coupling μ e he.toMeasurePreserving hU n hd p hp _ W'
  have hmass : (n : ℝ)*μ.real U≤1 := by
    have hh := tower_measure μ e he.toMeasurePreserving hU n hd
    have hhR := congrArg ENNReal.toReal hh
    rw [ENNReal.toReal_mul,ENNReal.toReal_natCast] at hhR
    have hi := measureReal_mono (μ:=μ) (subset_univ (⋃ i : Fin n,(e^[i.val]) '' U))
    simp only [Measure.real,measure_univ,ENNReal.toReal_one,hhR] at hi
    exact hi
  refine ⟨U,q,hU,hUp,hq,hd,hcover,hbase,?_,hoff⟩
  rw [hcost]
  calc
    W'.cost nameCost≤μ.real U*((n : ℝ)*(ε+η)) := hW
    _≤η+ε := by nlinarith [mul_le_mul_of_nonneg_right hmass (by linarith : 0≤ε+η)]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
lemma base_mass_to_law (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) [IsFiniteMeasure ν]
    {U : Set X} {p : X → A} {q : Y → A} (hp : Measurable p) (hq : Measurable q)
    (h : ∀ a,mass (μ.restrict U) p a=μ.real U*mass ν q a) :
    (μ.restrict U).map p=μ U • ν.map q := by
  apply Measure.ext_of_singleton
  intro a
  have hright : (μ U • ν.map q) {a}≠⊤ := by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hright).mp
  rw [Measure.map_apply hp (measurableSet_singleton a),Measure.smul_apply,smul_eq_mul,
    ENNReal.toReal_mul,Measure.map_apply hq (measurableSet_singleton a)]
  exact h a

def wordWindow {n m : ℕ} (i : ℕ) (hi : i+m≤n) (w : Fin n → A) : Fin m → A :=
  fun j => w ⟨j.val+i,by omega⟩

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A] in
lemma wordWindow_word (f : X → X) (p : X → A) {n m : ℕ} (i : ℕ) (hi : i+m≤n) (x : X) :
    wordWindow i hi (word f p n x)=word f p m (f^[i] x) := by
  funext j
  simp only [wordWindow,word,Function.iterate_add_apply]

omit [StandardBorelSpace X] in
lemma tower_interior_level_law (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν) {U : Set X}
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hbase : (μ.restrict U).map (word e p n)=μ U • ν.map (word f q n))
    (i : ℕ) (hi : i+m≤n) :
    (μ.restrict ((e^[i]) '' U)).map (word e p m)=μ U • ν.map (word f q m) := by
  have hpw := word_measurable e e.measurable p hp m
  have hqn := word_measurable f hf.measurable q hq n
  have hqm := word_measurable f hf.measurable q hq m
  have hW : Measurable (wordWindow (A:=A) i hi) := measurable_of_countable _
  have heI : MeasurePreserving (iterateEquiv e i) μ μ := by
    simpa only [funext (iterateEquiv_apply e i)] using he.iterate i
  change (μ.restrict ((iterateEquiv e i) '' U)).map (word e p m)=_
  rw [map_restrict_image_equiv μ (iterateEquiv e i) heI U (word e p m) hpw]
  have hcomp : word e p m ∘ iterateEquiv e i=wordWindow i hi ∘ word e p n := by
    funext x
    exact (wordWindow_word e p i hi x).symm
  rw [hcomp,←Measure.map_map hW (word_measurable e e.measurable p hp n),hbase,
    Measure.map_smul _ hW.aemeasurable,Measure.map_map hW hqn]
  have hcomp' : wordWindow i hi ∘ word f q n=word f q m ∘ f^[i] := by
    funext y
    exact wordWindow_word f q i hi y
  rw [hcomp',←Measure.map_map hqm (hf.measurable.iterate i),(hf.iterate i).map_eq]

omit [StandardBorelSpace X] in
lemma tower_interior_law (μ : Measure X) [IsFiniteMeasure μ]
    (ν : Measure Y) [IsFiniteMeasure ν] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν) {U : Set X} (hU : MeasurableSet U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hm : m≤n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (hbase : (μ.restrict U).map (word e p n)=μ U • ν.map (word f q n)) :
    (μ.restrict (⋃ i : Fin (n-m),(e^[i.val]) '' U)).map (word e p m)=
      (((n-m : ℕ) : ℝ≥0∞)*μ U) • ν.map (word f q m) := by
  have hd' : Pairwise (fun i j : Fin (n-m) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) := by
    intro i j hij
    apply hd (i:=⟨i.val,by omega⟩) (j:=⟨j.val,by omega⟩)
    intro hh
    exact hij (Fin.ext (congrArg (fun z : Fin n => z.val) hh))
  rw [map_restrict_finite_iUnion μ (fun i : Fin (n-m) => (e^[i.val]) '' U) (fun i => measurableSet_iterate_image e hU i.val) hd' _
    (word_measurable e e.measurable p hp m)]
  have hi (i : Fin (n-m)) := tower_interior_level_law μ ν e he f hf p q hp hq (m:=m) hbase i.val (by omega)
  simp_rw [hi]
  rw [←Finset.sum_smul]
  congr 1
  simp [nsmul_eq_mul]

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

omit [StandardBorelSpace X] in
theorem tower_short_word_lawClose (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (f : Y → Y) (hf : MeasurePreserving f ν ν) {U : Set X} (hU : MeasurableSet U) (hUp : 0<μ U)
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    {n m : ℕ} (hm : m<n)
    (hd : Pairwise (fun i j : Fin n => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)))
    (hbase : (μ.restrict U).map (word e p n)=μ U • ν.map (word f q n))
    {ε : ℝ} (hcover : μ.real (⋃ i : Fin n,(e^[i.val]) '' U)ᶜ<ε) :
    LawClose (μ.map (word e p m)) (ν.map (word f q m)) (ε+(m : ℝ)/(n : ℝ)) := by
  let C : Set X := ⋃ i : Fin (n-m),(e^[i.val]) '' U
  let T : Set X := ⋃ i : Fin n,(e^[i.val]) '' U
  have hC : MeasurableSet C := MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hU i.val)
  have hT : MeasurableSet T := MeasurableSet.iUnion (fun i => measurableSet_iterate_image e hU i.val)
  have hd' : Pairwise (fun i j : Fin (n-m) => Disjoint ((e^[i.val]) '' U) ((e^[j.val]) '' U)) := by
    intro i j hij
    apply hd (i:=⟨i.val,by omega⟩) (j:=⟨j.val,by omega⟩)
    intro hh
    exact hij (Fin.ext (congrArg (fun z : Fin n => z.val) hh))
  have hCm : μ C=((n-m : ℕ) : ℝ≥0∞)*μ U := tower_measure μ e he hU (n-m) hd'
  have hTm : μ T=(n : ℝ≥0∞)*μ U := tower_measure μ e he hU n hd
  have hCp : 0<μ C := by
    rw [hCm]
    exact ENNReal.mul_pos (by exact_mod_cast (show 0<n-m by omega).ne') hUp.ne'
  have hCr : μ.real C=((n : ℝ)-(m : ℝ))*μ.real U := by
    change (μ C).toReal=_
    rw [hCm,ENNReal.toReal_mul,ENNReal.toReal_natCast,Nat.cast_sub hm.le]
    rfl
  have hTr : μ.real T=(n : ℝ)*μ.real U := by
    change (μ T).toReal=_
    rw [hTm,ENNReal.toReal_mul,ENNReal.toReal_natCast]
    rfl
  have hi := tower_interior_law μ ν e he f hf hU p q hp hq hm.le hd hbase
  have hnorm : (((μ C)⁻¹ • μ.restrict C).map (word e p m))=ν.map (word f q m) := by
    rw [Measure.map_smul _ (word_measurable e e.measurable p hp m).aemeasurable]
    rw [hi,←hCm,smul_smul,ENNReal.inv_mul_cancel hCp.ne' (measure_ne_top _ _),one_smul]
  have hclose := (normalized_restriction_observation_close μ hC hCp (word e p m)
    (word_measurable e e.measurable p hp m)).symm
  rw [hnorm] at hclose
  have hTc : μ.real T+μ.real Tᶜ=1 := by
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
      measureReal_add_measureReal_compl (μ:=μ) hT
  have hTr1 : (n : ℝ)*μ.real U≤1 := by
    have hnon : 0≤μ.real Tᶜ := ENNReal.toReal_nonneg
    rw [hTr] at hTc
    linarith
  have hn : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hbound : (m : ℝ)*μ.real U≤(m : ℝ)/(n : ℝ) := by
    apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hTr1 (Nat.cast_nonneg m)
    nlinarith
  intro D hD
  apply (hclose D hD).trans
  rw [hCr]
  rw [hTr] at hTc
  have hc : μ.real Tᶜ<ε := hcover
  nlinarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

theorem dynamical_word_copy [TopologicalSpace X] [SecondCountableTopology X]
    [OpensMeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] [μ.OuterRegular] (e : X ≃ᵐ X) (he : Ergodic e μ)
    (ν : Measure Y) [IsProbabilityMeasure ν] (f : Y → Y) (hf : MeasurePreserving f ν ν)
    (p : X → A) (r : Y → A) (hp : Measurable p) (hr : Measurable r)
    {n m : ℕ} (hm : m<n)
    (R : MatrixCoupling (mass μ (word e p n)) (mass ν (word f r n)))
    {η ε : ℝ} (hη : 0≤η) (hε : 0<ε) (hR : R.cost nameCost≤(n : ℝ)*η) :
    ∃ q : X → A,Measurable q ∧ μ.real {x | p x≠q x}≤η+ε ∧
      LawClose (μ.map (word e q m)) (ν.map (word f r m)) (ε+(m : ℝ)/(n : ℝ)) := by
  obtain ⟨U,q,hU,hUp,hq,hd,hcover,hbase,hcost,_hoff⟩ :=
    lift_ambient_word_transport μ e he (by omega) p hp _ R hη hε hR
  have hmap := base_mass_to_law μ ν (word_measurable e e.measurable q hq n)
    (word_measurable f hf.measurable r hr n) hbase
  exact ⟨q,hq,hcost,tower_short_word_lawClose μ ν e he.toMeasurePreserving f hf hU hUp
    q r hq hr hm hd hmap hcover⟩
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [TopologicalSpace Y] [SecondCountableTopology Y] [OpensMeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

theorem weakBernoulli_dynamical_copy
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) {η : ℝ} (hη : 0<η) :
    ∃ m : ℕ,∃ δ : ℝ,0<δ ∧
      ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν) (_ : NullSingletonClass ν) (_ : ν.OuterRegular)
        (T : Y ≃ᵐ Y) (_ : Ergodic T ν) (q : Y → A),Measurable q →
        LawClose (μ.map (word e p m)) (ν.map (word T q m)) δ →
        rate μ e p-δ≤rate ν T q →
        ∀ (l : ℕ) (ε : ℝ),0<ε → ∃ q' : Y → A,Measurable q' ∧
          ν.real {y | q y≠q' y}<η ∧
          LawClose (ν.map (word T q' l)) (μ.map (word e p l)) ε := by
  obtain ⟨m,s,hs,δ,hδ,hfd⟩ := weakBernoulli_finite_determination (Y:=Y) μ e he p hp hwb
    (show 0<η/2 by positivity)
  refine ⟨m,δ,hδ,?_⟩
  intro ν hν hnull hreg T hT q hq hclose hrate l ε hε
  let : IsProbabilityMeasure ν := hν
  let : NullSingletonClass ν := hnull
  let : ν.OuterRegular := hreg
  let ε₀ : ℝ := min (η/4) (ε/2)
  have hε₀ : 0<ε₀ := lt_min (by positivity) (by positivity)
  obtain ⟨n,hn⟩ := exists_nat_gt (max ((l : ℝ)+1) (2*(l : ℝ)/ε))
  have hnl : (l : ℝ)<(n : ℝ) := lt_of_lt_of_le (by linarith) ((le_max_left _ _).trans hn.le)
  have hnp : 0<n := by
    have : 0<(n : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg l) hnl
    exact_mod_cast this
  have hns : n≤n*s := Nat.le_mul_of_pos_right n hs
  have hlN : l<n*s := by
    have : l<n := by exact_mod_cast hnl
    exact this.trans_le hns
  have hN : 0<(n*s : ℕ) := lt_of_le_of_lt (Nat.zero_le l) hlN
  have hNr : 0<((n*s : ℕ) : ℝ) := by exact_mod_cast hN
  have hlarge : 2*(l : ℝ)/ε<((n*s : ℕ) : ℝ) :=
    ((le_max_right _ _).trans_lt hn).trans_le (by exact_mod_cast hns)
  have hfrac : (l : ℝ)/((n*s : ℕ) : ℝ)<ε/2 := by
    apply (div_lt_iff₀ hNr).mpr
    have hh := (div_lt_iff₀ hε).mp hlarge
    nlinarith
  obtain ⟨R,hR⟩ := hfd ν hν hnull T hT.toMeasurePreserving q hq hclose hrate n
  have hRS : R.symm.cost nameCost≤((n*s : ℕ) : ℝ)*(η/2) := by
    rw [MatrixCoupling.symm_cost R nameCost nameCost_comm]
    nlinarith
  obtain ⟨q',hq',hpaint,hlaw⟩ := dynamical_word_copy ν T hT μ e he q p hq hp hlN R.symm
    (show 0≤η/2 by positivity) hε₀ hRS
  refine ⟨q',hq',?_,?_⟩
  · have hb : ε₀≤η/4 := min_le_left _ _
    linarith
  · have hb : ε₀≤ε/2 := min_le_right _ _
    exact hlaw.mono (by linarith)
end HyperbolicCoding

end
end

end OAI
