import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.FiniteMaximalCoupling

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]

theorem exists_disjoint_cuts (s : Finset A) (w : A → ℝ) (hw : ∀ a,0≤w a)
    {S : Set X} (hS : MeasurableSet S) (hsum : (∑ a∈s,w a)≤μ.real S) :
    ∃ E : A → Set X,(∀ a∈s,MeasurableSet (E a) ∧ E a⊆S ∧ μ.real (E a)=w a) ∧
      (∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) := by
  classical
  induction s using Finset.induction_on generalizing S with
  | empty => exact ⟨fun _ => ∅,by simp,by simp⟩
  | @insert a s ha ih =>
    have hsumnonneg : 0≤∑ b∈s,w b := Finset.sum_nonneg (fun b _ => hw b)
    rw [Finset.sum_insert ha] at hsum
    obtain ⟨D,hD,hDS,hDm⟩ := exists_subset_real_mass μ hS (hw a) (by linarith)
    have hrem : (∑ b∈s,w b)≤μ.real (S\D) := by
      rw [measureReal_sdiff hDS hD,hDm]
      linarith
    obtain ⟨F,hF,hFd⟩ := ih (hS.diff hD) hrem
    refine ⟨fun b => if b=a then D else F b,?_,?_⟩
    · intro b hb
      by_cases hba : b=a
      · subst b
        simpa using And.intro hD (And.intro hDS hDm)
      · have hbs : b∈s := (Finset.mem_insert.mp hb).resolve_left hba
        simpa only [ite_eq_right hba] using And.intro (hF b hbs).1
          (And.intro ((hF b hbs).2.1.trans sdiff_subset) (hF b hbs).2.2)
    · intro b hb c hc hbc
      by_cases hba : b=a
      · subst b
        have hca : c≠a := Ne.symm hbc
        have hcs := (Finset.mem_insert.mp hc).resolve_left hca
        simp only [ite_eq_right hca]
        exact disjoint_left.mpr (fun x hxD hxF => ((hF c hcs).2.1 hxF).2 hxD)
      · by_cases hca : c=a
        · subst c
          have hbs := (Finset.mem_insert.mp hb).resolve_left hba
          simp only [ite_eq_right hba]
          exact disjoint_left.mpr (fun x hxF hxD => ((hF b hbs).2.1 hxF).2 hxD)
        · simp only [ite_eq_right hba,ite_eq_right hca]
          exact hFd b ((Finset.mem_insert.mp hb).resolve_left hba) c
            ((Finset.mem_insert.mp hc).resolve_left hca) hbc

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set

lemma exists_measurable_coloring {X A : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Nonempty A] (s : Finset A) (E : A → Set X)
    (hm : ∀ a∈s,MeasurableSet (E a))
    (hd : ∀ a∈s,∀ b∈s,a≠b → Disjoint (E a) (E b)) :
    ∃ q : X → A,Measurable q ∧ ∀ a∈s,∀ x∈E a,q x=a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary A,measurable_const,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨q,hq,hqa⟩ := ih (fun b hb => hm b (Finset.mem_insert_of_mem hb))
      (fun b hb c hc => hd b (Finset.mem_insert_of_mem hb) c (Finset.mem_insert_of_mem hc))
    let q' : X → A := (E a).piecewise (fun _ => a) q
    refine ⟨q',measurable_const.piecewise (hm a (Finset.mem_insert_self _ _)) hq,?_⟩
    intro b hb x hx
    by_cases hba : b=a
    · subst b
      exact Set.piecewise_eq_of_mem _ _ _ hx
    · have hbs := (Finset.mem_insert.mp hb).resolve_left hba
      have hxa : x∉E a := fun hxa => (hd b hb a (Finset.mem_insert_self _ _) hba).le_bot ⟨hx,hxa⟩
      exact (Set.piecewise_eq_of_notMem _ _ _ hxa).trans (hqa b hbs x hx)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem exists_finite_random_variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [Nonempty A]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    {S : Set X} (hS : MeasurableSet S) (w : A → ℝ) (hw : ∀ a,0≤w a)
    (hwS : ∑ a,w a=μ.real S) :
    ∃ q : X → A,Measurable q ∧ ∀ a,μ.real (S∩q ⁻¹' {a})=w a := by
  classical
  obtain ⟨E,hE,hEd⟩ := exists_disjoint_cuts μ Finset.univ w hw hS hwS.le
  have hm (a : A) := (hE a (Finset.mem_univ a)).1
  have hsub (a : A) := (hE a (Finset.mem_univ a)).2.1
  have he (a : A) := (hE a (Finset.mem_univ a)).2.2
  have hd : Pairwise (Function.onFun Disjoint E) := fun a b hab =>
    hEd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  obtain ⟨q,hq,hqa⟩ := exists_measurable_coloring Finset.univ E
    (fun a _ => hm a) (fun a _ b _ => hd (i:=a) (j:=b))
  have hUm : MeasurableSet (⋃ a,E a) := MeasurableSet.iUnion hm
  have hUS : (⋃ a,E a)⊆S := iUnion_subset hsub
  have hUr : μ.real (⋃ a,E a)=μ.real S := by
    rw [measureReal_iUnion_fintype hd hm]
    simp_rw [he]
    exact hwS
  have hz : μ (S\⋃ a,E a)=0 := (measureReal_eq_zero_iff).mp (by
    rw [measureReal_sdiff hUS hUm,hUr,sub_self])
  have hAE : ∀ᵐ x ∂μ,x∈S → ∃ a,x∈E a := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with x hx hxS
    by_contra hh
    apply hx
    exact ⟨hxS,by simpa only [mem_iUnion,not_exists] using hh⟩
  refine ⟨q,hq,fun a => ?_⟩
  have hEq : (S∩q ⁻¹' {a} : Set X) =ᵐ[μ] E a := by
    filter_upwards [hAE] with x hx
    apply propext
    constructor
    · rintro ⟨hxS,hxq⟩
      obtain ⟨b,hxb⟩ := hx hxS
      have hba : b=a := (hqa b (Finset.mem_univ b) x hxb).symm.trans hxq
      change x∈E a
      exact hba ▸ hxb
    · intro hxa
      exact ⟨hsub a hxa,hqa a (Finset.mem_univ a) x hxa⟩
  exact (measureReal_congr hEq).trans (he a)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

omit [MeasurableSingletonClass B] in
theorem realize_finite_coupling (p : X → A) (hp : Measurable p)
    (r : A → B → ℝ) (hr : ∀ a b,0≤r a b) (hrow : ∀ a,∑ b,r a b=mass μ p a) :
    ∃ q : X → B,Measurable q ∧ ∀ a b,mass μ (fun x => (p x,q x)) (a,b)=r a b := by
  have hh (a : A) : ∃ q : X → B,Measurable q ∧
      ∀ b,μ.real ((p ⁻¹' {a})∩q ⁻¹' {b})=r a b :=
    exists_finite_random_variable μ (hp (measurableSet_singleton a)) (r a) (hr a) (hrow a)
  choose q hq hqr using hh
  let q' : X → B := fun x => q (p x) x
  have hq' : Measurable q' := (measurable_from_prod_countable_right
    (f:=fun ax : A×X => q ax.1 ax.2) hq).comp (hp.prodMk measurable_id)
  refine ⟨q',hq',fun a b => ?_⟩
  have hset : (fun x => (p x,q' x)) ⁻¹' {(a,b)}=(p ⁻¹' {a})∩q a ⁻¹' {b} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,mem_inter_iff,q']
    constructor
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
    · rintro ⟨ha,hb⟩
      exact ⟨ha,by simpa only [ha] using hb⟩
  simpa only [mass,hset,Measure.real] using hqr a b

omit [StandardBorelSpace X] [NullSingletonClass μ] in
lemma repaint_error_eq_sum [DecidableEq A] (p q : X → A) (hp : Measurable p) (hq : Measurable q) :
    μ.real {x | p x≠q x}=(∑ a,∑ b,mass μ (fun x => (p x,q x)) (a,b)*(if a=b then 0 else 1)) := by
  classical
  let g : A×A → ℝ := fun ab => if ab.1=ab.2 then 0 else 1
  have hs := sum_mass_mul_integral μ (fun x => (p x,q x)) (hp.prodMk hq) g
  rw [Fintype.sum_prod_type] at hs
  have hi : (∫ x,g (p x,q x) ∂μ)=μ.real {x | p x≠q x} := by
    have he : (fun x => g (p x,q x))={x | p x≠q x}.indicator (fun _x : X => (1 : ℝ)) := by
      funext x
      by_cases hx : p x=q x <;> simp [g,hx]
    have hD : MeasurableSet {x | p x≠q x} := (measurableSet_eq_fun hp hq).compl
    rw [he]
    change (∫ x,{x | p x≠q x}.indicator (fun _x : X => (1 : ℝ)) x ∂μ)=_
    rw [integral_indicator hD]
    simp
  exact hi.symm.trans hs.symm

theorem copy_finite_law [Nonempty A] [DecidableEq A] (p : X → A) (hp : Measurable p)
    (ν : Measure A) [IsProbabilityMeasure ν] {ε : ℝ} (hclose : LawClose (μ.map p) ν ε) :
    ∃ q : X → A,Measurable q ∧ μ.map q=ν ∧ μ.real {x | p x≠q x}≤ε := by
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  obtain ⟨r,hr,hrow,hcol,herr⟩ := finite_coupling_of_lawClose (μ.map p) ν hclose
  have hrow' (a : A) : ∑ b,r a b=mass μ p a := by
    rw [hrow,map_measureReal_apply hp (measurableSet_singleton a)]
    rfl
  obtain ⟨q,hq,hpq⟩ := realize_finite_coupling μ p hp r hr hrow'
  have hmap : μ.map q=ν := by
    apply Measure.ext_of_singleton
    intro b
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [←Measure.real,map_measureReal_apply hq (measurableSet_singleton b)]
    change mass μ q b=ν.real {b}
    rw [mass_joint_col μ p q hp hq]
    simp_rw [hpq]
    exact hcol b
  refine ⟨q,hq,hmap,?_⟩
  rw [repaint_error_eq_sum μ p q hp hq]
  simpa only [hpq] using herr

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set
open scoped BigOperators
variable {X A B C : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
variable (μ : Measure X) [IsFiniteMeasure μ]

omit [Fintype A] [Fintype C] in
lemma mass_triple_first_third (p : X → A) (q : X → B) (r : X → C)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (a : A) (c : C) :
    mass μ (fun x => (p x,r x)) (a,c)=
      ∑ b,mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  rw [mass_joint_row μ (fun x => (p x,r x)) q (hp.prodMk hr) hq (a,c)]
  apply Finset.sum_congr rfl
  intro b _hb
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  tauto

omit [Fintype B] [Fintype C] in
lemma mass_triple_second_third (p : X → A) (q : X → B) (r : X → C)
    (hp : Measurable p) (hq : Measurable q) (hr : Measurable r) (b : B) (c : C) :
    mass μ (fun x => (q x,r x)) (b,c)=
      ∑ a,mass μ (fun x => ((p x,q x),r x)) ((a,b),c) := by
  rw [mass_joint_row μ (fun x => (q x,r x)) p (hq.prodMk hr) hp (b,c)]
  apply Finset.sum_congr rfl
  intro a _ha
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq]
  tauto

end StandardMapEntropy.Entropy
end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem copy_independent_of_finite_past (p : X → A) (q : X → B)
    (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ q' : X → B,Measurable q' ∧ μ.map q'=μ.map q ∧
      μ.map (fun x => (p x,q' x))=(μ.map p).prod (μ.map q) ∧
      μ.real {x | q x≠q' x}≤ε := by
  classical
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  have : IsProbabilityMeasure (μ.map q) := inferInstance
  have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := inferInstance
  let u : A → B → ℝ := fun a b => mass μ (fun x => (p x,q x)) (a,b)
  let v : A → B → ℝ := fun a b => mass μ p a*mass μ q b
  have hu (a b) : 0≤u a b := mass_nonneg _ _ _
  have hv (a b) : 0≤v a b := mul_nonneg (mass_nonneg _ _ _) (mass_nonneg _ _ _)
  have hrow (a) : ∑ b,u a b=∑ b,v a b := by
    rw [←mass_joint_row μ p q hp hq]
    dsimp only [v]
    rw [←Finset.mul_sum,mass_sum μ q hq]
    simp
  have hc (a) := finite_maximal_coupling_equal_mass (u a) (v a) (hu a) (hv a) (hrow a)
  choose r hr hrrow hrcol hrerr using hc
  obtain ⟨q',hq',hqq'⟩ := realize_finite_coupling μ (fun x => (p x,q x))
    (hp.prodMk hq) (fun ab c => r ab.1 ab.2 c) (fun ab c => hr ab.1 ab.2 c)
    (fun ab => hrrow ab.1 ab.2)
  have hpair (a b) : mass μ (fun x => (p x,q' x)) (a,b)=v a b := by
    rw [mass_triple_first_third μ p q q' hp hq hq']
    simpa only [hqq'] using hrcol a b
  have hprod (a b) : ((μ.map p).prod (μ.map q)).real {(a,b)}=v a b := by
    rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
    rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
      map_measureReal_apply hq (measurableSet_singleton b)]
    rfl
  have hmap : μ.map (fun x => (p x,q' x))=(μ.map p).prod (μ.map q) := by
    apply Measure.ext_of_singleton
    rintro ⟨a,b⟩
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [←Measure.real,map_measureReal_apply (hp.prodMk hq') (measurableSet_singleton (a,b))]
    exact (hpair a b).trans (hprod a b).symm
  have hmarg : μ.map q'=μ.map q := by
    apply Measure.ext_of_singleton
    intro b
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    rw [←Measure.real,←Measure.real,map_measureReal_apply hq' (measurableSet_singleton b),
      map_measureReal_apply hq (measurableSet_singleton b)]
    change mass μ q' b=mass μ q b
    rw [mass_joint_col μ p q' hp hq']
    simp_rw [hpair]
    dsimp only [v]
    rw [←Finset.sum_mul,mass_sum μ p hp]
    simp
  refine ⟨q',hq',hmarg,hmap,?_⟩
  rw [repaint_error_eq_sum μ q q' hq hq']
  simp_rw [mass_triple_second_third μ p q q' hp hq hq',hqq',Finset.sum_mul]
  have herr : (∑ a,∑ b,∑ c,r a b c*(if b=c then (0 : ℝ) else 1))≤ε := by
    simp_rw [hrerr]
    have hh := positive_mass_difference_le (μ.map (fun x => (p x,q x)))
      ((μ.map p).prod (μ.map q)) hclose
    rw [Fintype.sum_prod_type] at hh
    have hu' (a b) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u a b :=
      map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
    simpa only [hu',hprod] using hh
  calc
    _=(∑ b,∑ a,∑ c,r a b c*(if b=c then (0 : ℝ) else 1)) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _=(∑ a,∑ b,∑ c,r a b c*(if b=c then (0 : ℝ) else 1)) := Finset.sum_comm
    _≤ε := herr

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]

noncomputable def symbolCost {E : Type*} (a b : E) : ℝ := by
  classical
  exact if a=b then 0 else 1

lemma symbolCost_self {E : Type*} (a : E) : symbolCost a a=0 := by simp [symbolCost]
lemma symbolCost_nonneg {E : Type*} (a b : E) : 0≤ symbolCost a b := by unfold symbolCost; split <;> norm_num
lemma symbolCost_triangle {E : Type*} (a b c : E) : symbolCost a c≤ symbolCost a b+symbolCost b c := by
  classical
  by_cases h1 : a=b <;> by_cases h2 : b=c <;> by_cases h3 : a=c <;> simp_all [symbolCost]

namespace MatrixCoupling
variable {p : A → ℝ} {q : B → ℝ}

noncomputable def reindex (r : MatrixCoupling p q) (e : C ≃ A) (f : D ≃ B) :
    MatrixCoupling (p ∘ e) (q ∘ f) where
  weight c d := r.weight (e c) (f d)
  nonneg c d := r.nonneg _ _
  row c := by rw [f.sum_comp]; exact r.row (e c)
  col d := (e.sum_comp (fun a => r.weight a (f d))).trans (r.col (f d))

lemma reindex_cost (r : MatrixCoupling p q) (e : C ≃ A) (f : D ≃ B) (d : A → B → ℝ) :
    (r.reindex e f).cost (fun a b => d (e a) (f b))=r.cost d := by
  change (∑ a,∑ b,r.weight (e a) (f b)*d (e a) (f b))=∑ a,∑ b,r.weight a b*d a b
  have hf (a : C) := f.sum_comp (fun b => r.weight (e a) b*d (e a) b)
  simp_rw [hf]
  exact e.sum_comp (fun a => ∑ b,r.weight a b*d a b)

end MatrixCoupling

noncomputable def nameCost {E : Type*} {n : ℕ} (a b : Fin n → E) : ℝ :=
  ∑ i,symbolCost (a i) (b i)

lemma nameCost_self {E : Type*} {n : ℕ} (a : Fin n → E) : nameCost a a=0 := by
  simp [nameCost,symbolCost_self]
lemma nameCost_triangle {E : Type*} {n : ℕ} (a b c : Fin n → E) :
    nameCost a c≤nameCost a b+nameCost b c := by
  simp only [nameCost,←Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => symbolCost_triangle _ _ _)
lemma nameCost_cons {E : Type*} {n : ℕ} (a b : E) (v w : Fin n → E) :
    nameCost (Fin.cons a v) (Fin.cons b w)=symbolCost a b+nameCost v w := by
  rw [nameCost,Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,nameCost]

section Copy
variable [StandardBorelSpace X] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

theorem coupling_step (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (t : A → ℝ) (r : MatrixCoupling (mass μ p) t)
    (d : A → A → ℝ) (hdiag : ∀ a,d a a=0) (htri : ∀ a b c,d a c≤d a b+d b c)
    {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ s : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*t ba.2),
      s.cost (fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2)≤ε+r.cost d := by
  classical
  obtain ⟨q',hq',_hm,hjoint,herr⟩ := copy_independent_of_finite_past μ p q hp hq hclose
  have hmass (b : B) (a : A) : mass μ (fun x => (q' x,p x)) (b,a)=mass μ q b*mass μ p a := by
    have hh := congrArg (fun M : Measure (A×B) => M.real {(a,b)}) hjoint
    rw [map_measureReal_apply (hp.prodMk hq') (measurableSet_singleton (a,b))] at hh
    have hprod : ((μ.map p).prod (μ.map q)).real {(a,b)}=mass μ p a*mass μ q b := by
      rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
      rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
        map_measureReal_apply hq (measurableSet_singleton b)]
      rfl
    rw [hprod] at hh
    have he : mass μ (fun x => (q' x,p x)) (b,a)=mass μ (fun x => (p x,q' x)) (a,b) := by
      unfold mass
      congr 2
      ext x
      simp only [mem_preimage,mem_singleton_iff,Prod.mk.injEq,and_comm]
    exact he.trans (hh.trans (mul_comm _ _))
  let R := MatrixCoupling.observations μ (fun x => (q x,p x)) (fun x => (q' x,p x))
    (hq.prodMk hp) (hq'.prodMk hp)
  let R' : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*mass μ p ba.2) := {
    weight := R.weight
    nonneg := R.nonneg
    row := R.row
    col := fun ba => (R.col ba).trans (hmass ba.1 ba.2) }
  let S := (MatrixCoupling.diagonal (mass μ q) (mass_nonneg μ q)).product r
  let cost : (B×A) → (B×A) → ℝ := fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2
  have hR : R'.cost cost≤ε := by
    change R.cost cost≤ε
    rw [MatrixCoupling.observations_cost]
    change (∫ x,symbolCost (q x) (q' x)+d (p x) (p x) ∂μ)≤ε
    simp only [hdiag,add_zero]
    have he : (∫ x,symbolCost (q x) (q' x) ∂μ)=μ.real {x | q x≠q' x} := by
      rw [←sum_mass_mul_integral μ (fun x => (q x,q' x)) (hq.prodMk hq')
        (fun ab => symbolCost ab.1 ab.2),Fintype.sum_prod_type]
      exact (repaint_error_eq_sum μ q q' hq hq').symm
    rwa [he]
  have hS : S.cost cost=r.cost d := by
    rw [MatrixCoupling.product_cost]
    · rw [MatrixCoupling.diagonal_cost _ _ symbolCost symbolCost_self,zero_add]
    · simp only [mass_sum μ q hq,measure_univ,ENNReal.toReal_one]
    · simp only [mass_sum μ p hp,measure_univ,ENNReal.toReal_one]
  refine ⟨R'.comp S,?_⟩
  have h := MatrixCoupling.comp_cost_le R' S cost cost cost (fun a b c => by
    dsimp [cost]
    have h1 := symbolCost_triangle a.1 b.1 c.1
    have h2 := htri a.2 b.2 c.2
    linarith)
  exact h.trans (by rw [hS]; linarith)

end Copy
end HyperbolicCoding

end
end

end OAI
