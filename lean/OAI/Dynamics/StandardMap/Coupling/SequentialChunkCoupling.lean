import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.AtomlessFinitePartition

namespace OAI

section
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def finiteName (q : ℕ → X → A) (i n : ℕ) (x : X) : Fin n → A := fun j => q (i+j) x

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma finiteName_measurable (q : ℕ → X → A) (hq : ∀ i,Measurable (q i)) (i n : ℕ) :
    Measurable (finiteName q i n) := Measurable.of_eval (fun index => hq (i+index))

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma finiteName_cons (q : ℕ → X → A) (i n : ℕ) (x : X) :
    finiteName q i (n+1) x=Fin.cons (q i x) (finiteName q (i+1) n x) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [finiteName]
  · simp [finiteName,Nat.add_comm,Nat.add_left_comm]

noncomputable def independentNameWeights (q : ℕ → X → A) (i n : ℕ) (w : Fin n → A) : ℝ :=
  ∏ j : Fin n,mass μ (q (i+j.val)) (w j)

omit [StandardBorelSpace X] [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [Nonempty A] [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma independentNameWeights_cons (q : ℕ → X → A) (i n : ℕ) (w : Fin (n+1) → A) :
    independentNameWeights μ q i (n+1) w=
      mass μ (q i) (w 0)*independentNameWeights μ q (i+1) n (Fin.tail w) := by
  rw [independentNameWeights,Fin.prod_univ_succ]
  simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Fin.tail,independentNameWeights]
  congr 2
  funext j
  congr 2
  omega

omit [StandardBorelSpace X] [IsProbabilityMeasure μ] [NullSingletonClass μ] in
lemma mass_equiv_inverse {B C : Type*} [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    (p : X → B) (e : B ≃ C) (c : C) : mass μ (e ∘ p) c=mass μ p (e.symm c) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,←Equiv.eq_symm_apply]

omit [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma nameCost_split {n : ℕ} (v w : Fin (n+1) → A) :
    nameCost v w=symbolCost (v 0) (w 0)+nameCost (Fin.tail v) (Fin.tail w) := by
  rw [nameCost,Fin.sum_univ_succ]
  rfl

theorem sequential_chunk_coupling (q : ℕ → X → A) (hq : ∀ i,Measurable (q i))
    {ε : ℝ}
    (hremote : ∀ i n : ℕ,LawClose
      (μ.map (fun x => (finiteName q (i+1) n x,q i x)))
      ((μ.map (finiteName q (i+1) n)).prod (μ.map (q i))) ε) :
    ∀ i n : ℕ,∃ r : MatrixCoupling (mass μ (finiteName q i n)) (independentNameWeights μ q i n),
      r.cost nameCost≤(n : ℝ)*ε := by
  intro i n
  induction n generalizing i with
  | zero =>
    have hm (w : Fin 0 → A) : mass μ (finiteName q i 0) w=1 := by
      have he : (finiteName q i 0) ⁻¹' {w}=univ := by
        ext x
        simp only [mem_preimage,mem_singleton_iff,mem_univ,iff_true]
        funext j
        exact j.elim0
      simp [mass,he]
    let r : MatrixCoupling (mass μ (finiteName q i 0)) (independentNameWeights μ q i 0) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun w => by simp [hm]
      col := fun w => by simp [independentNameWeights] }
    refine ⟨r,?_⟩
    simp [MatrixCoupling.cost,nameCost]
  | succ n ih =>
    obtain ⟨r,hr⟩ := ih (i+1)
    obtain ⟨s,hs⟩ := coupling_step μ (finiteName q (i+1) n) (q i)
      (finiteName_measurable q hq (i+1) n) (hq i)
      (independentNameWeights μ q (i+1) n) r nameCost nameCost_self nameCost_triangle (hremote i n)
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := s.reindex e.symm e.symm
    have hm (w : Fin (n+1) → A) :
        mass μ (fun x => (q i x,finiteName q (i+1) n x)) (e.symm w)=mass μ (finiteName q i (n+1)) w := by
      rw [←mass_equiv_inverse μ _ e w]
      congr 1
      funext x
      exact (finiteName_cons q i n x).symm
    have hw (w : Fin (n+1) → A) :
        mass μ (q i) (e.symm w).1*independentNameWeights μ q (i+1) n (e.symm w).2=
          independentNameWeights μ q i (n+1) w := (independentNameWeights_cons μ q i n w).symm
    let R : MatrixCoupling (mass μ (finiteName q i (n+1))) (independentNameWeights μ q i (n+1)) := {
      weight := t.weight
      nonneg := t.nonneg
      row := fun w => (t.row w).trans (hm w)
      col := fun w => (t.col w).trans (hw w) }
    have hcost : R.cost nameCost=s.cost (fun a b => symbolCost a.1 b.1+nameCost a.2 b.2) := by
      change t.cost nameCost=_
      have he : (nameCost : (Fin (n+1) → A) → (Fin (n+1) → A) → ℝ)=
          (fun v w => symbolCost (e.symm v).1 (e.symm w).1+nameCost (e.symm v).2 (e.symm w).2) := by
        funext v w
        exact nameCost_split v w
      rw [he]
      exact MatrixCoupling.reindex_cost s e.symm e.symm
        (fun a b : A×(Fin n → A) => symbolCost a.1 b.1+nameCost a.2 b.2)
    refine ⟨R,?_⟩
    rw [hcost]
    calc
      _≤ε+r.cost nameCost := hs
      _≤ε+(n : ℝ)*ε := by linarith
      _=((n+1 : ℕ) : ℝ)*ε := by push_cast; ring

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set
open scoped ENNReal
variable {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma LawClose.nonneg {ν η : Measure X} {ε : ℝ} (h : LawClose ν η ε) : 0≤ε := by
  simpa using h ∅ MeasurableSet.empty

lemma lawClose_pair_factor_left (p : X → A) (q : X → B) (c : A → C)
    (hp : Measurable p) (hq : Measurable q) (hc : Measurable c) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (c (p x),q x))) ((μ.map (c ∘ p)).prod (μ.map q)) ε := by
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  have : IsProbabilityMeasure (μ.map q) := inferInstance
  have hh := h.map (hc.prodMap measurable_id)
  rw [Measure.map_map (hc.prodMap measurable_id) (hp.prodMk hq)] at hh
  rw [←Measure.map_prod_map _ _ hc measurable_id,Measure.map_map hc hp,Measure.map_id] at hh
  exact hh

lemma lawClose_pair_swap (p : X → A) (q : X → B)
    (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (q x,p x))) ((μ.map q).prod (μ.map p)) ε := by
  have hh := h.map measurable_swap
  rw [Measure.map_map measurable_swap (hp.prodMk hq),Measure.prod_swap] at hh
  exact hh

omit [IsProbabilityMeasure μ] in
lemma map_observation_comp (T : X → X) (hT : MeasurePreserving T μ μ)
    (p : X → A) (hp : Measurable p) : μ.map (p ∘ T)=μ.map p := by
  rw [←Measure.map_map hp hT.measurable,hT.map_eq]

omit [IsProbabilityMeasure μ] in
lemma lawClose_pair_comp (T : X → X) (hT : MeasurePreserving T μ μ)
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    LawClose (μ.map (fun x => (p (T x),q (T x))))
      ((μ.map (p ∘ T)).prod (μ.map (q ∘ T))) ε := by
  rw [map_observation_comp μ T hT p hp,map_observation_comp μ T hT q hq]
  have he : (fun x => (p (T x),q (T x)))=(fun x => (p x,q x)) ∘ T := rfl
  rw [he,map_observation_comp μ T hT _ (hp.prodMk hq)]
  exact h

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]

def chunkObservation (f : X → X) (p : X → A) (k g i : ℕ) (x : X) : Fin k → A :=
  word f p k (f^[i*(k+g)] x)

omit [StandardBorelSpace X] [Fintype A] [MeasurableSingletonClass A] [Nonempty A] in
lemma chunkObservation_measurable (f : X → X) (p : X → A)
    (hf : Measurable f) (hp : Measurable p) (k g i : ℕ) :
    Measurable (chunkObservation f p k g i) :=
  (word_measurable f hf p hp k).comp (hf.iterate _)

def selectChunks (k g n : ℕ) (w : Fin (n*(k+g)) → A) : Fin n → Fin k → A :=
  fun j r => w ⟨j.val*(k+g)+r.val,by
    have h1 : (j.val+1)*(k+g)≤n*(k+g) := Nat.mul_le_mul_right _ j.isLt
    have h2 : r.val<k+g := lt_of_lt_of_le r.isLt (Nat.le_add_right _ _)
    nlinarith⟩

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma selectChunks_word (f : X → X) (p : X → A) (k g n : ℕ) (x : X) :
    selectChunks k g n (word f p (n*(k+g)) x)=
      finiteName (chunkObservation f p k g) 0 n x := by
  funext j r
  change p (f^[j.val*(k+g)+r.val] x)=p (f^[r.val] (f^[(0+j.val)*(k+g)] x))
  rw [←Function.iterate_add_apply]
  congr 2
  simp only [Nat.zero_add]
  omega

omit [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace A] [Fintype A]
  [MeasurableSingletonClass A] [Nonempty A] in
lemma chunkName_translate (f : X → X) (p : X → A) (k g i n : ℕ) (x : X) :
    finiteName (chunkObservation f p k g) 0 n (f^[i*(k+g)] x)=
      finiteName (chunkObservation f p k g) i n x := by
  funext j r
  change p (f^[r.val] (f^[(0+j.val)*(k+g)] (f^[i*(k+g)] x)))=
    p (f^[r.val] (f^[(i+j.val)*(k+g)] x))
  simp only [←Function.iterate_add_apply]
  congr 2
  ring

theorem stationary_chunk_coupling (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (k g : ℕ) {ε : ℝ}
    (hremote : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) ε) :
    ∀ n : ℕ,∃ r : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (fun w : Fin n → Fin k → A => ∏ j,mass μ (word f p k) (w j)),
      r.cost nameCost≤(n : ℝ)*ε := by
  have hq := chunkObservation_measurable f p hf.measurable hp k g
  have hc : ∀ i n : ℕ,LawClose
      (μ.map (fun x => (finiteName (chunkObservation f p k g) (i+1) n x,
        chunkObservation f p k g i x)))
      ((μ.map (finiteName (chunkObservation f p k g) (i+1) n)).prod
        (μ.map (chunkObservation f p k g i))) ε := by
    intro i n
    have hs : Measurable (selectChunks (A:=A) k g n) :=
      Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => measurable_pi_apply _))
    have h := lawClose_pair_factor_left μ _ _ (selectChunks k g n)
      ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _))
      (word_measurable f hf.measurable p hp k) hs (hremote (n*(k+g)))
    have hh := lawClose_pair_comp μ (f^[i*(k+g)]) (hf.iterate _) _ _
      (hs.comp ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _)))
      (word_measurable f hf.measurable p hp k) h
    have he (x : X) : selectChunks k g n
        (word f p (n*(k+g)) (f^[k+g] (f^[i*(k+g)] x)))=
          finiteName (chunkObservation f p k g) (i+1) n x := by
      rw [selectChunks_word,←Function.iterate_add_apply]
      rw [show k+g+i*(k+g)=(i+1)*(k+g) by ring]
      exact chunkName_translate f p k g (i+1) n x
    simp only [Function.comp_def,he] at hh
    exact hh
  intro n
  obtain ⟨r,hr⟩ := sequential_chunk_coupling μ _ hq hc 0 n
  have hw (w : Fin n → Fin k → A) :
      independentNameWeights μ (chunkObservation f p k g) 0 n w=
        ∏ j,mass μ (word f p k) (w j) := by
    apply Finset.prod_congr rfl
    intro j _
    have hh := congrArg (fun ν : Measure (Fin k → A) => ν.real {w j})
      (map_observation_comp μ _ (hf.iterate ((0+j.val)*(k+g)))
        (word f p k) (word_measurable f hf.measurable p hp k))
    rw [map_measureReal_apply ((word_measurable f hf.measurable p hp k).comp
      (hf.measurable.iterate _)) (measurableSet_singleton _),
      map_measureReal_apply (word_measurable f hf.measurable p hp k) (measurableSet_singleton _)] at hh
    exact hh
  let R : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (fun w : Fin n → Fin k → A => ∏ j,mass μ (word f p k) (w j)) := {
    weight := r.weight
    nonneg := r.nonneg
    row := r.row
    col := fun w => (r.col w).trans (hw w) }
  exact ⟨R,hr⟩

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

noncomputable def productWeights (w : B → A → ℝ) (D : B → A) : ℝ := ∏ b,w b (D b)
noncomputable def finiteExpectation {E : Type*} [Fintype E] (v : E → ℝ) (F : E → ℝ) : ℝ :=
  ∑ x,v x*F x

lemma productWeights_sum (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1) :
    ∑ D,productWeights w D=1 := by
  unfold productWeights
  rw [←Fintype.prod_sum]
  simp only [hw,Finset.prod_const_one]

omit [Fintype A] [DecidableEq B] in
lemma productWeights_nonneg (w : B → A → ℝ) (hw : ∀ b a,0≤w b a) (D : B → A) :
    0≤productWeights w D := Finset.prod_nonneg (fun b _ => hw b (D b))

lemma expectation_product (w f : B → A → ℝ) :
    finiteExpectation (productWeights w) (fun D => ∏ b,f b (D b))=
      ∏ b,∑ a,w b a*f b a := by
  simp only [finiteExpectation,productWeights,←Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun b a => w b a*f b a)).symm

omit [Fintype A] in
lemma product_one_coordinate (b : B) (f : A → ℝ) (D : B → A) :
    (∏ i,if i=b then f (D i) else 1)=f (D b) := by
  simp

lemma expectation_coordinate (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1)
    (b : B) (f : A → ℝ) :
    finiteExpectation (productWeights w) (fun D => f (D b))=∑ a,w b a*f a := by
  have h := expectation_product w (fun i a => if i=b then f a else 1)
  simp only [product_one_coordinate] at h
  rw [h]
  have hh (i : B) : (∑ a,w i a*(if i=b then f a else 1))=
      if i=b then ∑ a,w b a*f a else 1 := by
    by_cases hi : i=b
    · subst i; simp
    · simp [hi,hw]
  simp_rw [hh]
  simp

lemma expectation_distinct_coordinates (w : B → A → ℝ) (hw : ∀ b,∑ a,w b a=1)
    (b c : B) (hbc : b≠c) (f g : A → ℝ) :
    finiteExpectation (productWeights w) (fun D => f (D b)*g (D c))=
      (∑ a,w b a*f a)*(∑ a,w c a*g a) := by
  have h := expectation_product w
    (fun i a => (if i=b then f a else 1)*(if i=c then g a else 1))
  simp only [Finset.prod_mul_distrib,product_one_coordinate] at h
  rw [h]
  have hh (i : B) : (∑ a,w i a*((if i=b then f a else 1)*(if i=c then g a else 1)))=
      (if i=b then ∑ a,w b a*f a else 1)*(if i=c then ∑ a,w c a*g a else 1) := by
    by_cases hb : i=b
    · subst i; simp [hbc]
    · by_cases hc : i=c
      · subst i; simp [Ne.symm hbc]
      · simp [hb,hc,hw]
  simp_rw [hh]
  rw [Finset.prod_mul_distrib]
  simp

section Linear
variable {E I : Type*} [Fintype E] [Fintype I] (v : E → ℝ)
lemma finiteExpectation_add (F G : E → ℝ) :
    finiteExpectation v (fun x => F x+G x)=finiteExpectation v F+finiteExpectation v G := by
  simp [finiteExpectation,mul_add,Finset.sum_add_distrib]
lemma finiteExpectation_sub (F G : E → ℝ) :
    finiteExpectation v (fun x => F x-G x)=finiteExpectation v F-finiteExpectation v G := by
  simp [finiteExpectation,mul_sub,Finset.sum_sub_distrib]
lemma finiteExpectation_const (c : ℝ) : finiteExpectation v (fun _ => c)=(∑ x,v x)*c := by
  simp [finiteExpectation,Finset.sum_mul]
lemma finiteExpectation_smul (c : ℝ) (F : E → ℝ) :
    finiteExpectation v (fun x => c*F x)=c*finiteExpectation v F := by
  simp only [finiteExpectation,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring
lemma finiteExpectation_sum (F : I → E → ℝ) :
    finiteExpectation v (fun x => ∑ i,F i x)=∑ i,finiteExpectation v (F i) := by
  simp only [finiteExpectation,Finset.mul_sum]
  exact Finset.sum_comm
lemma finiteExpectation_mono (hv : ∀ x,0≤v x) (F G : E → ℝ) (h : ∀ x,F x≤G x) :
    finiteExpectation v F≤finiteExpectation v G :=
  Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (hv x))
end Linear
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open scoped BigOperators
variable {A : Type*} [Fintype A]
namespace MatrixCoupling
variable {p q : A → ℝ}

lemma symm_cost (r : MatrixCoupling p q) (d : A → A → ℝ) (hd : ∀ a b,d a b=d b a) :
    r.symm.cost d=r.cost d := by
  unfold cost symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hd]

theorem exists_power (r : MatrixCoupling p q) (hp : ∑ a,p a=1) :
    ∀ n : ℕ,∃ R : MatrixCoupling (fun w : Fin n → A => ∏ j,p (w j))
      (fun w : Fin n → A => ∏ j,q (w j)),R.cost nameCost=(n : ℝ)*r.cost symbolCost := by
  classical
  intro n
  induction n with
  | zero =>
    let R : MatrixCoupling (fun w : Fin 0 → A => ∏ j,p (w j)) (fun w : Fin 0 → A => ∏ j,q (w j)) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun _ => by simp
      col := fun _ => by simp }
    refine ⟨R,?_⟩
    simp [cost,nameCost]
  | succ n ih =>
    obtain ⟨R,hR⟩ := ih
    let S := r.product R
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := S.reindex e.symm e.symm
    let T : MatrixCoupling (fun w : Fin (n+1) → A => ∏ j,p (w j))
        (fun w : Fin (n+1) → A => ∏ j,q (w j)) := {
      weight := t.weight
      nonneg := t.nonneg
      row := fun w => (t.row w).trans (by exact (Fin.prod_univ_succ (fun j => p (w j))).symm)
      col := fun w => (t.col w).trans (by exact (Fin.prod_univ_succ (fun j => q (w j))).symm) }
    have he : (nameCost : (Fin (n+1) → A) → (Fin (n+1) → A) → ℝ)=
        (fun v w => symbolCost (e.symm v).1 (e.symm w).1+nameCost (e.symm v).2 (e.symm w).2) := by
      funext v w
      rw [nameCost,Fin.sum_univ_succ]
      rfl
    have hmass : (∑ w : Fin n → A,∏ j,p (w j))=1 :=
      productWeights_sum (fun _ : Fin n => p) (fun _ => hp)
    refine ⟨T,?_⟩
    change t.cost nameCost=_
    rw [he,MatrixCoupling.reindex_cost S e.symm e.symm
      (fun a b : A×(Fin n → A) => symbolCost a.1 b.1+nameCost a.2 b.2)]
    rw [MatrixCoupling.product_cost r R hp hmass symbolCost nameCost,hR]
    push_cast
    ring

end MatrixCoupling
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators

lemma symbolCost_comm {A : Type*} (a b : A) : symbolCost a b=symbolCost b a := by
  classical
  simp only [symbolCost,eq_comm]
lemma nameCost_comm {A : Type*} {n : ℕ} (a b : Fin n → A) : nameCost a b=nameCost b a := by
  simp only [nameCost,symbolCost_comm]

lemma coupling_of_observation_lawClose {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q) {ε : ℝ}
    (h : LawClose (μ.map p) (ν.map q) ε) :
    ∃ R : MatrixCoupling (mass μ p) (mass ν q),R.cost symbolCost≤ε := by
  classical
  have : IsProbabilityMeasure (μ.map p) := inferInstance
  have : IsProbabilityMeasure (ν.map q) := inferInstance
  obtain ⟨r,hr,hrow,hcol,hcost⟩ := finite_coupling_of_lawClose (μ.map p) (ν.map q) h
  let R : MatrixCoupling (mass μ p) (mass ν q) := {
    weight := r
    nonneg := hr
    row := fun a => (hrow a).trans (map_measureReal_apply hp (measurableSet_singleton a))
    col := fun a => (hcol a).trans (map_measureReal_apply hq (measurableSet_singleton a)) }
  exact ⟨R,hcost⟩

theorem chunk_process_transport {X Y A : Type*}
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ] [NullSingletonClass ν]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (T : Y → Y) (hT : MeasurePreserving T ν ν) (q : Y → A) (hq : Measurable q)
    (k g : ℕ) {εP εQ δ : ℝ}
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) εP)
    (hQ : ∀ M : ℕ,LawClose
      (ν.map (fun x => (word T q M (T^[k+g] x),word T q k x)))
      ((ν.map (fun x => word T q M (T^[k+g] x))).prod (ν.map (word T q k))) εQ)
    (hlaw : LawClose (μ.map (word f p k)) (ν.map (word T q k)) δ) :
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (finiteName (chunkObservation f p k g) 0 n))
      (mass ν (finiteName (chunkObservation T q k g) 0 n)),
      R.cost nameCost≤(n : ℝ)*(εP+δ+εQ) := by
  intro n
  obtain ⟨RP,hRP⟩ := stationary_chunk_coupling μ f hf p hp k g hP n
  obtain ⟨RQ,hRQ⟩ := stationary_chunk_coupling ν T hT q hq k g hQ n
  obtain ⟨r,hr⟩ := coupling_of_observation_lawClose μ ν (word f p k) (word T q k)
    (word_measurable f hf.measurable p hp k) (word_measurable T hT.measurable q hq k) hlaw
  obtain ⟨S,hS⟩ := r.exists_power (by
    simp only [mass_sum μ (word f p k) (word_measurable f hf.measurable p hp k),
      measure_univ,ENNReal.toReal_one]) n
  refine ⟨(RP.comp S).comp RQ.symm,?_⟩
  have h1 := MatrixCoupling.comp_cost_le RP S nameCost nameCost nameCost nameCost_triangle
  have h2 := MatrixCoupling.comp_cost_le (RP.comp S) RQ.symm nameCost nameCost nameCost nameCost_triangle
  rw [MatrixCoupling.symm_cost RQ nameCost nameCost_comm] at h2
  rw [hS] at h1
  have h3 := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg n)
  nlinarith

end HyperbolicCoding

end
end

end OAI
