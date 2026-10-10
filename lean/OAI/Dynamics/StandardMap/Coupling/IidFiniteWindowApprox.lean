import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.FullEntropyCopySequence
import OAI.Dynamics.StandardMap.Coupling.RelativeFiniteRealization

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {A B : Type*} [MeasurableSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

def centeredWindow (N : ℕ) (w : ℤ → A) : Fin (2*N+1) → A := fun i => w ((i.val : ℤ)-N)

lemma measurable_centeredWindow [Fintype A] [MeasurableSingletonClass A]
    (N : ℕ) : Measurable (centeredWindow (A:=A) N) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma centeredWindow_comap_monotone [Fintype A] [MeasurableSingletonClass A] :
    Monotone (fun N => MeasurableSpace.comap (centeredWindow (A:=A) N) inferInstance) := by
  intro N M hNM
  let r : (Fin (2*M+1) → A) → (Fin (2*N+1) → A) :=
    fun v i => v ⟨i.val+(M-N),by omega⟩
  have hm : Measurable[MeasurableSpace.comap (centeredWindow (A:=A) M) inferInstance]
      (centeredWindow (A:=A) M) := measurable_iff_comap_le.mpr le_rfl
  have hh := (measurable_of_countable r).comp hm
  have heq : r ∘ centeredWindow (A:=A) M=centeredWindow N := by
    funext w i
    dsimp [r,centeredWindow]
    congr 1
    omega
  rw [heq] at hh
  exact measurable_iff_comap_le.mp hh

lemma centeredWindow_generates [Fintype A] [MeasurableSingletonClass A] :
    (inferInstance : MeasurableSpace (ℤ → A))=
      ⨆ N,MeasurableSpace.comap (centeredWindow (A:=A) N) inferInstance := by
  let m := ⨆ N,MeasurableSpace.comap (centeredWindow (A:=A) N) inferInstance
  apply le_antisymm
  · have hi (i : ℤ) : @Measurable (ℤ → A) A m inferInstance (fun w => w i) := by
      let N := i.natAbs
      let j : Fin (2*N+1) := ⟨(i+N).toNat,by
        have h₁ := (Int.le_natAbs (a:=i))
        have h₂ : -i≤(i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a:=-i))
        dsimp [N]
        omega⟩
      have hN : @Measurable (ℤ → A) (Fin (2*N+1) → A) m inferInstance (centeredWindow N) :=
        measurable_iff_comap_le.mpr
          (le_iSup (fun n => MeasurableSpace.comap (centeredWindow (A:=A) n) inferInstance) N)
      have hh := (measurable_pi_apply j).comp hN
      have heq : (fun w => centeredWindow (A:=A) N w j)=(fun w => w i) := by
        funext w
        dsimp [centeredWindow,j,N]
        congr 1
        have h₂ : -i≤(i.natAbs : ℤ) := by simpa using (Int.le_natAbs (a:=-i))
        omega
      exact heq ▸ hh
    have hid : @Measurable (ℤ → A) (ℤ → A) m MeasurableSpace.pi id := Measurable.of_eval hi
    simpa only [MeasurableSpace.comap_id] using measurable_iff_comap_le.mp hid
  · apply iSup_le
    intro N
    exact measurable_iff_comap_le.mp (measurable_centeredWindow N)

lemma centeredWindow_as_word [Fintype A] [MeasurableSingletonClass A] (N : ℕ) (w : ℤ → A) :
    centeredWindow N w=word iidShift (fun z : ℤ → A => z 0) (2*N+1)
      (integerIterate iidShift (-(N : ℤ)) w) := by
  funext i
  simp only [iid_word_eq,integerIterate_neg_nat,iidShift_symm_iterate,centeredWindow]

theorem iid_finite_window_approx [Fintype A] [MeasurableSingletonClass A]
    (ν : Measure (ℤ → A)) [IsProbabilityMeasure ν]
    (b : (ℤ → A) → B) (hb : Measurable b) {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ,∃ D : (Fin (2*N+1) → A) → B,
      ν.real {w | D (centeredWindow N w)≠b w}<ε :=
  finite_factor_approx ν (fun N => Fin (2*N+1) → A) centeredWindow
    centeredWindow_comap_monotone centeredWindow_generates b hb hε
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators
variable {X Y A : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace A] [MeasurableSingletonClass A]

lemma mass_comp_factor [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A]
    (μ : Measure X) (ν : Measure Y) (π : X → Y)
    (hπ : MeasurePreserving π μ ν) (p : Y → A) (hp : Measurable p) :
    mass μ (p ∘ π)=mass ν p := by
  funext a
  unfold mass
  exact congrArg ENNReal.toReal (hπ.measure_preimage (hp (measurableSet_singleton a)).nullMeasurableSet)

lemma rate_of_factor [StandardBorelSpace X] [StandardBorelSpace Y] [Fintype A]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (e : X → X) (f : Y → Y) (hf : Measurable f)
    (π : X → Y) (hπ : MeasurePreserving π μ ν) (hcomm : ∀ x,π (e x)=f (π x))
    (p : Y → A) (hp : Measurable p) : rate μ e (p ∘ π)=rate ν f p := by
  have hh (n : ℕ) : obs μ (word e (p ∘ π) n)=obs ν (word f p n) := by
    rw [factor_word e f π hcomm p n]
    unfold obs
    rw [mass_comp_factor μ ν π hπ _ (word_measurable f hf p hp n)]
  unfold rate
  simp only [hh]
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [DecidableEq A] [MeasurableSingletonClass A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

theorem relative_iid_window_graph
    [TopologicalSpace X] [SecondCountableTopology X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : Ergodic e μ) (p : X → A) (_hp : Measurable p)
    (β : A → ℝ) (hβ : ∀ a,0≤β a) (hβsum : ∑ a,β a=1) (hβentropy : 0<weightEntropy β)
    (H : FiniteRateSupremum μ e (weightEntropy β))
    (hcode : MeasurePreserving (orbitName e p) μ (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)))
    (α : X → B) (hα : Measurable α) (m : ℕ) {ε : ℝ} (hε : 0<ε) :
    ∃ R : ℕ,∃ D : (Fin (2*R+1) → A) → B,
      LawClose (μ.map (word e (fun x => (p x,α x)) m))
        ((Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)).map
          (word iidShift (fun y : ℤ → A => (y 0,D (centeredWindow R y))) m)) ε ∧
      rate (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) iidShift
        (fun y : ℤ → A => (y 0,D (centeredWindow R y)))=weightEntropy β := by
  classical
  let : IsProbabilityMeasure (finiteWeightLaw β) := finiteWeightLaw_probability β hβ hβsum
  let ν := Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)
  let : NullSingletonClass ν := iid_nullSingleton β hβ hβsum hβentropy
  have hcomm : ∀ x,orbitName e p (e x)=iidShift (orbitName e p x) := fun x => orbitName_shift e p x
  have hf : Ergodic iidShift ν := hcode.ergodic_of_ergodic_semiconj he iidShift.measurable hcomm
  have hp0 : (fun x => orbitName e p x 0)=p := by funext x; simp [orbitName,integerIterate]
  obtain ⟨b,hb,hbLaw⟩ := relative_measurable_graph_approx μ ν e he.toMeasurePreserving iidShift hf
    (orbitName e p) hcode hcomm (fun w : ℤ → A => w 0) α (measurable_pi_apply 0) hα m (half_pos hε)
  obtain ⟨R,D,hD⟩ := iid_finite_window_approx ν b hb (show 0<ε/(2*((m : ℝ)+1)) by positivity)
  have hDmeas : Measurable (fun y : ℤ → A => D (centeredWindow R y)) :=
    (measurable_of_countable D).comp (measurable_centeredWindow R)
  have hpaint : ν.real {y | (y 0,b y)≠(y 0,D (centeredWindow R y))}<ε/(2*((m : ℝ)+1)) := by
    convert hD using 1
    congr 1
    ext y
    simp only [Set.mem_ofPred_eq,ne_eq,Prod.mk.injEq,true_and]
    exact ne_comm
  have hLaw := word_lawClose_of_repaint ν iidShift hf.toMeasurePreserving
    (fun y : ℤ → A => (y 0,b y)) (fun y : ℤ → A => (y 0,D (centeredWindow R y)))
    ((measurable_pi_apply 0).prodMk hb) ((measurable_pi_apply 0).prodMk hDmeas) m
  refine ⟨R,D,?_,?_⟩
  · have htrans := hbLaw.triangle hLaw
    change LawClose (μ.map (word e (fun x => (p x,α x)) m)) _ _ at htrans
    apply htrans.mono
    have hm0 : (0 : ℝ)≤ m := Nat.cast_nonneg m
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ)<2*((m : ℝ)+1))).mp hpaint
    have hn0 := measureReal_nonneg (μ:=ν) (s:={y | (y 0,b y)≠(y 0,D (centeredWindow R y))})
    nlinarith
  · have hfac := rate_of_factor μ ν e iidShift iidShift.measurable (orbitName e p) hcode hcomm
      (fun y : ℤ → A => (y 0,D (centeredWindow R y))) ((measurable_pi_apply 0).prodMk hDmeas)
    have hu := H.upper ((fun y : ℤ → A => (y 0,D (centeredWindow R y))) ∘ orbitName e p)
      (((measurable_pi_apply 0).prodMk hDmeas).comp hcode.measurable)
    rw [hfac] at hu
    apply le_antisymm hu
    have hl := rate_pair_ge_left ν iidShift hf.toMeasurePreserving (fun y : ℤ → A => y 0)
      (fun y => D (centeredWindow R y)) (measurable_pi_apply 0) hDmeas
    rwa [iid_rate β hβ hβsum] at hl
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

 theorem coupling_step_finite (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    (t : A → ℝ) (r : MatrixCoupling (mass μ p) t)
    (d : A → A → ℝ) (hdiag : ∀ a,d a a=0) (htri : ∀ a b c,d a c≤d a b+d b c)
    {ε : ℝ}
    (hclose : LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) ε) :
    ∃ s : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*t ba.2),
      s.cost (fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2)≤ε+r.cost d := by
  classical
  let u : A → B → ℝ := fun a b => mass μ (fun x => (p x,q x)) (a,b)
  let v : A → B → ℝ := fun a b => mass μ p a*mass μ q b
  have hrow (a) : ∑ b,u a b=∑ b,v a b := by
    rw [←mass_joint_row μ p q hp hq]
    dsimp only [v]
    rw [←Finset.mul_sum,mass_sum μ q hq]
    simp
  have hc (a) := finite_maximal_coupling_equal_mass (u a) (v a)
    (fun b => mass_nonneg μ _ _) (fun b => mul_nonneg (mass_nonneg μ _ _) (mass_nonneg μ _ _)) (hrow a)
  choose w hw hwrow hwcol hwerr using hc
  let R : MatrixCoupling (mass μ (fun x => (q x,p x)))
      (fun ba : B×A => mass μ q ba.1*mass μ p ba.2) := {
    weight := fun ba ca => if ba.2=ca.2 then w ba.2 ba.1 ca.1 else 0
    nonneg := fun ba ca => by split
                              · exact hw _ _ _
                              · exact le_rfl
    row := fun ba => by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      rw [hwrow]
      exact mass_joint_swap μ p q ba.2 ba.1
    col := fun ca => by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [hwcol]
      exact mul_comm _ _ }
  let S := (MatrixCoupling.diagonal (mass μ q) (mass_nonneg μ q)).product r
  let cost : (B×A) → (B×A) → ℝ := fun ba bb => symbolCost ba.1 bb.1+d ba.2 bb.2
  have hR : R.cost cost≤ε := by
    have he : R.cost cost=∑ a,∑ b,∑ c,w a b c*symbolCost b c := by
      simp only [MatrixCoupling.cost,R,cost,Fintype.sum_prod_type]
      have hh (b : B) (a : A) (c : B) :
          (∑ a', (if a=a' then w a b c else 0)*(symbolCost b c+d a a'))=
            w a b c*symbolCost b c := by
        simp [ite_mul,hdiag]
      simp only [hh]
      rw [Finset.sum_comm]
    rw [he]
    have : IsProbabilityMeasure (μ.map p) := inferInstance
    have : IsProbabilityMeasure (μ.map q) := inferInstance
    have : IsProbabilityMeasure (μ.map (fun x => (p x,q x))) := inferInstance
    have hprod (a : A) (b : B) : ((μ.map p).prod (μ.map q)).real {(a,b)}=v a b := by
      rw [←singleton_prod_singleton,Measure.real,Measure.prod_prod,ENNReal.toReal_mul]
      rw [←Measure.real,←Measure.real,map_measureReal_apply hp (measurableSet_singleton a),
        map_measureReal_apply hq (measurableSet_singleton b)]
      rfl
    have hsum : (∑ a,∑ b,max (u a b-v a b) 0)≤ε := by
      have h := positive_mass_difference_le _ _ hclose
      rw [Fintype.sum_prod_type] at h
      have hu (a : A) (b : B) : (μ.map (fun x => (p x,q x))).real {(a,b)}=u a b :=
        map_measureReal_apply (hp.prodMk hq) (measurableSet_singleton (a,b))
      simpa only [hu,hprod] using h
    apply le_trans _ hsum
    apply Finset.sum_le_sum
    intro a _
    simpa only [symbolCost] using (hwerr a).le
  have hS : S.cost cost=r.cost d := by
    rw [MatrixCoupling.product_cost]
    · rw [MatrixCoupling.diagonal_cost _ _ symbolCost symbolCost_self,zero_add]
    · simpa using mass_sum μ q hq
    · simpa using mass_sum μ p hp
  refine ⟨R.comp S,?_⟩
  have h := MatrixCoupling.comp_cost_le R S cost cost cost (fun a b c => by
    dsimp [cost]
    have h1 := symbolCost_triangle a.1 b.1 c.1
    have h2 := htri a.2 b.2 c.2
    linarith)
  exact h.trans (by rw [hS]; linarith)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X]
  [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma cond_constant [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (_hp : Measurable p) : StandardMapEntropy.Entropy.cond μ p (fun _ => (PUnit.unit : PUnit.{1}))=obs μ p := by
  unfold StandardMapEntropy.Entropy.cond
  have he : obs μ (fun x => (p x,(PUnit.unit : PUnit.{1})))=obs μ p := by
    let e : A ≃ A×PUnit.{1} := (Equiv.prodPUnit A).symm
    exact obs_equiv μ p e
  rw [he,obs_const,sub_zero]

lemma lawClose_of_mutual_information [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    {δ : ℝ} (hδ : 0 ≤ δ) (hdef : 4*(obs μ q-StandardMapEntropy.Entropy.cond μ q p) ≤ δ^2) :
    LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q)) δ := by
  have hconst : LawClose (μ.map (fun x => ((PUnit.unit : PUnit.{1}),q x)))
      ((μ.map (fun _ : X => (PUnit.unit : PUnit.{1}))).prod (μ.map q)) 0 := by
    have heq := (ProbabilityTheory.indepFun_const_left (μ:=μ) (PUnit.unit : PUnit.{1}) q).map_prod_eq_prod_map_map
      measurable_const.aemeasurable hq.aemeasurable
    rw [heq]
    intro D _
    simp only [sub_self,abs_zero]
    exact le_rfl
  have hd : 4*(StandardMapEntropy.Entropy.cond μ q ((fun _ : A => (PUnit.unit : PUnit.{1})) ∘ p)-StandardMapEntropy.Entropy.cond μ q p) ≤ δ^2 := by
    simpa only [Function.comp_def,cond_constant μ q hq] using hdef
  have hh := lawClose_of_coarse_independence μ p q (fun _ : A => (PUnit.unit : PUnit.{1})) hp hq hδ hconst hd
  simpa only [mul_zero,add_zero] using hh

lemma lawClose_entropy_budget [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B) (hp : Measurable p) (hq : Measurable q)
    {τ : ℝ} (hτ : 0 < τ) :
    LawClose (μ.map (fun x => (p x,q x))) ((μ.map p).prod (μ.map q))
      ((obs μ q-StandardMapEntropy.Entropy.cond μ q p)/τ+τ) := by
  have hI : 0 ≤ obs μ q-StandardMapEntropy.Entropy.cond μ q p := sub_nonneg.mpr (cond_le_obs μ q p hq hp)
  apply lawClose_of_mutual_information μ p q hp hq (by positivity)
  have he : ((obs μ q-StandardMapEntropy.Entropy.cond μ q p)/τ)*τ=obs μ q-StandardMapEntropy.Entropy.cond μ q p := div_mul_cancel₀ _ hτ.ne'
  nlinarith [sq_nonneg ((obs μ q-StandardMapEntropy.Entropy.cond μ q p)/τ-τ)]

variable (μ : Measure X)

noncomputable def sequenceEntropyDefect [Fintype A] (q : ℕ → X → A) (i n : ℕ) : ℝ :=
  (∑ j : Fin n,obs μ (q (i+j.val)))-obs μ (finiteName q i n)

lemma obs_finiteName_zero [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [StandardBorelSpace X] [Nonempty A] [IsProbabilityMeasure μ]
    (q : ℕ → X → A) (i : ℕ) : obs μ (finiteName q i 0)=0 := by
  have heq : finiteName q i 0=(fun _ => (fun j : Fin 0 => j.elim0 : Fin 0 → A)) := by
    funext x j
    exact j.elim0
  rw [heq,obs_const]

lemma sequenceEntropyDefect_cons [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [StandardBorelSpace X] [Nonempty A] [IsProbabilityMeasure μ]
    (q : ℕ → X → A) (i n : ℕ) :
    sequenceEntropyDefect μ q i (n+1)=
      (obs μ (q i)-StandardMapEntropy.Entropy.cond μ (q i) (finiteName q (i+1) n))+sequenceEntropyDefect μ q (i+1) n := by
  let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
  have heq : finiteName q i (n+1)=e ∘ (fun x => (q i x,finiteName q (i+1) n x)) :=
    funext (finiteName_cons q i n)
  have hobs : obs μ (finiteName q i (n+1))=obs μ (fun x => (q i x,finiteName q (i+1) n x)) := by
    rw [heq,obs_equiv]
  simp only [sequenceEntropyDefect,Fin.sum_univ_succ,Fin.val_zero,Nat.add_zero,Fin.val_succ,hobs,StandardMapEntropy.Entropy.cond]
  have hs : (∑ j : Fin n,obs μ (q (i+(j.val+1))))=
      ∑ j : Fin n,obs μ (q ((i+1)+j.val)) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    omega
  rw [hs]
  ring

lemma independentNameWeights_cons_finite [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [StandardBorelSpace X] [Nonempty A] [IsProbabilityMeasure μ]
    (q : ℕ → X → A) (i n : ℕ) (w : Fin (n+1) → A) :
    independentNameWeights μ q i (n+1) w=
      mass μ (q i) (w 0)*independentNameWeights μ q (i+1) n (Fin.tail w) := by
  rw [independentNameWeights,Fin.prod_univ_succ]
  simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,Fin.tail,independentNameWeights]
  congr 2
  funext j
  congr 2
  omega

lemma mass_equiv_inverse_finite [StandardBorelSpace X] [IsProbabilityMeasure μ]
    {C D : Type*} [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]
    (p : X → C) (e : C ≃ D) (d : D) : mass μ (e ∘ p) d=mass μ p (e.symm d) := by
  unfold mass
  congr 2
  ext x
  simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,← Equiv.eq_symm_apply]

theorem entropy_product_transport [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [StandardBorelSpace X] [Nonempty A] [IsProbabilityMeasure μ]
    (q : ℕ → X → A) (hq : ∀ i,Measurable (q i))
    {τ : ℝ} (hτ : 0 < τ) :
    ∀ i n : ℕ,∃ R : MatrixCoupling (mass μ (finiteName q i n)) (independentNameWeights μ q i n),
      R.cost nameCost ≤ sequenceEntropyDefect μ q i n/τ+(n : ℝ)*τ := by
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
    let R : MatrixCoupling (mass μ (finiteName q i 0)) (independentNameWeights μ q i 0) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun w => by simp [hm]
      col := fun w => by simp [independentNameWeights] }
    refine ⟨R,?_⟩
    simp [MatrixCoupling.cost,nameCost,sequenceEntropyDefect,obs_finiteName_zero]
  | succ n ih =>
    obtain ⟨r,hr⟩ := ih (i+1)
    have hc := lawClose_entropy_budget μ (finiteName q (i+1) n) (q i)
      (finiteName_measurable q hq (i+1) n) (hq i) hτ
    obtain ⟨s,hs⟩ := coupling_step_finite μ (finiteName q (i+1) n) (q i)
      (finiteName_measurable q hq (i+1) n) (hq i)
      (independentNameWeights μ q (i+1) n) r nameCost nameCost_self nameCost_triangle hc
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := s.reindex e.symm e.symm
    have hm (w : Fin (n+1) → A) :
        mass μ (fun x => (q i x,finiteName q (i+1) n x)) (e.symm w)=mass μ (finiteName q i (n+1)) w := by
      rw [←mass_equiv_inverse_finite μ _ e w]
      congr 1
      funext x
      exact (finiteName_cons q i n x).symm
    have hw (w : Fin (n+1) → A) :
        mass μ (q i) (e.symm w).1*independentNameWeights μ q (i+1) n (e.symm w).2=
          independentNameWeights μ q i (n+1) w := (independentNameWeights_cons_finite μ q i n w).symm
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
    rw [hcost,sequenceEntropyDefect_cons]
    have hh := hs.trans (add_le_add (le_refl _) hr)
    convert hh using 1; first | rfl | (push_cast; ring)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem sequential_coupling_budgets (q : ℕ → X → A) (hq : ∀ i,Measurable (q i))
    (N : ℕ) (b : ℕ → ℝ)
    (hremote : ∀ i n : ℕ,i+n+1≤N → LawClose
      (μ.map (fun x => (finiteName q (i+1) n x,q i x)))
      ((μ.map (finiteName q (i+1) n)).prod (μ.map (q i))) (b i)) :
    ∀ i n : ℕ,i+n≤N → ∃ R : MatrixCoupling (mass μ (finiteName q i n)) (independentNameWeights μ q i n),
      R.cost nameCost≤∑ j : Fin n,b (i+j.val) := by
  intro i n hi
  induction n generalizing i with
  | zero =>
    have hm (w : Fin 0 → A) : mass μ (finiteName q i 0) w=1 := by
      have he : (finiteName q i 0) ⁻¹' {w}=univ := by
        ext x
        simp only [mem_preimage,mem_singleton_iff,mem_univ,iff_true]
        funext j
        exact j.elim0
      simp [mass,he]
    let R : MatrixCoupling (mass μ (finiteName q i 0)) (independentNameWeights μ q i 0) := {
      weight := fun _ _ => 1
      nonneg := fun _ _ => zero_le_one
      row := fun w => by simp [hm]
      col := fun w => by simp [independentNameWeights] }
    refine ⟨R,?_⟩
    simp [MatrixCoupling.cost,nameCost]
  | succ n ih =>
    obtain ⟨r,hr⟩ := ih (i+1) (by omega)
    have hc := hremote i n hi
    obtain ⟨s,hs⟩ := coupling_step_finite μ (finiteName q (i+1) n) (q i)
      (finiteName_measurable q hq (i+1) n) (hq i)
      (independentNameWeights μ q (i+1) n) r nameCost nameCost_self nameCost_triangle hc
    let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
    let t := s.reindex e.symm e.symm
    have hm (w : Fin (n+1) → A) :
        mass μ (fun x => (q i x,finiteName q (i+1) n x)) (e.symm w)=mass μ (finiteName q i (n+1)) w := by
      rw [←mass_equiv_inverse_finite μ _ e w]
      congr 1
      funext x
      exact (finiteName_cons q i n x).symm
    have hw (w : Fin (n+1) → A) :
        mass μ (q i) (e.symm w).1*independentNameWeights μ q (i+1) n (e.symm w).2=
          independentNameWeights μ q i (n+1) w := (independentNameWeights_cons_finite μ q i n w).symm
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
    rw [hcost,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have he : (∑ j : Fin n,b (i+(j.val+1)))=∑ j : Fin n,b (i+1+j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      omega
    rw [he]
    exact hs.trans (add_le_add (le_refl _) hr)

lemma finiteName_entropy_chain (q : ℕ → X → A) (i n : ℕ) :
    obs μ (finiteName q i n)=∑ j : Fin n,StandardMapEntropy.Entropy.cond μ
      (q (i+j.val)) (finiteName q (i+j.val+1) (n-j.val-1)) := by
  induction n generalizing i with
  | zero => simp [obs_finiteName_zero]
  | succ n ih =>
    have he : obs μ (finiteName q i (n+1))=
        StandardMapEntropy.Entropy.cond μ (q i) (finiteName q (i+1) n)+obs μ (finiteName q (i+1) n) := by
      let e : (A×(Fin n → A)) ≃ (Fin (n+1) → A) := Fin.consEquiv (fun _ => A)
      have heq : finiteName q i (n+1)=e ∘ (fun x => (q i x,finiteName q (i+1) n x)) :=
        funext (finiteName_cons q i n)
      rw [heq,obs_equiv]
      unfold StandardMapEntropy.Entropy.cond
      ring
    rw [he,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Nat.sub_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hl : n+1-(j.val+1)-1=n-j.val-1 := by omega
    have hi : i+1+j.val=i+(j.val+1) := by omega
    simp only [hi]
    exact congrArg (fun m => StandardMapEntropy.Entropy.cond μ (q (i+(j.val+1)))
      (finiteName q (i+(j.val+1)+1) m)) hl.symm
end HyperbolicCoding

end

end OAI
