import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.IidFiniteWindowApprox

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B C D : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]

theorem coarse_conditional_budget (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (q : X → B) (c : A → C) (d : B → D)
    (hp : Measurable p) (hq : Measurable q) {ε τ : ℝ} (hτ : 0<τ)
    (hclose : LawClose (μ.map (fun x => (c (p x),d (q x))))
      ((μ.map (c ∘ p)).prod (μ.map (d ∘ q))) ε) :
    LawClose (μ.map (fun x => (p x,d (q x)))) ((μ.map p).prod (μ.map (d ∘ q)))
      ((StandardMapEntropy.Entropy.cond μ q (c ∘ p)-StandardMapEntropy.Entropy.cond μ q p)/τ+τ+2*ε) := by
  let Δ := StandardMapEntropy.Entropy.cond μ q (c ∘ p)-StandardMapEntropy.Entropy.cond μ q p
  have hΔ : 0≤Δ := sub_nonneg.mpr (cond_factor_right μ q p c hq hp)
  have hdata := conditional_defect_data_processing μ p q c d hp hq
  have hδ : 0≤Δ/τ+τ := by positivity
  have hsq : 4*Δ≤(Δ/τ+τ)^2 := by
    have he : (Δ/τ)*τ=Δ := div_mul_cancel₀ _ hτ.ne'
    nlinarith [sq_nonneg (Δ/τ-τ)]
  exact lawClose_of_coarse_independence μ p (d ∘ q) c hp
    ((measurable_of_countable d).comp hq) hδ hclose ((by linarith :
      4*(StandardMapEntropy.Entropy.cond μ (d ∘ q) (c ∘ p)-
        StandardMapEntropy.Entropy.cond μ (d ∘ q) p)≤4*Δ).trans hsq)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem finite_local_entropy_bridge (q : ℕ → X → B) (hq : ∀ i,Measurable (q i))
    (d : B → A) (N : ℕ) (C : ℕ → Type*) [∀ i,Fintype (C i)]
    [∀ i,MeasurableSpace (C i)] [∀ i,MeasurableSingletonClass (C i)]
    (c : (i : ℕ) → (Fin (N-i-1) → B) → C i) (ε : ℕ → ℝ) {τ : ℝ} (hτ : 0<τ)
    (hlocal : ∀ i : ℕ,i<N → LawClose
      (μ.map (fun x => (c i (finiteName q (i+1) (N-i-1) x),d (q i x))))
      ((μ.map (c i ∘ finiteName q (i+1) (N-i-1))).prod (μ.map (d ∘ q i))) (ε i)) :
    ∃ R : MatrixCoupling (mass μ (finiteName (fun i => d ∘ q i) 0 N))
        (independentNameWeights μ (fun i => d ∘ q i) 0 N),
      R.cost nameCost≤
        ((∑ j : Fin N,StandardMapEntropy.Entropy.cond μ (q j.val)
          (c j.val ∘ finiteName q (j.val+1) (N-j.val-1)))-obs μ (finiteName q 0 N))/τ+
        (N : ℝ)*τ+2*∑ j : Fin N,ε j.val := by
  let b : ℕ → ℝ := fun i =>
    (StandardMapEntropy.Entropy.cond μ (q i) (c i ∘ finiteName q (i+1) (N-i-1))-
      StandardMapEntropy.Entropy.cond μ (q i) (finiteName q (i+1) (N-i-1)))/τ+τ+2*ε i
  have hremote : ∀ i n : ℕ,i+n+1≤N → LawClose
      (μ.map (fun x => (finiteName (fun i => d ∘ q i) (i+1) n x,d (q i x))))
      ((μ.map (finiteName (fun i => d ∘ q i) (i+1) n)).prod (μ.map (d ∘ q i))) (b i) := by
    intro i n hi
    have hh := coarse_conditional_budget μ (finiteName q (i+1) (N-i-1)) (q i) (c i) d
      (finiteName_measurable q hq (i+1) (N-i-1)) (hq i) hτ (hlocal i (by omega))
    let r : (Fin (N-i-1) → B) → (Fin n → A) := fun w j => d (w ⟨j.val,by omega⟩)
    have hf := lawClose_pair_factor_left μ (finiteName q (i+1) (N-i-1)) (d ∘ q i) r
      (finiteName_measurable q hq _ _) ((measurable_of_countable d).comp (hq i))
      (measurable_of_countable r) hh
    exact hf
  obtain ⟨R,hR⟩ := sequential_coupling_budgets μ (fun i => d ∘ q i)
    (fun i => (measurable_of_countable d).comp (hq i)) N b hremote 0 N (by omega)
  refine ⟨R,hR.trans_eq ?_⟩
  simp only [b,Nat.zero_add,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hc := finiteName_entropy_chain μ q 0 N
  simp only [Nat.zero_add] at hc
  rw [←Finset.sum_div,Finset.sum_sub_distrib,←hc,←Finset.mul_sum]
end HyperbolicCoding

end
section
namespace HyperbolicCoding.MatrixCoupling
open scoped BigOperators
variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]
    (p : I → A → ℝ) (q : I → B → ℝ)

noncomputable def piCoupling (R : ∀ i,MatrixCoupling (p i) (q i)) :
    MatrixCoupling (fun a : I → A => ∏ i,p i (a i)) (fun b : I → B => ∏ i,q i (b i)) where
  weight a b := ∏ i,(R i).weight (a i) (b i)
  nonneg a b := Finset.prod_nonneg (fun i _ => (R i).nonneg _ _)
  row a := by
    rw [←Fintype.prod_sum]
    simp only [(R _).row]
  col b := by
    rw [←Fintype.prod_sum (fun i a => (R i).weight a (b i))]
    simp only [(R _).col]

lemma piCoupling_cost (R : ∀ i,MatrixCoupling (p i) (q i))
    (hp : ∀ i,∑ a,p i a=1) (d : I → A → B → ℝ) :
    (piCoupling p q R).cost (fun a b => ∑ i,d i (a i) (b i))=∑ i,(R i).cost (d i) := by
  classical
  let e : (I → A×B) ≃ ((I → A)×(I → B)) := {
    toFun := fun w => (fun i => (w i).1,fun i => (w i).2)
    invFun := fun w i => (w.1 i,w.2 i)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hw : ∀ i,∑ ab : A×B,(R i).weight ab.1 ab.2=1 := by
    intro i
    rw [Fintype.sum_prod_type]
    simp only [(R i).row,hp]
  change (∑ a : I → A,∑ b : I → B,(∏ i,(R i).weight (a i) (b i))*(∑ i,d i (a i) (b i)))=_
  rw [←Fintype.sum_prod_type (f := fun ab : (I → A)×(I → B) =>
    (∏ i,(R i).weight (ab.1 i) (ab.2 i))*(∑ i,d i (ab.1 i) (ab.2 i))),←e.sum_comp]
  change finiteExpectation (productWeights (fun i (ab : A×B) => (R i).weight ab.1 ab.2))
    (fun w => ∑ i,d i (w i).1 (w i).2)=_
  rw [finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [expectation_coordinate _ hw i (fun ab : A×B => d i ab.1 ab.2),Fintype.sum_prod_type]
  rfl
end HyperbolicCoding.MatrixCoupling

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A B : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B] [Nonempty B]

 theorem nonstationary_conditional_transport
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    {chunkLength : ℕ}
    (q : ℕ → Y → B) (hq : ∀ i,Measurable (q i)) (d : B → Fin chunkLength → A)
    (g n : ℕ) (C : ℕ → Type*) [∀ i,Fintype (C i)] [∀ i,MeasurableSpace (C i)]
    [∀ i,MeasurableSingletonClass (C i)]
    (c : (i : ℕ) → (Fin (n-i-1) → B) → C i) (ε δ : ℕ → ℝ) {ρ τ : ℝ} (hτ : 0<τ)
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[chunkLength+g] x),word f p chunkLength x)))
      ((μ.map (fun x => word f p M (f^[chunkLength+g] x))).prod (μ.map (word f p chunkLength))) ρ)
    (hlaw : ∀ j : Fin n,LawClose (μ.map (word f p chunkLength)) (ν.map (d ∘ q j.val)) (δ j.val))
    (hlocal : ∀ i : ℕ,i<n → LawClose
      (ν.map (fun x => (c i (finiteName q (i+1) (n-i-1) x),d (q i x))))
      ((ν.map (c i ∘ finiteName q (i+1) (n-i-1))).prod (ν.map (d ∘ q i))) (ε i)) :
    ∃ R : MatrixCoupling (mass μ (finiteName (chunkObservation f p chunkLength g) 0 n))
      (mass ν (finiteName (fun i => d ∘ q i) 0 n)),
      R.cost nameCost≤(n : ℝ)*(ρ+τ)+(∑ j : Fin n,δ j.val)+2*(∑ j : Fin n,ε j.val)+
        ((∑ j : Fin n,StandardMapEntropy.Entropy.cond ν (q j.val)
          (c j.val ∘ finiteName q (j.val+1) (n-j.val-1)))-obs ν (finiteName q 0 n))/τ := by
  classical
  obtain ⟨RP,hRP⟩ := stationary_chunk_coupling μ f hf p hp chunkLength g hP n
  obtain ⟨RQ,hRQ⟩ := finite_local_entropy_bridge ν q hq d n C c ε hτ hlocal
  have hcoups (j : Fin n) := coupling_of_observation_lawClose μ ν (word f p chunkLength) (d ∘ q j.val)
    (word_measurable f hf.measurable p hp chunkLength) ((measurable_of_countable d).comp (hq j.val)) (hlaw j)
  choose r hr using hcoups
  let S := MatrixCoupling.piCoupling (fun _ : Fin n => mass μ (word f p chunkLength))
    (fun j : Fin n => mass ν (d ∘ q j.val)) r
  have hS : S.cost nameCost≤∑ j : Fin n,δ j.val := by
    change (MatrixCoupling.piCoupling _ _ r).cost (fun a b => ∑ j : Fin n,symbolCost (a j) (b j))≤_
    rw [MatrixCoupling.piCoupling_cost (d := fun _ => symbolCost)]
    · exact Finset.sum_le_sum (fun j _ => hr j)
    · intro j
      simpa using mass_sum μ (word f p chunkLength) (word_measurable f hf.measurable p hp chunkLength)
  have hw (w : Fin n → Fin chunkLength → A) :
      independentNameWeights ν (fun i => d ∘ q i) 0 n w=∏ j,mass ν (d ∘ q j.val) (w j) := by
    simp only [independentNameWeights,Nat.zero_add]
  let RQ' : MatrixCoupling (mass ν (finiteName (fun i => d ∘ q i) 0 n))
      (fun w : Fin n → Fin chunkLength → A => ∏ j,mass ν (d ∘ q j.val) (w j)) := {
    weight := RQ.weight
    nonneg := RQ.nonneg
    row := RQ.row
    col := fun w => (RQ.col w).trans (hw w) }
  refine ⟨(RP.comp S).comp RQ'.symm,?_⟩
  have h1 := MatrixCoupling.comp_cost_le RP S nameCost nameCost nameCost nameCost_triangle
  have h2 := MatrixCoupling.comp_cost_le (RP.comp S) RQ'.symm nameCost nameCost nameCost nameCost_triangle
  rw [MatrixCoupling.symm_cost RQ' nameCost nameCost_comm] at h2
  have he : RQ'.cost nameCost=RQ.cost nameCost := rfl
  rw [he] at h2
  nlinarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A : Type*} [MeasurableSpace X]

def selectGaps (k g n : ℕ) (w : Fin (n*(k+g)) → A) : Fin n → Fin g → A :=
  fun j r => w (finProdFinEquiv (j,Fin.natAdd k r))

lemma retained_and_gaps_injective
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (k g n : ℕ) :
    Function.Injective (fun w : Fin (n*(k+g)) → A => (selectChunks k g n w,selectGaps k g n w)) := by
  intro v w h
  funext i
  obtain ⟨⟨j,r⟩,rfl⟩ := finProdFinEquiv.surjective i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) r
  · have hh := congrFun (congrFun (congrArg Prod.fst h) j) a
    have hv (u : Fin (n*(k+g)) → A) : u (finProdFinEquiv (j,Fin.castAdd g a))=selectChunks k g n u j a := by
      congr 1
      apply Fin.ext
      simp [finProdFinEquiv]
      ring
    simpa only [hv] using hh
  · exact congrFun (congrFun (congrArg Prod.snd h) j) b

lemma entropy_retained_chunks
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (k g n : ℕ) (q : X → Fin (n*(k+g)) → A) (hq : Measurable q) :
    obs μ q≤obs μ (selectChunks k g n ∘ q)+(n*g : ℕ)*Real.log (Fintype.card A) := by
  classical
  let c : (Fin (n*(k+g)) → A) → ((Fin n → Fin k → A)×(Fin n → Fin g → A)) :=
    fun w => (selectChunks k g n w,selectGaps k g n w)
  have hc : Measurable c := measurable_of_countable c
  have hinv : Function.invFun c ∘ (c ∘ q)=q := by
    funext x
    exact Function.leftInverse_invFun (retained_and_gaps_injective k g n) (q x)
  have hf := obs_factor μ (c ∘ q) (Function.invFun c) (hc.comp hq)
    ((measurable_of_countable _).comp (hc.comp hq))
  rw [hinv] at hf
  have hs := obs_pair_subadd_prob μ (selectChunks k g n ∘ q) (selectGaps k g n ∘ q)
    ((measurable_of_countable _).comp hq) ((measurable_of_countable _).comp hq)
  have hg := obs_bound μ (selectGaps k g n ∘ q) ((measurable_of_countable _).comp hq)
  have he : Real.log (Fintype.card (Fin n → Fin g → A))=(n*g : ℕ)*Real.log (Fintype.card A) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow,Nat.cast_mul]
    ring
  rw [he] at hg
  exact hf.trans (hs.trans (add_le_add (le_refl _) hg))
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty A]

 theorem nonstationary_chunk_transport
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    {chunkLength : ℕ}
    (q : ℕ → Y → Fin chunkLength → A) (hq : ∀ i,Measurable (q i))
    (g n : ℕ) {ε δ τ : ℝ} (hτ : 0<τ)
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[chunkLength+g] x),word f p chunkLength x)))
      ((μ.map (fun x => word f p M (f^[chunkLength+g] x))).prod (μ.map (word f p chunkLength))) ε)
    (hlaw : ∀ j : Fin n,LawClose (μ.map (word f p chunkLength)) (ν.map (q j.val)) δ) :
    ∃ R : MatrixCoupling (mass μ (finiteName (chunkObservation f p chunkLength g) 0 n))
      (mass ν (finiteName q 0 n)),
      R.cost nameCost≤(n : ℝ)*(ε+δ+τ)+sequenceEntropyDefect ν q 0 n/τ := by
  classical
  obtain ⟨RP,hRP⟩ := stationary_chunk_coupling μ f hf p hp chunkLength g hP n
  obtain ⟨RQ,hRQ⟩ := entropy_product_transport ν q hq hτ 0 n
  have hcoups (j : Fin n) := coupling_of_observation_lawClose μ ν (word f p chunkLength) (q j.val)
    (word_measurable f hf.measurable p hp chunkLength) (hq j.val) (hlaw j)
  choose r hr using hcoups
  let S := MatrixCoupling.piCoupling (fun _ : Fin n => mass μ (word f p chunkLength))
    (fun j : Fin n => mass ν (q j.val)) r
  have hS : S.cost nameCost≤(n : ℝ)*δ := by
    change (MatrixCoupling.piCoupling _ _ r).cost (fun a b => ∑ j : Fin n,symbolCost (a j) (b j))≤_
    rw [MatrixCoupling.piCoupling_cost (d := fun _ => symbolCost)]
    · exact (Finset.sum_le_sum (fun j _ => hr j)).trans_eq (by simp)
    · intro j
      simpa using mass_sum μ (word f p chunkLength) (word_measurable f hf.measurable p hp chunkLength)
  have hweights (w : Fin n → Fin chunkLength → A) : independentNameWeights ν q 0 n w=∏ j,mass ν (q j.val) (w j) := by
    simp only [independentNameWeights,Nat.zero_add]
  let RQ' : MatrixCoupling (mass ν (finiteName q 0 n)) (fun w : Fin n → Fin chunkLength → A => ∏ j,mass ν (q j.val) (w j)) := {
    weight := RQ.weight
    nonneg := RQ.nonneg
    row := RQ.row
    col := fun w => (RQ.col w).trans (hweights w) }
  refine ⟨(RP.comp S).comp RQ'.symm,?_⟩
  have h1 := MatrixCoupling.comp_cost_le RP S nameCost nameCost nameCost nameCost_triangle
  have h2 := MatrixCoupling.comp_cost_le (RP.comp S) RQ'.symm nameCost nameCost nameCost nameCost_triangle
  rw [MatrixCoupling.symm_cost RQ' nameCost nameCost_comm] at h2
  have he : RQ'.cost nameCost=RQ.cost nameCost := rfl
  rw [he] at h2
  nlinarith

noncomputable def extractedChunk (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A)
    (i : ℕ) (x : Y) : Fin k → A :=
  if hi : i<n then selectChunks k g n (q x) ⟨i,hi⟩ else fun _ => Classical.ofNonempty

lemma extractedChunk_measurable
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) (hq : Measurable q) (i : ℕ) :
    Measurable (extractedChunk k g n q i) := by
  classical
  unfold extractedChunk
  by_cases hi : i<n
  · simp only [hi,dite_true]
    exact
      (measurable_of_countable (fun w : Fin (n*(k+g)) → A => selectChunks k g n w ⟨i,hi⟩)).comp hq
  · simp only [hi,dite_false]
    exact measurable_const

lemma extractedChunk_name
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) :
    finiteName (extractedChunk k g n q) 0 n=selectChunks k g n ∘ q := by
  funext x j
  simp only [finiteName,Nat.zero_add,extractedChunk,j.isLt,dite_true,Function.comp_apply]

theorem nonstationary_word_transport
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) (hq : Measurable q)
    {ε δ τ : ℝ} (hτ : 0<τ)
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) ε)
    (hlaw : ∀ j : Fin n,LawClose (μ.map (word f p k)) (ν.map (extractedChunk k g n q j.val)) δ) :
    ∃ R : MatrixCoupling (mass μ (word f p (n*(k+g)))) (mass ν q),
      R.cost nameCost≤(k : ℝ)*((n : ℝ)*(ε+δ+τ)+
        sequenceEntropyDefect ν (extractedChunk k g n q) 0 n/τ)+(n*g : ℕ) := by
  obtain ⟨S,hS⟩ := nonstationary_chunk_transport μ ν f hf p hp (extractedChunk k g n q)
    (extractedChunk_measurable k g n q hq) g n hτ hP hlaw
  have hPsel : selectChunks k g n ∘ word f p (n*(k+g))=
      finiteName (chunkObservation f p k g) 0 n := funext (selectChunks_word f p k g n)
  let S' : MatrixCoupling (mass μ (selectChunks k g n ∘ word f p (n*(k+g))))
      (mass ν (selectChunks k g n ∘ q)) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun w => by rw [hPsel]; exact S.row w
    col := fun w => by rw [←extractedChunk_name k g n q]; exact S.col w }
  obtain ⟨R,hR⟩ := lift_observation_transport μ ν (word f p (n*(k+g))) q
    (word_measurable f hf.measurable p hp _) hq
    (selectChunks k g n) S' nameCost nameCost_self nameCost_triangle
  refine ⟨R,?_⟩
  have hmass : (∑ v,mass μ (word f p (n*(k+g))) v)=1 := by
    simpa using mass_sum μ _ (word_measurable f hf.measurable p hp _)
  have hbd := R.cost_mono nameCost
    (fun v w => (k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ))
    (nameCost_le_retained_chunks k g n)
  rw [R.cost_affine hmass] at hbd
  exact hbd.trans (add_le_add (mul_le_mul_of_nonneg_left (hR.trans hS) (Nat.cast_nonneg k)) (le_refl _))

lemma extractedChunk_entropy_defect
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) (hq : Measurable q)
    {H h : ℝ} (hshort : ∀ j : Fin n,obs ν (extractedChunk k g n q j.val)≤H)
    (hlong : (n*(k+g) : ℕ)*h≤obs ν q) :
    sequenceEntropyDefect ν (extractedChunk k g n q) 0 n≤
      (n : ℝ)*(H-(k+g : ℕ)*h+(g : ℝ)*Real.log (Fintype.card A)) := by
  have hs : (∑ j : Fin n,obs ν (extractedChunk k g n q j.val))≤(n : ℝ)*H :=
    (Finset.sum_le_sum (fun j _ => hshort j)).trans_eq (by simp)
  have hc := entropy_retained_chunks ν k g n q hq
  rw [sequenceEntropyDefect,extractedChunk_name]
  simp only [Nat.zero_add]
  push_cast at hlong hc ⊢
  nlinarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty A]

noncomputable def fullBlock (s n : ℕ) (q : Y → Fin (n*s) → A)
    (i : ℕ) (x : Y) : Fin s → A :=
  if hi : i<n then wordPack n s (q x) ⟨i,hi⟩ else fun _ => Classical.ofNonempty

lemma fullBlock_measurable
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n : ℕ) (q : Y → Fin (n*s) → A) (hq : Measurable q) (i : ℕ) :
    Measurable (fullBlock s n q i) := by
  classical
  unfold fullBlock
  by_cases hi : i<n
  · simp only [hi,dite_true]
    exact (measurable_of_countable (fun w : Fin (n*s) → A => wordPack n s w ⟨i,hi⟩)).comp hq
  · simp only [hi,dite_false]
    exact measurable_const

lemma fullBlock_name
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n : ℕ) (q : Y → Fin (n*s) → A) :
    finiteName (fullBlock s n q) 0 n=wordPack n s ∘ q := by
  funext x j
  simp only [finiteName,Nat.zero_add,fullBlock,j.isLt,dite_true,Function.comp_apply]

lemma fullBlock_prefix_name
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) :
    finiteName (fun i => (fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) ∘
      fullBlock (k+g) n q i) 0 n=selectChunks k g n ∘ q := by
  funext x j a
  simp only [finiteName,Nat.zero_add,Function.comp_apply,fullBlock,j.isLt,dite_true,
    wordPack,Equiv.trans_apply,Equiv.curry_apply]
  change q x (finProdFinEquiv (j,a.castAdd g))=selectChunks k g n (q x) j a
  unfold selectChunks
  congr 1
  apply Fin.ext
  dsimp [finProdFinEquiv]
  ring

theorem nonstationary_conditional_word_transport
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g n : ℕ) (q : Y → Fin (n*(k+g)) → A) (hq : Measurable q)
    (C : ℕ → Type*) [∀ i,Fintype (C i)] [∀ i,MeasurableSpace (C i)]
    [∀ i,MeasurableSingletonClass (C i)]
    (c : (i : ℕ) → (Fin (n-i-1) → Fin (k+g) → A) → C i)
    (ε δ : ℕ → ℝ) {ρ τ : ℝ} (hτ : 0<τ)
    (hP : ∀ M : ℕ,LawClose
      (μ.map (fun x => (word f p M (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p M (f^[k+g] x))).prod (μ.map (word f p k))) ρ)
    (hlaw : ∀ j : Fin n,LawClose (μ.map (word f p k))
      (ν.map ((fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) ∘
        fullBlock (k+g) n q j.val)) (δ j.val))
    (hlocal : ∀ i : ℕ,i<n → LawClose
      (ν.map (fun x => (c i (finiteName (fullBlock (k+g) n q) (i+1) (n-i-1) x),
        fun a : Fin k => fullBlock (k+g) n q i x (a.castAdd g))))
      ((ν.map (c i ∘ finiteName (fullBlock (k+g) n q) (i+1) (n-i-1))).prod
        (ν.map ((fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) ∘
          fullBlock (k+g) n q i))) (ε i)) :
    ∃ R : MatrixCoupling (mass μ (word f p (n*(k+g)))) (mass ν q),
      R.cost nameCost≤(k : ℝ)*((n : ℝ)*(ρ+τ)+(∑ j : Fin n,δ j.val)+
        2*(∑ j : Fin n,ε j.val)+((∑ j : Fin n,StandardMapEntropy.Entropy.cond ν
          (fullBlock (k+g) n q j.val)
          (c j.val ∘ finiteName (fullBlock (k+g) n q) (j.val+1) (n-j.val-1)))-obs ν q)/τ)+
          (n*g : ℕ) := by
  obtain ⟨S,hS⟩ := nonstationary_conditional_transport μ ν f hf p hp (fullBlock (k+g) n q)
    (fullBlock_measurable (k+g) n q hq)
    (fun w : Fin (k+g) → A => fun a : Fin k => w (a.castAdd g)) g n C c ε δ hτ hP hlaw hlocal
  have hPsel : selectChunks k g n ∘ word f p (n*(k+g))=
      finiteName (chunkObservation f p k g) 0 n := funext (selectChunks_word f p k g n)
  let S' : MatrixCoupling (mass μ (selectChunks k g n ∘ word f p (n*(k+g))))
      (mass ν (selectChunks k g n ∘ q)) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun w => by rw [hPsel]; exact S.row w
    col := fun w => by rw [←fullBlock_prefix_name k g n q]; exact S.col w }
  obtain ⟨R,hR⟩ := lift_observation_transport μ ν (word f p (n*(k+g))) q
    (word_measurable f hf.measurable p hp _) hq
    (selectChunks k g n) S' nameCost nameCost_self nameCost_triangle
  have he : obs ν (finiteName (fullBlock (k+g) n q) 0 n)=obs ν q := by
    rw [fullBlock_name]
    exact obs_equiv ν q (wordPack n (k+g))
  rw [he] at hS
  refine ⟨R,?_⟩
  have hmass : (∑ v,mass μ (word f p (n*(k+g))) v)=1 := by
    simpa using mass_sum μ _ (word_measurable f hf.measurable p hp _)
  have hbd := R.cost_mono nameCost
    (fun v w => (k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ))
    (nameCost_le_retained_chunks k g n)
  rw [R.cost_affine hmass] at hbd
  exact hbd.trans (add_le_add (mul_le_mul_of_nonneg_left (hR.trans hS) (Nat.cast_nonneg k)) (le_refl _))
end HyperbolicCoding

end

end OAI
