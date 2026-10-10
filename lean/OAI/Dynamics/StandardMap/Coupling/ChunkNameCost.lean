import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Bernoulli.ReverseTailProjection
import OAI.Dynamics.StandardMap.Coupling.SequentialChunkCoupling

namespace OAI

section
section
namespace HyperbolicCoding
open scoped BigOperators
lemma symbolCost_le_one {A : Type*} (a b : A) : symbolCost a b≤1 := by
  unfold symbolCost
  split <;> norm_num
lemma nameCost_le_card {A : Type*} {n : ℕ} (v w : Fin n → A) : nameCost v w≤(n : ℝ) := by
  calc
    _≤∑ _i : Fin n,(1 : ℝ) := Finset.sum_le_sum (fun i _ => symbolCost_le_one _ _)
    _=_ := by simp
lemma nameCost_le_chunkCost {A : Type*} {n : ℕ} (v w : Fin n → A) :
    nameCost v w≤(n : ℝ)*symbolCost v w := by
  classical
  by_cases h : v=w
  · subst w; simp only [nameCost_self,symbolCost_self,mul_zero,le_refl]
  · simpa only [symbolCost,ite_eq_right h,mul_one] using nameCost_le_card v w

theorem nameCost_le_retained_chunks {A : Type*} (k g n : ℕ)
    (v w : Fin (n*(k+g)) → A) :
    nameCost v w≤(k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ) := by
  have he : nameCost v w=∑ j : Fin n,∑ r : Fin (k+g),
      symbolCost (v (finProdFinEquiv (j,r))) (w (finProdFinEquiv (j,r))) := by
    rw [nameCost,←Equiv.sum_comp finProdFinEquiv (fun i => symbolCost (v i) (w i)),Fintype.sum_prod_type]
  rw [he]
  have hb (j : Fin n) : (∑ r : Fin (k+g),
      symbolCost (v (finProdFinEquiv (j,r))) (w (finProdFinEquiv (j,r))))≤
      (k : ℝ)*symbolCost (selectChunks k g n v j) (selectChunks k g n w j)+(g : ℝ) := by
    rw [Fin.sum_univ_add]
    have hp : (∑ r : Fin k,symbolCost (v (finProdFinEquiv (j,Fin.castAdd g r)))
        (w (finProdFinEquiv (j,Fin.castAdd g r))))=
        nameCost (selectChunks k g n v j) (selectChunks k g n w j) := by
      apply Finset.sum_congr rfl
      intro r _
      unfold selectChunks
      congr 2 <;> apply Fin.ext <;> dsimp [finProdFinEquiv] <;> ring
    have hg : (∑ r : Fin g,symbolCost (v (finProdFinEquiv (j,Fin.natAdd k r)))
        (w (finProdFinEquiv (j,Fin.natAdd k r))))≤(g : ℝ) := by
      calc
        _≤∑ _r : Fin g,(1 : ℝ) := Finset.sum_le_sum (fun r _ => symbolCost_le_one _ _)
        _=_ := by simp
    rw [hp]
    have hc := nameCost_le_chunkCost (selectChunks k g n v j) (selectChunks k g n w j)
    linarith
  calc
    _≤∑ j : Fin n,((k : ℝ)*symbolCost (selectChunks k g n v j) (selectChunks k g n w j)+(g : ℝ)) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _=_ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,nameCost]
      norm_cast

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
namespace MatrixCoupling
variable {A B : Type*} [Fintype A] [Fintype B] {p : A → ℝ} {q : B → ℝ}
lemma cost_mono (r : MatrixCoupling p q) (d e : A → B → ℝ) (h : ∀ a b,d a b≤e a b) :
    r.cost d≤r.cost e :=
  Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ =>
    mul_le_mul_of_nonneg_left (h a b) (r.nonneg a b)))
lemma cost_affine (r : MatrixCoupling p q) (hp : ∑ a,p a=1) (K C : ℝ) (d : A → B → ℝ) :
    r.cost (fun a b => K*d a b+C)=K*r.cost d+C := by
  unfold cost
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · simp only [←Finset.sum_mul,r.row,hp,one_mul]
end MatrixCoupling

variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

theorem lift_observation_transport (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (q : Y → A) (hp : Measurable p) (hq : Measurable q)
    (c : A → B) (S : MatrixCoupling (mass μ (c ∘ p)) (mass ν (c ∘ q)))
    (d : B → B → ℝ) (hdiag : ∀ b,d b b=0) (htri : ∀ a b c,d a c≤d a b+d b c) :
    ∃ R : MatrixCoupling (mass μ p) (mass ν q),R.cost (fun a b => d (c a) (c b))≤S.cost d := by
  have hc : Measurable c := measurable_of_countable c
  let P := MatrixCoupling.observations μ p (c ∘ p) hp (hc.comp hp)
  let Q := MatrixCoupling.observations ν (c ∘ q) q (hc.comp hq) hq
  have hP : P.cost (fun a b => d (c a) b)=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [Function.comp_apply,hdiag,integral_zero]
  have hQ : Q.cost (fun a b => d a (c b))=0 := by
    rw [MatrixCoupling.observations_cost]
    simp only [Function.comp_apply,hdiag,integral_zero]
  refine ⟨(P.comp S).comp Q,?_⟩
  have h1 := MatrixCoupling.comp_cost_le P S (fun a b => d (c a) b) d
    (fun a b => d (c a) b) (fun a b v => htri (c a) b v)
  have h2 := MatrixCoupling.comp_cost_le (P.comp S) Q (fun a b => d (c a) b)
    (fun a b => d a (c b)) (fun a b => d (c a) (c b)) (fun a b v => htri (c a) b (c v))
  rw [hP,zero_add] at h1
  rw [hQ,add_zero] at h2
  exact h2.trans h1

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators

theorem full_word_transport {X Y A : Type*}
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
    ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word f p (n*(k+g))))
      (mass ν (word T q (n*(k+g)))),
      R.cost nameCost≤(n : ℝ)*((k : ℝ)*(εP+δ+εQ)+(g : ℝ)) := by
  intro n
  obtain ⟨S,hS⟩ := chunk_process_transport μ ν f hf p hp T hT q hq k g hP hQ hlaw n
  have hPsel : selectChunks k g n ∘ word f p (n*(k+g))=
      finiteName (chunkObservation f p k g) 0 n := funext (selectChunks_word f p k g n)
  have hQsel : selectChunks k g n ∘ word T q (n*(k+g))=
      finiteName (chunkObservation T q k g) 0 n := funext (selectChunks_word T q k g n)
  let S' : MatrixCoupling (mass μ (selectChunks k g n ∘ word f p (n*(k+g))))
      (mass ν (selectChunks k g n ∘ word T q (n*(k+g)))) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun w => by rw [hPsel]; exact S.row w
    col := fun w => by rw [hQsel]; exact S.col w }
  obtain ⟨R,hR⟩ := lift_observation_transport μ ν (word f p (n*(k+g))) (word T q (n*(k+g)))
    (word_measurable f hf.measurable p hp _) (word_measurable T hT.measurable q hq _)
    (selectChunks k g n) S' nameCost nameCost_self nameCost_triangle
  refine ⟨R,?_⟩
  have hmass : (∑ v,mass μ (word f p (n*(k+g))) v)=1 := by
    simp only [mass_sum μ _ (word_measurable f hf.measurable p hp _),measure_univ,ENNReal.toReal_one]
  have hbd := R.cost_mono nameCost
    (fun v w => (k : ℝ)*nameCost (selectChunks k g n v) (selectChunks k g n w)+(n*g : ℕ))
    (nameCost_le_retained_chunks k g n)
  rw [R.cost_affine hmass] at hbd
  have hk0 : 0≤(k : ℝ) := Nat.cast_nonneg k
  have h1 := mul_le_mul_of_nonneg_left hR hk0
  have hS' : S'.cost nameCost≤(n : ℝ)*(εP+δ+εQ) := hS
  have h2 := mul_le_mul_of_nonneg_left hS' hk0
  push_cast at hbd
  nlinarith

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter
open scoped ENNReal Topology
variable {X A B C : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C]
variable (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (α : X → A) (hα : Measurable α)

include he hα
lemma finite_remote_lawClose {n : ℕ} {ε : ℝ}
    (h : LawClose (μ.map (remotePair e e.symm α n)) (remoteProductLaw μ e e.symm α) ε)
    (f : (ℕ → A) → B) (g : (ℕ → A) → C) (hf : Measurable f) (hg : Measurable g) :
    LawClose (μ.map (fun x => (f (tailName e.symm α n x),g (tailName e α n x))))
      ((μ.map (fun x => f (tailName e.symm α n x))).prod
        (μ.map (fun x => g (tailName e α n x)))) ε := by
  have hh := h.map (hf.prodMap hg)
  rw [Measure.map_map (hf.prodMap hg) (measurable_remotePair e.measurable e.symm.measurable hα n)] at hh
  have hmf : (μ.map (tailName e.symm α 0)).map f=μ.map (fun x => f (tailName e.symm α n x)) := by
    rw [←stationary_tail_law μ (he.symm e) hα n,Measure.map_map hf
      (measurable_tailName e.symm.measurable hα n)]
    rfl
  have hmg : (μ.map (tailName e α 0)).map g=μ.map (fun x => g (tailName e α n x)) := by
    rw [←stationary_tail_law μ he hα n,Measure.map_map hg
      (measurable_tailName e.measurable hα n)]
    rfl
  unfold remoteProductLaw at hh
  rw [←Measure.map_prod_map _ _ hf hg,hmf,hmg] at hh
  exact hh

theorem weakBernoulli_finite_copy [StandardBorelSpace X] [NullSingletonClass μ]
    [Fintype B] [MeasurableSingletonClass B]
    [Fintype C] [MeasurableSingletonClass C] [Nonempty C]
    (hwb : WeakBernoulliProcess μ e α) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop,∀ (f : (ℕ → A) → B) (g : (ℕ → A) → C),
      Measurable f → Measurable g →
      ∃ q : X → C,Measurable q ∧ μ.map q=μ.map (fun x => g (tailName e α n x)) ∧
        μ.map (fun x => (f (tailName e.symm α n x),q x))=
          (μ.map (fun x => f (tailName e.symm α n x))).prod
            (μ.map (fun x => g (tailName e α n x))) ∧
        μ.real {x | g (tailName e α n x)≠q x}≤ε := by
  filter_upwards [hwb ε hε] with n hn
  intro f g hf hg
  exact copy_independent_of_finite_past μ _ _
    (hf.comp (measurable_tailName e.symm.measurable hα n))
    (hg.comp (measurable_tailName e.measurable hα n))
    (finite_remote_lawClose μ e he α hα hn f g hf hg)

end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    [Fintype A] [MeasurableSingletonClass A]
variable (μ : Measure X) [IsProbabilityMeasure μ]

omit [Fintype A] [MeasurableSingletonClass A] in
theorem weakBernoulli_forward_blocks (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : X → A) (hα : Measurable α) (hwb : WeakBernoulliProcess μ e α)
    {ε : ℝ} (hε : 0<ε) : ∃ g : ℕ,∀ k M : ℕ,LawClose
      (μ.map (fun x => (word e α M (e^[k+g] x),word e α k x)))
      ((μ.map (fun x => word e α M (e^[k+g] x))).prod (μ.map (word e α k))) ε := by
  obtain ⟨N,hN⟩ := (hwb ε hε).exists
  refine ⟨2*N,?_⟩
  intro k M
  let P : (ℕ → A) → (Fin k → A) := fun w i => w (k-i.val)
  let Q : (ℕ → A) → (Fin M → A) := fun w i => w i.val
  have hP : Measurable P := Measurable.of_eval (fun index => measurable_pi_apply (k-index.val))
  have hQ : Measurable Q := Measurable.of_eval (fun index => measurable_pi_apply index.val)
  have hfin := finite_remote_lawClose μ e he α hα hN P Q hP hQ
  have hp : Measurable (fun x => P (tailName e.symm α N x)) :=
    hP.comp (measurable_tailName e.symm.measurable hα N)
  have hq : Measurable (fun x => Q (tailName e α N x)) :=
    hQ.comp (measurable_tailName e.measurable hα N)
  have hcomp := lawClose_pair_comp μ (e^[k+N]) (he.iterate (k+N)) _ _ hp hq hfin
  have hswap := lawClose_pair_swap μ _ _ (hp.comp (he.measurable.iterate (k+N)))
    (hq.comp (he.measurable.iterate (k+N))) hcomp
  have hp' (x : X) : P (tailName e.symm α N (e^[k+N] x))=word e α k x := by
    funext i
    change α (e.symm^[(k-i.val)+N] (e^[k+N] x))=α (e^[i.val] x)
    rw [inverse_iterate_forward_sub e (by omega)]
    congr 2
    omega
  have hq' (x : X) : Q (tailName e α N (e^[k+N] x))=word e α M (e^[k+2*N] x) := by
    funext i
    change α (e^[i.val+N] (e^[k+N] x))=α (e^[i.val] (e^[k+2*N] x))
    rw [←Function.iterate_add_apply,←Function.iterate_add_apply]
    congr 2
    omega
  simpa only [Function.comp_def,hp',hq'] using hswap

end HyperbolicCoding

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set HyperbolicCoding
open scoped ENNReal Topology BigOperators
variable {A X Y : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma continuous_shannon : Continuous (shannon (α:=A)) := by
  unfold shannon
  fun_prop

theorem finite_entropy_continuity (μ : Measure A) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ ν : Measure A,LawClose μ ν δ →
      |shannon (fun a => μ.real {a})-shannon (fun a => ν.real {a})|<ε := by
  obtain ⟨η,hη,hcont⟩ := Metric.continuousAt_iff.mp (continuous_shannon (A:=A)).continuousAt ε hε
  refine ⟨η/2,half_pos hη,?_⟩
  intro ν hν
  have hd : dist (fun a => ν.real {a}) (fun a => μ.real {a})<η := by
    apply (dist_pi_lt_iff hη).mpr
    intro a
    rw [Real.dist_eq,abs_sub_comm]
    exact (hν {a} (measurableSet_singleton a)).trans_lt (half_lt_self hη)
  simpa only [Real.dist_eq,abs_sub_comm] using hcont hd

lemma obs_eq_entropy_map (μ : Measure X) (p : X → A) (hp : Measurable p) :
    obs μ p=shannon (fun a => (μ.map p).real {a}) := by
  unfold obs
  congr 1
  funext a
  exact (map_measureReal_apply hp (measurableSet_singleton a)).symm

theorem obs_continuity_in_law (μ : Measure X) (p : X → A) (hp : Measurable p)
    {ε : ℝ} (hε : 0<ε) : ∃ δ : ℝ,0<δ ∧
    ∀ (ν : Measure Y) (q : Y → A),Measurable q → LawClose (μ.map p) (ν.map q) δ →
      |obs μ p-obs ν q|<ε := by
  obtain ⟨δ,hδ,hh⟩ := finite_entropy_continuity (μ.map p) hε
  refine ⟨δ,hδ,?_⟩
  intro ν q hq hclose
  rw [obs_eq_entropy_map μ p hp,obs_eq_entropy_map ν q hq]
  exact hh _ hclose

end StandardMapEntropy.Entropy

end
section
namespace StandardMapEntropy.Entropy
open MeasureTheory Set
open scoped BigOperators ENNReal
variable {X A B C D : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [Fintype C] [MeasurableSingletonClass C]
    [MeasurableSpace D] [Fintype D] [MeasurableSingletonClass D]
variable (μ : Measure X) [IsProbabilityMeasure μ]

lemma cond_factor_chain (q : X → B) (r : X → A) (d : B → D)
    (hq : Measurable q) (hr : Measurable r) :
    cond μ q r=cond μ (d ∘ q) r+cond μ q (fun x => (d (q x),r x)) := by
  have hd : Measurable (d ∘ q) := (measurable_of_countable d).comp hq
  have he : cond μ (fun x => (d (q x),q x)) r=cond μ q r := by
    apply le_antisymm
    · exact cond_factor_left μ q r (fun b => (d b,b)) hq hr
    · exact cond_factor_left μ (fun x => (d (q x),q x)) r Prod.snd (hd.prodMk hq) hr
  rw [←he,cond_chain]
  rfl

theorem conditional_defect_data_processing (p : X → A) (q : X → B)
    (c : A → C) (d : B → D) (hp : Measurable p) (hq : Measurable q) :
    cond μ (d ∘ q) (c ∘ p)-cond μ (d ∘ q) p≤
      cond μ q (c ∘ p)-cond μ q p := by
  have hc : Measurable (c ∘ p) := (measurable_of_countable c).comp hp
  have hd : Measurable (d ∘ q) := (measurable_of_countable d).comp hq
  have h1 := cond_factor_chain μ q (c ∘ p) d hq hc
  have h2 := cond_factor_chain μ q p d hq hp
  have h3 := cond_factor_right μ q (fun x => (d (q x),p x))
    (fun v : D×A => (v.1,c v.2)) hq (hd.prodMk hp)
  change cond μ q (fun x => (d (q x),p x))≤
    cond μ q (fun x => (d (q x),c (p x))) at h3
  simp only [Function.comp_def] at h1 h2 ⊢
  linarith

end StandardMapEntropy.Entropy

end
section
namespace HyperbolicCoding
open scoped BigOperators

noncomputable def relativeInformation {A : Type*} [Fintype A] (p q : A → ℝ) : ℝ :=
  ∑ a,p a*(Real.log (p a)-Real.log (q a))

lemma log_ratio_hellinger_bound {p q : ℝ} (hp : 0≤p) (hq : 0≤q)
    (hs : p≠0 → q≠0) : 2*p-2*Real.sqrt p*Real.sqrt q≤p*(Real.log p-Real.log q) := by
  by_cases hp0 : p=0
  · simp [hp0]
  have hp' : 0<p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0<q := lt_of_le_of_ne hq (Ne.symm (hs hp0))
  have ha : 0<Real.sqrt p := Real.sqrt_pos.mpr hp'
  have hb : 0<Real.sqrt q := Real.sqrt_pos.mpr hq'
  have hh := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hb ha)) (mul_nonneg (by norm_num : (0 : ℝ)≤2) hp)
  rw [Real.log_div hb.ne' ha.ne',Real.log_sqrt hq,Real.log_sqrt hp] at hh
  have hr : p*(Real.sqrt q/Real.sqrt p)=Real.sqrt p*Real.sqrt q := by
    calc
      _=(Real.sqrt p*Real.sqrt p)*(Real.sqrt q/Real.sqrt p) :=
        congrArg (fun t : ℝ => t*(Real.sqrt q/Real.sqrt p)) (Real.mul_self_sqrt hp).symm
      _=_ := by field_simp
  have he : 2*p*(Real.sqrt q/Real.sqrt p-1)=2*Real.sqrt p*Real.sqrt q-2*p := by
    calc
      _=2*(p*(Real.sqrt q/Real.sqrt p))-2*p := by ring
      _=_ := by rw [hr]; ring
  rw [he] at hh
  nlinarith

theorem finite_pinsker_sq {A : Type*} [Fintype A] (p q : A → ℝ)
    (hp : ∀ a,0≤p a) (hq : ∀ a,0≤q a)
    (hp1 : ∑ a,p a=1) (hq1 : ∑ a,q a=1) (hs : ∀ a,p a≠0 → q a≠0) :
    (∑ a,|p a-q a|)^2≤4*relativeInformation p q := by
  let u : A → ℝ := fun a => Real.sqrt (p a)-Real.sqrt (q a)
  let v : A → ℝ := fun a => Real.sqrt (p a)+Real.sqrt (q a)
  have hu (a) : (u a)^2=p a+q a-2*Real.sqrt (p a)*Real.sqrt (q a) := by
    dsimp [u]
    nlinarith [Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
  have huv (a) : |p a-q a|=|u a| * v a := by
    have he : p a-q a=u a*v a := by
      dsimp [u,v]
      nlinarith [Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
    rw [he,abs_mul,abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  have hH : (∑ a,(u a)^2)≤relativeInformation p q := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => log_ratio_hellinger_bound (hp a) (hq a) (hs a))
    have he : (∑ a,(u a)^2)=(∑ a,(2*p a-2*Real.sqrt (p a)*Real.sqrt (q a))) := by
      simp_rw [hu]
      rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hp1,hq1,Finset.sum_sub_distrib,←Finset.mul_sum,hp1]
      norm_num
    rw [he]
    exact hh
  have hV : (∑ a,(v a)^2)≤4 := by
    have hv (a) : (v a)^2≤2*p a+2*q a := by
      dsimp [v]
      nlinarith [sq_nonneg (u a),hu a,Real.sq_sqrt (hp a),Real.sq_sqrt (hq a)]
    calc
      _≤∑ a,(2*p a+2*q a) := Finset.sum_le_sum (fun a _ => hv a)
      _=4 := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,hp1,hq1]; norm_num
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s:=Finset.univ) (fun a => |u a|) v
  simp only [sq_abs] at hc
  simp_rw [huv]
  calc
    _≤(∑ a,(u a)^2)*(∑ a,(v a)^2) := hc
    _≤(∑ a,(u a)^2)*4 := mul_le_mul_of_nonneg_left hV (Finset.sum_nonneg (fun a _ => sq_nonneg (u a)))
    _≤4*relativeInformation p q := by nlinarith [hH]

end HyperbolicCoding

end
end

end OAI
