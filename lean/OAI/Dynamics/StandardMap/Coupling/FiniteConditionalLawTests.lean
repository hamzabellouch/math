import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.CoarseConditionalBudget

namespace OAI

section
universe u
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X Y A B D : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSpace D]

lemma conditional_entropy_law_test [Fintype B] [MeasurableSingletonClass B]
    (μ : Measure X) (p : X → A) (r : X → B)
    (hp : Measurable p) (hr : Measurable r) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (ν : Measure Y) (q : Y → A) (s : Y → B),
      Measurable q → Measurable s →
      LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun y => (q y,s y))) δ →
      |StandardMapEntropy.Entropy.cond μ p r-StandardMapEntropy.Entropy.cond ν q s|<ε := by
  obtain ⟨δ₁,hδ₁,h₁⟩ := obs_continuity_in_law (Y:=Y) μ (fun x => (p x,r x)) (hp.prodMk hr)
    (show 0<ε/2 by positivity)
  obtain ⟨δ₂,hδ₂,h₂⟩ := obs_continuity_in_law (Y:=Y) μ r hr (show 0<ε/2 by positivity)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_⟩
  intro ν q s hq hs hlaw
  have hm := hlaw.map measurable_snd
  rw [Measure.map_map measurable_snd (hp.prodMk hr),
    Measure.map_map measurable_snd (hq.prodMk hs)] at hm
  have hh₁ := h₁ ν (fun y => (q y,s y)) (hq.prodMk hs) (hlaw.mono (min_le_left _ _))
  have hh₂ := h₂ ν s hs (hm.mono (min_le_right _ _))
  unfold StandardMapEntropy.Entropy.cond
  have he : obs μ (fun x => (p x,r x))-obs μ r-
      (obs ν (fun y => (q y,s y))-obs ν s)=
      (obs μ (fun x => (p x,r x))-obs ν (fun y => (q y,s y)))-(obs μ r-obs ν s) := by ring
  rw [he]
  exact (abs_sub _ _).trans_lt (by linarith)

lemma conditional_entropy_law_test_uniform [Fintype B] [MeasurableSingletonClass B]
    (μ : Measure X) (p : X → A) (r : X → B)
    (hp : Measurable p) (hr : Measurable r) {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (Y : Type u) [MeasurableSpace Y] (ν : Measure Y)
      (q : Y → A) (s : Y → B),Measurable q → Measurable s →
      LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun y => (q y,s y))) δ →
      |StandardMapEntropy.Entropy.cond μ p r-StandardMapEntropy.Entropy.cond ν q s|<ε := by
  obtain ⟨δ₁,hδ₁,h₁⟩ := finite_entropy_continuity (μ.map (fun x => (p x,r x)))
    (show 0<ε/2 by positivity)
  obtain ⟨δ₂,hδ₂,h₂⟩ := finite_entropy_continuity (μ.map r) (show 0<ε/2 by positivity)
  refine ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,?_⟩
  intro Y mY ν q s hq hs hlaw
  have hm := hlaw.map measurable_snd
  rw [Measure.map_map measurable_snd (hp.prodMk hr),
    Measure.map_map measurable_snd (hq.prodMk hs)] at hm
  have hh₁ := h₁ (ν.map (fun y => (q y,s y))) (hlaw.mono (min_le_left _ _))
  have hh₂ := h₂ (ν.map s) (hm.mono (min_le_right _ _))
  rw [←obs_eq_entropy_map μ (fun x => (p x,r x)) (hp.prodMk hr),
    ←obs_eq_entropy_map ν (fun y => (q y,s y)) (hq.prodMk hs)] at hh₁
  rw [←obs_eq_entropy_map μ r hr,←obs_eq_entropy_map ν s hs] at hh₂
  unfold StandardMapEntropy.Entropy.cond
  have he : obs μ (fun x => (p x,r x))-obs μ r-
      (obs ν (fun y => (q y,s y))-obs ν s)=
      (obs μ (fun x => (p x,r x))-obs ν (fun y => (q y,s y)))-(obs μ r-obs ν s) := by ring
  rw [he]
  exact (abs_sub _ _).trans_lt (by linarith)

lemma marginal_joint_test [Fintype B] [MeasurableSingletonClass B]
    [Fintype D] [MeasurableSingletonClass D] (μ : Measure X) (ν : Measure Y)
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (d : A → D) {δ : ℝ}
    (hlaw : LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun y => (q y,s y))) δ) :
    LawClose (μ.map (d ∘ p)) (ν.map (d ∘ q)) δ := by
  have hd : Measurable (fun z : A×B => d z.1) := (measurable_of_countable d).comp measurable_fst
  have hh := hlaw.map hd
  simpa only [Measure.map_map hd (hp.prodMk hr),Measure.map_map hd (hq.prodMk hs),Function.comp_def] using hh

lemma independence_joint_test [Fintype B] [MeasurableSingletonClass B]
    [Fintype D] [MeasurableSingletonClass D] (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : X → A) (r : X → B) (q : Y → A) (s : Y → B)
    (hp : Measurable p) (hr : Measurable r) (hq : Measurable q) (hs : Measurable s)
    (d : A → D) {δ ε : ℝ}
    (hlaw : LawClose (μ.map (fun x => (p x,r x))) (ν.map (fun y => (q y,s y))) δ)
    (hremote : LawClose (μ.map (fun x => (r x,d (p x))))
      ((μ.map r).prod (μ.map (d ∘ p))) ε) :
    LawClose (ν.map (fun y => (s y,d (q y)))) ((ν.map s).prod (ν.map (d ∘ q))) (ε+3*δ) := by
  have hd : Measurable (fun z : A×B => (z.2,d z.1)) :=
    measurable_snd.prodMk ((measurable_of_countable d).comp measurable_fst)
  have hh := hlaw.map hd
  rw [Measure.map_map hd (hp.prodMk hr),Measure.map_map hd (hq.prodMk hs)] at hh
  exact independence_law_stable μ ν r (d ∘ p) s (d ∘ q) hr
    ((measurable_of_countable d).comp hp) hs ((measurable_of_countable d).comp hq) hh hremote
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {Y A B : Type*} [Nonempty A]

lemma wordPack_apply_coord {A : Type*} (n s : ℕ) (w : Fin (n*s) → A)
    (i : Fin n) (a : Fin s) : wordPack n s w i a=w (finProdFinEquiv (i,a)) := rfl

lemma wordPack_symm_coord {A : Type*} (n s : ℕ) (w : Fin n → Fin s → A)
    (i : Fin n) (a : Fin s) : (wordPack n s).symm w (finProdFinEquiv (i,a))=w i a := by
  have hh := congrFun (congrFun ((wordPack n s).apply_symm_apply w) i) a
  exact hh

lemma fullBlock_packed [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n : ℕ) (V : Y → Fin n → Fin s → A) (i : Fin n) :
    fullBlock s n (fun x => (wordPack n s).symm (V x)) i.val=fun x => V x i := by
  funext x
  simp only [fullBlock,i.isLt,dite_true,Equiv.apply_symm_apply]

def suffixPrefix (n L i : ℕ) (h : i+L<n) (w : Fin (n-i-1) → B) : Fin L → B :=
  fun a => w ⟨a.val,by omega⟩

def vectorFuture (n L i : ℕ) (h : i+L<n) (w : Fin n → B) : Fin L → B :=
  fun a => w ⟨i+1+a.val,by omega⟩

lemma fullBlock_local_future [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (s n L i : ℕ) (h : i+L<n)
    (V : Y → Fin n → Fin s → A) :
    suffixPrefix n L i h ∘ finiteName (fullBlock s n (fun x => (wordPack n s).symm (V x)))
      (i+1) (n-i-1)=vectorFuture n L i h ∘ V := by
  funext x a
  simp only [Function.comp_apply,suffixPrefix,finiteName,vectorFuture,fullBlock]
  have hi : i+1+a.val<n := by omega
  simp only [hi,dite_true,Equiv.apply_symm_apply]

lemma block_inner_future_lt (M J L : ℕ) (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    (finProdFinEquiv (I,j)).val+L<M*J := by
  have hm := Nat.mul_le_mul_right J I.isLt
  change j.val+J*I.val+L<M*J
  nlinarith

lemma vectorFuture_inside_block (M J L : ℕ) (I : Fin M) (j : Fin J) (hj : j.val+L<J)
    (V : Fin M → Fin J → B) :
    vectorFuture (M*J) L (finProdFinEquiv (I,j)).val (block_inner_future_lt M J L I j hj)
      ((wordPack M J).symm V)=vectorFuture J L j.val hj (V I) := by
  funext a
  unfold vectorFuture
  have he : (⟨(finProdFinEquiv (I,j)).val+1+a.val,by
      have hh := block_inner_future_lt M J L I j hj
      omega⟩ : Fin (M*J))=finProdFinEquiv (I,⟨j.val+1+a.val,by omega⟩) := by
    apply Fin.ext
    dsimp [finProdFinEquiv]
    ring
  rw [he,wordPack_symm_coord]

lemma word_vectorFuture [MeasurableSpace Y] [StandardBorelSpace Y]
    (f : Y → Y) (p : Y → B) (J L : ℕ) (j : Fin J) (hj : j.val+L<J) :
    vectorFuture J L j.val hj ∘ word f p J=fun x => word f p L (f^[j.val+1] x) := by
  funext x a
  simp only [Function.comp_apply,vectorFuture,word]
  rw [←Function.iterate_add_apply]
  congr 2
  omega

lemma nameCost_wordPack {A : Type*} (n s : ℕ) (v w : Fin (n*s) → A) :
    nameCost v w=∑ i : Fin n,nameCost (wordPack n s v i) (wordPack n s w i) := by
  rw [nameCost,←Equiv.sum_comp finProdFinEquiv (fun i => symbolCost (v i) (w i)),Fintype.sum_prod_type]
  rfl

lemma fullBlock_nested_head [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) :
    fullBlock s (M*J) (fun x => (wordPack (M*J) s).symm ((wordPack M J).symm (V x)))
      (finProdFinEquiv (I,j)).val=fun x => V x I j := by
  rw [fullBlock_packed]
  funext x a
  exact congrFun (wordPack_symm_coord M J (V x) I j) a

lemma fullBlock_nested_future [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (M J s L : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    suffixPrefix (M*J) L (finProdFinEquiv (I,j)).val (block_inner_future_lt M J L I j hj) ∘
      finiteName (fullBlock s (M*J) (fun x => (wordPack (M*J) s).symm ((wordPack M J).symm (V x))))
        ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)=
      fun x => vectorFuture J L j.val hj (V x I) := by
  rw [fullBlock_local_future]
  funext x
  exact vectorFuture_inside_block M J L I j hj (V x)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma map_word_coordinate [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (J : ℕ) (j : Fin J) :
    μ.map (fun x => word f p J x j)=μ.map p := by
  change μ.map (p ∘ f^[j.val])=μ.map p
  rw [←Measure.map_map hp (hf.measurable.iterate _),(hf.iterate j.val).map_eq]

lemma map_word_head_future [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (f : X → X) (hf : MeasurePreserving f μ μ)
    (p : X → A) (hp : Measurable p) (J L : ℕ) (j : Fin J) (hj : j.val+L<J) :
    μ.map (fun x => (word f p J x j,vectorFuture J L j.val hj (word f p J x)))=
      μ.map (fun x => (p x,word f p L (f x))) := by
  have hF : Measurable (fun x => (p x,word f p L (f x))) :=
    hp.prodMk ((word_measurable f hf.measurable p hp L).comp hf.measurable)
  have he : (fun x => (word f p J x j,vectorFuture J L j.val hj (word f p J x)))=
      (fun x => (p x,word f p L (f x))) ∘ f^[j.val] := by
    funext x
    apply Prod.ext
    · rfl
    · funext a
      simp only [vectorFuture,word,Function.comp_apply]
      rw [←Function.iterate_succ_apply' f j.val x,←Function.iterate_add_apply]
      congr 2
      omega
  rw [he,←Measure.map_map hF (hf.measurable.iterate _),(hf.iterate j.val).map_eq]

lemma block_law_head_test [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y)
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (J : ℕ) (V : Y → Fin J → A) (hV : Measurable V) {δ : ℝ}
    (hlaw : LawClose (μ.map (word f p J)) (ν.map V) δ) (j : Fin J) :
    LawClose (μ.map p) (ν.map (fun y => V y j)) δ := by
  have hh := hlaw.map (measurable_pi_apply j)
  rw [Measure.map_map (measurable_pi_apply j) (word_measurable f hf.measurable p hp J),
    Measure.map_map (measurable_pi_apply j) hV] at hh
  change LawClose (μ.map (fun x => word f p J x j)) (ν.map (fun y => V y j)) δ at hh
  rw [map_word_coordinate μ f hf p hp J j] at hh
  exact hh

lemma block_law_local_test [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) (ν : Measure Y)
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (J L : ℕ) (V : Y → Fin J → A) (hV : Measurable V) {δ : ℝ}
    (hlaw : LawClose (μ.map (word f p J)) (ν.map V) δ)
    (j : Fin J) (hj : j.val+L<J) :
    LawClose (μ.map (fun x => (p x,word f p L (f x))))
      (ν.map (fun y => (V y j,vectorFuture J L j.val hj (V y)))) δ := by
  let d : (Fin J → A) → A×(Fin L → A) := fun w => (w j,vectorFuture J L j.val hj w)
  have hd : Measurable d := measurable_of_countable d
  have hh := hlaw.map hd
  rw [Measure.map_map hd (word_measurable f hf.measurable p hp J),Measure.map_map hd hV] at hh
  change LawClose (μ.map (fun x => (word f p J x j,vectorFuture J L j.val hj (word f p J x)))) _ _ at hh
  rw [map_word_head_future μ f hf p hp J L j hj] at hh
  exact hh

lemma eventually_conditional_single_test [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℕ in atTop,StandardMapEntropy.Entropy.cond μ p
      (fun x => word f p L (f x))<rate μ f p+ε := by
  have hh := (entropy_increment_tendsto μ f hf p hp).eventually
    (gt_mem_nhds (show rate μ f p<rate μ f p+ε by linarith))
  simpa only [entropy_increment_eq μ f hf p hp] using hh

lemma remote_law_as_blocks [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L : ℕ) {ρ : ℝ}
    (hremote : LawClose (μ.map (fun x => (word f p (L*(k+g)) (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p (L*(k+g)) (f^[k+g] x))).prod (μ.map (word f p k))) ρ) :
    LawClose (μ.map (fun x => (word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x))).prod
        (μ.map (word f p k))) ρ := by
  have hh := lawClose_pair_factor_left μ (fun x => word f p (L*(k+g)) (f^[k+g] x))
    (word f p k) (wordPack L (k+g))
    ((word_measurable f hf.measurable p hp _).comp (hf.measurable.iterate _))
    (word_measurable f hf.measurable p hp k) (measurable_of_countable _) hremote
  simpa only [Function.comp_def,wordPack_apply] using hh
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {Y A B : Type*} [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma lawClose_one (μ ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    LawClose μ ν 1 := by
  intro D _
  apply abs_le.mpr
  constructor <;> linarith [measureReal_nonneg (μ:=μ) (s:=D),measureReal_nonneg (μ:=ν) (s:=D),
    measureReal_le_one (μ:=μ) (s:=D),measureReal_le_one (μ:=ν) (s:=D)]

noncomputable def insideCoarse [Nonempty B] (M J L : ℕ) (i : Fin (M*J))
    (w : Fin (M*J-i.val-1) → B) : Fin L → B :=
  if h : (finProdFinEquiv.symm i).2.val+L<J then
    suffixPrefix (M*J) L i.val (by
      have hh := block_inner_future_lt M J L (finProdFinEquiv.symm i).1
        (finProdFinEquiv.symm i).2 h
      simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using hh) w
  else fun _ => Classical.ofNonempty

noncomputable def extendedCoarse [Nonempty B] (M J L i : ℕ)
    (w : Fin (M*J-i-1) → B) : Fin L → B :=
  if hi : i<M*J then insideCoarse M J L ⟨i,hi⟩ w else fun _ => Classical.ofNonempty

lemma extendedCoarse_at [Nonempty B] (M J L : ℕ) (i : Fin (M*J)) :
    extendedCoarse (B:=B) M J L i.val=insideCoarse M J L i := by
  funext w
  simp only [extendedCoarse,i.isLt,dite_true]

lemma insideCoarse_good [Nonempty B] (M J L : ℕ) (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    insideCoarse (B:=B) M J L (finProdFinEquiv (I,j))=
      suffixPrefix (M*J) L (finProdFinEquiv (I,j)).val (block_inner_future_lt M J L I j hj) := by
  funext w
  simp only [insideCoarse,Equiv.symm_apply_apply,hj,dite_true]

lemma insideCoarse_bad [Nonempty B] (M J L : ℕ) (I : Fin M) (j : Fin J) (hj : ¬j.val+L<J) :
    insideCoarse (B:=B) M J L (finProdFinEquiv (I,j))=fun _ _ => Classical.ofNonempty := by
  funext w
  simp only [insideCoarse,Equiv.symm_apply_apply,hj,dite_false]

noncomputable def boundaryLoss (M J L : ℕ) (i : Fin (M*J)) : ℝ :=
  if (finProdFinEquiv.symm i).2.val+L<J then 0 else 1

lemma boundaryLoss_nonneg (M J L : ℕ) (i : Fin (M*J)) : 0≤boundaryLoss M J L i := by
  unfold boundaryLoss
  split_ifs <;> norm_num

lemma boundary_count_le (J L : ℕ) :
    (∑ j : Fin J,if j.val+L<J then (0 : ℝ) else 1)≤(L : ℝ) := by
  classical
  let S : Finset (Fin J) := Finset.univ.filter (fun j => ¬j.val+L<J)
  let F : S → Fin L := fun j => ⟨j.val.val+L-J,by
    have hj : ¬j.val.val+L<J := (Finset.mem_filter.mp j.property).2
    have hJ := j.val.isLt
    omega⟩
  have hF : Function.Injective F := by
    intro i j hij
    have hi : ¬i.val.val+L<J := (Finset.mem_filter.mp i.property).2
    have hj : ¬j.val.val+L<J := (Finset.mem_filter.mp j.property).2
    have he := congrArg Fin.val hij
    apply Subtype.ext
    apply Fin.ext
    dsimp [F] at he
    omega
  have hcard : S.card≤L := by
    simpa using Fintype.card_le_of_injective F hF
  have he : (∑ j : Fin J,if j.val+L<J then (0 : ℝ) else 1)=(S.card : ℝ) := by
    dsimp [S]
    rw [←Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp_all
  rw [he]
  exact_mod_cast hcard

lemma boundaryLoss_sum_le (M J L : ℕ) :
    (∑ i : Fin (M*J),boundaryLoss M J L i)≤(M*L : ℕ) := by
  rw [←Equiv.sum_comp finProdFinEquiv (boundaryLoss M J L),Fintype.sum_prod_type]
  simp only [boundaryLoss,Equiv.symm_apply_apply]
  calc
    _≤∑ _I : Fin M,(L : ℝ) := Finset.sum_le_sum (fun _ _ => boundary_count_le J L)
    _=_ := by simp
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

noncomputable def nestedOutput (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (y : Y) : Fin ((M*J)*s) → A :=
  (wordPack (M*J) s).symm ((wordPack M J).symm (V y))

lemma nestedOutput_measurable [StandardBorelSpace Y] [Nonempty A]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (hV : Measurable V) : Measurable (nestedOutput M J s V) :=
  (measurable_of_countable (fun v => (wordPack (M*J) s).symm ((wordPack M J).symm v))).comp hV

lemma nestedOutput_head [StandardBorelSpace Y] [Nonempty A]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) :
    fullBlock s (M*J) (nestedOutput M J s V) (finProdFinEquiv (I,j)).val=fun x => V x I j :=
  fullBlock_nested_head M J s V I j

lemma nestedOutput_future [StandardBorelSpace Y] [Nonempty A]
    (M J s L : ℕ) (V : Y → Fin M → Fin J → Fin s → A)
    (I : Fin M) (j : Fin J) (hj : j.val+L<J) :
    extendedCoarse (B:=Fin s → A) M J L (finProdFinEquiv (I,j)).val ∘
      finiteName (fullBlock s (M*J) (nestedOutput M J s V))
        ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)=
      fun x => vectorFuture J L j.val hj (V x I) := by
  rw [extendedCoarse_at,insideCoarse_good M J L I j hj]
  exact fullBlock_nested_future M J s L V I j hj

theorem block_recoding_word_transport [StandardBorelSpace Y] [Nonempty A]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [NullSingletonClass μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p)
    (k g L M J : ℕ) (V : Y → Fin M → Fin J → Fin (k+g) → A) (hV : Measurable V)
    {ρ τ δ H : ℝ} (hρ : 0≤ρ) (hτ : 0<τ) (hδ : 0≤δ) (hH : 0≤H)
    (hP : ∀ T : ℕ,LawClose
      (μ.map (fun x => (word f p T (f^[k+g] x),word f p k x)))
      ((μ.map (fun x => word f p T (f^[k+g] x))).prod (μ.map (word f p k))) ρ)
    (hlaw : ∀ I : Fin M,LawClose
      (μ.map (word (f^[k+g]) (word f p (k+g)) J)) (ν.map (fun y => V y I)) δ)
    (htest : ∀ (q : Y → Fin (k+g) → A) (r : Y → Fin L → Fin (k+g) → A),
      Measurable q → Measurable r →
      LawClose (μ.map (fun x => (word f p (k+g) x,
        word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x))))
        (ν.map (fun y => (q y,r y))) δ → StandardMapEntropy.Entropy.cond ν q r≤H) :
    ∃ R : MatrixCoupling (mass μ (word f p ((M*J)*(k+g))))
        (mass ν (nestedOutput M J (k+g) V)),
      R.cost nameCost≤(k : ℝ)*((M*J : ℕ)*(3*ρ+τ+7*δ)+2*(M*L : ℕ)+
        (((M*J : ℕ)*H+(M*L : ℕ)*Real.log (Fintype.card (Fin (k+g) → A)))-
          obs ν (nestedOutput M J (k+g) V))/τ)+(M*J*g : ℕ) := by
  classical
  let q := nestedOutput M J (k+g) V
  have hq : Measurable q := nestedOutput_measurable M J (k+g) V hV
  let c := extendedCoarse (B:=Fin (k+g) → A) M J L
  let ε : ℕ → ℝ := fun i => ρ+3*δ+if hi : i<M*J then boundaryLoss M J L ⟨i,hi⟩ else 0
  have he (i : Fin (M*J)) : ε i.val=ρ+3*δ+boundaryLoss M J L i := by
    simp only [ε,i.isLt,dite_true]
  let d : (Fin (k+g) → A) → Fin k → A := fun w a => w (a.castAdd g)
  have hd : Measurable d := measurable_of_countable d
  have hw := word_measurable f hf.measurable p hp (k+g)
  have hpref : d ∘ word f p (k+g)=word f p k := by funext x a; rfl
  have hpref' (x : X) : d (word f p (k+g) x)=word f p k x := congrFun hpref x
  have hhead (i : Fin (M*J)) : LawClose (μ.map (word f p k))
      (ν.map (d ∘ fullBlock (k+g) (M*J) q i.val)) δ := by
    obtain ⟨⟨I,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    have hh := block_law_head_test μ ν (f^[k+g]) (hf.iterate _) (word f p (k+g)) hw J
      (fun y => V y I) ((measurable_pi_apply I).comp hV) (hlaw I) j
    have hh' := hh.map hd
    have hvij : Measurable (fun y => V y I j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply I).comp hV)
    rw [Measure.map_map hd hw,Measure.map_map hd hvij,hpref] at hh'
    simpa only [q,nestedOutput_head] using hh'
  have hremote := remote_law_as_blocks μ f hf p hp k g L (hP (L*(k+g)))
  have hpair (I : Fin M) (j : Fin J) (hj : j.val+L<J) :=
    block_law_local_test μ ν (f^[k+g]) (hf.iterate _) (word f p (k+g)) hw J L
      (fun y => V y I) ((measurable_pi_apply I).comp hV) (hlaw I) j hj
  have hlocal (i : ℕ) (hi : i<M*J) : LawClose
      (ν.map (fun x => (c i (finiteName (fullBlock (k+g) (M*J) q) (i+1) (M*J-i-1) x),
        d (fullBlock (k+g) (M*J) q i x))))
      ((ν.map (c i ∘ finiteName (fullBlock (k+g) (M*J) q) (i+1) (M*J-i-1))).prod
        (ν.map (d ∘ fullBlock (k+g) (M*J) q i))) (ε i) := by
    let a : Fin (M*J) := ⟨i,hi⟩
    change LawClose _ _ (ε a.val)
    rw [he]
    obtain ⟨⟨I,j⟩,ha⟩ := finProdFinEquiv.surjective a
    have hiv : i=(finProdFinEquiv (I,j)).val := congrArg Fin.val ha.symm
    subst i
    by_cases hj : j.val+L<J
    · have hh := independence_joint_test μ ν (word f p (k+g))
        (fun x => word (f^[k+g]) (word f p (k+g)) L (f^[k+g] x))
        (fun y => V y I j) (fun y => vectorFuture J L j.val hj (V y I)) hw
        ((word_measurable (f^[k+g]) (hf.measurable.iterate _) (word f p (k+g)) hw L).comp
          (hf.measurable.iterate _))
        ((measurable_pi_apply j).comp ((measurable_pi_apply I).comp hV))
        ((measurable_of_countable (vectorFuture J L j.val hj)).comp ((measurable_pi_apply I).comp hV)) d (hpair I j hj)
        (by simpa only [hpref,hpref'] using hremote)
      have hb : boundaryLoss M J L a=0 := by rw [←ha]; simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_true]
      rw [hb,add_zero]
      change LawClose (ν.map (fun x => ((c _ ∘ _) x,d (fullBlock _ _ q _ x)))) _ _
      simpa only [c,q,nestedOutput_future M J (k+g) L V I j hj,nestedOutput_head]
        using hh
    · apply (lawClose_one _ _).mono
      have hb : boundaryLoss M J L a=1 := by rw [←ha]; simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_false]
      rw [hb]
      linarith
  have hcond (i : Fin (M*J)) : StandardMapEntropy.Entropy.cond ν
      (fullBlock (k+g) (M*J) q i.val)
      (c i.val ∘ finiteName (fullBlock (k+g) (M*J) q) (i.val+1) (M*J-i.val-1))≤
      H+boundaryLoss M J L i*Real.log (Fintype.card (Fin (k+g) → A)) := by
    obtain ⟨⟨I,j⟩,rfl⟩ := finProdFinEquiv.surjective i
    by_cases hj : j.val+L<J
    · simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_true,zero_mul,add_zero]
      change StandardMapEntropy.Entropy.cond ν _ (extendedCoarse M J L _ ∘ _)≤H
      rw [nestedOutput_future M J (k+g) L V I j hj,nestedOutput_head]
      exact htest _ _ ((measurable_pi_apply j).comp ((measurable_pi_apply I).comp hV))
        ((measurable_of_countable (vectorFuture J L j.val hj)).comp ((measurable_pi_apply I).comp hV)) (hpair I j hj)
    · simp only [boundaryLoss,Equiv.symm_apply_apply,hj,ite_false,one_mul]
      have hh := cond_le_obs ν (fullBlock (k+g) (M*J) q (finProdFinEquiv (I,j)).val)
        (c (finProdFinEquiv (I,j)).val ∘ finiteName (fullBlock (k+g) (M*J) q)
          ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1))
        (fullBlock_measurable _ _ q hq _)
        ((measurable_of_countable (c (finProdFinEquiv (I,j)).val)).comp
          (finiteName_measurable _ (fullBlock_measurable _ _ q hq)
            ((finProdFinEquiv (I,j)).val+1) (M*J-(finProdFinEquiv (I,j)).val-1)))
      have hb := obs_bound ν (fullBlock (k+g) (M*J) q (finProdFinEquiv (I,j)).val)
        (fullBlock_measurable _ _ q hq _)
      linarith
  obtain ⟨R,hR⟩ := nonstationary_conditional_word_transport μ ν f hf p hp k g (M*J) q hq
    (fun _ => Fin L → Fin (k+g) → A) c ε (fun _ => δ) hτ hP hhead hlocal
  refine ⟨R,hR.trans ?_⟩
  have hlog : 0≤Real.log (Fintype.card (Fin (k+g) → A)) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α:=Fin (k+g) → A))
  have hcs : (∑ i : Fin (M*J),StandardMapEntropy.Entropy.cond ν
      (fullBlock (k+g) (M*J) q i.val)
      (c i.val ∘ finiteName (fullBlock (k+g) (M*J) q) (i.val+1) (M*J-i.val-1)))≤
      (M*J : ℕ)*H+(M*L : ℕ)*Real.log (Fintype.card (Fin (k+g) → A)) := by
    calc
      _≤∑ i : Fin (M*J),(H+boundaryLoss M J L i*Real.log (Fintype.card (Fin (k+g) → A))) :=
        Finset.sum_le_sum (fun i _ => hcond i)
      _=(M*J : ℕ)*H+(∑ i : Fin (M*J),boundaryLoss M J L i)*Real.log (Fintype.card (Fin (k+g) → A)) := by
        rw [Finset.sum_add_distrib,←Finset.sum_mul]; simp
      _≤_ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (boundaryLoss_sum_le M J L) hlog)
  have hes : (∑ i : Fin (M*J),ε i.val)≤(M*J : ℕ)*(ρ+3*δ)+(M*L : ℕ) := by
    simp only [he,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hh := boundaryLoss_sum_le M J L
    nlinarith
  apply add_le_add _ (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  have hh := div_le_div_of_nonneg_right (sub_le_sub_right hcs (obs ν q)) hτ.le
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  dsimp only [q] at hh ⊢
  nlinarith
end HyperbolicCoding

end

end OAI
