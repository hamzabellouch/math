import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coupling.FiniteConditionalLawTests
import OAI.Dynamics.StandardMap.Coupling.FiniteVectorEntropy

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A B : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]

lemma observations_vector_cost [Nonempty B] (μ : Measure X) [IsProbabilityMeasure μ]
    (N : ℕ) (P : X → Fin N → A) (Q : X → Fin N → B) (hP : Measurable P) (hQ : Measurable Q)
    (d : A → B → ℝ) :
    (MatrixCoupling.observations μ P Q hP hQ).cost (fun v w => ∑ i,d (v i) (w i))=
      ∑ i : Fin N,(MatrixCoupling.observations μ (fun x => P x i) (fun x => Q x i)
        ((measurable_pi_apply i).comp hP) ((measurable_pi_apply i).comp hQ)).cost d := by
  simp only [MatrixCoupling.observations_cost]
  exact integral_finsetSum _ (fun i _ => integrable_finite_observation μ
    (fun x => (P x i,Q x i)) (((measurable_pi_apply i).comp hP).prodMk
      ((measurable_pi_apply i).comp hQ)) (fun ab => d ab.1 ab.2))

lemma recodingLaw_entropy_lower [Nonempty B] (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    {η : ℝ}
    (hin : ∀ i : Fin N,obs ν (fun y => Q y i)≤obs μ p+η)
    (hout : ∀ i : Fin N,obs μ r-η≤obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.2 i)) :
    obs ν Q+(N : ℝ)*(obs μ r-obs μ p-2*η)≤
      obs (recodingLaw μ p r hp hr ν N Q) Prod.snd := by
  have := recodingLaw_probability μ p r hp hr ν N Q hQ
  have hh := finiteChannelLaw_entropy N (mass ν Q) (mass_nonneg _ _)
    (by simpa using mass_sum ν Q hQ) (fun _ => recodingKernel μ p r hp hr)
    (fun _ => recodingKernel_nonneg μ p r hp hr) (fun _ => recodingKernel_sum μ p r hp hr)
  change obs ν Q+(∑ i : Fin N,(obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.2 i)-
    obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i)))≤_ at hh
  apply le_trans _ hh
  apply add_le_add (le_refl _)
  calc
    _=∑ _i : Fin N,(obs μ r-obs μ p-2*η) := by simp; ring
    _≤_ := by
      apply Finset.sum_le_sum
      intro i _
      have he : obs (recodingLaw μ p r hp hr ν N Q) (fun vw => vw.1 i)=obs ν (fun y => Q y i) := by
        unfold obs
        congr 1
        funext a
        exact recodingLaw_input_coordinate μ p r hp hr ν N Q hQ i a
      rw [he]
      linarith [hin i,hout i]

lemma recodingLaw_transport_cost [Nonempty B] (μ : Measure X) [IsProbabilityMeasure μ]
    (p : X → A) (r : X → B) (hp : Measurable p) (hr : Measurable r)
    (ν : Measure Y) [IsProbabilityMeasure ν] (N : ℕ) (Q : Y → Fin N → A) (hQ : Measurable Q)
    {δ M : ℝ} (hM : 0≤M) (hlaw : ∀ i : Fin N,LawClose (μ.map p) (ν.map (fun y => Q y i)) δ)
    (d : A → B → ℝ) (hd : ∀ a b,|d a b|≤M) :
    ∃ R : MatrixCoupling (mass ν Q) (mass (recodingLaw μ p r hp hr ν N Q) Prod.snd),
      R.cost (fun v w => ∑ i,d (v i) (w i))≤
        (N : ℝ)*((MatrixCoupling.observations μ p r hp hr).cost d+2*δ*M) := by
  let ξ := recodingLaw μ p r hp hr ν N Q
  have : IsProbabilityMeasure ξ := recodingLaw_probability μ p r hp hr ν N Q hQ
  let S := MatrixCoupling.observations ξ Prod.fst Prod.snd measurable_fst measurable_snd
  let R : MatrixCoupling (mass ν Q) (mass ξ Prod.snd) := {
    weight := S.weight
    nonneg := S.nonneg
    row := fun v => (S.row v).trans (recodingLaw_input_mass μ p r hp hr ν N Q v)
    col := S.col }
  refine ⟨R,?_⟩
  change S.cost (fun v w => ∑ i,d (v i) (w i))≤_
  rw [observations_vector_cost]
  calc
    _≤∑ _i : Fin N,((MatrixCoupling.observations μ p r hp hr).cost d+2*δ*M) := by
      apply Finset.sum_le_sum
      intro i _
      apply channel_cost_stability μ ξ p r (fun vw => vw.1 i) (fun vw => vw.2 i) hp hr
        ((measurable_pi_apply i).comp measurable_fst) ((measurable_pi_apply i).comp measurable_snd)
        (recodingKernel μ p r hp hr) (recodingKernel_nonneg μ p r hp hr)
        (recodingKernel_sum μ p r hp hr) (recodingKernel_joint μ p r hp hr)
        (recodingLaw_joint_coordinate μ p r hp hr ν N Q hQ i) hM _ d hd
      change LawClose (μ.map p) ((recodingLaw μ p r hp hr ν N Q).map (fun vw => vw.1 i)) δ
      rw [recodingLaw_input_law μ p r hp hr ν N Q hQ i]
      exact hlaw i
    _=_ := by simp; ring
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*}

noncomputable def nestedPack (M J s : ℕ) : (Fin ((M*J)*s) → A) ≃ (Fin M → Fin J → Fin s → A) :=
  (wordPack (M*J) s).trans (wordPack M J)

lemma nestedPack_symm [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A) :
    (nestedPack M J s).symm ∘ V=nestedOutput M J s V := rfl

lemma nestedPack_word [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (f : X → X) (p : X → A) (M J s : ℕ) (x : X) :
    nestedPack M J s (word f p ((M*J)*s) x)=
      word (f^[J*s]) (word (f^[s]) (word f p s) J) M x := by
  funext I j a
  simp only [nestedPack,Equiv.trans_apply,wordPack_apply_coord,word]
  change p (f^[a.val+s*(j.val+J*I.val)] x)=_
  simp only [←Function.iterate_mul,←Function.iterate_add_apply]
  congr 2
  ring

lemma obs_nestedPack_word [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (p : X → A) (M J s : ℕ) :
    obs μ (word (f^[J*s]) (word (f^[s]) (word f p s) J) M)=
      obs μ (word f p ((M*J)*s)) := by
  simpa only [Function.comp_def,nestedPack_word] using
    obs_equiv μ (word f p ((M*J)*s)) (nestedPack M J s)

lemma obs_nestedOutput [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (M J s : ℕ) (V : Y → Fin M → Fin J → Fin s → A) :
    obs ν (nestedOutput M J s V)=obs ν V :=
  obs_equiv ν V (nestedPack M J s).symm

noncomputable def fineWordCost (J s : ℕ) (v w : Fin J → Fin s → A) : ℝ :=
  nameCost ((wordPack J s).symm v) ((wordPack J s).symm w)

lemma fineWordCost_sum [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (J s : ℕ) (v w : Fin J → Fin s → A) :
    fineWordCost J s v w=∑ j,nameCost (v j) (w j) := by
  simp only [fineWordCost,nameCost_wordPack,Equiv.apply_symm_apply]

lemma nameCost_nestedPack [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (M J s : ℕ) (v w : Fin ((M*J)*s) → A) :
    nameCost v w=∑ I : Fin M,fineWordCost J s (nestedPack M J s v I) (nestedPack M J s w I) := by
  rw [nameCost_wordPack,←Equiv.sum_comp finProdFinEquiv (fun i : Fin (M*J) =>
    nameCost (wordPack (M*J) s v i) (wordPack (M*J) s w i)),Fintype.sum_prod_type]
  simp only [fineWordCost_sum,nestedPack,Equiv.trans_apply,wordPack_apply_coord]

lemma observations_word_cost [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p r : X → A) (hp : Measurable p) (hr : Measurable r)
    (n : ℕ) :
    (MatrixCoupling.observations μ (word f p n) (word f r n)
      (word_measurable f hf.measurable p hp n) (word_measurable f hf.measurable r hr n)).cost nameCost=
      (n : ℝ)*μ.real {x | p x≠r x} := by
  rw [show nameCost=(fun v w : Fin n → A => ∑ i,symbolCost (v i) (w i)) from rfl,
    observations_vector_cost]
  have hi (i : Fin n) : (MatrixCoupling.observations μ (fun x => word f p n x i)
      (fun x => word f r n x i) ((measurable_pi_apply i).comp (word_measurable f hf.measurable p hp n))
      ((measurable_pi_apply i).comp (word_measurable f hf.measurable r hr n))).cost symbolCost=
      μ.real {x | p x≠r x} := by
    rw [MatrixCoupling.observations_cost]
    rw [finite_symbolCost_integral μ (fun x => word f p n x i) (fun x => word f r n x i)
      ((measurable_pi_apply i).comp (word_measurable f hf.measurable p hp n))
      ((measurable_pi_apply i).comp (word_measurable f hf.measurable r hr n))]
    change μ.real ((f^[i.val]) ⁻¹' {x | p x≠r x})=μ.real {x | p x≠r x}
    exact congrArg ENNReal.toReal ((hf.iterate i.val).measure_preimage
      (measurableSet_eq_fun hp hr).compl.nullMeasurableSet)
  simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma observations_fineWordCost [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p r : X → A) (hp : Measurable p) (hr : Measurable r)
    (J s : ℕ) :
    (MatrixCoupling.observations μ (word (f^[s]) (word f p s) J) (word (f^[s]) (word f r s) J)
      (word_measurable _ (hf.measurable.iterate _) _ (word_measurable f hf.measurable p hp s) J)
      (word_measurable _ (hf.measurable.iterate _) _ (word_measurable f hf.measurable r hr s) J)).cost
      (fineWordCost J s)=(J*s : ℕ)*μ.real {x | p x≠r x} := by
  rw [MatrixCoupling.observations_cost]
  have he (x : X) : fineWordCost J s (word (f^[s]) (word f p s) J x)
      (word (f^[s]) (word f r s) J x)=nameCost (word f p (J*s) x) (word f r (J*s) x) := by
    simp only [fineWordCost,←wordPack_apply,Equiv.symm_apply_apply]
  simp_rw [he]
  rw [←MatrixCoupling.observations_cost μ _ _
    (word_measurable f hf.measurable p hp _) (word_measurable f hf.measurable r hr _)]
  exact observations_word_cost μ f hf p r hp hr (J*s)

lemma fineWordCost_abs_le [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (J s : ℕ) (v w : Fin J → Fin s → A) :
    |fineWordCost J s v w|≤(J*s : ℕ) := by
  unfold fineWordCost
  rw [abs_of_nonneg (nameCost_nonneg _ _)]
  exact nameCost_le_card _ _

lemma obs_word_rate_lower [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → X) (hf : MeasurePreserving f μ μ) (p : X → A) (hp : Measurable p) (n : ℕ) :
    (n : ℝ)*rate μ f p≤obs μ (word f p n) := by
  by_cases hn : n=0
  · subst n; simpa using obs_nonneg μ (word f p 0) (word_measurable f hf.measurable p hp 0)
  · have hh := (le_div_iff₀ (show (0 : ℝ)<n by exact_mod_cast Nat.pos_of_ne_zero hn)).mp
      (rate_le_div μ f hf p hp hn)
    nlinarith
end HyperbolicCoding

end
section
namespace HyperbolicCoding
lemma recoding_entropy_scalar {n j s a δ hp hr P S Q O : ℝ}
    (hn : 0≤n) (hδ : s*δ≤a^2)
    (hQ : n*j*s*(hp-δ)≤Q) (hP : P≤j*s*hp+j*a^2) (hS : j*s*hr≤S)
    (hO : Q+n*(S-P-2)≤O) (hj : 0≤j) :
    n*j*s*hr-2*(n*j)*a^2-2*n≤O := by
  have h₁ := mul_le_mul_of_nonneg_left hP hn
  have h₂ := mul_le_mul_of_nonneg_left hS hn
  have h₃ := mul_le_mul_of_nonneg_left hδ (mul_nonneg hn hj)
  nlinarith only [hQ,h₁,h₂,h₃,hO]

lemma recoding_deficit_scalar {n j s L C a hr O : ℝ}
    (hn : 0≤n) (hB : 2+L*C≤j*a^2)
    (hO : n*j*s*hr-2*(n*j)*a^2-2*n≤O) :
    n*j*(s*hr+a^2)+n*L*C-O≤4*(n*j)*a^2 := by
  have h₁ := mul_le_mul_of_nonneg_left hB hn
  nlinarith only [h₁,hO]

lemma recoding_wb_cost_scalar {c n j k g L a δ D : ℝ}
    (hn : 0≤n) (hj : 0≤j) (hk : 0≤k) (hg : 0≤g) (ha : 0<a)
    (hδ : δ≤a) (hB : 2*L≤j*a) (hgap : g≤a*k)
    (hD : D≤4*(n*j)*a^2)
    (hc : c≤k*(n*j*(3*a+a+7*δ)+2*(n*L)+D/a)+n*j*g) :
    c≤17*a*(n*j*(k+g)) := by
  have hdiv : D/a≤4*(n*j)*a := (div_le_iff₀ ha).mpr (by nlinarith only [hD])
  have h₁ := mul_le_mul_of_nonneg_left hδ (mul_nonneg hn hj)
  have h₂ := mul_le_mul_of_nonneg_left hB hn
  have h₃ := mul_le_mul_of_nonneg_left hgap (mul_nonneg hn hj)
  have hinside : n*j*(3*a+a+7*δ)+2*(n*L)+D/a≤16*a*(n*j) := by
    nlinarith only [hdiv,h₁,h₂]
  have h₄ := mul_le_mul_of_nonneg_left hinside hk
  have h₅ := mul_nonneg (mul_nonneg (mul_nonneg hn hj) hg) ha.le
  nlinarith only [hc,h₃,h₄,h₅]
end HyperbolicCoding
end
section
namespace HyperbolicCoding
open MeasureTheory Set StandardMapEntropy.Entropy
open scoped BigOperators ENNReal
variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

lemma nestedOutput_word [StandardBorelSpace X] (f : X → X) (p : X → A) (n J s : ℕ) :
    nestedOutput n J s (word (f^[J*s]) (word (f^[s]) (word f p s) J) n)=
      word f p ((n*J)*s) := by
  funext x
  change (nestedPack n J s).symm (word (f^[J*s]) (word (f^[s]) (word f p s) J) n x)=_
  rw [←nestedPack_word,Equiv.symm_apply_apply]

lemma recoding_nested_entropy [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (n J s : ℕ)
    (P S : X → Fin J → Fin s → A) (hP : Measurable P) (hS : Measurable S)
    (Q : Y → Fin n → Fin J → Fin s → A) (hQ : Measurable Q)
    {a δ hp hr : ℝ} (hδ : (s : ℝ)*δ≤a^2)
    (hQlo : ((n*J)*s : ℕ)*(hp-δ)≤obs ν Q)
    (hPhi : obs μ P≤(J*s : ℕ)*hp+(J : ℝ)*a^2)
    (hSlo : (J*s : ℕ)*hr≤obs μ S)
    (hin : ∀ i : Fin n,obs ν (fun y => Q y i)≤obs μ P+1)
    (hout : ∀ i : Fin n,obs μ S-1≤obs (recodingLaw μ P S hP hS ν n Q) (fun vw => vw.2 i)) :
    ((n*J)*s : ℕ)*hr-2*(n*J : ℕ)*a^2-2*(n : ℝ)≤
      obs (recodingLaw μ P S hP hS ν n Q) (nestedOutput n J s Prod.snd) := by
  let : StandardBorelSpace (Fin n → Fin J → Fin s → A) := inferInstance
  have := recodingLaw_probability μ P S hP hS ν n Q hQ
  rw [obs_nestedOutput]
  have hh := recodingLaw_entropy_lower μ P S hP hS ν n Q hQ hin hout
  push_cast at hQlo hPhi hSlo ⊢
  exact recoding_entropy_scalar (Nat.cast_nonneg n) hδ hQlo hPhi hSlo (by simpa only [mul_one] using hh)
    (Nat.cast_nonneg J)

lemma nested_reindex_transport [StandardBorelSpace Y]
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z]
    (ν : Measure Y) [IsProbabilityMeasure ν] (ξ : Measure Z) [IsProbabilityMeasure ξ]
    (n J s : ℕ) (Q : Y → Fin n → Fin J → Fin s → A) (V : Z → Fin n → Fin J → Fin s → A)
    (R : MatrixCoupling (mass ν Q) (mass ξ V)) :
    ∃ R' : MatrixCoupling (mass ν (nestedOutput n J s Q)) (mass ξ (nestedOutput n J s V)),
      R'.cost nameCost=R.cost (fun v w => ∑ i,fineWordCost J s (v i) (w i)) := by
  let E := nestedPack (A:=A) n J s
  let U := R.reindex E E
  have hrow (w : Fin ((n*J)*s) → A) : mass ν Q (E w)=mass ν (nestedOutput n J s Q) w :=
    (mass_equiv_inverse_finite ν Q E.symm w).symm
  have hcol (w : Fin ((n*J)*s) → A) : mass ξ V (E w)=mass ξ (nestedOutput n J s V) w :=
    (mass_equiv_inverse_finite ξ V E.symm w).symm
  let R' : MatrixCoupling (mass ν (nestedOutput n J s Q)) (mass ξ (nestedOutput n J s V)) := {
    weight := U.weight
    nonneg := U.nonneg
    row := fun w => (U.row w).trans (hrow w)
    col := fun w => (U.col w).trans (hcol w) }
  refine ⟨R',?_⟩
  change U.cost nameCost=_
  have hc : (nameCost : (Fin ((n*J)*s) → A) → (Fin ((n*J)*s) → A) → ℝ)=
      fun v w => ∑ i,fineWordCost J s (E v i) (E w i) :=
    funext (fun v => funext (fun w => nameCost_nestedPack n J s v w))
  rw [hc]
  exact MatrixCoupling.reindex_cost R E E (fun v w => ∑ i,fineWordCost J s (v i) (w i))

lemma recoding_nested_transport [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (n J s : ℕ)
    (P S : X → Fin J → Fin s → A) (hP : Measurable P) (hS : Measurable S)
    (Q : Y → Fin n → Fin J → Fin s → A) (hQ : Measurable Q)
    {δ : ℝ} (hb : ∀ i : Fin n,LawClose (μ.map P) (ν.map (fun y => Q y i)) δ) :
    ∃ R : MatrixCoupling (mass ν (nestedOutput n J s Q))
      (mass (recodingLaw μ P S hP hS ν n Q) (nestedOutput n J s Prod.snd)),
      R.cost nameCost≤(n : ℝ)*((MatrixCoupling.observations μ P S hP hS).cost
        (fineWordCost J s)+2*δ*(J*s : ℕ)) := by
  let : StandardBorelSpace (Fin n → Fin J → Fin s → A) := inferInstance
  let ξ := recodingLaw μ P S hP hS ν n Q
  have : IsProbabilityMeasure ξ := recodingLaw_probability μ P S hP hS ν n Q hQ
  obtain ⟨R,hR⟩ := recodingLaw_transport_cost μ P S hP hS ν n Q hQ
    (Nat.cast_nonneg (J*s)) hb (fineWordCost J s) (fineWordCost_abs_le J s)
  obtain ⟨R',hR'⟩ := nested_reindex_transport ν ξ n J s Q Prod.snd R
  exact ⟨R',hR'.trans_le hR⟩

lemma block_recoding_small_cost [StandardBorelSpace X] [StandardBorelSpace Y]
    (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (r : X → A) (hr : Measurable r)
    (k g L n J : ℕ) (V : Y → Fin n → Fin J → Fin (k+g) → A) (hV : Measurable V)
    {a δ : ℝ} (ha : 0<a) (hδ₀ : 0≤δ) (hδ : δ≤a)
    (hgap : (g : ℝ)≤a*k) (hB₁ : 2+(L : ℝ)*Real.log (Fintype.card (Fin (k+g) → A))≤(J : ℝ)*a^2)
    (hB₂ : 2*(L : ℝ)≤(J : ℝ)*a)
    (hremote : ∀ T : ℕ,LawClose
      (μ.map (fun x => (word e r T (e^[k+g] x),word e r k x)))
      ((μ.map (fun x => word e r T (e^[k+g] x))).prod (μ.map (word e r k))) a)
    (hlaw : ∀ I : Fin n,LawClose
      (μ.map (word (e^[k+g]) (word e r (k+g)) J)) (ν.map (fun y => V y I)) δ)
    (htest : ∀ (q : Y → Fin (k+g) → A) (v : Y → Fin L → Fin (k+g) → A),
      Measurable q → Measurable v →
      LawClose (μ.map (fun x => (word e r (k+g) x,
        word (e^[k+g]) (word e r (k+g)) L (e^[k+g] x))))
        (ν.map (fun y => (q y,v y))) δ → StandardMapEntropy.Entropy.cond ν q v≤
          (k+g : ℕ)*rate μ e r+a^2)
    (hentropy : ((n*J)*(k+g) : ℕ)*rate μ e r-2*(n*J : ℕ)*a^2-2*(n : ℝ)≤
      obs ν (nestedOutput n J (k+g) V)) :
    ∃ R : MatrixCoupling (mass μ (word e r ((n*J)*(k+g))))
        (mass ν (nestedOutput n J (k+g) V)),
      R.cost nameCost≤17*a*((n*J)*(k+g) : ℕ) := by
  have hH : 0≤(k+g : ℕ)*rate μ e r+a^2 := by
    have := rate_nonneg μ e he r hr
    positivity
  obtain ⟨R,hR⟩ := block_recoding_word_transport μ ν e he r hr k g L n J V hV
    ha.le ha hδ₀ hH hremote hlaw htest
  refine ⟨R,?_⟩
  have hD : (n*J : ℕ)*((k+g : ℕ)*rate μ e r+a^2)+(n*L : ℕ)*Real.log (Fintype.card (Fin (k+g) → A))-
      obs ν (nestedOutput n J (k+g) V)≤4*(n*J : ℕ)*a^2 := by
    push_cast at hentropy ⊢
    exact recoding_deficit_scalar (Nat.cast_nonneg n) hB₁ hentropy
  push_cast at hR hD ⊢
  exact recoding_wb_cost_scalar (Nat.cast_nonneg n) (Nat.cast_nonneg J) (Nat.cast_nonneg k)
    (Nat.cast_nonneg g) ha hδ hB₂ hgap hD hR
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped ENNReal BigOperators
variable {X A B : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    [MeasurableSpace B]

lemma WeakBernoulliProcess.factor [Fintype B] [MeasurableSingletonClass B]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (p : X → A) (hp : Measurable p) (hwb : WeakBernoulliProcess μ e p)
    (d : A → B) : WeakBernoulliProcess μ e (d ∘ p) := by
  let D : (ℕ → A) → (ℕ → B) := fun w i => d (w i)
  have hD : Measurable D := Measurable.of_eval
    (fun i => (measurable_of_countable d).comp (measurable_pi_apply i))
  intro ε hε
  filter_upwards [hwb ε hε] with n hn
  have h := hn.map (hD.prodMap hD)
  have hrem := measurable_remotePair e.measurable e.symm.measurable hp n
  have hlu := measurable_tailName e.symm.measurable hp 0
  have hru := measurable_tailName e.measurable hp 0
  rw [Measure.map_map (hD.prodMap hD) hrem] at h
  unfold remoteProductLaw at h
  rw [←Measure.map_prod_map _ _ hD hD,Measure.map_map hD hlu,Measure.map_map hD hru] at h
  exact h

theorem separating_wb_approximation [StandardBorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (e : X ≃ᵐ X)
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M))
    [Nonempty A] (p : X → A) (hp : Measurable p) {ε : ℝ} (hε : 0<ε) :
    ∃ q : X → A,Measurable q ∧ WeakBernoulliProcess μ e q ∧ μ.real {x | q x≠p x}<ε := by
  obtain ⟨M,D,hD⟩ := joinedBinary_approximates μ α hα hsep p hp hε
  exact ⟨D ∘ joinedBinary α M,(measurable_of_countable D).comp (measurable_joinedBinary hα M),
    WeakBernoulliProcess.factor μ e (joinedBinary α M) (measurable_joinedBinary hα M) (hwb M) D,hD⟩
end HyperbolicCoding

end
section
universe u v w
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X : Type u} {Y : Type v} {A : Type w}
    [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
    [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]

lemma finite_observation_entropy_test_uniform [StandardBorelSpace X] [Nonempty A]
    (μ : Measure X) (p : X → A) (hp : Measurable p)
    {ε : ℝ} (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ (Z : Type v) [MeasurableSpace Z] (ν : Measure Z) (q : Z → A),
      Measurable q → LawClose (μ.map p) (ν.map q) δ → |obs μ p-obs ν q|<ε := by
  obtain ⟨δ,hδ,ht⟩ := finite_entropy_continuity (μ.map p) hε
  refine ⟨δ,hδ,?_⟩
  intro Z mZ ν q hq hlaw
  have hh := ht (ν.map q) hlaw
  rwa [←obs_eq_entropy_map μ p hp,←obs_eq_entropy_map ν q hq] at hh

theorem weakBernoulli_limit_finite_determination [StandardBorelSpace X] [Nonempty A]
    (μ : Measure X) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (happrox : ∀ ε : ℝ,0<ε → ∃ r : X → A,Measurable r ∧ WeakBernoulliProcess μ e r ∧
      μ.real {x | p x≠r x}<ε) {η : ℝ} (hη : 0<η) :
    ∃ m s₀ : ℕ,0<s₀ ∧ ∃ δ : ℝ,0<δ ∧
      ∀ (ν : Measure Y) (_ : IsProbabilityMeasure ν) (T : Y → Y)
        (_hT : MeasurePreserving T ν ν) (q : Y → A),Measurable q →
        LawClose (μ.map (word e p m)) (ν.map (word T q m)) δ →
        rate μ e p-δ≤rate ν T q →
        ∀ n : ℕ,∃ R : MatrixCoupling (mass μ (word e p (n*s₀))) (mass ν (word T q (n*s₀))),
          R.cost nameCost≤η*(n*s₀ : ℕ) := by
  let a := η/100
  have ha : 0<a := div_pos hη (by norm_num)
  have ha2 : 0<a^2 := sq_pos_of_pos ha
  obtain ⟨r,hr,hwb,hpaint⟩ := happrox a ha
  obtain ⟨g,hg⟩ := weakBernoulli_forward_blocks μ e he r hr hwb ha
  obtain ⟨k,hk⟩ := exists_nat_gt ((g : ℝ)/a+1)
  have hkpos : 0<k := by
    have hh : 0≤(g : ℝ)/a := div_nonneg (Nat.cast_nonneg _) ha.le
    have : (0 : ℝ)<k := by linarith
    exact_mod_cast this
  have hgap : (g : ℝ)≤a*(k : ℝ) := by
    have hh := (div_lt_iff₀ ha).mp (show (g : ℝ)/a<(k : ℝ) by linarith)
    nlinarith
  let s := k+g
  have hs : 0<s := by dsimp [s]; omega
  have hsR : (0 : ℝ)<s := by exact_mod_cast hs
  let pr := word e r s
  let pp := word e p s
  have hpr : Measurable pr := word_measurable e he.measurable r hr s
  have hpp : Measurable pp := word_measurable e he.measurable p hp s
  obtain ⟨L,hL⟩ := (eventually_conditional_single_test μ (e^[s]) (he.iterate _) pr hpr
    (show 0<a^2/2 by positivity)).exists
  rw [rate_power_word μ e he r hr s hs] at hL
  have hfuture : Measurable (fun x => word (e^[s]) pr L (e^[s] x)) :=
    (word_measurable _ (he.measurable.iterate _) pr hpr L).comp (he.measurable.iterate _)
  obtain ⟨δc,hδc,hct⟩ := conditional_entropy_law_test_uniform.{w} μ pr
    (fun x => word (e^[s]) pr L (e^[s] x)) hpr hfuture (show 0<a^2/2 by positivity)
  let C := Real.log (Fintype.card (Fin s → A))
  have hC : 0≤C := Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α:=Fin s → A))
  have hconv := (rate_tendsto μ (e^[s]) (he.iterate _) pp hpp).eventually
    (gt_mem_nhds (show rate μ (e^[s]) pp<rate μ (e^[s]) pp+a^2 by linarith))
  rw [rate_power_word μ e he p hp s hs] at hconv
  obtain ⟨J₀,hJ₀⟩ := exists_nat_gt (max ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)+1)
  obtain ⟨J,hJbound,hJconv⟩ := (hconv.and (eventually_ge_atTop J₀)).exists

  have hJge : J₀≤J := hJconv
  have hJent : obs μ (word (e^[s]) pp J)/(J : ℝ)<(s : ℝ)*rate μ e p+a^2 := hJbound
  have hJpos : 0<J := by
    have hb : 0≤(2+(L : ℝ)*C)/a^2 := div_nonneg (by positivity) ha2.le
    have hJr : (0 : ℝ)<J₀ := by linarith [le_max_left ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)]
    have : 0<J₀ := by exact_mod_cast hJr
    omega
  have hJR : (0 : ℝ)<J := by exact_mod_cast hJpos
  have hboundary₁ : 2+(L : ℝ)*C≤(J : ℝ)*a^2 := by
    have h₀ : (2+(L : ℝ)*C)/a^2<(J : ℝ) := by
      have hnat : (J₀ : ℝ)≤J := by exact_mod_cast hJge
      linarith [le_max_left ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)]
    exact ((div_lt_iff₀ ha2).mp h₀).le
  have hboundary₂ : 2*(L : ℝ)≤(J : ℝ)*a := by
    have h₀ : 2*(L : ℝ)/a<(J : ℝ) := by
      have hnat : (J₀ : ℝ)≤J := by exact_mod_cast hJge
      linarith [le_max_right ((2+(L : ℝ)*C)/a^2) (2*(L : ℝ)/a)]
    exact ((div_lt_iff₀ ha).mp h₀).le
  let P := word (e^[s]) pp J
  let S := word (e^[s]) pr J
  have hP : Measurable P := word_measurable _ (he.measurable.iterate _) pp hpp J
  have hS : Measurable S := word_measurable _ (he.measurable.iterate _) pr hpr J
  obtain ⟨δp,hδp,hpt⟩ := finite_observation_entropy_test_uniform.{u,v} μ P hP (show (0 : ℝ)<1 by norm_num)
  obtain ⟨δr,hδr,hrt⟩ := finite_observation_entropy_test_uniform.{u,w} μ S hS (show (0 : ℝ)<1 by norm_num)
  let δ := min (a/2) (min (a^2/s) (min (δc/2) (min δp (δr/2))))
  have hδ : 0<δ := lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
    (lt_min hδp (by positivity))))
  have hd₁ : 2*δ≤a := by have := min_le_left (a/2) (min (a^2/s) (min (δc/2) (min δp (δr/2)))); dsimp [δ]; linarith
  have hd₂ : (s : ℝ)*δ≤a^2 := by
    have hh : δ≤a^2/(s : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ hsR).mp hh
    nlinarith
  have hd₃ : 2*δ≤δc := by
    have hh : δ≤δc/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hd₄ : δ≤δp := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd₅ : 2*δ≤δr := by
    have hh : δ≤δr/2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  refine ⟨J*s,J*s,Nat.mul_pos hJpos hs,δ,hδ,?_⟩
  intro ν hν T hT q hq hclose hrate n
  rw [←Nat.mul_assoc]
  let := hν
  let Q₀ := word (T^[s]) (word T q s) J
  let Q := word (T^[J*s]) Q₀ n
  have hQ₀ : Measurable Q₀ := word_measurable _ (hT.measurable.iterate _) _ (word_measurable T hT.measurable q hq s) J
  have hQ : Measurable Q := word_measurable _ (hT.measurable.iterate _) Q₀ hQ₀ n
  have hb₀ : LawClose (μ.map P) (ν.map Q₀) δ := by
    have hh := hclose.map (measurable_of_countable (wordPack J s))
    rw [Measure.map_map (measurable_of_countable (wordPack J s)) (word_measurable e he.measurable p hp _),
      Measure.map_map (measurable_of_countable (wordPack J s)) (word_measurable T hT.measurable q hq _)] at hh
    simpa only [Function.comp_def,wordPack_apply] using hh
  have hb (i : Fin n) : LawClose (μ.map P) (ν.map (fun y => Q y i)) δ := by
    rw [map_word_coordinate ν (T^[J*s]) (hT.iterate _) Q₀ hQ₀ n i]
    exact hb₀
  let : StandardBorelSpace (Fin n → Fin J → Fin s → A) := inferInstance
  let ξ := recodingLaw μ P S hP hS ν n Q
  have : IsProbabilityMeasure ξ := recodingLaw_probability μ P S hP hS ν n Q hQ
  have houtlaw (i : Fin n) : LawClose (μ.map S) (ξ.map (fun vw => vw.2 i)) (2*δ) :=
    recodingLaw_output_lawClose μ P S hP hS ν n Q hQ i (hb i)
  have hin (i : Fin n) : obs ν (fun y => Q y i)≤obs μ P+1 := by
    have hh := hpt Y ν (fun y => Q y i) ((measurable_pi_apply i).comp hQ) ((hb i).mono hd₄)
    linarith [(abs_lt.mp hh).1]
  have hout (i : Fin n) : obs μ S-1≤obs ξ (fun vw => vw.2 i) := by
    have hh := hrt _ ξ (fun vw => vw.2 i) ((measurable_pi_apply i).comp measurable_snd)
      ((houtlaw i).mono hd₅)
    linarith [(abs_lt.mp hh).2]
  have hentropy := recodingLaw_entropy_lower μ P S hP hS ν n Q hQ hin hout
  have hquadlo : ((n*J)*s : ℕ)*rate ν T q≤obs ν Q := by
    rw [obs_nestedPack_word]
    exact obs_word_rate_lower ν T hT q hq _
  have hSlo : (J*s : ℕ)*rate μ e r≤obs μ S := by
    rw [obs_word_pack]
    exact obs_word_rate_lower μ e he r hr _
  have hPhi : obs μ P≤(J*s : ℕ)*rate μ e p+(J : ℝ)*a^2 := by
    have hh := (div_lt_iff₀ hJR).mp hJent
    dsimp only [P]
    push_cast
    nlinarith
  have hQlo : ((n*J)*s : ℕ)*(rate μ e p-δ)≤obs ν Q :=
    (mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg ((n*J)*s))).trans hquadlo
  have hwholeEntropy := recoding_nested_entropy μ ν n J s P S hP hS Q hQ hd₂ hQlo hPhi hSlo hin hout
  obtain ⟨R₁,hR₁budget⟩ := block_recoding_small_cost μ ξ e he r hr k g L n J Prod.snd measurable_snd
    ha (show 0≤2*δ by positivity) hd₁ hgap hboundary₁ hboundary₂ (hg k) houtlaw (by
      intro u v hu hv hlaw
      have hh := hct _ ξ u v hu hv (hlaw.mono hd₃)
      have hh' := (abs_lt.mp hh).1
      dsimp only [pr,s] at hL hh' ⊢
      linarith only [hh',hL]) hwholeEntropy
  have htransport := recoding_nested_transport μ ν n J s P S hP hS Q hQ hb
  have hQflat : nestedOutput n J s Q=word T q ((n*J)*s) := nestedOutput_word T q n J s
  rw [hQflat] at htransport
  obtain ⟨R₂,hR₂⟩ := htransport
  rw [observations_fineWordCost μ e he p r hp hr J s] at hR₂
  have hR₂budget : R₂.cost nameCost≤2*a*((n*J)*s : ℕ) := by
    have hs' : μ.real {x | p x≠r x}+2*δ≤2*a := by linarith only [hpaint,hd₁]
    have hh := mul_le_mul_of_nonneg_left hs' (Nat.cast_nonneg ((n*J)*s))
    apply hR₂.trans
    push_cast at hh ⊢
    nlinarith only [hh]
  let R₀ := MatrixCoupling.observations μ (word e p ((n*J)*s)) (word e r ((n*J)*s))
    (word_measurable e he.measurable p hp _) (word_measurable e he.measurable r hr _)
  have hR₀ : R₀.cost nameCost≤a*((n*J)*s : ℕ) := by
    change (MatrixCoupling.observations μ _ _ _ _).cost nameCost≤_
    rw [observations_word_cost μ e he p r hp hr]
    have hh := mul_le_mul_of_nonneg_left hpaint.le (Nat.cast_nonneg ((n*J)*s))
    nlinarith only [hh]
  let R := (R₀.comp R₁).comp R₂.symm
  have hR : R.cost nameCost≤η*((n*J)*s : ℕ) := by
    have h₁ := MatrixCoupling.comp_cost_le R₀ R₁ nameCost nameCost nameCost nameCost_triangle
    have h₂ := MatrixCoupling.comp_cost_le (R₀.comp R₁) R₂.symm nameCost nameCost nameCost nameCost_triangle
    rw [MatrixCoupling.symm_cost R₂ nameCost nameCost_comm] at h₂
    have hηa : η=100*a := by dsimp [a]; ring
    dsimp only [R]
    rw [hηa]
    have hpos := mul_nonneg ha.le (Nat.cast_nonneg ((n*J)*s))
    nlinarith only [h₁,h₂,hR₀,hR₁budget,hR₂budget,hpos]
  exact ⟨R,hR⟩
end HyperbolicCoding

end

end OAI
