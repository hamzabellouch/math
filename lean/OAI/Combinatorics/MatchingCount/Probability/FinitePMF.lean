import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.RowPeak

namespace OAI

namespace MatchingFPRAS.Concentration

open MeasureTheory ProbabilityTheory Finset

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem hoeffding_mean (X : I → Ω → ℝ) (hi : iIndepFun X μ)
    (hm : ∀ i,AEMeasurable (X i) μ) (hb : ∀ i,∀ᵐ ω ∂μ,X i ω∈Set.Icc (0:ℝ) 1)
    (m : ℝ) (hmean : ∀ i,(∫ ω,X i ω ∂μ)=m)
    (hI : 0<Fintype.card I) (t : ℝ) (ht : 0≤t) :
    μ.real {ω | t < |(∑ i,X i ω)/(Fintype.card I : ℝ)-m|} ≤
      2*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
  classical
  have hN : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr hI
  have hc (i : I) : HasSubgaussianMGF (fun ω => X i ω-m) (1/4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
    rw [hmean i] at h
    norm_num at h ⊢
    exact h
  have hind : iIndepFun (fun i ω => X i ω-m) μ := by
    exact hi.comp (fun _ x => x-m) (fun _ => by fun_prop)
  have hs : HasSubgaussianMGF (fun ω => ∑ i,(X i ω-m))
      ((Fintype.card I : NNReal)/4) μ := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one_div,Finset.card_univ] using HasSubgaussianMGF.sum_of_iIndepFun hind (s:=univ) (fun i _ => hc i)
  have hh := hs.measure_ge_le (mul_nonneg hN.le ht)
  have hl := hs.neg.measure_ge_le (mul_nonneg hN.le ht)
  have he : -((Fintype.card I : ℝ)*t)^2 /
      (2*((Fintype.card I : NNReal)/4 : NNReal)) = -2*(Fintype.card I : ℝ)*t^2 := by
    push_cast
    field_simp [ne_of_gt hN]
    ring
  rw [he] at hh hl
  calc
    _ ≤ μ.real ({ω | (Fintype.card I : ℝ)*t ≤ ∑ i,(X i ω-m)} ∪
        {ω | (Fintype.card I : ℝ)*t ≤ -(∑ i,(X i ω-m))}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro ω hω
      simp only [Set.mem_ofPred_eq,Set.mem_union] at hω ⊢
      by_cases h : (Fintype.card I : ℝ)*t ≤ ∑ i,(X i ω-m)
      · exact Or.inl h
      · right
        simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,Finset.card_univ] at h ⊢
        rcases lt_abs.mp hω with hv | hv
        · have hv' := (lt_div_iff₀ hN).mp (by linarith : m+t < (∑ i,X i ω)/(Fintype.card I : ℝ))
          nlinarith
        · have hv' := (div_lt_iff₀ hN).mp (by linarith : (∑ i,X i ω)/(Fintype.card I : ℝ) < m-t)
          nlinarith
    _ ≤ μ.real {ω | (Fintype.card I : ℝ)*t ≤ ∑ i,(X i ω-m)} +
        μ.real {ω | (Fintype.card I : ℝ)*t ≤ -(∑ i,(X i ω-m))} := measureReal_union_le _ _
    _ ≤ _ := by simpa only [Pi.neg_apply, two_mul] using add_le_add hh hl

theorem hoeffding_observables [Fintype J] (X : J → I → Ω → ℝ)
    (hi : ∀ j,iIndepFun (X j) μ) (hm : ∀ j i,AEMeasurable (X j i) μ)
    (hb : ∀ j i,∀ᵐ ω ∂μ,X j i ω∈Set.Icc (0:ℝ) 1)
    (m : J → ℝ) (hmean : ∀ j i,(∫ ω,X j i ω ∂μ)=m j)
    (hI : 0<Fintype.card I) (t : ℝ) (ht : 0≤t) :
    μ.real {ω | ∃ j,t < |(∑ i,X j i ω)/(Fintype.card I : ℝ)-m j|} ≤
      2*(Fintype.card J : ℝ)*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
  classical
  have he : {ω | ∃ j,t < |(∑ i,X j i ω)/(Fintype.card I : ℝ)-m j|} =
      ⋃ j,{ω | t < |(∑ i,X j i ω)/(Fintype.card I : ℝ)-m j|} := by ext; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _ : J,2*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
      apply sum_le_sum
      intro j hj
      exact hoeffding_mean (X j) (hi j) (hm j) (hb j) (m j) (hmean j) hI t ht
    _ = _ := by simp; ring



open MeasureTheory ProbabilityTheory Finset
open scoped Classical

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J]

noncomputable def finitePMF (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) : PMF Ω :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [←ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x),hs]
    simp)

lemma finitePMF_apply (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) (x : Ω) :
    (finitePMF p hp hs x).toReal=p x := by simp [finitePMF,hp x]

theorem finite_hoeffding [DecidableEq I] (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1)
    (f : J → Ω → ℝ) (hf : ∀ j x,f j x∈Set.Icc (0:ℝ) 1)
    (hI : 0<Fintype.card I) (t : ℝ) (ht : 0≤t) :
    ∑ v : I → Ω,(if ∃ j,t < |(∑ i,f j (v i))/(Fintype.card I : ℝ)-∑ x,p x*f j x|
      then ∏ i,p (v i) else 0) ≤
      2*(Fintype.card J : ℝ)*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
  classical
  let : MeasurableSpace Ω := ⊤
  let q := finitePMF p hp hs
  let μ : Measure (I → Ω) := Measure.pi (fun _ : I => q.toMeasure)
  have hi (j : J) : iIndepFun (fun i (v : I → Ω) => f j (v i)) μ := by
    exact iIndepFun_pi (fun _ : I => (measurable_of_finite (f j)).aemeasurable)
  have hm (j : J) (i : I) : AEMeasurable (fun v : I → Ω => f j (v i)) μ :=
    (measurable_of_finite _).aemeasurable
  have hb (j : J) (i : I) : ∀ᵐ v ∂μ,f j (v i)∈Set.Icc (0:ℝ) 1 :=
    Filter.Eventually.of_forall (fun v => hf j (v i))
  have he (j : J) (i : I) : (∫ v,f j (v i) ∂μ)=∑ x,p x*f j x := by
    have hev := (measurePreserving_eval (fun _ : I => q.toMeasure) i).map_eq
    have hmap := integral_map ((measurable_of_finite (Function.eval i)).aemeasurable (μ:=μ))
      ((measurable_of_finite (f j)).aestronglyMeasurable (μ:=Measure.map (Function.eval i) μ))
    rw [hev] at hmap
    rw [←hmap, PMF.integral_eq_sum]
    apply sum_congr rfl
    intro x hx
    simp [q,finitePMF_apply,smul_eq_mul]
  have h := hoeffding_observables (μ:=μ) (fun j i v => f j (v i)) hi hm hb
    (fun j => ∑ x,p x*f j x) he hI t ht
  have hsingle (v : I → Ω) : μ.real {v}=∏ i,p (v i) := by
    simp only [Measure.real,μ,Measure.pi_singleton,ENNReal.toReal_prod]
    apply prod_congr rfl
    intro i hi
    simp [q,finitePMF,hp (v i)]
  let B : Finset (I → Ω) := univ.filter (fun v => ∃ j,t < |(∑ i,f j (v i))/(Fintype.card I : ℝ)-∑ x,p x*f j x|)
  have hB : (B : Set (I → Ω))={v | ∃ j,t < |(∑ i,f j (v i))/(Fintype.card I : ℝ)-∑ x,p x*f j x|} := by
    ext v; simp [B]
  rw [←hB,←sum_measureReal_singleton] at h
  simpa only [hsingle, B, sum_filter] using h



lemma observables_exp_tail (n K : ℕ) (hK : 0<K) :
    2*((n:ℝ)^2+2)*Real.exp (-20*((n:ℝ)+K+1)) < 1/(100*K) := by
  have hK0 : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have h1 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hc : (200:ℝ)<Real.exp 8 := by
    calc
      (200:ℝ) < 2^8 := by norm_num
      _ ≤ (Real.exp 1)^8 := pow_le_pow_left₀ (by norm_num) h1 _
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hn : (n:ℝ)^2+2≤Real.exp (2*((n:ℝ)+1)) := by
    have h := Real.add_one_le_exp ((n:ℝ)+1)
    have hh : 0≤(n:ℝ)+2 := by positivity
    calc
      _ ≤ ((n:ℝ)+2)^2 := by nlinarith
      _ ≤ (Real.exp ((n:ℝ)+1))^2 := pow_le_pow_left₀ hh (by linarith) _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hk : (K:ℝ)≤Real.exp (K:ℝ) := by linarith [Real.add_one_le_exp (K:ℝ)]
  have hprod : 200*(K:ℝ)*((n:ℝ)^2+2)<Real.exp (20*((n:ℝ)+K+1)) := by
    calc
      _ ≤ 200*Real.exp (K:ℝ)*Real.exp (2*((n:ℝ)+1)) := by gcongr
      _ < Real.exp 8*Real.exp (K:ℝ)*Real.exp (2*((n:ℝ)+1)) := by gcongr
      _ = Real.exp (8+(K:ℝ)+2*((n:ℝ)+1)) := by rw [Real.exp_add,Real.exp_add]
      _ < _ := Real.exp_lt_exp.mpr (by nlinarith)
  have he : 0<Real.exp (20*((n:ℝ)+K+1)) := Real.exp_pos _
  rw [show -20*((n:ℝ)+K+1)= -(20*((n:ℝ)+K+1)) by ring,Real.exp_neg]
  apply (lt_div_iff₀ (by positivity : (0:ℝ)<100*K)).mpr
  rw [← div_eq_mul_inv, (div_mul_eq_mul_div), div_lt_one he]
  nlinarith [hprod]

lemma stage_hoeffding_budget (n K S : ℕ) (hK : 0<K) (sigma : ℝ)
    (hS : 10*((n:ℝ)+K+1)≤(S:ℝ)*sigma^2) :
    2*((n:ℝ)^2+2)*Real.exp (-2*(S:ℝ)*sigma^2)<1/(100*K) := by
  apply lt_of_le_of_lt _ (observables_exp_tail n K hK)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

def trials (ell : ℕ) : ℕ := 10*(ell+1)+1

lemma median_tail (ell : ℕ) :
    Real.exp (-2*(4/10:ℝ)^2*(trials ell)) < (2:ℝ)^(-(ell:ℤ)) := by
  have hlog : Real.log 2<1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hx := Real.add_one_lt_exp (by norm_num : (1:ℝ)≠0)
    norm_num at hx
    exact hx
  have he : Real.exp (-((ell:ℝ)*Real.log 2))=(2:ℝ)^(-(ell:ℤ)) := by
    rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    simp
  rw [← he]
  apply Real.exp_lt_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg ell : (0:ℝ)≤ell)
  dsimp [trials]
  push_cast
  norm_num at *
  nlinarith [(Nat.cast_nonneg ell : (0:ℝ)≤ell)]

end MatchingFPRAS.Concentration

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

omit [Fintype V] [Nontrivial V] in
lemma logicalActivity_le_off (w w₁ : V → V → ℝ)
    (h : ∀ i j,i≠j → w₁ i j ≤ w i j) (e : LogicalEdge V) :
    logicalActivity w₁ e ≤ logicalActivity w e := by
  unfold logicalActivity edgeActivity
  split_ifs
  · exact h _ _ e.property.ne
  · exact h _ _ e.property.ne.symm

lemma bagReweight_range_off (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (e : BagEdge (sourceBags w K)) :
    0 ≤ bagReweight w w₁ K e ∧ bagReweight w w₁ K e ≤ 1 := by
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · have h₀ : 0 < logicalActivity w he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw _ _
      have h₁ : 0 ≤ logicalActivity w₁ he.choose.1 := by
        unfold logicalActivity edgeActivity; split_ifs <;> exact hw₁ _ _
      exact ⟨div_nonneg h₁ h₀.le,(div_le_one h₀).mpr (logicalActivity_le_off w w₁ hle _)⟩
    · norm_num
  · norm_num

lemma observableD_range_off (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (a : SourceMarked w K) :
    0 ≤ observableD w w₁ K a ∧ observableD w w₁ K a ≤ 1 := by
  unfold observableD
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one₀ (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

lemma observableProbe_range_off (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (e₀ : LogicalEdge V) (a : SourceMarked w K) :
    0 ≤ observableProbe w w₁ K e₀ a ∧ observableProbe w w₁ K e₀ a ≤ 1 := by
  unfold observableProbe
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one₀ (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

abbrev ObservableIndex (V : Type*) [LinearOrder V] := Fin 2 ⊕ LogicalEdge V

noncomputable def sourceObservable (w w₁ : V → V → ℝ) (K : ℕ) :
    ObservableIndex V → SourceMarked w K → ℝ
  | Sum.inl i => if i=0 then observableA w K else observableD w w₁ K
  | Sum.inr e => observableProbe w w₁ K e

lemma sourceObservable_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (j : ObservableIndex V) (a : SourceMarked w K) :
    sourceObservable w w₁ K j a∈Set.Icc (0:ℝ) 1 := by
  cases j with
  | inl i =>
    dsimp [sourceObservable]
    split_ifs
    · exact observableA_range w K a
    · exact observableD_range_off w w₁ hw hw₁ hle K a
  | inr e => exact observableProbe_range_off w w₁ hw hw₁ hle K e a

omit [Nontrivial V] in
lemma observableIndex_card : Fintype.card (ObservableIndex V) ≤ (Fintype.card V)^2+2 := by
  have h := Fintype.card_subtype_le (fun e : V×V => e.1<e.2)
  change Fintype.card (LogicalEdge V) ≤ Fintype.card (V×V) at h
  simp only [Fintype.card_prod] at h
  simpa only [ObservableIndex,Fintype.card_sum,Fintype.card_fin,pow_two,Nat.add_comm] using Nat.add_le_add_left h 2

noncomputable def sampleAverage {Ω : Type*} {S : ℕ} (f : Ω → ℝ) (x : Fin S → Ω) : ℝ :=
  (∑ i,f (x i))/(S:ℝ)

noncomputable def sourceMean (w w₁ : V → V → ℝ) (K : ℕ) (j : ObservableIndex V) : ℝ :=
  ∑ x : SourceMarked w K,sourceLaw w K (sourceD (V:=V) K) x*sourceObservable w w₁ K j x

def StageGood {S : ℕ} (w w₁ : V → V → ℝ) (K : ℕ) (σ : ℝ) (x : Fin S → SourceMarked w K) : Prop :=
  ∀ j : ObservableIndex V, |sampleAverage (sourceObservable w w₁ K j) x-sourceMean w w₁ K j| ≤ σ

theorem source_ideal_concentration (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (hz : 0 < partition w ∅) (K S : ℕ) (hS : 0<S) (σ : ℝ) (hσ : 0≤σ) :
    ∑ x : Fin S → SourceMarked w K,(if ¬StageGood w w₁ K σ x
      then ∏ i,sourceLaw w K (sourceD (V:=V) K) (x i) else 0) ≤
      2*((Fintype.card V:ℝ)^2+2)*Real.exp (-2*(S:ℝ)*σ^2) := by
  have hp := sourceBagZ_pos w hw hz K (sourceD (V:=V) K)
  have h := MatchingFPRAS.Concentration.finite_hoeffding (I:=Fin S)
    (sourceLaw w K (sourceD (V:=V) K)) (sourceLaw_nonneg w hw K _ hp.le)
    (sourceLaw_sum w K _ hp.ne') (sourceObservable w w₁ K) (sourceObservable_range w w₁ hw hw₁ hle K)
    (by simpa using hS) σ hσ
  have he : ∀ x : Fin S → SourceMarked w K,
      (¬StageGood w w₁ K σ x) ↔
      (∃ j,σ < |(∑ i,sourceObservable w w₁ K j (x i))/(Fintype.card (Fin S):ℝ)-
        ∑ a,sourceLaw w K (sourceD (V:=V) K) a*sourceObservable w w₁ K j a|) := by
    intro x
    simp only [StageGood,not_forall,not_le,sampleAverage,sourceMean,Fintype.card_fin]
  simp_rw [he] at ⊢
  apply h.trans
  have hc : (Fintype.card (ObservableIndex V):ℝ) ≤ (Fintype.card V:ℝ)^2+2 := by
    exact_mod_cast (observableIndex_card (V:=V))
  simpa only [Fintype.card_fin] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (Real.exp_pos _).le

variable {n K T S : ℕ} [Nontrivial (Fin n)]

noncomputable def empiricalData (c : StageData n K T) (x : Fin S → SourceMarked c.w K)
    (h : StageGood c.w c.next K (RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon) x) : EmpiricalData c where
  abar := sampleAverage (observableA c.w K) x
  dbar := sampleAverage (observableD c.w c.next K) x
  zbar e := sampleAverage (observableProbe c.w c.next K e) x
  errorA := by simpa only [sourceObservable,ite_true,sourceMean,meanA] using h (Sum.inl 0)
  errorD := by simpa only [sourceObservable,show (1:Fin 2)≠0 by decide,ite_false,sourceMean,meanD] using h (Sum.inl 1)
  errorProbe e := by simpa only [sourceObservable,sourceMean,meanProbe] using h (Sum.inr e)

lemma StageData.sigma_pos (c : StageData n K T) : 0 < RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold RealStage.sigma RealStage.alpha
  have hD : 0 < sourceD (V:=Fin n) K := sourceD_one K
  have ht : 0 < T := c.stages
  have he := c.epsilon_positive
  exact lt_min (by positivity) (by positivity)

noncomputable def stageSampleCount (n D T : ℕ) (ε : ℝ) : ℕ :=
  ⌈10*((RealStage.sigma D T ε)⁻¹)^2*((n:ℝ)+T+1)⌉₊

lemma StageData.sampleCount_pos (c : StageData n K T) :
    0 < stageSampleCount n (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold stageSampleCount
  apply Nat.ceil_pos.mpr
  have hs := c.sigma_pos
  positivity

lemma StageData.sampleCount_bound (c : StageData n K T) :
    10*((n:ℝ)+T+1) ≤
      (stageSampleCount n (sourceD (V:=Fin n) K) T c.epsilon:ℝ)*
        (RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon)^2 := by
  have hs := c.sigma_pos
  have h := mul_le_mul_of_nonneg_right
    (Nat.le_ceil (10*((RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon)⁻¹)^2*((n:ℝ)+T+1)))
    (sq_nonneg (RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon))
  convert h using 1
  all_goals first | rfl | field_simp [ne_of_gt hs]

theorem source_ideal_budget (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (hz : 0 < partition w ∅) (K T S : ℕ) (hT : 0<T) (hS : 0<S)
    (σ : ℝ) (hσ : 0≤σ) (hsize : 10*((Fintype.card V:ℝ)+T+1) ≤ (S:ℝ)*σ^2) :
    ∑ x : Fin S → SourceMarked w K,(if ¬StageGood w w₁ K σ x
      then ∏ i,sourceLaw w K (sourceD (V:=V) K) (x i) else 0) < 1/(100*T) := by
  exact (source_ideal_concentration w w₁ hw hw₁ hle hz K S hS σ hσ).trans_lt
    (MatchingFPRAS.Concentration.stage_hoeffding_budget (Fintype.card V) T S hT σ hsize)



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourcePM w K) := Classical.decEq _

theorem source_nearby_budget (w w₁ : V → V → ℝ) (hw : ∀ x y,0<w x y)
    (hw₁ : ∀ x y,0≤w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (hz : 0<Switching.partition w ∅) (K T S : ℕ) (hT : 0<T) (hS : 0<S)
    (σ : ℝ) (hσ : 0≤σ) (hsize : 10*((Fintype.card V:ℝ)+T+1) ≤ (S:ℝ)*σ^2)
    (p : SourceMarked w K → ℝ) (hp : ∀ a,0≤p a) (hpsum : ∑ a,p a=1)
    (htv : Variation.tv p (sourceLaw w K (sourceD (V:=V) K)) ≤ 3/(1000*T*S)) :
    Variation.event (Variation.iid p S) (fun x => ¬StageGood w w₁ K σ x) < 13/(1000*T) := by
  have hpos := sourceBagZ_pos w hw hz K (sourceD (V:=V) K)
  have hq := sourceLaw_nonneg w hw K _ hpos.le
  have hqs := sourceLaw_sum w K _ hpos.ne'
  have hiid := Variation.iid_tv p (sourceLaw w K (sourceD (V:=V) K)) hp hpsum hq hqs S
  have he := Variation.event_sub_le (Variation.iid p S)
    (Variation.iid (sourceLaw w K (sourceD (V:=V) K)) S)
    (by rw [Variation.iid_sum p hpsum,Variation.iid_sum _ hqs])
    (fun x => ¬StageGood w w₁ K σ x)
  have hv := (le_abs_self _).trans (he.trans hiid)
  have hh := source_ideal_budget w w₁ hw hw₁ hle hz K T S hT hS σ hσ hsize
  have ht := mul_le_mul_of_nonneg_left htv (Nat.cast_nonneg S : (0:ℝ)≤S)
  have hid : (1:ℝ)/(100*T)+(S:ℝ)*(3/(1000*T*S))=13/(1000*T) := by
    have ht0 : (T:ℝ)≠0 := by exact_mod_cast hT.ne'
    have hs0 : (S:ℝ)≠0 := by exact_mod_cast hS.ne'
    field_simp
    ring
  have hh' : Variation.event (Variation.iid (sourceLaw w K (sourceD (V:=V) K)) S)
      (fun x => ¬StageGood w w₁ K σ x) < 1/(100*T) := by
    convert hh using 1
    unfold Variation.event Variation.iid
    congr 1
    funext x
    split_ifs <;> rfl
  linarith

theorem source_run_stage_budget (hn : 2 ≤ Fintype.card V)
    (w w₁ : V → V → ℝ) (hw : ∀ x y,0<w x y)
    (hw₁ : ∀ x y,0≤w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (hz : 0<Switching.partition w ∅) (K T S : ℕ) (hT : 0<T) (hS : 0<S)
    (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K)
    (σ : ℝ) (hσ : 0≤σ) (hsize : 10*((Fintype.card V:ℝ)+T+1) ≤ (S:ℝ)*σ^2)
    (L : ℕ) (hL : max (sourceD (V:=V) K:ℝ) (3*4^K) ≤ (tierBase (SourceVertex V K))^L)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K))
    (z : Slot L (ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K)) → SourcePM w K) :
    let ξ : ℝ := 1/(1000*T*S)
    let p := sourceRun w K hK L _ hq z
      (ladderSteps (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K) K L ξ)
    Variation.event (Variation.iid p S) (fun x => ¬StageGood w w₁ K σ x) < 13/(1000*T) := by
  dsimp only
  apply source_nearby_budget w w₁ hw hw₁ hle hz K T S hT hS σ hσ hsize
  · exact sourceRun_nonneg w hw K hK L _ hq z _
  · exact sourceRun_sum w hw K hK L _ hq z _
  · have ht : (1:ℝ)≤T := by exact_mod_cast hT
    have hs : (1:ℝ)≤S := by exact_mod_cast hS
    have hd : (1:ℝ)<1000*T*S := by nlinarith
    exact (sourceRun_tv hn w hw K hK L hL hq z _ (by positivity)
      ((div_lt_one (by positivity)).mpr hd)).trans (by gcongr; norm_num)

end MatchingFPRAS.Enlargement

end OAI
