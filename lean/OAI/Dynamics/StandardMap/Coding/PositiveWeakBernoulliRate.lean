import OAI.Dynamics.StandardMap.EntropyEndpoint
import OAI.Dynamics.StandardMap.Coding.FullEntropyCopySequence

namespace OAI

section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
  [Fintype A] [MeasurableSingletonClass A] [Nonempty A]

lemma weakBernoulli_zero_rate_diagonal (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) (hz : rate μ e p=0) :
    ∀ ε : ℝ,0 < ε → LawClose (μ.map (fun x => (p x,p x))) ((μ.map p).prod (μ.map p)) ε := by
  have hf := tailObservable_self_of_rate_zero μ e he p hp hz
  have hb := hf.reverse μ e he p p hp hp
  intro ε hε
  obtain ⟨n,hn⟩ := (hwb ε hε).exists
  obtain ⟨F,hF,hFeq⟩ := hf n
  obtain ⟨B,hB,hBeq⟩ := hb n
  have hh := hn.map (hB.prodMap hF)
  have hPast : (μ.map (tailName e.symm p 0)).map B=μ.map p := by
    rw [←stationary_tail_law μ (he.symm e) hp n,
      Measure.map_map hB (measurable_tailName e.symm.measurable hp n)]
    exact Measure.map_congr hBeq.symm
  have hFuture : (μ.map (tailName e p 0)).map F=μ.map p := by
    rw [←stationary_tail_law μ he hp n,
      Measure.map_map hF (measurable_tailName e.measurable hp n)]
    exact Measure.map_congr hFeq.symm
  have hJoint : (μ.map (remotePair e e.symm p n)).map (Prod.map B F)=μ.map (fun x => (p x,p x)) := by
    rw [Measure.map_map (hB.prodMap hF) (measurable_remotePair e.measurable e.symm.measurable hp n)]
    apply Measure.map_congr
    filter_upwards [hBeq,hFeq] with x hx hy
    exact Prod.ext hx.symm hy.symm
  rw [hJoint,remoteProductLaw,←Measure.map_prod_map _ _ hB hF,hPast,hFuture] at hh
  exact hh

lemma weakBernoulli_zero_rate_constant (μ : Measure X) [IsProbabilityMeasure μ]
    (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ) (p : X → A) (hp : Measurable p)
    (hwb : WeakBernoulliProcess μ e p) (hz : rate μ e p=0) :
    ∃ a : A,∀ᵐ x ∂μ,p x=a := by
  classical
  have hmass (a : A) : mass μ p a=0 ∨ mass μ p a=1 := by
    have heq : mass μ p a-mass μ p a*mass μ p a=0 := by
      apply abs_eq_zero.mp
      apply le_antisymm ?_ (abs_nonneg _)
      apply le_of_forall_pos_le_add
      intro ε hε
      simp only [zero_add]
      have hh := weakBernoulli_zero_rate_diagonal μ e he p hp hwb hz (ε/2) (half_pos hε)
        ({a} ×ˢ {a}) ((measurableSet_singleton a).prod (measurableSet_singleton a))
      have hdiag : (fun x => (p x,p x)) ⁻¹' ({a} ×ˢ {a})=p ⁻¹' {a} := by
        ext x
        simp
      rw [Measure.real,Measure.map_apply (hp.prodMk hp)
        ((measurableSet_singleton a).prod (measurableSet_singleton a)),hdiag] at hh
      have hprod : ((μ.map p).prod (μ.map p)).real ({a} ×ˢ {a})=mass μ p a*mass μ p a := by
        simp only [Measure.real,Measure.prod_prod,ENNReal.toReal_mul,
          Measure.map_apply hp (measurableSet_singleton a),mass]
      rw [hprod] at hh
      exact hh.trans (by linarith)
    rcases mul_eq_zero.mp (show mass μ p a*(1-mass μ p a)=0 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hs : ∑ a,mass μ p a=1 := by
    simpa only [measure_univ,ENNReal.toReal_one] using mass_sum μ p hp
  have hex : ∃ a,mass μ p a=1 := by
    by_contra! h
    have hz : ∀ a,mass μ p a=0 := fun a => (hmass a).resolve_right (h a)
    simp only [hz,Finset.sum_const_zero] at hs
    norm_num at hs
  obtain ⟨a,ha⟩ := hex
  refine ⟨a,?_⟩
  have hm : μ (p ⁻¹' {a})=1 := by
    rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
    change ENNReal.ofReal (mass μ p a)=1
    rw [ha,ENNReal.ofReal_one]
  exact (ae_iff_prob_eq_one (measurableSet_setOfPred.mp (measurableSet_eq_fun hp measurable_const))).mpr hm

theorem separating_weakBernoulli_positive_rate (μ : Measure X) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (e : X ≃ᵐ X) (he : MeasurePreserving e μ μ)
    (α : ℕ → ℕ → X → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun x => fun i j => α i j x))
    (hwb : ∀ M,WeakBernoulliProcess μ e (joinedBinary α M)) :
    ∃ M : ℕ,0 < rate μ e (joinedBinary α M) := by
  by_contra! h
  have hz (M : ℕ) : rate μ e (joinedBinary α M)=0 :=
    le_antisymm (h M) (rate_nonneg μ e he _ (measurable_joinedBinary hα M))
  choose a ha using fun M => weakBernoulli_zero_rate_constant μ e he
    (joinedBinary α M) (measurable_joinedBinary hα M) (hwb M) (hz M)
  have hall : ∀ᵐ x ∂μ,∀ M,joinedBinary α M x=a M := ae_all_iff.mpr ha
  obtain ⟨x,hx⟩ := hall.exists
  have hone : ∀ᵐ y ∂μ,y=x := by
    filter_upwards [hall] with y hy
    apply hsep
    funext i j
    let M := max i j+1
    have hij : (⟨i,by dsimp [M]; omega⟩,⟨j,by dsimp [M]; omega⟩) ∈
        (Set.univ : Set (Fin M × Fin M)) := mem_univ _
    have hh := congrFun ((hy M).trans (hx M).symm)
      (⟨i,by dsimp [M]; omega⟩,⟨j,by dsimp [M]; omega⟩)
    exact hh
  have hset : ({x} : Set X)=ᵐ[μ]univ := by
    filter_upwards [hone] with y hy
    change (y=x)=True
    simp only [hy,eq_self]
  have hm := measure_congr hset
  exact zero_ne_one (by simpa only [measure_singleton,measure_univ] using hm)
end HyperbolicCoding

end
section
namespace HyperbolicCoding
open MeasureTheory Set Filter StandardMapEntropy.Entropy
open scoped BigOperators ENNReal Topology

lemma weightEntropy_eq_shannon {A : Type*} [Fintype A] (p : A → ℝ) :
    weightEntropy p=shannon p := by
  unfold weightEntropy shannon
  apply Finset.sum_congr rfl
  intro a _
  rw [Real.negMulLog]
  ring

noncomputable def entropyPath (n : ℕ) (t : ℝ) (a : Fin (n+2)) : ℝ :=
  (1-t)*(if a=0 then 1 else 0)+t/(n+2 : ℝ)

lemma entropyPath_nonneg (n : ℕ) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) (a : Fin (n+2)) :
    0 ≤ entropyPath n t a := by
  unfold entropyPath
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (by split_ifs <;> norm_num))
    (div_nonneg ht.1 (by positivity))

lemma entropyPath_sum (n : ℕ) (t : ℝ) : ∑ a,entropyPath n t a=1 := by
  have hc : (n+2 : ℝ)≠0 := ne_of_gt (by positivity)
  simp only [entropyPath,Finset.sum_add_distrib,←Finset.mul_sum,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  field_simp
  ring

lemma entropyPath_continuous (n : ℕ) : Continuous (fun t => weightEntropy (entropyPath n t)) := by
  simp_rw [weightEntropy_eq_shannon]
  apply continuous_shannon.comp
  apply continuous_pi
  intro a
  unfold entropyPath
  fun_prop

lemma entropyPath_zero (n : ℕ) : weightEntropy (entropyPath n 0)=0 := by
  unfold weightEntropy entropyPath
  simp only [sub_zero,mul_ite,mul_one,mul_zero,zero_div,add_zero]
  apply Finset.sum_eq_zero
  intro a _
  split_ifs <;> simp

lemma entropyPath_one (n : ℕ) : weightEntropy (entropyPath n 1)=Real.log (n+2 : ℝ) := by
  have hc : (n+2 : ℝ)≠0 := ne_of_gt (by positivity)
  unfold weightEntropy entropyPath
  simp only [sub_self,zero_mul,zero_add,one_div,Real.log_inv,neg_neg,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_ofNat]
  rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]

theorem exists_finite_weight_entropy (h : ℝ) (hh : 0 ≤ h) :
    ∃ n : ℕ,∃ β : Fin (n+2) → ℝ,(∀ a,0 ≤ β a) ∧ (∑ a,β a=1) ∧ weightEntropy β=h := by
  obtain ⟨n,hn⟩ := exists_nat_gt (Real.exp h)
  have hn2 : Real.exp h < (n+2 : ℝ) := by linarith
  have hl : h < Real.log (n+2 : ℝ) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos h) hn2
  have him := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    (entropyPath_continuous n).continuousOn
  have hmem : h∈Icc (weightEntropy (entropyPath n 0)) (weightEntropy (entropyPath n 1)) := by
    rw [entropyPath_zero,entropyPath_one]
    exact ⟨hh,hl.le⟩
  obtain ⟨t,ht,heq⟩ := him hmem
  exact ⟨n,entropyPath n t,entropyPath_nonneg n ht,entropyPath_sum n t,heq⟩
end HyperbolicCoding

end
section
namespace StandardMapEntropy
open MeasureTheory Set Filter HyperbolicCoding Entropy
open scoped BigOperators ENNReal Topology

lemma normalizedArea_nullSingleton (E : Set Torus) : NullSingletonClass (normalizedArea E) := by
  have : NullSingletonClass area := by unfold area; infer_instance
  constructor
  intro z
  exact normalizedArea_absolutelyContinuous E (measure_singleton z)

theorem actual_return_full_entropy_iid_factor (k : ℝ) (hk : 0 ≤ k) (N : ℕ)
    (E : Set Torus) (hE : 0 < area E)
    (htotal : ∀ m : ℕ,0 < m → Ergodic (((standardMap k)^[N])^[m]) (normalizedArea E))
    (α : ℕ → ℕ → Torus → Bool) (hα : ∀ i j,Measurable (α i j))
    (hsep : Function.Injective (fun z => fun i j => α i j z))
    (hwb : ∀ M : ℕ,WeakBernoulliProcess (normalizedArea E)
      (iterateEquiv (standardMap_measurableEquiv k) N) (joinedBinary α M)) :
    ∃ n : ℕ,∃ β : Fin (n+2) → ℝ,∃ p : Torus → Fin (n+2),
      (∀ a,0 ≤ β a) ∧ (∑ a,β a=1) ∧ 0 < weightEntropy β ∧ Measurable p ∧
      FiniteRateSupremum (normalizedArea E) ((standardMap k)^[N]) (weightEntropy β) ∧
      MeasurePreserving (orbitName (iterateEquiv (standardMap_measurableEquiv k) N) p)
        (normalizedArea E) (Measure.infinitePi (fun _ : ℤ => finiteWeightLaw β)) ∧
      rate (normalizedArea E) ((standardMap k)^[N]) p=weightEntropy β ∧
      (∀ z,orbitName (iterateEquiv (standardMap_measurableEquiv k) N) p ((standardMap k)^[N] z)=
        fun i => orbitName (iterateEquiv (standardMap_measurableEquiv k) N) p z (i+1)) ∧
      (∀ r : ℕ,∀ γ : Torus → Fin (r+1),Measurable γ →
        rate (normalizedArea E) ((standardMap k)^[N]) (fun z => (p z,γ z))=weightEntropy β) := by
  let := normalizedArea_probability hE
  let := normalizedArea_nullSingleton E
  let e := iterateEquiv (standardMap_measurableEquiv k) N
  have heq : (e : Torus → Torus)=(standardMap k)^[N] := funext (iterateEquiv_apply _ N)
  have he : Ergodic e (normalizedArea E) := by
    rw [heq]
    simpa only [Function.iterate_one] using htotal 1 (by omega)
  have het : ∀ m : ℕ,0 < m → Ergodic (e^[m]) (normalizedArea E) := by
    simpa only [heq] using htotal
  obtain ⟨h,H,_hbound⟩ := exists_finiteRateSupremum (normalizedArea E) ((standardMap k)^[N])
    ((Real.log 1000+(∫ z,Real.log ‖standardDerivativeProduct k z N‖ ∂area))/area.real E)
    (fun r p hp => restricted_finite_rate_upper k hk N E hE
      (by simpa only [heq] using he.toMeasurePreserving) p hp)
  have H' : FiniteRateSupremum (normalizedArea E) e h := by simpa only [heq] using H
  obtain ⟨M,hM⟩ := separating_weakBernoulli_positive_rate (normalizedArea E) e
    he.toMeasurePreserving α hα hsep hwb
  have hh : 0 < h := hM.trans_le (H'.upper _ (measurable_joinedBinary hα M))
  obtain ⟨n,β,hβ,hβsum,hβentropy⟩ := exists_finite_weight_entropy h hh.le
  have hpos : 0 < weightEntropy β := hβentropy.symm ▸ hh
  have Hβ : FiniteRateSupremum (normalizedArea E) e (weightEntropy β) := hβentropy.symm ▸ H'
  obtain ⟨p,hp,hcode,hr,hshift,hjoint⟩ := full_entropy_iid_factor (normalizedArea E) e he het
    β hβ hβsum hpos Hβ (⟨0,by omega⟩ : Fin (n+2)) (⟨1,by omega⟩ : Fin (n+2))
    (by intro h; have hv := congrArg Fin.val h; simp only at hv; omega)
  refine ⟨n,β,p,hβ,hβsum,hpos,hp,?_,hcode,?_,?_,?_⟩
  · simpa only [heq] using Hβ
  · simpa only [heq] using hr
  · simpa only [heq] using hshift
  · simpa only [heq] using hjoint
end StandardMapEntropy

end

end OAI
