import Mathlib
import OAI.Probability.JammingConcavity.WeightedMarkedFactorial

namespace OAI

/-! Row Common Rank Continuity. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def rowClosedProfile (p : SphericalProfile) (s : ℝ) : ℝ := p.val (min 1 (max 0 s))

def rowFullRankCovariance (r : ℕ) (Q : ℝ) (p : SphericalProfile)
    (U : RankArray) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => if i=j then Q else rowClosedProfile p (U i.val j.val)

def RowCommonRankContinuityStatement : Prop :=
  ∀ (Q : ℝ) (pn : ℕ → SphericalProfile) (p : SphericalProfile),
    (∀ n, (pn n).val 1 ≤ Q) → p.val 1 ≤ Q →
    Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) atTop (𝓝 0) →
  ∀ r : ℕ, ∃ (ρ : ℕ → ProbabilityMeasure (RankArray × EuclideanSpace ℝ (Fin r)))
    (ρ₀ : ProbabilityMeasure (RankArray × EuclideanSpace ℝ (Fin r))),
    (∀ n, (ρ n : Measure _) = gaussianAdjunctionMeasure r (rowFullRankCovariance r Q (pn n)) realizedRankLaw) ∧
    (ρ₀ : Measure _) = gaussianAdjunctionMeasure r (rowFullRankCovariance r Q p) realizedRankLaw ∧
    Tendsto ρ atTop (𝓝 ρ₀)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MicroscopicJamming

def rowReplicaDiagonal (k : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) : ℝ≥0 :=
  p₀ + ∑ j : Fin k, d j + Δ

def RowReplicaMomentsStatement : Prop :=
  ∀ (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0),
    ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ (rowReplicaKernel ms Δ)).map
      (rowReplicaSiteField ms.length) = gaussianReal 0 (rowReplicaDiagonal ms.length d p₀ Δ) ∧
  ∀ (u : ℝ → ℝ) (A L a : ℝ), Measurable u → 0 ≤ A → 0 ≤ L → 0 < a →
    (∀ z, |u z| ≤ A+L*|z|) →
    Integrable (fun z => Real.exp (a*|u (rowReplicaSiteField ms.length z)|))
      ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ (rowReplicaKernel ms Δ)) ∧
    (∫ z, Real.exp (a*|u (rowReplicaSiteField ms.length z)|)
      ∂((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ (rowReplicaKernel ms Δ))) ≤
      2*Real.exp (a*A+(rowReplicaDiagonal ms.length d p₀ Δ : ℝ)*(a*L)^2/2)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
lemma rpcStepLevel_monotone (ms : List ℝ) : Monotone (rpcStepLevel ms) := by
  intro s t hst
  unfold rpcStepLevel
  induction ms with
  | nil => simp
  | cons a ms ih =>
    simp only [List.filter_cons, decide_eq_true_eq]
    split_ifs with hs ht
    · simpa using ih
    · exact False.elim (ht (le_trans hs hst))
    · simp only [List.length_cons]; omega
    · exact ih
 

def rowCascadeProfile (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) : SphericalProfile where
  val s := (p₀:ℝ) + ∑ a : Fin ms.length, if a.val+1 ≤ rpcStepLevel ms s then (d a:ℝ) else 0
  mono := by
    intro s hs t ht hst
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro a _
    split_ifs with ha hb
    · rfl
    · exact False.elim (hb (ha.trans (rpcStepLevel_monotone ms hst)))
    · exact (d a).coe_nonneg
    · rfl
  nonneg := by
    intro s hs
    apply add_nonneg p₀.coe_nonneg
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact (d a).coe_nonneg
    · rfl
 

def RowCascadeLogContinuityStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ (ms : ℕ → List ℝ), (∀ n, (ms n).Pairwise (· < ·)) →
    (∀ n m, m ∈ ms n → 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℕ → ℝ≥0) (p₀ Δ : ℕ → ℝ≥0) (Q : ℝ≥0) (p : SphericalProfile),
    (∀ n, rowReplicaDiagonal (ms n).length (d n) (p₀ n) (Δ n) = Q) → p.val 1 ≤ Q →
    Tendsto (fun n => sphericalProfileDistance (rowCascadeProfile (ms n) (d n) (p₀ n)).val p.val)
      atTop (𝓝 0) →
    ∃ ℓ : ℝ, Tendsto (fun n => ∫ ω, Real.log
      (replicaZ (rowReplicaKernel (ms n) (Δ n)) (rowFullPotential (ms n) u) ω)
        ∂rowReplicaEnvironmentLaw (ms n) (d n) (p₀ n)) atTop (𝓝 ℓ)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def replicaFirst {S : Type*} (r k : ℕ) (xs : Fin (r+k) → S) : Fin r → S :=
  fun i => xs (Fin.castAdd k i)

def replicaFieldView {Ω S : Type*} {r : ℕ} (V : Ω × S → ℝ)
    (B : Ω × (Fin r → S) → ℝ) (k : ℕ)
    (z : Ω × (Fin (r+k) → S)) : ℝ × (Fin (r+k) → ℝ) :=
  (B (z.1,replicaFirst r k z.2),fun i => V (z.1,z.2 i))

def replicaFieldLaw {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ν : Measure Ω) (G : Kernel Ω S) {r : ℕ} (V : Ω × S → ℝ)
    (B : Ω × (Fin r → S) → ℝ) (k : ℕ) : Measure (ℝ × (Fin (r+k) → ℝ)) :=
  (ν ⊗ₘ replicaKernel G (r+k)).map (replicaFieldView V B k)

def ReplicaLawContinuityStatement : Prop :=
  ∀ (Ω S : ℕ → Type) (_mΩ : ∀ n, MeasurableSpace (Ω n))
    (_mS : ∀ n, MeasurableSpace (S n)),
  ∀ (ν : ∀ n, Measure (Ω n)) (G : ∀ n, Kernel (Ω n) (S n)),
    (∀ n, IsProbabilityMeasure (ν n)) → (∀ n, IsMarkovKernel (G n)) →
  ∀ (V : ∀ n, Ω n × S n → ℝ), (∀ n, Measurable (V n)) →
    (∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ n,
      Integrable (fun z => Real.exp (a * |V n z|)) ((ν n) ⊗ₘ (G n)) ∧
      (∫ z, Real.exp (a * |V n z|) ∂((ν n) ⊗ₘ (G n))) ≤ C) →
  ∀ (r : ℕ) (B : ∀ n, Ω n × (Fin r → S n) → ℝ),
    (∀ n, Measurable (B n)) → (∃ K : ℝ, ∀ n z, |B n z| ≤ K) →
    (∀ k : ℕ, ∃ (ρ : ℕ → ProbabilityMeasure (ℝ × (Fin (r+k) → ℝ)))
      (ρ₀ : ProbabilityMeasure (ℝ × (Fin (r+k) → ℝ))),
      (∀ n, (ρ n : Measure _) = replicaFieldLaw (ν n) (G n) (V n) (B n) k) ∧
      Tendsto ρ atTop (𝓝 ρ₀)) →
    (∃ ℓ : ℝ, Tendsto (fun n => ∫ ω, Real.log (replicaZ (G n) (V n) ω) ∂ν n)
      atTop (𝓝 ℓ)) ∧
    (∃ b : ℝ, Tendsto (fun n => ∫ ω,
      replicaNum (G n) (V n) (B n) ω / (replicaZ (G n) (V n) ω)^r ∂ν n)
      atTop (𝓝 b))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
 

def RowRetainedRankLawStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) (B : ℕ → ℝ) (k : ℕ),
    replicaFieldLaw (rowReplicaEnvironmentLaw ms d p₀) (rowReplicaKernel ms Δ)
      (rowFullPotential ms u) (rowFullPair ms u B) k =
    (gaussianAdjunctionMeasure (2+k)
      (rowFullRankCovariance (2+k) (rowReplicaDiagonal ms.length d p₀ Δ)
        (rowCascadeProfile ms d p₀)) realizedRankLaw).map (fun z =>
      (B (rpcStepLevel ms (z.1 0 1)) *
        (deriv u (z.2 (Fin.castAdd k (0:Fin 2))) *
          deriv u (z.2 (Fin.castAdd k (1:Fin 2)))),
       fun i => u (z.2 i)))
end MicroscopicJamming

 
open MeasureTheory Set
open scoped NNReal BigOperators

namespace MicroscopicJamming

lemma rankBirth_nonneg {n : ℕ} (R : Fin n → Fin n → ℝ) (j : Fin n) : 0 ≤ rankBirth R j :=
  NNReal.coe_nonneg _

lemma rankBirth_le_one {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R) (j : Fin n) :
    rankBirth R j ≤ 1 := by
  change ↑((Finset.univ.filter (fun i => i < j)).sup (fun i => (R i j).toNNReal)) ≤ (1:ℝ)
  rw [← NNReal.coe_one, NNReal.coe_le_coe]
  exact Finset.sup_le fun i _ => (Real.toNNReal_le_iff_le_coe).mpr (hR.2.2.1 i j).2

lemma le_rankBirth_iff {n : ℕ} {R : Fin n → Fin n → ℝ} (_hR : FiniteRank R)
    (j : Fin n) {m : ℝ} (hm : 0 < m) :
    m ≤ rankBirth R j ↔ ∃ i : Fin n, i < j ∧ m ≤ R i j := by
  unfold rankBirth
  rw [← Real.toNNReal_le_iff_le_coe, Finset.le_sup_iff (Real.toNNReal_pos.mpr hm)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Real.toNNReal_le_toNNReal_iff_of_pos hm]

lemma birth_cluster_iff {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i j : Fin n) {m : ℝ} (hm : 0 < m) (hj : j ∈ rankCluster R i m) :
    m ≤ rankBirth R j ↔ ∃ k ∈ rankCluster R i m, k < j := by
  rw [le_rankBirth_iff hR j hm]
  have hj' : m ≤ R i j := (Finset.mem_filter.mp hj).2
  constructor
  · rintro ⟨k,hk,hkj⟩
    refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hk⟩
    calc m ≤ min (R i j) (R j k) := le_min hj' (by rwa [hR.2.1 j k])
         _ ≤ R i k := hR.2.2.2 i j k
  · rintro ⟨k,hk,hkj⟩
    refine ⟨k,hkj,?_⟩
    calc m ≤ min (R k i) (R i j) := le_min (by rw [hR.2.1 k i]; exact (Finset.mem_filter.mp hk).2) hj'
         _ ≤ R k j := hR.2.2.2 k i j

lemma rankCluster_nonempty {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i : Fin n) {m : ℝ} (hm : m ≤ 1) : (rankCluster R i m).Nonempty := by
  refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  simpa [hR.1 i] using hm

lemma rankBirth_lt_at_min {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i : Fin n) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    rankBirth R ((rankCluster R i m).min' (rankCluster_nonempty hR i hm1)) < m := by
  apply lt_of_not_ge
  rw [birth_cluster_iff hR i _ hm (Finset.min'_mem _ _)]
  rintro ⟨k,hk,hlt⟩
  exact (not_lt_of_ge (Finset.min'_le _ k hk)) hlt

lemma le_rankBirth_of_not_min {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i j : Fin n) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hj : j ∈ rankCluster R i m)
    (hne : j ≠ (rankCluster R i m).min' (rankCluster_nonempty hR i hm1)) :
    m ≤ rankBirth R j := by
  rw [birth_cluster_iff hR i j hm hj]
  exact ⟨_, Finset.min'_mem _ _, lt_of_le_of_ne (Finset.min'_le _ j hj) (Ne.symm hne)⟩

lemma rankInsert_finiteRank {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (j : Fin n) {v : ℝ} (_hv : v ∈ Set.Icc (0:ℝ) 1) : FiniteRank (rankInsert R j v) := by
  have hb0 := rankBirth_nonneg R j
  have hb1 := rankBirth_le_one hR j
  have hL0 : ∀ i, 0 ≤ rankLink R j v i := fun i => le_min (hR.2.2.1 i j).1 (le_max_of_le_left hb0)
  have hL1 : ∀ i, rankLink R j v i ≤ 1 := fun i => min_le_left _ _ |>.trans (hR.2.2.1 i j).2
  have hU1 : ∀ i k, min (rankLink R j v i) (rankLink R j v k) ≤ R i k := by
    intro i k
    apply le_trans _ (hR.2.2.2 i j k)
    exact min_le_min (min_le_left _ _) ((min_le_left _ _).trans_eq (hR.2.1 k j))
  have hU2 : ∀ i k, min (R i k) (rankLink R j v k) ≤ rankLink R j v i := by
    intro i k
    apply le_min
    · exact (min_le_min_left _ (min_le_left _ _)).trans (hR.2.2.2 i k j)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨?_,?_,?_,?_⟩
  · intro a; refine Fin.lastCases ?_ (fun i => ?_) a
    · simp [rankInsert]
    · simpa [rankInsert] using hR.1 i
  · intro a b; refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun k => ?_) b
    all_goals simp [rankInsert, hR.2.1]
  · intro a b; refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun k => ?_) b
    all_goals simp only [rankInsert, Fin.lastCases_last, Fin.lastCases_castSucc]
    · norm_num
    · exact ⟨hL0 _,hL1 _⟩
    · exact ⟨hL0 _,hL1 _⟩
    · exact hR.2.2.1 _ _
  · intro a b c
    refine Fin.lastCases ?_ (fun i => ?_) a <;>
      refine Fin.lastCases ?_ (fun k => ?_) b <;>
        refine Fin.lastCases ?_ (fun l => ?_) c
    all_goals simp only [rankInsert, Fin.lastCases_last, Fin.lastCases_castSucc]
    · simp
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hL1 _)
    · rw [min_comm, hR.2.1 k l]; exact hU2 _ _
    · exact min_le_left _ _
    · exact hU1 _ _
    · exact hU2 _ _
    · exact hR.2.2.2 _ _ _
end MicroscopicJamming

 
open MeasureTheory Set
open scoped NNReal BigOperators

namespace MicroscopicJamming

lemma continuous_rankBirth {n : ℕ} (j : Fin n) :
    Continuous (fun R : Fin n → Fin n → ℝ => rankBirth R j) := by
  unfold rankBirth
  apply NNReal.continuous_coe.comp
  apply Continuous.finset_sup_apply
  intro i _
  fun_prop

lemma continuous_rankInsert_fixed {n : ℕ} (j : Fin n) :
    Continuous (fun z : (Fin n → Fin n → ℝ) × ℝ => rankInsert z.1 j z.2) := by
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun k => ?_) b
  all_goals simp only [rankInsert, Fin.lastCases_last, Fin.lastCases_castSucc, rankLink]
  · exact continuous_const
  · exact (show Continuous (fun z : (Fin n → Fin n → ℝ) × ℝ => z.1 k j) by fun_prop).min
      (((continuous_rankBirth j).comp continuous_fst).max continuous_snd)
  · exact (show Continuous (fun z : (Fin n → Fin n → ℝ) × ℝ => z.1 i j) by fun_prop).min
      (((continuous_rankBirth j).comp continuous_fst).max continuous_snd)
  · fun_prop

lemma continuous_rankInsert (n : ℕ) :
    Continuous (fun z : (Fin n → Fin n → ℝ) × (Fin n × ℝ) =>
      rankInsert z.1 z.2.1 z.2.2) := by
  have h : Continuous (fun z : Fin n × ((Fin n → Fin n → ℝ) × ℝ) =>
      rankInsert z.2.1 z.1 z.2.2) :=
    continuous_prod_of_discrete_left.mpr continuous_rankInsert_fixed
  exact h.comp (show Continuous (fun z : (Fin n → Fin n → ℝ) × (Fin n × ℝ) =>
    (z.2.1,(z.1,z.2.2))) by fun_prop)

lemma rankLink_volume {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i j : Fin n) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    (volume {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R j v i}).toReal =
      (if j ∈ rankCluster R i m then (1:ℝ) else 0) -
        (if j = (rankCluster R i m).min' (rankCluster_nonempty hR i hm1) then m else 0) := by
  classical
  let C := rankCluster R i m
  let b : Fin n := C.min' (rankCluster_nonempty hR i hm1)
  by_cases hj : j ∈ C
  · by_cases hje : j=b
    · subst j
      have hb := rankBirth_lt_at_min hR i hm hm1
      have hi : m ≤ R i b := (Finset.mem_filter.mp (Finset.min'_mem C _)).2
      have he : {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R b v i} = Set.Icc m 1 := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_Icc, rankLink, le_min_iff, le_max_iff]
        have hh : ¬ m ≤ rankBirth R b := not_le.mpr hb
        simp only [hi,hh,false_or,true_and]
        constructor
        · rintro ⟨⟨_,hv⟩,hmv⟩; exact ⟨hmv,hv⟩
        · rintro ⟨hmv,hv⟩; exact ⟨⟨hm.le.trans hmv,hv⟩,hmv⟩
      rw [he,Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hm1)]
      simp [C,b,Finset.min'_mem]
    · have hb := le_rankBirth_of_not_min hR i j hm hm1 hj hje
      have hi : m ≤ R i j := (Finset.mem_filter.mp hj).2
      have he : {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R j v i} = Set.Icc (0:ℝ) 1 := by
        ext v
        simp [rankLink, le_max_iff, hi, hb]
      rw [he,Real.volume_Icc]
      simp only [sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one]
      simp only [show j ∈ rankCluster R i m from hj, ite_true,
        show j ≠ (rankCluster R i m).min' _ from hje, ite_false, sub_zero]
  · have hi : ¬ m ≤ R i j := by simpa [C,rankCluster] using hj
    have hje : j ≠ b := by rintro rfl; exact hj (Finset.min'_mem C _)
    have he : {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R j v i} = ∅ := by
      ext v; simp [rankLink,hi]
    rw [he,measure_empty,ENNReal.toReal_zero]
    simp only [show j ∉ rankCluster R i m from hj, ite_false,
      show j ≠ (rankCluster R i m).min' _ from hje, sub_self]

lemma rankInsert_cluster_probability {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i : Fin n) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    (∑ j : Fin n, (volume {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R j v i}).toReal) /
      (n:ℝ) = ((rankCluster R i m).card-m)/(n:ℝ) := by
  classical
  simp_rw [rankLink_volume hR i _ hm hm1]
  congr 1
  rw [Finset.sum_sub_distrib]
  simp

 theorem rpcRankInsertion : RPCRankInsertionStatement := by
  refine ⟨?_, continuous_rankInsert, ?_⟩
  · intro n R j v hR hv
    exact rankInsert_finiteRank hR j hv
  · intro n R i m hR hm hm1
    exact rankInsert_cluster_probability hR i hm hm1
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace MicroscopicJamming

lemma continuous_rankGrowing (n : ℕ) : Continuous (rankGrowing n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact (continuous_rankInsert (n+1)).comp (ih.prodMk (continuous_apply n))

lemma rankGrowing_stable {n N : ℕ} (h : n ≤ N) (z : RankSeed) (i j : Fin (n+1)) :
    rankGrowing N z (Fin.castLE (Nat.succ_le_succ h) i) (Fin.castLE (Nat.succ_le_succ h) j) =
      rankGrowing n z i j := by
  induction N with
  | zero =>
    have hn : n=0 := Nat.eq_zero_of_le_zero h
    subst n
    simp
  | succ N ih =>
    by_cases hn : n=N+1
    · subst n; simp
    · have hnN : n ≤ N := by omega
      change rankInsert (rankGrowing N z) (z N).1 (z N).2
        (Fin.castLE (Nat.succ_le_succ hnN) i).castSucc
        (Fin.castLE (Nat.succ_le_succ hnN) j).castSucc = _
      simp only [rankInsert,Fin.lastCases_castSucc]
      exact ih hnN

lemma realizedRank_stage (n : ℕ) (z : RankSeed) (i j : Fin (n+1)) :
    realizedRank z i j=rankGrowing n z i j := by
  have h : max i.val j.val ≤ n := max_le (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt)
  have hh := rankGrowing_stable h z
    (⟨i.val,Nat.lt_succ_of_le (le_max_left _ _)⟩ : Fin (max i.val j.val+1))
    (⟨j.val,Nat.lt_succ_of_le (le_max_right _ _)⟩ : Fin (max i.val j.val+1))
  exact hh.symm

lemma continuous_realizedRank : Continuous realizedRank := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply _).comp ((continuous_apply _).comp (continuous_rankGrowing (max i j))))

lemma rankGrowing_finiteRank {z : RankSeed} (hz : ∀ k, (z k).2 ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    FiniteRank (rankGrowing n z) := by
  induction n with
  | zero =>
    refine ⟨fun i => rfl,fun i j => rfl,fun i j => ?_,fun i j k => ?_⟩
    · norm_num [rankGrowing]
    · simp [rankGrowing]
  | succ n ih => exact rankInsert_finiteRank ih (z n).1 (hz n)

lemma realizedRank_constraints {z : RankSeed} (hz : ∀ k, (z k).2 ∈ Set.Icc (0:ℝ) 1) :
    (∀ i, realizedRank z i i=1) ∧ (∀ i j, realizedRank z i j=realizedRank z j i) ∧
    (∀ i j, 0 ≤ realizedRank z i j ∧ realizedRank z i j ≤ 1) ∧
    (∀ i j k, min (realizedRank z i j) (realizedRank z j k) ≤ realizedRank z i k) := by
  have hpair (i j : ℕ) :
      realizedRank z i j=rankGrowing (max i j) z
        ⟨i,Nat.lt_succ_of_le (le_max_left _ _)⟩ ⟨j,Nat.lt_succ_of_le (le_max_right _ _)⟩ := rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    exact (realizedRank_stage i z (Fin.last i) (Fin.last i)).trans
      ((rankGrowing_finiteRank hz i).1 (Fin.last i))
  · intro i j
    let a : Fin (max i j+1) := ⟨i,Nat.lt_succ_of_le (le_max_left _ _)⟩
    let b : Fin (max i j+1) := ⟨j,Nat.lt_succ_of_le (le_max_right _ _)⟩
    change realizedRank z a b=realizedRank z b a
    rw [realizedRank_stage,realizedRank_stage]
    exact (rankGrowing_finiteRank hz _).2.1 _ _
  · intro i j
    rw [hpair]
    exact (rankGrowing_finiteRank hz _).2.2.1 _ _
  · intro i j k
    let n := max (max i j) k
    let a : Fin (n+1) := ⟨i,Nat.lt_succ_of_le ((le_max_left i j).trans (le_max_left _ _))⟩
    let b : Fin (n+1) := ⟨j,Nat.lt_succ_of_le ((le_max_right i j).trans (le_max_left _ _))⟩
    let c : Fin (n+1) := ⟨k,Nat.lt_succ_of_le (le_max_right _ _)⟩
    change min (realizedRank z a b) (realizedRank z b c) ≤ realizedRank z a c
    rw [realizedRank_stage,realizedRank_stage,realizedRank_stage]
    exact (rankGrowing_finiteRank hz n).2.2.2 a b c

lemma realizedRank_pair {z : RankSeed} (hz : (z 0).2 ∈ Set.Icc (0:ℝ) 1) :
    realizedRank z 0 1 = (z 0).2 := by
  have hj : (z 0).1 = 0 := by
    apply Fin.ext
    have h := (z 0).1.isLt
    change (z 0).1.val = 0
    omega
  change rankGrowing 1 z (0 : Fin 2) (Fin.last 1) = _
  change rankInsert (rankGrowing 0 z) (z 0).1 (z 0).2 (Fin.castSucc 0) (Fin.last 1) = _
  simp only [rankInsert,Fin.lastCases_castSucc,Fin.lastCases_last,rankLink,hj,rankGrowing]
  have hb : rankBirth (fun _ _ : Fin 1 => (1:ℝ)) 0 = 0 := by
    simp [rankBirth]
  rw [hb,max_eq_right hz.1,min_eq_right hz.2]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace MicroscopicJamming

instance rankUnitInterval_probability : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  ⟨by simp [Real.volume_Icc]⟩

instance rankInnovationLaw_probability (n : ℕ) : IsProbabilityMeasure (rankInnovationLaw n) := by
  unfold rankInnovationLaw
  infer_instance

instance rankSeedLaw_probability : IsProbabilityMeasure rankSeedLaw := by
  unfold rankSeedLaw
  infer_instance

instance realizedRankLaw_probability : IsProbabilityMeasure realizedRankLaw := by
  unfold realizedRankLaw
  infer_instance

lemma rankInnovation_second (n : ℕ) :
    (rankInnovationLaw n).map Prod.snd = volume.restrict (Set.Icc (0:ℝ) 1) := by
  simp [rankInnovationLaw,Measure.map_snd_prod]

lemma rankSeed_coordinate (n : ℕ) :
    rankSeedLaw.map (fun z => (z n).2) = volume.restrict (Set.Icc (0:ℝ) 1) := by
  have h1 : Measurable (fun z : RankSeed => z n) := by fun_prop
  rw [show (fun z : RankSeed => (z n).2) = Prod.snd ∘ (fun z : RankSeed => z n) from rfl,
    ← Measure.map_map measurable_snd h1,rankSeedLaw,Measure.infinitePi_map_eval,rankInnovation_second]

lemma rankSeed_valid : ∀ᵐ z ∂rankSeedLaw, ∀ n, (z n).2 ∈ Set.Icc (0:ℝ) 1 := by
  rw [ae_all_iff]
  intro n
  have h : ∀ᵐ v ∂rankSeedLaw.map (fun z => (z n).2), v ∈ Set.Icc (0:ℝ) 1 := by
    rw [rankSeed_coordinate]
    exact ae_restrict_mem measurableSet_Icc
  exact ae_of_ae_map (show Measurable (fun z : RankSeed => (z n).2) by fun_prop).aemeasurable h

lemma realizedRankLaw_constraints :
    ∀ᵐ U ∂realizedRankLaw, (∀ i, U i i=1) ∧ (∀ i j, U i j=U j i) ∧
      (∀ i j, 0 ≤ U i j ∧ U i j ≤ 1) ∧
      (∀ i j k, min (U i j) (U j k) ≤ U i k) := by
  apply (ae_map_iff continuous_realizedRank.measurable.aemeasurable ?_).mpr
  · exact rankSeed_valid.mono fun z hz => realizedRank_constraints hz
  · simp only [ofPred_and,ofPred_forall]
    apply MeasurableSet.inter
    · exact MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) measurable_const
    · apply MeasurableSet.inter
      · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_eq_fun (by fun_prop) (by fun_prop)
      · apply MeasurableSet.inter
        · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
            (measurableSet_le measurable_const (by fun_prop)).inter
              (measurableSet_le (by fun_prop) measurable_const)
        · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
            measurableSet_le (by fun_prop) (by fun_prop)

lemma realizedRankLaw_uniform :
    realizedRankLaw.map (fun U => U 0 1) = volume.restrict (Set.Icc (0:ℝ) 1) := by
  rw [realizedRankLaw,Measure.map_map (by fun_prop) continuous_realizedRank.measurable]
  trans rankSeedLaw.map (fun z => (z 0).2)
  · apply Measure.map_congr
    exact rankSeed_valid.mono fun z hz => realizedRank_pair (hz 0)
  · exact rankSeed_coordinate 0

 theorem rpcRankRealization : RPCRankRealizationStatement :=
  ⟨continuous_realizedRank,inferInstance,realizedRank_stage,
    realizedRankLaw_constraints,realizedRankLaw_uniform⟩
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def rankJoinEvent {n : ℕ} (R : Fin (n+1) → Fin (n+1) → ℝ) (i : Fin (n+1)) (m : ℝ) :
    Set (Fin (n+1) × ℝ) := {z | m ≤ rankLink R z.1 z.2 i}

lemma measurableSet_rankJoinEvent {n : ℕ} (R : Fin (n+1) → Fin (n+1) → ℝ)
    (i : Fin (n+1)) (m : ℝ) : MeasurableSet (rankJoinEvent R i m) := by
  apply measurableSet_le measurable_const
  unfold rankLink
  have h1 : Measurable (fun z : Fin (n+1) × ℝ => R i z.1) :=
    (measurable_of_countable (R i)).comp measurable_fst
  have h2 : Measurable (fun z : Fin (n+1) × ℝ => rankBirth R z.1) :=
    (measurable_of_countable (rankBirth R)).comp measurable_fst
  exact h1.min (h2.max measurable_snd)

lemma rankJoinEvent_real {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ} (hR : FiniteRank R)
    (i : Fin (n+1)) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    (rankInnovationLaw n).real (rankJoinEvent R i m) =
      ((rankCluster R i m).card-m)/((n:ℝ)+1) := by
  classical
  have he (j : Fin (n+1)) :
      (volume.restrict (Set.Icc (0:ℝ) 1)) (Prod.mk j ⁻¹' rankJoinEvent R i m) =
        volume {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R j v i} := by
    rw [Measure.restrict_apply ((measurableSet_rankJoinEvent R i m).preimage (by fun_prop))]
    congr 1
    ext v
    simp only [Set.mem_inter_iff,Set.mem_preimage,rankJoinEvent,Set.mem_ofPred_eq]
    exact and_comm
  have hf (j : Fin (n+1)) : volume {v : ℝ | v ∈ Set.Icc (0:ℝ) 1 ∧ m ≤ rankLink R j v i} ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (by intro v hv; exact hv.1)).trans_lt (by simp [Real.volume_Icc])
  unfold Measure.real rankInnovationLaw
  rw [Measure.prod_apply (measurableSet_rankJoinEvent R i m),lintegral_fintype]
  simp_rw [he,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),PMF.uniformOfFintype_apply,
    Fintype.card_fin]
  rw [← Finset.sum_mul,ENNReal.toReal_mul,ENNReal.toReal_sum (fun j _ => hf j)]
  simp only [ENNReal.toReal_inv,Nat.cast_add,Nat.cast_one,← div_eq_mul_inv]
  simpa [ENNReal.toReal_add] using rankInsert_cluster_probability hR i hm hm1

lemma rankJoinEvent_zero {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ} (hR : FiniteRank R)
    (i : Fin (n+1)) : rankJoinEvent R i 0=univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact le_min (hR.2.2.1 i z.1).1 (le_max_of_le_left (rankBirth_nonneg R z.1))

lemma rankJoinEvent_real_nonneg {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ} (hR : FiniteRank R)
    (i : Fin (n+1)) {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1) :
    (rankInnovationLaw n).real (rankJoinEvent R i m) =
      ((rankCluster R i m).card-m)/((n:ℝ)+1) := by
  rcases hm.eq_or_lt with rfl|hm
  · rw [rankJoinEvent_zero hR i]
    have hc : rankCluster R i 0 = Finset.univ := by
      ext j
      simp [rankCluster,(hR.2.2.1 i j).1]
    simp [hc,show (n:ℝ)+1≠0 by positivity]
  · exact rankJoinEvent_real hR i hm hm1

lemma rankLink_parent_le {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (p i j : Fin n) (v : ℝ) : min (R p i) (rankLink R j v i) ≤ rankLink R j v p := by
  unfold rankLink
  exact le_min ((min_le_min_left _ (min_le_left _ _)).trans (hR.2.2.2 p i j))
    ((min_le_right _ _).trans (min_le_right _ _))

lemma rankLink_pair_le {n : ℕ} {R : Fin n → Fin n → ℝ} (hR : FiniteRank R)
    (i k j : Fin n) (v : ℝ) : min (rankLink R j v i) (rankLink R j v k) ≤ R i k := by
  unfold rankLink
  exact (min_le_min (min_le_left _ _) ((min_le_left _ _).trans_eq (hR.2.1 k j))).trans
    (hR.2.2.2 i j k)

lemma rankJoinEvent_subset {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ} (hR : FiniteRank R)
    (p i : Fin (n+1)) {η m : ℝ} (hηm : η ≤ m) (hpi : η ≤ R p i) :
    rankJoinEvent R i m ⊆ rankJoinEvent R p η := by
  intro z hz
  exact (le_min hpi (hηm.trans hz)).trans (rankLink_parent_le hR p i z.1 z.2)

lemma rankJoinEvent_disjoint {n : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ} (hR : FiniteRank R)
    (i k : Fin (n+1)) {m : ℝ} (hik : R i k < m) :
    Disjoint (rankJoinEvent R i m) (rankJoinEvent R k m) := by
  apply Set.disjoint_left.mpr
  intro z hi hk
  exact not_le_of_gt hik ((le_min hi hk).trans (rankLink_pair_le hR i k z.1 z.2))

 

lemma rankFreshBranch_real {n r : ℕ} {R : Fin (n+1) → Fin (n+1) → ℝ}
    (hR : FiniteRank R) (p : Fin (n+1)) (c : Fin r → Fin (n+1))
    {η m : ℝ} (hη : 0 ≤ η) (hηm : η ≤ m) (hm : 0 < m) (hm1 : m ≤ 1)
    (hparent : ∀ a, η ≤ R p (c a))
    (hchild : ∀ a b, a ≠ b → R (c a) (c b) < m)
    (hcover : (rankCluster R p η).card = ∑ a, (rankCluster R (c a) m).card) :
    (rankInnovationLaw n).real
      (rankJoinEvent R p η \ ⋃ a, rankJoinEvent R (c a) m) =
        ((r:ℝ)*m-η)/((n:ℝ)+1) := by
  have hsub : (⋃ a, rankJoinEvent R (c a) m) ⊆ rankJoinEvent R p η := by
    simp only [iUnion_subset_iff]
    exact fun a => rankJoinEvent_subset hR p (c a) hηm (hparent a)
  rw [measureReal_sdiff hsub (MeasurableSet.iUnion (fun a => measurableSet_rankJoinEvent R (c a) m))]
  rw [rankJoinEvent_real_nonneg hR p hη (hηm.trans hm1),
    measureReal_iUnion_fintype (fun a b hab => rankJoinEvent_disjoint hR _ _ (hchild a b hab))
      (fun a => measurableSet_rankJoinEvent R (c a) m)]
  simp_rw [rankJoinEvent_real hR _ hm hm1]
  rw [← Finset.sum_div,Finset.sum_sub_distrib]
  push_cast [hcover]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

end MicroscopicJamming

end

end OAI
