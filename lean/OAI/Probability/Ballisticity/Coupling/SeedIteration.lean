import Mathlib
import OAI.Probability.Ballisticity.Estimates.RawPair
import OAI.Probability.Ballisticity.Coupling.SeedStateOrder

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def seedHeight (a : ℤ) (H : ℕ) : ℕ → ℤ
  | 0 => a
  | n+1 => seedHeight a H n+H

lemma seedHeight_eq (a : ℤ) (H n : ℕ) : seedHeight a H n=a+(n:ℤ)*H := by
  induction n with
  | zero => simp [seedHeight]
  | succ n ih => simp only [seedHeight,ih,Nat.cast_add,Nat.cast_one]; ring

lemma seedHeight_mono (a : ℤ) (H : ℕ) : Monotone (seedHeight a H) := by
  intro m n hmn
  rw [seedHeight_eq,seedHeight_eq]
  have hm : (m:ℤ) ≤ n := by exact_mod_cast hmn
  exact add_le_add_right (mul_le_mul_of_nonneg_right hm (Int.natCast_nonneg H)) a

lemma seedBelow_mono {d : ℕ} (e : Direction d) {a b : ℤ} (h : a≤b) : seedBelow e a ⊆ seedBelow e b := fun _ hx => hx.trans_le h

noncomputable def seedRun {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) : (n : ℕ) → Environment d → SeedState e (seedHeight a H n)
  | 0, _ => q
  | n+1, ω => seedStateStep e f (seedHeight a H n) s k H θ z b j
      (seedRun e f a s k H θ z b j q n ω) ω

lemma seedRun_measurable {d : ℕ} (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (q : SeedState e a) (n : ℕ) :
    @Measurable _ _ (rowSigma (seedBelow e (seedHeight a H n))) _ (seedRun e f a s k H θ z b j q n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hle := rowSigma_mono (seedBelow_mono e (seedHeight_mono a H (Nat.le_succ n)))
    exact (seedStateStep_joint_rows e f (seedHeight a H n) s k hH θ z b j
      (seedBelow e (seedHeight a H n+H)) (strip_subset_seedBelow e (seedHeight a H n) H)).comp
        ((ih.mono hle le_rfl).prodMk measurable_id)

lemma seedRun_count_step {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (n : ℕ) (ω : Environment d) :
    (seedRun e f a s k H θ z b j q n ω).1 ≤ (seedRun e f a s k H θ z b j q (n+1) ω).1 ∧
    (seedRun e f a s k H θ z b j q (n+1) ω).1 ≤ (seedRun e f a s k H θ z b j q n ω).1+1 :=
  (seedStateStep_count e f (seedHeight a H n) s k H θ z b j _ ω).imp_right And.left

lemma seedRun_count_mono {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (ω : Environment d) :
    Monotone (fun n => (seedRun e f a s k H θ z b j q n ω).1) :=
  monotone_nat_of_le_succ fun n => (seedRun_count_step e f a s k H θ z b j q n ω).1

lemma seedRun_count_bounds {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j : ℝ) (q : SeedState e a) (hq : 0<q.1) (hqk : q.1≤k) (n : ℕ) (ω : Environment d) :
    0<(seedRun e f a s k H θ z b j q n ω).1 ∧ (seedRun e f a s k H θ z b j q n ω).1≤k := by
  induction n with
  | zero => exact ⟨hq,hqk⟩
  | succ n ih => exact ⟨ih.1.trans_le (seedRun_count_step e f a s k H θ z b j q n ω).1,
      (seedStateStep_count e f (seedHeight a H n) s k H θ z b j _ ω).2.2 ih.2⟩

lemma seedEndpointRaw_zero {d : ℕ} (e : Direction d) (μ : Measure (Lattice d)) (ω : Environment d) :
    seedEndpointRaw e 0 (fun _ _ => True) μ ω=μ := by
  simp only [seedEndpointRaw,Set.ofPred_true,Measure.restrict_univ]
  have he (x : Lattice d) : variableHitKernel (realPosition (step e)) 0 (ω,x)=Measure.dirac x :=
    by
      simpa only [variableHitKernel,Kernel.coe_mk,Nat.cast_zero] using
        hitKernel_height_zero (realPosition (step e)) x ω
  simp_rw [he]
  exact Measure.bind_dirac

lemma seedRun_retained {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0≤j) (hc : 0≤c)
    (n : ℕ) (ω : Environment d)
    (hp : ∀ t<n, SeedPreserved e f (seedHeight a H t) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) t ω) ω) :
    SeedStateRetained e (seedHeight a H n) (n*H) μ.measure ω
      ((ENNReal.ofReal (min c j)/2)^n) (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) := by
  induction n with
  | zero =>
    intro i hi
    simp only [seedRun,pow_zero,one_smul,Nat.zero_mul,seedEndpointRaw_zero]
    exact le_rfl
  | succ n ih =>
    have hh := seedStateStep_retained e f (seedHeight a H n) s k H (n*H) θ z b j c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω μ.measure
      ((ENNReal.ofReal (min c j)/2)^n)
      (seedRun_count_bounds e f a s k H θ z b j (1,fun _ => μ) (by norm_num) hk n ω).1 hj hc
      (ih (fun t ht => hp t (ht.trans (Nat.lt_succ_self n)))) (hp n (Nat.lt_succ_self n))
    simpa only [seedRun,seedHeight,Nat.add_mul,Nat.one_mul,pow_succ] using hh

lemma seedRun_ordered {d : ℕ} (e f : Direction d) (a s : ℤ) (k H : ℕ)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0<j) (hc : 0<c)
    (hs : s=1 ∨ s= -1) (hz : 0≤z) (n : ℕ) (ω : Environment d)
    (hg : 0≤b+z-2*(n:ℝ)*z)
    (hp : ∀ t<n, SeedPreserved e f (seedHeight a H t) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) t ω) ω) :
    SeedStateOrdered f s (b+z-2*(n:ℝ)*z) (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) := by
  induction n with
  | zero => intro i t hit ht; change t<1 at ht; omega
  | succ n ih =>
    have hn : (n:ℝ)+1=(n+1:ℕ) := by norm_num
    have hgprev : 0≤b+z-2*(n:ℝ)*z := by push_cast at hg; nlinarith
    apply seedStateStep_ordered e f (seedHeight a H n) s k H θ z b j c (b+z-2*(n:ℝ)*z) _ _ ω hs
      (seedRun_count_bounds e f a s k H θ z b j (1,fun _ => μ) (by norm_num) hk n ω).1 hj hc hg
    · push_cast; ring_nf; exact le_rfl
    · push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    · exact ih hgprev (fun t ht => hp t (ht.trans (Nat.lt_succ_self n)))
    · exact hp n (Nat.lt_succ_self n)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedPreserved_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k H : ℕ) (θ z c : ℝ) (ε : ℝ≥0∞)
    (hc : ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e H (SeedCentral f H θ z) μ.toMeasure ω Set.univ).toReal<c} ≤ ε)
    (q : SeedState e a) (hq : q.1≤k) :
    environmentLaw ν {ω | ¬SeedPreserved e f a s k H θ z c q ω} ≤ k*ε := by
  have hs : {ω | ¬SeedPreserved e f a s k H θ z c q ω} ⊆ ⋃ i∈Finset.range k,
      {ω | (seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k q i).measure ω Set.univ).toReal<c} := by
    intro ω hω
    obtain ⟨i,hi⟩ := not_forall.mp hω
    have hi' : i<q.1 := by by_contra h; exact hi (fun h' => (h h').elim)
    have hm := not_le.mp (fun h => hi (fun _ => h))
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (hi'.trans_le hq),hm⟩⟩
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ ∑ i∈Finset.range k, environmentLaw ν {ω |
      (seedEndpointRaw e H (SeedCentral f H θ z) (seedCentralInput e f a s k q i).measure ω Set.univ).toReal<c} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i∈Finset.range k, ε := Finset.sum_le_sum fun i _ => hc (seedCentralInput e f a s k q i).val
    _ = _ := by simp

lemma seedRun_preservation_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j c : ℝ) (ε : ℝ≥0∞) (μ : SeedProfile e a) (hk : 1≤k)
    (hc : ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e H (SeedCentral f H θ z) μ.toMeasure ω Set.univ).toReal<c} ≤ ε)
    (J : ℕ) : environmentLaw ν {ω | ∃ n<J, ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} ≤ J*(k*ε) := by
  have hb (n : ℕ) : environmentLaw ν {ω | ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} ≤ k*ε := by
    have hh := seed_fresh_test_bound ν e (seedHeight a H n)
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n)
      (seedRun_measurable e f a s k hH θ z b j _ n) Set.univ MeasurableSet.univ
      {p | ¬SeedPreserved e f (seedHeight a H n) s k H θ z c p.1 p.2}
      (seedPreserved_joint_rows e f (seedHeight a H n) s k hH θ z c (seedAbove e (seedHeight a H n))
        (strip_subset_seedAbove e (seedHeight a H n) H)).compl (k*ε)
      (fun η _ => seedPreserved_failure_bound ν e f (seedHeight a H n) s k H θ z c ε hc _
        (seedRun_count_bounds e f a s k H θ z b j (1,fun _ => μ) (by norm_num) hk n η).2)
    simpa only [Set.mem_univ,true_and,measure_univ,mul_one,Set.mem_ofPred_eq] using hh
  have he : {ω | ∃ n<J, ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} = ⋃ n∈Finset.range J,
      {ω | ¬SeedPreserved e f (seedHeight a H n) s k H θ z c
      (seedRun e f a s k H θ z b j (1,fun _ => μ) n ω) ω} := by ext ω; simp
  rw [he]
  exact (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum fun n _ => hb n).trans_eq (by simp))

lemma seedRun_stall_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (q : SeedState e a) (ρ : ℝ≥0∞)
    (hf : ∀ (a : ℤ) (q : SeedState e a), environmentLaw ν {ω | ¬seedSplitTest e f a s H θ b j q ω}≤ρ)
    (u N : ℕ) : environmentLaw ν {ω | (seedRun e f a s k H θ z b j q u ω).1<k ∧
      (seedRun e f a s k H θ z b j q (u+N) ω).1=(seedRun e f a s k H θ z b j q u ω).1} ≤ ρ^N := by
  let run := seedRun e f a s k H θ z b j q
  let E := fun n => {ω : Environment d | (run u ω).1<k ∧ (run (u+n) ω).1=(run u ω).1}
  have hm (n : ℕ) : MeasurableSet[rowSigma (seedBelow e (seedHeight a H (u+n)))] (E n) := by
    have hn := (measurable_fst.comp (seedRun_measurable e f a s k hH θ z b j q (u+n)))
    have hu := (measurable_fst.comp (seedRun_measurable e f a s k hH θ z b j q u)).mono
      (rowSigma_mono (seedBelow_mono e (seedHeight_mono a H (Nat.le_add_right u n)))) le_rfl
    exact (measurableSet_lt hu measurable_const).inter (measurableSet_eq_fun hn hu)
  have hb (n : ℕ) : environmentLaw ν (E (n+1)) ≤ ρ*environmentLaw ν (E n) := by
    have hs : E (n+1) ⊆ {ω | ω∈E n ∧ ¬seedSplitTest e f (seedHeight a H (u+n)) s H θ b j (run (u+n) ω) ω} := by
      intro ω hω
      change (run u ω).1<k ∧ (run (u+(n+1)) ω).1=(run u ω).1 at hω
      have hmono := seedRun_count_mono e f a s k H θ z b j q ω
      have hlow := hmono (Nat.le_add_right u n)
      have hhigh := hmono (show u+n≤u+(n+1) by omega)
      change (run u ω).1 ≤ (run (u+n) ω).1 at hlow
      change (run (u+n) ω).1 ≤ (run (u+(n+1)) ω).1 at hhigh
      have he : (run (u+n) ω).1=(run u ω).1 := by omega
      refine ⟨⟨hω.1,he⟩,fun ht => ?_⟩
      have ht' := seedStateStep_strict e f (seedHeight a H (u+n)) s k H θ z b j (run (u+n) ω) ω (he.symm ▸ hω.1) ht
      change (run (u+n) ω).1<(run (u+n+1) ω).1 at ht'
      have he' : (run (u+n+1) ω).1=(run u ω).1 :=
        (congrArg (fun t => (run t ω).1) (by omega : u+n+1=u+(n+1))).trans hω.2
      omega
    apply (measure_mono hs).trans
    exact seed_fresh_test_bound ν e (seedHeight a H (u+n)) (run (u+n))
      (seedRun_measurable e f a s k hH θ z b j q (u+n)) (E n) (hm n)
      {p | ¬seedSplitTest e f (seedHeight a H (u+n)) s H θ b j p.1 p.2}
      (seedSplitTest_joint_rows e f (seedHeight a H (u+n)) s hH θ b j (seedAbove e (seedHeight a H (u+n)))
        (strip_subset_seedAbove e (seedHeight a H (u+n)) H)).compl ρ (fun η _ => hf _ _)
  change environmentLaw ν (E N)≤ρ^N
  induction N with
  | zero => simpa using (measure_mono (μ:=environmentLaw ν) (Set.subset_univ (E 0)))
  | succ n ih =>
    calc
      _ ≤ ρ*environmentLaw ν (E n) := hb n
      _ ≤ ρ*ρ^n := by gcongr
      _ = ρ^(n+1) := by rw [pow_succ,mul_comm]

lemma monotone_count_failure_stall (v : ℕ → ℕ) (hv : Monotone v) (hzero : 1≤v 0)
    (k N : ℕ) (hk : 1≤k) (hfail : v ((k-1)*N)<k) :
    ∃ l<k-1, v (l*N)<k ∧ v ((l+1)*N)=v (l*N) := by
  by_contra h
  have hstrict (l : ℕ) (hl : l<k-1) : v (l*N)<v ((l+1)*N) := by
    have he : v ((l+1)*N)≠v (l*N) := fun he => h ⟨l,hl,
      (hv (Nat.mul_le_mul_right N (by omega))).trans_lt hfail,he⟩
    exact lt_of_le_of_ne (hv (Nat.mul_le_mul_right N (Nat.le_succ l))) (Ne.symm he)
  have hcount (l : ℕ) (hl : l≤k-1) : l+1≤v (l*N) := by
    induction l with
    | zero => simpa using hzero
    | succ l ih => have hh := hstrict l (by omega); have hi := ih (by omega); omega
  have hf := hcount (k-1) le_rfl
  omega

lemma seedRun_completion_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k : ℕ) {H : ℕ} (hH : 0<H)
    (θ z b j : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (ρ : ℝ≥0∞)
    (hf : ∀ (a : ℤ) (q : SeedState e a), environmentLaw ν {ω | ¬seedSplitTest e f a s H θ b j q ω}≤ρ)
    (N : ℕ) : environmentLaw ν {ω | (seedRun e f a s k H θ z b j (1,fun _ => μ) ((k-1)*N) ω).1<k} ≤ (k-1:ℕ)*ρ^N := by
  let run := seedRun e f a s k H θ z b j (1,fun _ => μ)
  let E := fun l => {ω : Environment d | (run (l*N) ω).1<k ∧ (run (l*N+N) ω).1=(run (l*N) ω).1}
  have hs : {ω | (run ((k-1)*N) ω).1<k} ⊆ ⋃ l∈Finset.range (k-1), E l := by
    intro ω hω
    obtain ⟨l,hl,hcount,he⟩ := monotone_count_failure_stall (fun n => (run n ω).1)
      (seedRun_count_mono e f a s k H θ z b j _ ω) (by exact le_rfl) k N hk hω
    exact Set.mem_iUnion.mpr ⟨l,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hl,hcount,(congrArg (fun t => (run t ω).1) (by simp [Nat.add_mul] : l*N+N=(l+1)*N)).trans he⟩⟩
  calc
    _ ≤ _ := measure_mono hs
    _ ≤ ∑ l∈Finset.range (k-1), environmentLaw ν (E l) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _l∈Finset.range (k-1), ρ^N := Finset.sum_le_sum fun l _ => seedRun_stall_probability ν e f a s k hH θ z b j _ ρ hf (l*N) N
    _ = _ := by simp

end DirectionalTransience

end

end OAI
