import Mathlib
import OAI.Probability.Ballisticity.Coupling.SeedIteration

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def SeedOptions {d : ℕ} (f : Direction d) (k : ℕ) (s : ℤ) (g : ℝ)
    (δ : ℝ≥0∞) (ρ : Measure (Lattice d)) : Prop :=
  ∃ μ : Fin k → ProbabilityMeasure (Lattice d),
    (∀ i, δ • (μ i).toMeasure ≤ ρ) ∧
    ∀ i j, i<j → SeedOrdered f s g (μ i).toMeasure (μ j).toMeasure

lemma seedOptions_of_run {d : ℕ} (e f : Direction d) (a s : ℤ) (k h J L : ℕ)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0<j) (hc : 0<c)
    (hs : s=1 ∨ s= -1) (hz : 0≤z) (ω : Environment d)
    (hg : 0≤b+z-2*(J:ℝ)*z)
    (hcount : (seedRun e f a s k h θ z b j (1,fun _ => μ) J ω).1=k)
    (hp : ∀ t<J, SeedPreserved e f (seedHeight a h t) s k h θ z c
      (seedRun e f a s k h θ z b j (1,fun _ => μ) t ω) ω)
    (ht : ∀ i<k, c≤(seedEndpointRaw e L (SeedCentral f L θ z)
      ((seedRun e f a s k h θ z b j (1,fun _ => μ) J ω).2 i).measure ω Set.univ).toReal) :
    SeedOptions f k s (b-z-2*(J:ℝ)*z)
      (((ENNReal.ofReal (min c j)/2)^J)*ENNReal.ofReal c)
      (seedEndpointRaw e (J*h+L) (fun _ _ => True) μ.measure ω) := by
  let q := seedRun e f a s k h θ z b j (1,fun _ => μ) J ω
  refine ⟨fun i => (seedAdvance e (seedHeight a h J) L (SeedCentral f L θ z) (q.2 i) ω).val,?_,?_⟩
  · intro i
    have hr := seedRun_retained e f a s k h θ z b j c μ hk hj.le hc.le J ω hp i.val (hcount.symm ▸ i.isLt)
    have hm : ENNReal.ofReal c ≤ seedEndpointRaw e L (SeedCentral f L θ z) (q.2 i).measure ω Set.univ := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal (ht i.val i.isLt)
    exact seedAdvance_retained e (seedHeight a h J) (J*h) L (SeedCentral f L θ z) μ.measure (q.2 i) ω _ _ hr hm
  · intro i t hit
    have ho := seedRun_ordered e f a s k h θ z b j c μ hk hj hc hs hz J ω hg hp i.val t.val hit (hcount.symm ▸ t.isLt)
    have hm (i : Fin k) : seedEndpointRaw e L (SeedCentral f L θ z) (q.2 i).measure ω Set.univ≠0 := by
      intro he
      have hh := ht i.val i.isLt
      change c≤(seedEndpointRaw e L (SeedCentral f L θ z) (q.2 i).measure ω Set.univ).toReal at hh
      rw [he,ENNReal.toReal_zero] at hh
      exact (not_le_of_gt hc) hh
    have hh := seedOrdered_central e f (seedHeight a h J) s L θ z (b+z-2*(J:ℝ)*z) hs (q.2 i) (q.2 t) ω (hm i) (hm t) ho
    convert hh using 1 <;> first | rfl | ring

lemma seed_tail_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a : ℤ) (k : ℕ) {L : ℕ} (hL : 0<L) (θ z c : ℝ) (ε : ℝ≥0∞)
    (μ : Environment d → ℕ → SeedProfile e a)
    (hμ : @Measurable _ _ (rowSigma (seedBelow e a)) _ μ)
    (hc : ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e L (SeedCentral f L θ z) μ.toMeasure ω Set.univ).toReal<c} ≤ ε) :
    environmentLaw ν {ω | ∃ i<k, (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal<c} ≤ k*ε := by
  have hb (i : ℕ) : environmentLaw ν {ω | (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal<c}≤ε := by
    have hh := seed_fresh_test_bound ν e a (fun ω => μ ω i) ((measurable_pi_apply i).comp hμ)
      Set.univ MeasurableSet.univ
      {p : SeedProfile e a × Environment d | (seedEndpointRaw e L (SeedCentral f L θ z) p.1.measure p.2 Set.univ).toReal<c}
      (measurableSet_lt (seedProfileRaw_joint_rows e a hL (SeedCentral f L θ z) (seedAbove e a)
        (strip_subset_seedAbove e a L)) measurable_const) ε (fun η _ => hc (μ η i).val)
    simpa only [Set.mem_univ,true_and,Set.mem_ofPred_eq,measure_univ,mul_one] using hh
  have he : {ω | ∃ i<k, (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal<c} = ⋃ i∈Finset.range k,
      {ω | (seedEndpointRaw e L (SeedCentral f L θ z) (μ ω i).measure ω Set.univ).toReal<c} := by ext ω; simp
  rw [he]
  exact (measure_biUnion_finset_le _ _).trans ((Finset.sum_le_sum fun i _ => hb i).trans_eq (by simp))

lemma seedOptions_failure_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (a s : ℤ) (k N : ℕ) {h L : ℕ} (hh : 0<h) (hL : 0<L)
    (θ z b j c : ℝ) (μ : SeedProfile e a) (hk : 1≤k) (hj : 0<j) (hc : 0<c)
    (hs : s=1 ∨ s= -1) (hz : 0≤z) (ε ρ : ℝ≥0∞)
    (hg : 0≤b+z-2*((k-1)*N:ℕ)*z)
    (hclip : ∀ t∈({h,L}:Finset ℕ), ∀ μ : ProbabilityMeasure (Lattice d), environmentLaw ν {ω |
      (seedEndpointRaw e t (SeedCentral f t θ z) μ.toMeasure ω Set.univ).toReal<c}≤ε)
    (hjump : ∀ (a : ℤ) (q : SeedState e a), environmentLaw ν {ω | ¬seedSplitTest e f a s h θ b j q ω}≤ρ) :
    environmentLaw ν {ω | ¬SeedOptions f k s (b-z-2*((k-1)*N:ℕ)*z)
      (((ENNReal.ofReal (min c j)/2)^((k-1)*N))*ENNReal.ofReal c)
      (seedEndpointRaw e (((k-1)*N)*h+L) (fun _ _ => True) μ.measure ω)} ≤
        (k-1:ℕ)*ρ^N+((k-1)*N:ℕ)*(k*ε)+k*ε := by
  let J := (k-1)*N
  let run := seedRun e f a s k h θ z b j (1,fun _ => μ)
  let A := {ω | (run J ω).1<k}
  let B := {ω | ∃ t<J, ¬SeedPreserved e f (seedHeight a h t) s k h θ z c (run t ω) ω}
  let C := {ω | ∃ i<k, (seedEndpointRaw e L (SeedCentral f L θ z) ((run J ω).2 i).measure ω Set.univ).toReal<c}
  have hA : environmentLaw ν A≤(k-1:ℕ)*ρ^N := seedRun_completion_probability ν e f a s k hh θ z b j μ hk ρ hjump N
  have hB : environmentLaw ν B≤J*(k*ε) := seedRun_preservation_failure ν e f a s k hh θ z b j c ε μ hk (hclip h (by simp)) J
  have hC : environmentLaw ν C≤k*ε := seed_tail_failure_bound ν e f (seedHeight a h J) k hL θ z c ε
    (fun ω => (run J ω).2) (measurable_snd.comp (seedRun_measurable e f a s k hh θ z b j _ J)) (hclip L (by simp))
  have he : {ω | ¬SeedOptions f k s (b-z-2*(J:ℝ)*z)
      (((ENNReal.ofReal (min c j)/2)^J)*ENNReal.ofReal c)
      (seedEndpointRaw e (J*h+L) (fun _ _ => True) μ.measure ω)} ⊆ (A∪B)∪C := by
    intro ω hω
    by_contra hn
    have ha : ω∉A := fun ha => hn (Or.inl (Or.inl ha))
    have hb : ω∉B := fun hb => hn (Or.inl (Or.inr hb))
    have hc' : ω∉C := fun hc => hn (Or.inr hc)
    apply hω
    apply seedOptions_of_run e f a s k h J L θ z b j c μ hk hj hc hs hz ω hg
    · have hcount := (seedRun_count_bounds e f a s k h θ z b j (1,fun _ => μ) (by norm_num) hk J ω).2
      exact le_antisymm hcount (Nat.le_of_not_gt ha)
    · intro t ht
      exact not_not.mp (fun hbad => hb ⟨t,ht,hbad⟩)
    · intro i hi
      exact le_of_not_gt (fun hbad => hc' ⟨i,hi,hbad⟩)
  exact (measure_mono he).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hA hB)) hC))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma seedOrdered_near_impossible {d : ℕ} (f : Direction d) (s : ℤ) (g r : ℝ)
    (hs : s=1 ∨ s= -1) (hg : 2*r<g) (μ ρ : Measure (Lattice d))
    (ho : SeedOrdered f s g μ ρ) (x y z : Lattice d) (hx : μ {x}≠0) (hy : ρ {y}≠0)
    (hxn : |signedCoordinate f x-signedCoordinate f z|<r)
    (hyn : |signedCoordinate f y-signedCoordinate f z|<r) : False := by
  have hh := ho x hx y hy
  rw [abs_lt] at hxn hyn
  rcases hs with rfl | rfl <;> norm_num at hh <;> linarith [hxn.1,hxn.2,hyn.1,hyn.2]

lemma seedOptions_avoid_mass {d k n : ℕ} (f : Direction d) (s : ℤ) (g r : ℝ)
    (hs : s=1 ∨ s= -1) (hg : 2*r<g) (δ : ℝ≥0∞) (ρ : Measure (Lattice d))
    (ho : SeedOptions f k s g δ ρ) (hn : n<k) (v : Fin n → Lattice d) :
    δ ≤ ρ {x | ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|} := by
  obtain ⟨μ,hdom,hord⟩ := ho
  have hex : ∃ i : Fin k, ∀ x, (μ i).toMeasure {x}≠0 → ∀ j : Fin n,
      r≤|signedCoordinate f x-signedCoordinate f (v j)| := by
    by_contra hnex
    have hbad (i : Fin k) : ∃ j : Fin n, ∃ x, (μ i).toMeasure {x}≠0 ∧
        |signedCoordinate f x-signedCoordinate f (v j)|<r := by
      have hi : ¬∀ x, (μ i).toMeasure {x}≠0 → ∀ j : Fin n,
          r≤|signedCoordinate f x-signedCoordinate f (v j)| := fun hi => hnex ⟨i,hi⟩
      push Not at hi
      obtain ⟨x,hx,j,hj⟩ := hi
      exact ⟨j,x,hx,hj⟩
    choose j x hx hnear using hbad
    have hj : Function.Injective j := by
      intro i t he
      by_contra hit
      rcases lt_or_gt_of_ne hit with hit | hti
      · exact seedOrdered_near_impossible f s g r hs hg _ _ (hord i t hit) (x i) (x t) (v (j i)) (hx i) (hx t)
          (hnear i) (he.symm ▸ hnear t)
      · exact seedOrdered_near_impossible f s g r hs hg _ _ (hord t i hti) (x t) (x i) (v (j i)) (hx t) (hx i)
          (he.symm ▸ hnear t) (hnear i)
    have hc := Fintype.card_le_of_injective j hj
    simp only [Fintype.card_fin] at hc
    omega
  obtain ⟨i,hi⟩ := hex
  have hae : ∀ᵐ x ∂(μ i).toMeasure, ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)| :=
    ae_iff_of_countable.mpr hi
  have hm : (μ i).toMeasure {x | ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|}=1 :=
    (prob_compl_eq_zero_iff (Set.to_countable _).measurableSet).mp (ae_iff.mp hae)
  have hh := hdom i {x | ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|}
  simpa only [Measure.smul_apply,smul_eq_mul,hm,mul_one] using hh

lemma countable_pi_cons_apply {A : Type*} [MeasurableSpace A] [Countable A]
    [MeasurableSingletonClass A] (n : ℕ) (μ : Fin (n+1) → Measure A) [∀ i, SigmaFinite (μ i)]
    (S : Set (Fin (n+1) → A)) :
    Measure.pi μ S = ∫⁻ t, μ 0 {x | Fin.cons x t∈S} ∂Measure.pi (fun j => μ j.succ) := by
  have hm := (measurePreserving_piFinSuccAbove μ 0).symm.map_eq
  rw [← hm,Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    Measure.prod_apply_symm (Set.to_countable _).measurableSet]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero,Fin.zero_succAbove]
  rfl

lemma tupleSeparated_cons {d n : ℕ} (f : Direction d) (r : ℝ) (x : Lattice d) (v : Fin n → Lattice d)
    (hv : TupleSeparated f r v) (hx : ∀ j, r≤|signedCoordinate f x-signedCoordinate f (v j)|) :
    TupleSeparated f r (Fin.cons x v) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j => simpa using hx j
  | succ i =>
    cases j using Fin.cases with
    | zero => simpa only [Fin.cons_succ,Fin.cons_zero,abs_sub_comm] using hx i
    | succ j => simpa only [Fin.cons_succ] using hv i j (fun he => hij (congrArg Fin.succ he))

lemma seedOptions_product_mass {d k n : ℕ} (f : Direction d) (s : ℤ) (g r : ℝ)
    (hs : s=1 ∨ s= -1) (hg : 2*r<g) (δ : ℝ≥0∞) (μ : Fin n → Measure (Lattice d))
    [∀ i, IsFiniteMeasure (μ i)] (hn : n≤k)
    (ho : ∀ i, SeedOptions f k s g δ (μ i)) :
    δ^n ≤ Measure.pi μ {v | TupleSeparated f r v} := by
  induction n with
  | zero =>
    have he : {v : Fin 0 → Lattice d | TupleSeparated f r v}=Set.univ := by
      ext v; simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]; intro i; exact Fin.elim0 i
    rw [he,Measure.pi_univ,pow_zero]
    simp
  | succ n ih =>
    have hi := ih (fun i => μ i.succ) (by omega) (fun i => ho i.succ)
    rw [countable_pi_cons_apply]
    have hb (v : Fin n → Lattice d) :
        {v | TupleSeparated f r v}.indicator (fun _ => δ) v ≤ μ 0 {x | TupleSeparated f r (Fin.cons x v)} := by
      by_cases hv : TupleSeparated f r v
      · simp only [Set.indicator,Set.mem_ofPred_eq,ite_eq_left hv]
        exact (seedOptions_avoid_mass f s g r hs hg δ (μ 0) (ho 0) (by omega) v).trans
          (measure_mono fun x hx => tupleSeparated_cons f r x v hv hx)
      · simp only [Set.indicator,Set.mem_ofPred_eq,ite_eq_right hv]; exact bot_le
    calc
      δ^(n+1) = δ*δ^n := by rw [pow_succ,mul_comm]
      _ ≤ δ*Measure.pi (fun i => μ i.succ) {v | TupleSeparated f r v} := by gcongr
      _ = ∫⁻ v, {v | TupleSeparated f r v}.indicator (fun _ => δ) v ∂Measure.pi (fun i => μ i.succ) := by
        rw [lintegral_indicator (Set.to_countable _).measurableSet,lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
      _ ≤ _ := lintegral_mono hb

end DirectionalTransience

end

end OAI
