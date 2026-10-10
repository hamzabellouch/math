import OAI.Analysis.C0Absorption.Duality

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology

theorem thin_sequence {r : ℕ → ℕ → Prop} (hr : ∀ i, ∀ᶠ j in atTop, r i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j, i < j → r (φ i) (φ j) := by
  have he (t : Set ℕ) (ht : t.Finite) : ∀ᶠ j in atTop, ∀ i ∈ t, i<j ∧ r i j :=
    (eventually_all_finite ht).mpr (fun i _ => (eventually_gt_atTop i).and (hr i))
  obtain ⟨φ,hφ⟩ := seq_of_forall_finite_exists (fun t ht => (he t ht).exists)
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_comm.mp hφ.1, forall_comm.mp hφ.2⟩

theorem finite_constant_subsequence {A : Type*} [Finite A] (f : ℕ → A) :
    ∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a := by
  have hh : ∃ a, ∃ᶠ i in atTop, f i=a := by
    by_contra hn
    push Not at hn
    have hf : ∀ᶠ i in atTop, ∀ a, f i≠a := Filter.eventually_all.mpr hn
    obtain ⟨i,hi⟩ := hf.exists
    exact hi (f i) rfl
  obtain ⟨a,ha⟩ := hh
  obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
  exact ⟨a,φ,hm,hp⟩

theorem constant_or_injective_subsequence {A : Type*} (f : ℕ → A) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (f ∘ φ)) := by
  by_cases h : ∃ a, ∃ᶠ i in atTop, f i=a
  · obtain ⟨a,ha⟩ := h
    obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
    exact Or.inl ⟨a,φ,hm,hp⟩
  · push Not at h
    obtain ⟨φ,hm,hp⟩ := thin_sequence (r := fun i j => f i≠f j) (fun i => by
      simpa only [ne_eq, eq_comm] using h (f i))
    refine Or.inr ⟨φ,hm,?_⟩
    intro i j hij
    apply le_antisymm <;> by_contra hn
    · exact hp j i (lt_of_not_ge hn) hij.symm
    · exact hp i j (lt_of_not_ge hn) hij

theorem nat_constant_or_tendsto (f : ℕ → ℕ) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    Tendsto f atTop atTop := by
  by_cases h : ∃ a, ∃ᶠ i in atTop, f i=a
  · obtain ⟨a,ha⟩ := h
    obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
    exact Or.inl ⟨a,φ,hm,hp⟩
  · push Not at h
    apply Or.inr
    apply tendsto_atTop.mpr
    intro N
    have hh : ∀ᶠ i in atTop, ∀ a ∈ Finset.range N, f i≠a :=
      (eventually_all_finite (Finset.range N).finite_toSet).mpr (fun a _ => h a)
    filter_upwards [hh] with i hi
    by_contra hn
    exact hi (f i) (Finset.mem_range.mpr (lt_of_not_ge hn)) rfl

theorem finite_subsequence_selection {A : Type*} [Finite A]
    (P : A → (ℕ → ℕ) → Prop)
    (hstable : ∀ a (φ ψ : ℕ → ℕ), StrictMono φ → StrictMono ψ → P a φ → P a (φ ∘ ψ))
    (hselect : ∀ a (φ : ℕ → ℕ), StrictMono φ → ∃ ψ, StrictMono ψ ∧ P a (φ ∘ ψ)) :
    ∃ φ, StrictMono φ ∧ ∀ a, P a φ := by
  classical
  let := Fintype.ofFinite A
  suffices h : ∀ s : Finset A, ∃ φ, StrictMono φ ∧ ∀ a ∈ s, P a φ from
    by simpa using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨id,strictMono_id,by simp⟩
  | @insert a s ha ih =>
    obtain ⟨φ,hm,hp⟩ := ih
    obtain ⟨ψ,hn,hq⟩ := hselect a φ hm
    refine ⟨φ ∘ ψ,hm.comp hn,?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hq
    · exact hstable b φ ψ hm hn (hp b hb)

theorem choose_mono_sequence {P : ℕ → ℕ → Prop} (hP : ∀ i, ∀ᶠ j in atTop, P i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, P i (φ i) := by
  have he (i j : ℕ) : ∃ k, j<k ∧ P i k := ((eventually_gt_atTop j).and (hP i)).exists
  choose next hn using he
  let φ : ℕ → ℕ := fun n => Nat.rec (next 0 0) (fun n prev => next (n+1) prev) n
  have hφs (n : ℕ) : φ (n+1) = next (n+1) (φ n) := rfl
  refine ⟨φ,strictMono_nat_of_lt_succ (fun n => ?_),?_⟩
  · rw [hφs]; exact (hn (n+1) (φ n)).1
  · intro i
    cases i with
    | zero => exact (hn 0 0).2
    | succ i => exact (hn (i+1) (φ i)).2

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem nested_selection_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : Convex ℝ S) (u b : ℕ → S → ℝ) (C : ℕ → Set S) (e : ℕ → ℝ)
    (K Kb : ℝ≥0) (hu : ∀ i, Continuous (u i)) (hb : ∀ i, LipschitzWith Kb (b i))
    (hF : ∀ i, LipschitzWith K (fun x => u i x*b i x))
    (hC : ∀ i, IsOpen (C i)) (hc : ∀ i, ∀ x ∈ C i, u i x=e i)
    (hnest : ∀ i, ∀ᶠ j in atTop, tsupport (u j) ⊆ C i)
    (hsmall : Tendsto (fun i => |e i| *(Kb : ℝ)) atTop (nhds 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (K+1) (fun x => ∑ i, ε i * (u (φ i) x*b (φ i) x)) := by
  have he (i : ℕ) : ∀ᶠ j in atTop, |e j| *(Kb : ℝ) ≤ (1/2 : ℝ)^(i+1) :=
    hsmall.eventually (eventually_le_nhds (by positivity))
  obtain ⟨ψ,hψ,heψ⟩ := choose_mono_sequence he
  obtain ⟨η,hη,hrel⟩ := thin_sequence (r := fun i j => tsupport (u (ψ j)) ⊆ C (ψ i))
    (fun i => hψ.tendsto_atTop.eventually (hnest (ψ i)))
  let φ := ψ ∘ η
  refine ⟨φ,hψ.comp hη,?_⟩
  have hprod (i : ℕ) : |e (φ i)| *(Kb : ℝ) ≤ (1/2 : ℝ)^(i+1) := by
    exact (heψ (η i)).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.add_le_add_right (hη.id_le i) 1))
  intro n ε hε
  have hh := nested_supports_signed_lipschitz hS n
    (fun i : Fin n => u (φ i)) (fun i : Fin n => b (φ i))
    (fun i : Fin n => e (φ i)) (fun i : Fin n => C (φ i)) K
    (fun _ : Fin n => Kb) (fun i => hu _) (fun i => hb _) (fun i => hF _)
    (fun i => hC _) (fun i => hc _) (fun i j hij => hrel i j hij) ε hε
  apply hh.weaken
  refine add_le_add le_rfl ?_
  have hsum : (∑ i : Fin n, |e (φ i)| *(Kb : ℝ)) ≤ 1 := by
    calc
      _ ≤ ∑ i : Fin n, (1/2 : ℝ)^(i.val+1) := Finset.sum_le_sum (fun i _ => hprod i)
      _ = ∑ i ∈ Finset.range n, (1/2 : ℝ)^(i+1) := (Finset.sum_range (fun i : ℕ => (1/2 : ℝ)^(i+1))).symm
      _ ≤ ∑' i : ℕ, (1/2 : ℝ)^(i+1) := Summable.sum_le_tsum _ (fun _ _ => by positivity) geometric_summable
      _ = 1 := geometric_tsum
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one] using hsum

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

structure TagLocalization {Γ : Type*} (B : CylinderBases Γ) where
  tag : Γ → ℕ → Icc (-1 : ℝ) 1
  contains_prefix : ∀ γ, Finset.range (B.band γ) ⊆ B.coordinates γ
  ell_tendsto : Tendsto B.ell atTop (nhds 0)
  base_support : ∀ γ (k : B.coordinates γ), k.val < B.band γ →
    ∀ x ∈ tsupport (B.base γ), dist (x k) (tag γ k.val) ≤ 2*dyadic (B.band γ)

namespace TagLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)

theorem representation_support {γ : Γ} (r : GeneratedRepresentation B γ)
    (k : ℕ) (hk : k < B.band γ) (s : C0Ball) (hs : s ∈ tsupport r.value) :
    dist (s.val k) (loc.tag γ k).val ≤ 2*dyadic (B.band γ)+B.ell (B.band γ)/2 := by
  let l : B.coordinates γ := ⟨k,loc.contains_prefix γ (Finset.mem_range.mpr hk)⟩
  let φ : Cube (B.coordinates γ) → ℝ := fun x => dist (x l) (loc.tag γ k)
  have hφ : LipschitzWith 1 φ := by
    simpa only [φ,Function.comp_def,one_mul] using (LipschitzWith.dist_left (loc.tag γ k)).comp (LipschitzWith.eval l)
  have hp := r.support_bound hφ (loc.base_support γ l hk) s hs
  exact hp.trans (add_le_add le_rfl r.budget.le)

theorem projected_concentration (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i))
    (hj : Tendsto (fun i => B.band (γ i)) atTop atTop)
    (v : ℕ → Icc (-1 : ℝ) 1) (hv : Tendsto (fun i => loc.tag (γ i)) atTop (nhds v))
    (I : Finset ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ s ∈ tsupport (r i).value,
      dist (cubeRestrict I s) (fun k : I => v k.val) < ε := by
  have ha : Tendsto (fun i => 2*dyadic (B.band (γ i))+B.ell (B.band (γ i))/2) atTop (nhds 0) := by
    simpa only [Function.comp_def,mul_zero,zero_div,zero_add] using
      ((dyadic_tendsto.comp hj).const_mul 2).add ((loc.ell_tendsto.comp hj).div_const 2)
  have he := ha.eventually (eventually_lt_nhds (half_pos hε))
  have hall : ∀ᶠ i in atTop, ∀ k : I, k.val < B.band (γ i) ∧
      dist (loc.tag (γ i) k.val) (v k.val) < ε/2 := by
    apply Filter.eventually_all.mpr
    intro k
    exact (hj.eventually (eventually_gt_atTop k.val)).and
      ((Metric.tendsto_nhds.mp (tendsto_pi_nhds.mp hv k.val)) (ε/2) (half_pos hε))
  filter_upwards [he,hall] with i hi htag
  intro s hs
  apply (dist_pi_lt_iff hε).mpr
  intro k
  have hb := loc.representation_support (r i) k.val (htag k).1 s hs
  have hc := (htag k).2
  have hd := dist_triangle (cubeRestrict I s k) (loc.tag (γ i) k.val) (v k.val)
  change dist (s.val k.val) (v k.val).val < ε
  change dist (s.val k.val) (v k.val).val ≤
    dist (s.val k.val) (loc.tag (γ i) k.val).val + dist (loc.tag (γ i) k.val) (v k.val) at hd
  linarith

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem high_bands_compatible {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)
    (γ : ℕ → Γ) (r : ∀ i, GeneratedRepresentation B (γ i)) (h : ℕ)
    (hr : ∀ i, (r i).operations.length ≤ h)
    (hj : Tendsto (fun i => B.band (γ i)) atTop atTop)
    (m : ℕ → SourceSpace B) {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ i, δ ≤ |completedPairing (sourceClasses B) c0Origin (r i).value (m i)|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ F : ℕ → C0Ball → ℝ,
      (∀ i, F i ∈ TClass B (h+1)) ∧
      (∀ i, δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (F i) (m (φ i))|) ∧
      ∀ n (ε : Fin n → ℝ), (∀ i, |ε i|=1) →
        LipschitzWith (4^(h+1)*B.L0+1) (fun s => ∑ i, ε i*F i s) := by
  obtain ⟨v,hv,ψ,hψ,hvψ⟩ := isCompact_univ.isSeqCompact.subseq_of_frequently_in
    (x := fun i => loc.tag (γ i)) (Filter.Eventually.of_forall (fun _ => mem_univ _)).frequently
  have hfl (i : ℕ) := (r (ψ i)).exists_flatten_T h (hr (ψ i))
    (fun k => v k.val) (m (ψ i)) (half_pos hδ) (show (0 : ℝ)<1 by norm_num)
  choose a rr hcap hops hdif hflat hsup using hfl
  have hmem (i : ℕ) : (rr i).value ∈ TClass B (h+1) := by
    refine ⟨γ (ψ i),rr i,?_,rfl⟩
    rw [hops i,List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (hr (ψ i)) 1
  let C (i : ℕ) : Set C0Ball :=
    {s | dist (cubeRestrict (B.coordinates (γ (ψ i))) s)
      (fun k => v k.val) < 3*dyadic (a i)/8}
  let e (i : ℕ) := (r (ψ i)).cubeValue
    (flattenOperation (B.coordinates (γ (ψ i))) (a i) (fun k => v k.val)).point
  have hC (i : ℕ) : IsOpen (C i) :=
    Metric.isOpen_ball.preimage (cubeRestrict_lipschitz _).continuous
  have hnest (i : ℕ) : ∀ᶠ j in atTop, tsupport (rr j).value ⊆ C i := by
    have hp := loc.projected_concentration (γ ∘ ψ) rr (hj.comp hψ.tendsto_atTop) v hvψ
      (B.coordinates (γ (ψ i))) (show 0 < 3*dyadic (a i)/8 by have := dyadic_pos (a i); positivity)
    exact hp
  obtain ⟨η,hη,hLip⟩ := nested_selection_lipschitz (convex_closedBall (0 : C0) 1)
    (fun i => (rr i).value) (fun _ _ => 1) C e (4^(h+1)*B.L0) 0
    (fun i => (rr i).value_lipschitz.continuous) (fun _ => LipschitzWith.const 1)
    (fun i => by simpa only [mul_one] using TClass_lipschitz B (h+1) (hmem i))
    hC (fun i s hs => hflat i s hs) hnest (by simp only [NNReal.coe_zero,mul_zero]; exact tendsto_const_nhds)
  refine ⟨ψ ∘ η,hψ.comp hη,fun i => (rr (η i)).value,fun i => hmem _,?_,?_⟩
  · intro i
    have hb := hdif (η i)
    have ha := hd (ψ (η i))
    have hab := abs_sub_abs_le_abs_sub
      (completedPairing (sourceClasses B) c0Origin (r (ψ (η i))).value (m (ψ (η i))))
      (completedPairing (sourceClasses B) c0Origin (rr (η i)).value (m (ψ (η i))))
    rw [abs_sub_comm] at hab
    change δ/2 ≤ |completedPairing (sourceClasses B) c0Origin (rr (η i)).value (m (ψ (η i)))|
    linarith
  · intro n ε hε
    simpa only [mul_one] using hLip n ε hε

end
end C0Absorption

end OAI
