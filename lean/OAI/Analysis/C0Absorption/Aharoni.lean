import OAI.Analysis.C0Absorption.Absorption

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section Aharoni
variable {M : Type*} [MetricSpace M]

def earlierCut (q : ℕ → M) (r : ℝ) : ℕ → M → ℝ
  | 0, _ => r
  | n+1, x => min (earlierCut q r n x) (dist x (q n)-r/4)

theorem earlierCut_le_scale (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : earlierCut q r n x≤ r := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (min_le_left _ _).trans ih

theorem earlierCut_le_point (q : ℕ → M) (r : ℝ) {n j : ℕ} (hj : j< n) (x : M) :
    earlierCut q r n x≤ dist x (q j)-r/4 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j=n
    · subst j; exact min_le_right _ _
    · exact (min_le_left _ _).trans (ih (by omega))

theorem le_earlierCut (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) {b : ℝ}
    (hb : b≤ r) (h : ∀ j< n,b≤ dist x (q j)-r/4) : b≤ earlierCut q r n x := by
  induction n with
  | zero => exact hb
  | succ n ih => exact le_min (ih (fun j hj => h j (by omega))) (h n (by omega))

theorem earlierCut_lipschitz (q : ℕ → M) (r : ℝ) (n : ℕ) : LipschitzWith 1 (earlierCut q r n) := by
  induction n with
  | zero => exact (LipschitzWith.const r).weaken (by norm_num)
  | succ n ih =>
    have hd : LipschitzWith 1 (fun x => dist x (q n)-r/4) := by
      simpa only [add_zero] using (LipschitzWith.dist_left (q n)).sub (LipschitzWith.const (r/4))
    simpa only [earlierCut,max_self] using ih.min hd

def metricBump (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : ℝ :=
  max 0 (min (r-dist x (q n)) (min (dist x (q 0)-r) (earlierCut q r n x)))

theorem metricBump_nonneg (q : ℕ → M) (r : ℝ) (n : ℕ) (x : M) : 0≤ metricBump q r n x := le_max_left _ _

theorem metricBump_le_scale (q : ℕ → M) {r : ℝ} (hr : 0≤ r) (n : ℕ) (x : M) : metricBump q r n x≤ r :=
  max_le hr ((min_le_left _ _).trans (sub_le_self _ dist_nonneg))

theorem metricBump_zero_of_far (q : ℕ → M) {r : ℝ} (n : ℕ) (x : M) (h : r≤ dist x (q n)) :
    metricBump q r n x=0 :=
  max_eq_left ((min_le_left _ _).trans (sub_nonpos.mpr h))

theorem metricBump_zero_of_base (q : ℕ → M) {r : ℝ} (n : ℕ) (x : M) (h : dist x (q 0)≤ r) :
    metricBump q r n x=0 :=
  max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (sub_nonpos.mpr h)))

theorem metricBump_lipschitz (q : ℕ → M) (r : ℝ) (n : ℕ) : LipschitzWith 1 (metricBump q r n) := by
  have ha : LipschitzWith 1 (fun x => r-dist x (q n)) := by
    simpa only [zero_add] using (LipschitzWith.const r).sub (LipschitzWith.dist_left (q n))
  have hb : LipschitzWith 1 (fun x => dist x (q 0)-r) := by
    simpa only [add_zero] using (LipschitzWith.dist_left (q 0)).sub (LipschitzWith.const r)
  have hh := (ha.min (hb.min (earlierCut_lipschitz q r n))).const_max 0
  unfold metricBump
  simpa only [max_self] using hh

theorem metricBump_eventually_zero (q : ℕ → M) (hq : DenseRange q) {r : ℝ} (hr : 0< r) (x : M) :
    ∃ N : ℕ, ∀ n, N≤ n → metricBump q r n x=0 := by
  obtain ⟨j,hj⟩ := hq.exists_dist_lt x (show 0< r/4 by positivity)
  refine ⟨j+1,fun n hn => ?_⟩
  apply max_eq_left
  exact (min_le_right _ _).trans ((min_le_right _ _).trans
    ((earlierCut_le_point q r (n := n) (j := j) (by omega) x).trans (by linarith)))

def dyadicBump (q : ℕ → M) (p : ℤ × ℕ) (x : M) : ℝ := metricBump q ((2 : ℝ)^p.1) p.2 x

theorem dyadicBump_nonneg (q : ℕ → M) (p : ℤ × ℕ) (x : M) : 0 ≤ dyadicBump q p x :=
  metricBump_nonneg q _ _ x

theorem dyadicBump_finite_large (q : ℕ → M) (hq : DenseRange q) (x : M) {ε : ℝ} (hε : 0<ε) :
    {p : ℤ × ℕ | ε≤ dyadicBump q p x}.Finite := by
  classical
  obtain ⟨L,hL,hL'⟩ := exists_mem_Ico_zpow hε (show (1 : ℝ)<2 by norm_num)
  obtain ⟨U,hU,hU'⟩ := exists_mem_Ico_zpow (show 0< max 1 (dist x (q 0)) by positivity)
    (show (1 : ℝ)<2 by norm_num)
  choose N hN using fun k : ℤ => metricBump_eventually_zero q hq (zpow_pos (by norm_num : (0 : ℝ)<2) k) x
  have hfinite : (⋃ k∈Set.Icc L U, ({k} : Set ℤ) ×ˢ Set.Iio (N k)).Finite :=
    (Set.finite_Icc L U).biUnion (fun k hk => (Set.finite_singleton k).prod (Set.finite_Iio _))
  apply hfinite.subset
  rintro ⟨k,n⟩ hp
  have hnonzero : dyadicBump q (k,n) x≠0 := ne_of_gt (hε.trans_le hp)
  have hkL : L≤ k := by
    by_contra hh
    have hr := zpow_lt_zpow_right₀ (a := (2 : ℝ)) (by norm_num) (lt_of_not_ge hh)
    have hb := metricBump_le_scale q (zpow_pos (by norm_num : (0 : ℝ)<2) k).le n x
    change metricBump q ((2 : ℝ)^k) n x≥ε at hp
    linarith
  have hkU : k≤ U := by
    by_contra hh
    have hk : U+1≤ k := by omega
    have hr := zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hk
    apply hnonzero
    exact metricBump_zero_of_base q n x ((le_max_right _ _).trans (hU'.le.trans hr))
  have hn : n< N k := by
    by_contra hh
    exact hnonzero (hN k n (le_of_not_gt hh))
  exact Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨⟨hkL,hkU⟩,⟨rfl,hn⟩⟩⟩

theorem dyadicBump_tendsto (q : ℕ → M) (hq : DenseRange q) (x : M) :
    Tendsto (fun p => dyadicBump q p x) cofinite (nhds 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply Filter.eventually_cofinite.mpr
  simpa only [Real.dist_eq,sub_zero,dyadicBump,abs_of_nonneg (metricBump_nonneg q _ _ x),not_lt]
    using dyadicBump_finite_large q hq x hε

def dyadicC0 (q : ℕ → M) (hq : DenseRange q) (x : M) : C₀(ℤ × ℕ,ℝ) :=
  cfunOfTendsto (fun p => dyadicBump q p x) (dyadicBump_tendsto q hq x)

@[simp] theorem dyadicC0_apply (q : ℕ → M) (hq : DenseRange q) (x : M) (p : ℤ × ℕ) :
    dyadicC0 q hq x p=dyadicBump q p x := rfl

theorem dyadicC0_upper (q : ℕ → M) (hq : DenseRange q) (x y : M) : dist (dyadicC0 q hq x) (dyadicC0 q hq y)≤ dist x y := by
  rw [dist_eq_norm]
  apply cfun_norm_le _ dist_nonneg
  intro p
  change |dyadicBump q p x-dyadicBump q p y|≤ dist x y
  simpa only [dyadicBump,NNReal.coe_one,one_mul,Real.dist_eq] using
    (metricBump_lipschitz q ((2 : ℝ)^p.1) p.2).dist_le_mul x y

end Aharoni
end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section AharoniLower
variable {M : Type*} [MetricSpace M]

theorem dyadicBump_separates (q : ℕ → M) (hq : DenseRange q) (x y : M)
    (hxy : 0 < dist x y) (hbase : dist x y/2 ≤ dist x (q 0)) :
    ∃ p : ℤ × ℕ, dist x y/32 ≤ dyadicBump q p x ∧ dyadicBump q p y=0 := by
  classical
  obtain ⟨k,hk,hk'⟩ := exists_mem_Ico_zpow (show 0 < dist x y/4 by positivity)
    (show (1 : ℝ)<2 by norm_num)
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ)≠0)] at hk'
  let r : ℝ := (2 : ℝ)^k
  have hr : 0 < r := zpow_pos (by norm_num) k
  have hr_upper : r≤ dist x y/4 := hk
  have hr_lower : dist x y/8 < r := by change dist x y/4 < r*2 at hk'; linarith
  have hex := hq.exists_dist_lt x (half_pos hr)
  let n := Nat.find hex
  have hn : dist x (q n) < r/2 := Nat.find_spec hex
  have hbefore : ∀ j< n, r/2≤ dist x (q j) := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hcut : r/4≤ earlierCut q r n x := le_earlierCut q r n x (by linarith)
    (fun j hj => by have h := hbefore j hj; linarith)
  have hbx : r/4≤ metricBump q r n x := by
    apply le_trans _ (le_max_right _ _)
    apply le_min (by linarith)
    exact le_min (by linarith) hcut
  have hyfar : r≤ dist y (q n) := by
    have ht := dist_triangle x (q n) y
    rw [dist_comm (q n) y] at ht
    linarith
  exact ⟨(k,n),(by change dist x y/32≤ metricBump q r n x; linarith),
    metricBump_zero_of_far q n y hyfar⟩

theorem dyadicC0_lower (q : ℕ → M) (hq : DenseRange q) (x y : M) :
    (1/32 : ℝ)*dist x y≤ dist (dyadicC0 q hq x) (dyadicC0 q hq y) := by
  by_cases hxy : x=y
  · subst y; simp
  have hpos : 0 < dist x y := dist_pos.mpr hxy
  have hbase : dist x y/2≤ dist x (q 0) ∨ dist x y/2≤ dist y (q 0) := by
    have ht := dist_triangle x (q 0) y
    rw [dist_comm (q 0) y] at ht
    by_cases h : dist x y/2≤ dist x (q 0)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rw [dist_eq_norm]
  rcases hbase with hx|hy
  · obtain ⟨p,hp,hp0⟩ := dyadicBump_separates q hq x y hpos hx
    have hb := cfun_norm_apply_le (dyadicC0 q hq x-dyadicC0 q hq y) p
    change |dyadicBump q p x-dyadicBump q p y|≤_ at hb
    rw [hp0,sub_zero,abs_of_nonneg (dyadicBump_nonneg q p x)] at hb
    linarith
  · obtain ⟨p,hp,hp0⟩ := dyadicBump_separates q hq y x (by rwa [dist_comm]) (by rwa [dist_comm])
    have hb := cfun_norm_apply_le (dyadicC0 q hq x-dyadicC0 q hq y) p
    change |dyadicBump q p x-dyadicBump q p y|≤_ at hb
    rw [hp0,zero_sub,abs_neg,abs_of_nonneg (dyadicBump_nonneg q p y)] at hb
    rw [dist_comm y x] at hp
    linarith

end AharoniLower

section C0Reindex
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]

theorem cfunPull_dist_eq_of_surjective (j : A → B) (hj : Tendsto j cofinite cofinite)
    (hs : Function.Surjective j) (f g : C₀(B,ℝ)) :
    dist (cfunPull j hj f) (cfunPull j hj g)=dist f g := by
  rw [dist_eq_norm,dist_eq_norm]
  apply le_antisymm
  · apply cfun_norm_le _ (norm_nonneg _)
    intro a
    exact cfun_norm_apply_le (f-g) (j a)
  · apply cfun_norm_le _ (norm_nonneg _)
    intro b
    obtain ⟨a,rfl⟩ := hs b
    exact cfun_norm_apply_le (cfunPull j hj f-cfunPull j hj g) a

end C0Reindex

section AharoniEmbedding
variable {M : Type*} [MetricSpace M]

def dyadicEnumeration : (ℤ × ℕ) ≃ ℕ := Denumerable.eqv _

def aharoniEmbedding (q : ℕ → M) (hq : DenseRange q) (x : M) : C0 :=
  cfunPull dyadicEnumeration.symm dyadicEnumeration.symm.injective.tendsto_cofinite (dyadicC0 q hq x)

theorem aharoniEmbedding_dist (q : ℕ → M) (hq : DenseRange q) (x y : M) :
    dist (aharoniEmbedding q hq x) (aharoniEmbedding q hq y)=dist (dyadicC0 q hq x) (dyadicC0 q hq y) :=
  cfunPull_dist_eq_of_surjective _ _ dyadicEnumeration.symm.surjective _ _

theorem aharoniEmbedding_bilip (q : ℕ → M) (hq : DenseRange q) : BiLip (aharoniEmbedding q hq) := by
  refine ⟨1/32,1,by norm_num,by norm_num,fun x y => ?_⟩
  rw [aharoniEmbedding_dist,one_mul]
  exact ⟨dyadicC0_lower q hq x y,dyadicC0_upper q hq x y⟩

end AharoniEmbedding

theorem c0_metricUniversal : MetricUniversal C0 := by
  intro M instM instSep
  rcases isEmpty_or_nonempty M with hM|hM
  · let := hM
    refine ⟨fun x => isEmptyElim x,1,1,by norm_num,by norm_num,fun x y => ?_⟩
    exact isEmptyElim x
  · let := hM
    obtain ⟨q,hq⟩ := TopologicalSpace.exists_dense_seq M
    exact ⟨aharoniEmbedding q hq,aharoniEmbedding_bilip q hq⟩

end
end C0Absorption

end OAI
