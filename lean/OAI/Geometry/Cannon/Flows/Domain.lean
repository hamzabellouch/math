import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryBasedRay
import OAI.Geometry.Cannon.Flows.WeightedOscillation

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
section
open Set Topology
open Set Metric Topology
open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology
open Set Filter Topology Metric

namespace CannonMagnification

lemma all_bound_of_eventual (v : ℕ → ℝ) (B : ℝ)
    (h : ∀ᶠ n in atTop, |v n| ≤ B) : ∃ D ≥ 0, ∀ n, |v n| ≤ D := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  obtain ⟨C,hC⟩ := ((Finset.range N).finite_toSet.image (fun n => |v n|)).bddAbove
  refine ⟨max 0 (max C B),le_max_left _ _,fun n => ?_⟩
  by_cases hn : n < N
  · exact (hC (mem_image_of_mem _ (by simpa using hn))).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hN n (le_of_not_gt hn)).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma equicontinuous_of_eventual_holder {X : Type*} [MetricSpace X]
    [LocallyCompactSpace X] (f : ℕ → C(X,ℝ)) (α : ℝ) (hα : 0 < α)
    (hlocal : ∀ K : Set X, IsCompact K → ∃ C ≥ 0, ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ y ∈ K, dist (f n x) (f n y) ≤ C*(dist x y)^α) :
    Equicontinuous (fun n x => f n x) := by
  intro x
  apply Metric.equicontinuousAt_iff_right.mpr
  intro ε hε
  obtain ⟨K,hK,hKx⟩ := exists_compact_mem_nhds x
  obtain ⟨C,_hC,hC⟩ := hlocal K hK
  obtain ⟨N,hN⟩ := eventually_atTop.mp hC
  have hfinite : ∀ᶠ y in 𝓝 x, ∀ n ∈ Finset.range N, dist (f n x) (f n y) < ε := by
    apply (eventually_all_finset _).mpr
    intro n _hn
    simpa only [Metric.mem_ball,dist_comm] using
      (f n).continuous.continuousAt.eventually (ball_mem_nhds (f n x) hε)
  have ht : Tendsto (fun y => C*(dist x y)^α) (𝓝 x) (𝓝 0) := by
    have hc := (Real.continuous_rpow_const hα.le).comp ((continuous_const : Continuous (fun _ : X => x)).dist continuous_id)
    have ht' : Tendsto (fun y => C*(dist x y)^α) (𝓝 x) (𝓝 (C*(dist x x)^α)) :=
      (hc.const_mul C).tendsto x
    simpa only [dist_self,Real.zero_rpow (ne_of_gt hα),mul_zero] using ht'
  filter_upwards [hfinite,hKx,ht.eventually (gt_mem_nhds hε)] with y hfin hy hnear n
  by_cases hn : n < N
  · exact hfin n (by simpa using hn)
  · exact (hN n (le_of_not_gt hn) x (mem_of_mem_nhds hKx) y hy).trans_lt hnear

theorem locally_bounded_holder_subsequence {X : Type*} [MetricSpace X]
    [LocallyCompactSpace X] [SigmaCompactSpace X]
    (f : ℕ → C(X,ℝ)) (α : ℝ) (hα : 0 < α)
    (hlocal : ∀ K : Set X, IsCompact K → ∃ C ≥ 0, ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ y ∈ K, dist (f n x) (f n y) ≤ C*(dist x y)^α)
    (hb : ∀ x, ∃ B, ∀ᶠ n in atTop, |f n x| ≤ B) :
    ∃ F : C(X,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (f ∘ φ) atTop (𝓝 F) ∧
      ∀ K : Set X, IsCompact K → ∃ C ≥ 0,
        ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ C*(dist x y)^α := by
  classical
  have heq := equicontinuous_of_eventual_holder f α hα hlocal
  have hball (x : X) : ∃ B ≥ 0, ∀ n, |f n x| ≤ B := by
    obtain ⟨B,hB⟩ := hb x
    exact all_bound_of_eventual (fun n => f n x) B hB
  have : T2Space (UniformOnFun X ℝ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (by
      apply eq_univ_of_forall
      intro x
      exact mem_sUnion_of_mem (mem_singleton x) isCompact_singleton)
  have hcompact : IsCompact (closure (range f)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := fun g : C(X,ℝ) => (g : X → ℝ)) (𝔖 := {K | IsCompact K}) (fun _ h => h)
    · exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
    · intro K hK
      have hindex : ∀ g : range f, ∃ n, f n = g.val := fun g => g.property
      choose index hindex using hindex
      have heq' := heq.comp index
      have heq'' : Equicontinuous (fun g : range f => (g.val : X → ℝ)) := by
        convert heq' using 1
        funext g x
        exact congrArg (fun h : C(X,ℝ) => h x) (hindex g).symm
      exact heq''.equicontinuousOn K
    · intro K _hK x _hx
      obtain ⟨B,_hB,hB⟩ := hball x
      refine ⟨Icc (-B) B,isCompact_Icc,?_⟩
      rintro g ⟨n,rfl⟩
      exact abs_le.mp (hB n)
  obtain ⟨F,_hF,φ,hφ,ht⟩ := hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨F,φ,hφ,ht,fun K hK => ?_⟩
  obtain ⟨C,hC,hbound⟩ := hlocal K hK
  refine ⟨C,hC,fun x hx y hy => ?_⟩
  apply le_of_tendsto (((continuous_eval_const x).tendsto F |>.comp ht).dist
    ((continuous_eval_const y).tendsto F |>.comp ht))
  exact (hφ.tendsto_atTop.eventually hbound).mono (fun n hn => hn x hx y hy)

end CannonMagnification

namespace CannonMagnification

open Set Metric Filter Topology

theorem punctured_nonconstant_subsequence {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : ℕ → C(X,ℝ)) (p : X) (α : ℝ) (hα : 0 < α)
    (htails : ∀ K : Set X, IsCompact K → p ∉ K → ∃ M H : ℝ, 0 ≤ M ∧ 0 ≤ H ∧
      ∀ᶠ n in atTop, (∀ x ∈ K, |f n x| ≤ M) ∧
        (∀ x ∈ K, ∀ y ∈ K, dist (f n x) (f n y) ≤ H*(dist x y)^α))
    (e v : ℝ) (he : 0 < e) (hv : 0 < v)
    (hvariation : ∀ᶠ n in atTop, ∃ x y : X, e ≤ dist x p ∧ e ≤ dist y p ∧
      v ≤ dist (f n x) (f n y)) :
    ∃ F : C(({p}ᶜ : Set X),ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n : ℕ => (f (φ n)).comp ⟨Subtype.val,continuous_subtype_val⟩) atTop (𝓝 F) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ H*(dist x y)^α) ∧
      (∃ x y, F x ≠ F y) := by
  classical
  let Y := ({p}ᶜ : Set X)
  let : LocallyCompactSpace Y := isClosed_singleton.isOpen_compl.locallyCompactSpace
  let g : ℕ → C(Y,ℝ) := fun n => (f n).comp ⟨Subtype.val,continuous_subtype_val⟩
  have hlocal (K : Set Y) (hK : IsCompact K) : ∃ H ≥ 0, ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ y ∈ K, dist (g n x) (g n y) ≤ H*(dist x y)^α := by
    have hKn : p ∉ Subtype.val '' K := by
      rintro ⟨x,_hx,hx⟩
      exact x.property (by simpa only [mem_singleton_iff] using hx)
    obtain ⟨M,H,_hM,hH,h⟩ := htails _ (hK.image continuous_subtype_val) hKn
    refine ⟨H,hH,h.mono (fun n hn x hx y hy => ?_)⟩
    exact hn.2 x (mem_image_of_mem _ hx) y (mem_image_of_mem _ hy)
  have hb (x : Y) : ∃ M, ∀ᶠ n in atTop, |g n x| ≤ M := by
    have hxn : p ∉ ({x.val} : Set X) := by simpa only [mem_singleton_iff] using Ne.symm (show x.val ≠ p from x.property)
    obtain ⟨M,H,_hM,_hH,h⟩ := htails _ isCompact_singleton hxn
    exact ⟨M,h.mono (fun n hn => hn.1 _ (mem_singleton _))⟩
  obtain ⟨F,φ,hφ,ht,hholder⟩ := locally_bounded_holder_subsequence g α hα hlocal hb
  refine ⟨F,φ,hφ,ht,hholder,?_⟩
  by_contra hnc
  push Not at hnc
  let K : Set X := {x | e ≤ dist x p}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  have hKY : K ⊆ Y := by
    intro x hx
    change x ≠ p
    intro hxp
    have hh : e ≤ dist x p := hx
    rw [hxp,dist_self] at hh
    exact (not_le_of_gt he) hh
  let L : Set Y := Subtype.val ⁻¹' K
  have hL : IsCompact L := by
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' L = K := by
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩; exact hz
      · intro hx; exact ⟨⟨x,hKY hx⟩,hx,rfl⟩
    rwa [heq]
  have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht L hL
  have hclose := Metric.tendstoUniformlyOn_iff.mp hu (v/3) (by positivity)
  obtain ⟨n,hn,hv'⟩ := (hclose.and (hφ.tendsto_atTop.eventually hvariation)).exists
  obtain ⟨x,y,hx,hy,hxy⟩ := hv'
  let x' : Y := ⟨x,hKY hx⟩
  let y' : Y := ⟨y,hKY hy⟩
  have hxx := hn x' hx
  have hyy := hn y' hy
  have hdist := dist_triangle (g (φ n) x') (F x') (g (φ n) y')
  rw [hnc x' y'] at hdist
  have hg : dist (f (φ n) x) (f (φ n) y) < 2*(v/3) := by
    change dist (g (φ n) x') (g (φ n) y') < _
    have heq : dist (g (φ n) x') (F y') = dist (F x') (g (φ n) x') := by rw [hnc x' y',dist_comm]
    rw [heq] at hdist
    simp only [Function.comp_apply] at hxx hyy
    linarith
  linarith

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma oscillation_attained {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (hf : Continuous f) (A : Set X) (hA : IsCompact A) (hne : A.Nonempty) :
    ∃ u ∈ A, ∃ v ∈ A, |f u-f v| = oscillation f A := by
  obtain ⟨u,hu,hfu⟩ := (hA.image hf).sSup_mem (hne.image f)
  obtain ⟨v,hv,hfv⟩ := (hA.image hf).sInf_mem (hne.image f)
  refine ⟨u,hu,v,hv,?_⟩
  rw [hfu,hfv]
  exact abs_of_nonneg (oscillation_nonneg hf hA hne)

theorem expansion_record_limit {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (Lp a b CE LE d : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hb : 1 < b)
    (hCE : 0 ≤ CE) (hLE : 0 < LE) (hd : 0 < d)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (k : ℕ → ℕ) (hk : StrictMono k) (x : ℕ → X) (σ : ℕ → ℝ)
    (hx : ∀ i, x i ∈ O) (hσ : ∀ i, 0 < σ i)
    (h : ℕ → X ≃ₜ X) (z₀ pLim : X)
    (hsep : ∀ i, d ≤ dist (x i) z₀)
    (hexp : ∀ i, Expansion (h i) (x i) ((a^(k i))⁻¹) CE LE)
    (hp : Tendsto (fun i => h i z₀) atTop (𝓝 pLim))
    (hescape : Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop)
    (hrec : ∀ i j y, y ∈ O →
      infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
        (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1))
    (hvar : ∀ i, σ i/2 < oscillation f (closedBall (x i) ((a^(k i))⁻¹))) :
    ∃ F : C(({pLim}ᶜ : Set X),ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n : ℕ => (⟨normalized f (h (φ n)) (x (φ n)) (σ (φ n)),
        continuous_normalized f hf _ _ _⟩ : C(X,ℝ)).comp ⟨Subtype.val,continuous_subtype_val⟩)
          atTop (𝓝 F) ∧
      (∀ K : Set ({pLim}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤ H*(dist z w)^(Real.log b/Real.log a)) ∧
      (∃ z w, F z ≠ F w) := by
  let fn : ℕ → C(X,ℝ) := fun i => ⟨normalized f (h i) (x i) (σ i),continuous_normalized f hf _ _ _⟩
  have ht := expansion_record_tails q CP hCP hpack hdiam f hf O hO hOc Lp a b CE LE d
    hLp ha hb hCE hLE hd hpaths k hk x σ hx hσ h z₀ pLim hsep hexp hp hescape hrec
  let e := d/(4*LE)
  have he : 0 < e := div_pos hd (by positivity)
  have hrt : Tendsto (fun i => (a^(k i))⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_pos.mpr (zero_lt_one.trans ha)).le
        (inv_lt_one_of_one_lt₀ ha)).comp hk.tendsto_atTop
  have hvariation : ∀ᶠ i in atTop, ∃ z w : X, e ≤ dist z pLim ∧ e ≤ dist w pLim ∧
      (1:ℝ)/2 ≤ dist (fn i z) (fn i w) := by
    filter_upwards [hrt.eventually (gt_mem_nhds (half_pos hd)),hp.eventually (ball_mem_nhds pLim he)] with i hi hpi
    have hr : 0 < (a^(k i))⁻¹ := inv_pos.mpr (pow_pos (zero_lt_one.trans ha) _)
    have hball : (closedBall (x i) ((a^(k i))⁻¹)).Nonempty := ⟨x i,mem_closedBall_self hr.le⟩
    obtain ⟨u,hu,v,hv,huv⟩ := oscillation_attained f hf _ (isCompact_closedBall _ _) hball
    have haway (y : X) (hy : y ∈ closedBall (x i) ((a^(k i))⁻¹)) : e ≤ dist (h i y) pLim := by
      have hh := image_ball_avoids_puncture (h i) (x i) z₀ y _ CE LE d hr hLE hd hi.le
        (hexp i) hdiam (hsep i) (by simpa only [mem_closedBall,dist_comm] using hy)
      have htri := dist_triangle (h i y) pLim (h i z₀)
      have hnear : dist pLim (h i z₀) < e := by simpa only [mem_ball,dist_comm] using hpi
      have hfract : d/(2*LE) = 2*e := by dsimp [e]; ring
      rw [hfract] at hh
      linarith
    refine ⟨h i u,h i v,haway u hu,haway v hv,?_⟩
    change (1:ℝ)/2 ≤ dist (normalized f (h i) (x i) (σ i) (h i u))
      (normalized f (h i) (x i) (σ i) (h i v))
    rw [normalized_dist f (h i) (x i) (σ i) (hσ i), (h i).symm_apply_apply,(h i).symm_apply_apply,huv]
    apply (le_div_iff₀ (hσ i)).mpr
    linarith [hvar i]
  apply punctured_nonconstant_subsequence fn pLim _ (div_pos (Real.log_pos hb) (Real.log_pos ha))
    (fun K hK hKp => ?_) e (1/2) he (by norm_num) hvariation
  obtain ⟨M,H,hM,hH,hest⟩ := ht K hK hKp
  exact ⟨M,H,hM,hH,hest.mono (fun _ hn => hn.2)⟩

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

lemma continuous_oscillation_bound {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) : ∃ B ≥ 0, ∀ A : Set X, IsCompact A → A.Nonempty →
      oscillation f A ≤ B := by
  obtain ⟨B,hB⟩ := (isCompact_univ.image hf.abs).bddAbove
  refine ⟨2*max B 0,by positivity,fun A hA hne => ?_⟩
  apply oscillation_le_of_pairwise f hf A hA hne
  intro x hx y hy
  have hx' : |f x| ≤ max B 0 := (hB (mem_image_of_mem _ (mem_univ x))).trans (le_max_left _ _)
  have hy' : |f y| ≤ max B 0 := (hB (mem_image_of_mem _ (mem_univ y))).trans (le_max_left _ _)
  exact (le_abs_self _).trans ((abs_sub _ _).trans (by linarith))

lemma upper_geometric_of_eventual (A : ℕ → ℝ) (β C : ℝ) (hβ : 0 < β)
    (hA : ∀ᶠ n in atTop, A n ≤ C*β^n) : ∃ D ≥ 0, ∀ n, A n ≤ D*β^n := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp hA
  obtain ⟨B,hB⟩ := ((Finset.range N).finite_toSet.image (fun n => A n/β^n)).bddAbove
  refine ⟨max 0 (max B C),le_max_left _ _,fun n => ?_⟩
  by_cases hn : n < N
  · apply (div_le_iff₀ (pow_pos hβ n)).mp
    exact (hB (mem_image_of_mem _ (by simpa using hn))).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hN n (le_of_not_gt hn)).trans
      (mul_le_mul_of_nonneg_right ((le_max_right B C).trans (le_max_right _ _)) (pow_pos hβ n).le)

theorem holder_weighted_records {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O P : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (hP : IsCompact P) (hPcon : IsConnected P) (hPO : P ⊆ O)
    (hvary : 0 < oscillation f P)
    (a α s C : ℝ) (ha : 1 < a) (hα : 0 < α) (hs : 0 < s) (hC : 0 ≤ C)
    (hholder : ∀ x ∈ O, ∀ y ∈ closedBall x s, ∀ z ∈ closedBall x s,
      |f y-f z| ≤ C*(dist y z)^α) :
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ), StrictMono k ∧
      (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      (∀ i, σ i/2 < oscillation f (closedBall (x i) ((a^(k i))⁻¹))) ∧
      (∀ i j y, y ∈ O →
        infDist y Oᶜ ^ (q+1) * oscillation f (closedBall y ((a^(k i+j))⁻¹)) ≤
          (b^j)⁻¹ * σ i * infDist (x i) Oᶜ ^ (q+1)) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop := by
  let w := fun x => infDist x Oᶜ ^ (q+1)
  let A := fun n : ℕ => weightedOscillation f w O ((a^n)⁻¹)
  let β := (a⁻¹)^α
  have ha0 : 0 < a := zero_lt_one.trans ha
  have hβ : 0 < β := Real.rpow_pos_of_pos (inv_pos.mpr ha0) _
  have hβ1 : β < 1 := Real.rpow_lt_one (inv_pos.mpr ha0).le (inv_lt_one_of_one_lt₀ ha) hα
  have hβi : 1 < β⁻¹ := (one_lt_inv₀ hβ).mpr hβ1
  obtain ⟨b,hb,hbi⟩ := exists_between hβi
  have hβb : β*b < 1 := by
    have hh := (lt_div_iff₀ hβ).mp (show b < 1/β by simpa only [one_div] using hbi)
    nlinarith
  obtain ⟨B,hB,hBbound⟩ := continuous_oscillation_bound f hf
  have hbound : ∀ x ∈ O, ∀ r, 0 ≤ r → oscillation f (closedBall x r) ≤ B := by
    intro x _hx r hr
    exact hBbound _ (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr⟩
  have hw (x : X) (hx : x ∈ O) : w x ∈ Icc (0:ℝ) 1 :=
    ⟨(infDist_compl_weight O hO hOc hdiam q x hx).1.le,(infDist_compl_weight O hO hOc hdiam q x hx).2⟩
  obtain ⟨η,hη,hwP⟩ := infDist_compl_compact_lower O P hO hOc hP hPcon.1 hPO q
  have hlower : ∀ n : ℕ, (η*oscillation f P/(max CP 1))*((a^n)⁻¹)^q ≤ A n := by
    intro n
    apply weightedOscillation_lower q CP hpack hdiam f w hf O P hP hPcon hPO hw
      _ hvary le_rfl η hη hwP B hB hbound _ (inv_pos.mpr (pow_pos ha0 _))
    exact inv_le_one_of_one_le₀ (one_le_pow₀ ha.le)
  have hrt : Tendsto (fun n : ℕ => (a^n)⁻¹) atTop (𝓝 0) := by
    simpa only [inv_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_pos.mpr ha0).le (inv_lt_one_of_one_lt₀ ha)
  have hupper : ∀ᶠ n in atTop, A n ≤ (C*2^α)*β^n := by
    filter_upwards [hrt.eventually (gt_mem_nhds hs)] with n hn
    have hr : 0 < (a^n)⁻¹ := inv_pos.mpr (pow_pos ha0 _)
    have hosc (x : X) (hx : x ∈ O) : oscillation f (closedBall x ((a^n)⁻¹)) ≤ C*(2*(a^n)⁻¹)^α := by
      apply oscillation_le_of_pairwise f hf _ (isCompact_closedBall _ _) ⟨x,mem_closedBall_self hr.le⟩
      intro y hy z hz
      have hy' : y ∈ closedBall x s := closedBall_subset_closedBall hn.le hy
      have hz' : z ∈ closedBall x s := closedBall_subset_closedBall hn.le hz
      have hdist : dist y z ≤ 2*(a^n)⁻¹ := by
        have ht := dist_triangle y x z
        have hy'' := mem_closedBall.mp hy
        have hz'' := mem_closedBall.mp hz
        rw [dist_comm x z] at ht
        linarith
      exact (le_abs_self _).trans ((hholder x hx y hy' z hz').trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hdist hα.le) hC))
    have hA := (weightedOscillation_bounds f w hf O (hPcon.1.mono hPO) hw _ hr.le
      (C*(2*(a^n)⁻¹)^α) (by positivity) hosc).2.1
    have heq : (C*2^α)*β^n = C*(2*(a^n)⁻¹)^α := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hr.le,← inv_pow]
      rw [← Real.rpow_pow_comm (inv_pos.mpr ha0).le]
      dsimp [β]
      ring
    exact hA.trans_eq heq.symm
  obtain ⟨D,hD,hDupper⟩ := upper_geometric_of_eventual A β (C*2^α) hβ hupper
  refine ⟨b,hb,?_⟩
  exact select_weighted_magnifications f hf O hO (hPcon.1.mono hPO) hOc hdiam q a ha β b
    hβ hb hβb (η*oscillation f P/(max CP 1)) D B (by positivity) hD hB hbound hlower hDupper

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

theorem holder_magnification_global {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (f : X → ℝ) (hf : Continuous f) (O P : Set X) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (hP : IsCompact P) (hPcon : IsConnected P) (hPO : P ⊆ O) (hvary : 0 < oscillation f P)
    (Lp a CE LE : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hCE : 0 ≤ CE) (hLE : 0 < LE)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (expand : X → ℕ → X ≃ₜ X)
    (hexpand : ∀ x k, Expansion (expand x k) x ((a^k)⁻¹) CE LE)
    (α s C : ℝ) (hα : 0 < α) (hs : 0 < s) (hC : 0 ≤ C)
    (hholder : ∀ x ∈ O, ∀ y ∈ closedBall x s, ∀ z ∈ closedBall x s,
      |f y-f z| ≤ C*(dist y z)^α)
    (z₀ : X) (d : ℝ) (hd : 0 < d) (hsep : ∀ x ∈ O, d ≤ dist x z₀) :
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ) (p : X)
      (F : C(({p}ᶜ : Set X),ℝ)), StrictMono k ∧ (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      Tendsto (fun i => expand (x i) (k i) z₀) atTop (𝓝 p) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop ∧
      (∀ K : Set X, IsCompact K → p ∉ K → ∀ᶠ i in atTop,
        ∀ z ∈ K, (expand (x i) (k i)).symm z ∈ O) ∧
      Tendsto (fun i : ℕ => (⟨normalized f (expand (x i) (k i)) (x i) (σ i),
        continuous_normalized f hf _ _ _⟩ : C(X,ℝ)).comp ⟨Subtype.val,continuous_subtype_val⟩)
          atTop (𝓝 F) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤ H*(dist z w)^(Real.log b/Real.log a)) ∧
      (∃ z w, F z ≠ F w) := by
  obtain ⟨b,hb,k,x,σ,hk,hx,hvar,hrec,hescape⟩ := holder_weighted_records q CP hpack hdiam
    f hf O P hO hOc hP hPcon hPO hvary a α s C ha hα hs hC hholder
  obtain ⟨p,_hp,ψ,hψ,hpt⟩ := (isCompact_univ : IsCompact (univ : Set X)).tendsto_subseq
    (fun i => mem_univ (expand (x i) (k i) z₀))
  let k' := k ∘ ψ
  let x' := x ∘ ψ
  let σ' := σ ∘ ψ
  let h' := fun i => expand (x' i) (k' i)
  have hhproj : ∀ i, Expansion (h' i) (x' i) ((a^(k' i))⁻¹) CE LE := fun i => hexpand _ _
  obtain ⟨F,φ,hφ,ht,hFholder,hFvar⟩ := expansion_record_limit q CP hCP hpack hdiam f hf O hO hOc
    Lp a b CE LE d hLp ha hb hCE hLE hd hpaths k' (hk.comp hψ) x' σ'
    (fun i => (hx (ψ i)).1) (fun i => (hx (ψ i)).2) h' z₀ p
    (fun i => hsep _ (hx (ψ i)).1) hhproj hpt (hescape.comp hψ.tendsto_atTop)
    (fun i j y hy => hrec (ψ i) j y hy) (fun i => hvar (ψ i))
  refine ⟨b,hb,k' ∘ φ,x' ∘ φ,σ' ∘ φ,p,F,(hk.comp hψ).comp hφ,
    (fun i => hx (ψ (φ i))),hpt.comp hφ.tendsto_atTop,
    (hescape.comp hψ.tendsto_atTop).comp hφ.tendsto_atTop,?_,ht,hFholder,hFvar⟩
  intro K hK hKp
  obtain ⟨M,H,_hM,_hH,hest⟩ := expansion_record_tails q CP hCP hpack hdiam f hf O hO hOc
    Lp a b CE LE d hLp ha hb hCE hLE hd hpaths k' (hk.comp hψ) x' σ'
    (fun i => (hx (ψ i)).1) (fun i => (hx (ψ i)).2) h' z₀ p
    (fun i => hsep _ (hx (ψ i)).1) hhproj hpt (hescape.comp hψ.tendsto_atTop)
    (fun i j y hy => hrec (ψ i) j y hy) K hK hKp
  exact (hφ.tendsto_atTop.eventually hest).mono (fun _ hn => hn.1)

end CannonMagnification

open Set Metric Topology

namespace CannonMagnification

theorem local_holder_extension {X : Type*} [MetricSpace X] [CompactSpace X]
    (Ω O : Set X) (hΩ : IsOpen Ω) (hOΩ : closure O ⊆ Ω)
    (f : C(Ω,ℝ)) (α : ℝ)
    (hholder : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α) :
    ∃ g : C(X,ℝ), ∃ s C : ℝ, 0 < s ∧ 0 ≤ C ∧
      (∀ x ∈ O, ∀ hx : x ∈ Ω, g x = f ⟨x,hx⟩) ∧
      (∀ x ∈ O, ∀ y ∈ closedBall x s, ∀ z ∈ closedBall x s,
        |g y-g z| ≤ C*(dist y z)^α) := by
  obtain ⟨s,hs,hsΩ⟩ := isClosed_closure.isCompact.exists_cthickening_subset_open hΩ hOΩ
  let K := cthickening s (closure O)
  have hK : IsClosed K := isClosed_cthickening
  let fK : C(K,ℝ) := f.comp ⟨fun x => ⟨x.val,hsΩ x.property⟩,continuous_subtype_val.subtype_mk _⟩
  obtain ⟨g,hg⟩ := fK.exists_extension' hK.isClosedEmbedding_subtypeVal
  have hagree (x : X) (hx : x ∈ K) : g x = f ⟨x,hsΩ hx⟩ := by
    exact congrFun hg ⟨x,hx⟩
  obtain ⟨C,hC,hH⟩ := hholder K hK.isCompact hsΩ
  refine ⟨g,s,C,hs,hC,?_,?_⟩
  · intro x hx hxΩ
    have hxK : x ∈ K := self_subset_cthickening _ (subset_closure hx)
    exact hagree x hxK
  · intro x hx y hy z hz
    have hyK : y ∈ K := closedBall_subset_cthickening (subset_closure hx) s hy
    have hzK : z ∈ K := closedBall_subset_cthickening (subset_closure hx) s hz
    rw [hagree y hyK,hagree z hzK]
    exact hH ⟨y,hsΩ hyK⟩ ⟨z,hsΩ hzK⟩ hyK hzK

end CannonMagnification

namespace CannonMagnification

open CannonCrossEnergy CannonPacking Set Metric Filter Topology

def onDomain {X : Type*} [TopologicalSpace X] {Ω : Set X} (f : C(Ω,ℝ)) (x : X) : ℝ :=
  by classical exact if h : x ∈ Ω then f ⟨x,h⟩ else 0

lemma onDomain_eq {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (f : C(Ω,ℝ)) (x : X) (hx : x ∈ Ω) : onDomain f x = f ⟨x,hx⟩ := by simp only [onDomain,dite_eq_left hx]

theorem local_holder_magnification {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ) (CP : ℝ) (hCP : 0 ≤ CP) (hpack : PolynomialPacking (X := X) q CP)
    (hdiam : ∀ x y : X, dist x y ≤ 1)
    (Ω O P : Set X) (hΩ : IsOpen Ω) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (hOΩ : closure O ⊆ Ω) (hP : IsCompact P) (hPcon : IsConnected P) (hPO : P ⊆ O)
    (f : C(Ω,ℝ)) (hvary : ∃ u ∈ P, ∃ v ∈ P, onDomain f u ≠ onDomain f v)
    (Lp a CE LE : ℝ) (hLp : 1 ≤ Lp) (ha : 1 < a) (hCE : 0 ≤ CE) (hLE : 0 < LE)
    (hpaths : ∀ (o u v : X) (s : ℝ), 0 < s → dist o u ≤ s → dist o v ≤ s →
      JoinedIn {z | dist o z < Lp*s} u v)
    (expand : X → ℕ → X ≃ₜ X)
    (hexpand : ∀ x k, Expansion (expand x k) x ((a^k)⁻¹) CE LE)
    (α : ℝ) (hα : 0 < α)
    (hholder : ∀ K : Set X, IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α)
    (z₀ : X) (d : ℝ) (hd : 0 < d) (hsep : ∀ x ∈ O, d ≤ dist x z₀) :
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → X) (σ : ℕ → ℝ) (p : X)
      (F : C(({p}ᶜ : Set X),ℝ)), StrictMono k ∧ (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      Tendsto (fun i => expand (x i) (k i) z₀) atTop (𝓝 p) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((a^(k i))⁻¹)) atTop atTop ∧
      (∀ K : Set X, IsCompact K → p ∉ K → ∀ᶠ i in atTop,
        ∀ z ∈ K, (expand (x i) (k i)).symm z ∈ Ω) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K →
        TendstoUniformlyOn (fun i z => normalized (onDomain f) (expand (x i) (k i))
          (x i) (σ i) z.val) F atTop K) ∧
      (∀ K : Set ({p}ᶜ : Set X), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤ H*(dist z w)^(Real.log b/Real.log a)) ∧
      (∃ z w, F z ≠ F w) := by
  obtain ⟨g,s,C,hs,hC,hagree,hH⟩ := local_holder_extension Ω O hΩ hOΩ f α hholder
  have hOΩ' : O ⊆ Ω := subset_closure.trans hOΩ
  have hgeq (x : X) (hx : x ∈ O) : g x = onDomain f x := by
    rw [onDomain_eq f x (hOΩ' hx)]
    exact hagree x hx (hOΩ' hx)
  have hgvar : 0 < oscillation g P := by
    obtain ⟨u,hu,v,hv,huv⟩ := hvary
    have hne : g u ≠ g v := by simpa only [hgeq u (hPO hu),hgeq v (hPO hv)] using huv
    exact (abs_pos.mpr (sub_ne_zero.mpr hne)).trans_le (abs_sub_le_oscillation g g.continuous P hP hu hv)
  obtain ⟨b,hb,k,x,σ,p,F,hk,hx,hp,he,hpre,ht,hF,hvar⟩ := holder_magnification_global
    q CP hCP hpack hdiam g g.continuous O P hO hOc hP hPcon hPO hgvar
    Lp a CE LE hLp ha hCE hLE hpaths expand hexpand α s C hα hs hC hH z₀ d hd hsep
  refine ⟨b,hb,k,x,σ,p,F,hk,hx,hp,he,?_,?_,hF,hvar⟩
  · intro K hK hKp
    exact (hpre K hK hKp).mono (fun i hi z hz => hOΩ' (hi z hz))
  · intro K hK
    have hKp : p ∉ Subtype.val '' K := by
      rintro ⟨z,_hz,hz⟩
      exact z.property (by simpa only [mem_singleton_iff] using hz)
    have hu := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht K hK
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu ε hε,
      hpre (Subtype.val '' K) (hK.image continuous_subtype_val) hKp] with i hi hpi z hz
    have heq : normalized (onDomain f) (expand (x i) (k i)) (x i) (σ i) z.val =
        normalized g (expand (x i) (k i)) (x i) (σ i) z.val := by
      unfold normalized
      rw [hgeq _ (hpi _ (mem_image_of_mem _ hz)),hgeq _ (hx i).1]
    rw [heq]
    exact hi z hz

end CannonMagnification

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryHolderMagnificationSetoid : Setoid (BasedRay D) := raySetoid D

theorem boundary_holder_magnification (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∀ (Ω O P : Set (Boundary D)), IsOpen Ω → IsOpen O → Oᶜ.Nonempty →
    closure O ⊆ Ω → IsCompact P → IsConnected P → P ⊆ O →
    ∀ f : C(Ω,ℝ), (∃ u ∈ P, ∃ v ∈ P, onDomain f u ≠ onDomain f v) →
    ∀ α : ℝ, 0 < α →
    (∀ K : Set (Boundary D), IsCompact K → K ⊆ Ω → ∃ C ≥ 0,
      ∀ x y : Ω, x.val ∈ K → y.val ∈ K → |f x-f y| ≤ C*(dist x y)^α) →
    ∀ (z₀ : Boundary D) (d : ℝ), 0 < d → (∀ x ∈ O, d ≤ dist x z₀) →
    ∃ b : ℝ, 1 < b ∧ ∃ (k : ℕ → ℕ) (x : ℕ → Boundary D) (σ : ℕ → ℝ) (p : Boundary D)
      (F : C(({p}ᶜ : Set (Boundary D)),ℝ)),
      StrictMono k ∧ (∀ i, x i ∈ O ∧ 0 < σ i) ∧
      Tendsto (fun i => boundaryExpansion D hδ (x i) (k i) z₀) atTop (𝓝 p) ∧
      Tendsto (fun i => infDist (x i) Oᶜ / ((Real.exp (2*visualExponent δ)^(k i))⁻¹)) atTop atTop ∧
      (∀ K : Set (Boundary D), IsCompact K → p ∉ K → ∀ᶠ i in atTop,
        ∀ z ∈ K, (boundaryExpansion D hδ (x i) (k i)).symm z ∈ Ω) ∧
      (∀ K : Set ({p}ᶜ : Set (Boundary D)), IsCompact K →
        TendstoUniformlyOn (fun i z => normalized (onDomain f) (boundaryExpansion D hδ (x i) (k i))
          (x i) (σ i) z.val) F atTop K) ∧
      (∀ K : Set ({p}ᶜ : Set (Boundary D)), IsCompact K → ∃ H ≥ 0,
        ∀ z ∈ K, ∀ w ∈ K, dist (F z) (F w) ≤
          H*(dist z w)^(Real.log b/Real.log (Real.exp (2*visualExponent δ)))) ∧
      (∃ z w, F z ≠ F w) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  intro Ω O P hΩ hO hOc hOΩ hP hPcon hPO f hvary α hα hholder z₀ d hd hsep
  obtain ⟨q,CP,_hq,hCP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨Lp,hLp,hpaths⟩ := boundary_controlled_paths D hδ φ
  exact local_holder_magnification q CP hCP.le hpack (boundaryDist_le_one D hδ)
    Ω O P hΩ hO hOc hOΩ hP hPcon hPO f hvary Lp
    (Real.exp (2*visualExponent δ))
    (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
    (8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))) hLp
    (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ)))
    (by positivity) (by positivity) hpaths (boundaryExpansion D hδ)
    (boundaryExpansion_formula D hδ) α hα hholder z₀ d hd hsep

end CannonRelease

end
end
end
end
end
end
end
end
end
end

end OAI
