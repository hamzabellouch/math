import Mathlib

namespace OAI

noncomputable section
namespace DeGiorgiCompactness
open Filter Set Topology
open scoped NNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

lemma equicontinuous_of_local_fderiv_bound {n : ℕ} {ι : Type*}
    {f : ι → Space n → ℝ} (hf : ∀ i, Differentiable ℝ (f i))
    (hb : ∀ R > (0 : ℝ), ∃ M : ℝ≥0, ∀ i x, ‖x‖ ≤ R → ‖fderiv ℝ (f i) x‖ ≤ M) :
    Equicontinuous f := by
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨M, hM⟩ := hb (‖x‖ + 1) (by positivity)
  have hLip (i : ι) : LipschitzOnWith M (f i) (Metric.closedBall 0 (‖x‖ + 1)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun z _ => hf i z)
    · intro z hz
      exact hM i z (by simpa using hz)
    · exact convex_closedBall _ _
  refine ⟨min 1 (ε / (M + 1)), lt_min (by norm_num) (div_pos hε (by positivity)), ?_⟩
  intro y hy i
  have hy1 : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hyb : y ∈ Metric.closedBall (0 : Space n) (‖x‖ + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖y‖ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add y x
         _ ≤ ‖x‖ + 1 := by rw [← dist_eq_norm] at *; linarith
  have hxb : x ∈ Metric.closedBall (0 : Space n) (‖x‖ + 1) := by simp
  calc dist (f i x) (f i y) ≤ M * dist x y := (hLip i).dist_le_mul x hxb y hyb
       _ < ε := by
         have hd : dist x y < ε / (M + 1) := by
           rw [dist_comm]; exact lt_of_lt_of_le hy (min_le_right _ _)
         have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < M + 1)).mp hd
         nlinarith [dist_nonneg (x := x) (y := y)]

lemma compact_closure_of_local_bounds {n : ℕ} {ι : Type*}
    {f : ι → Space n → ℝ} (hf : ∀ i, Differentiable ℝ (f i))
    (hb : ∀ R > (0 : ℝ), ∃ M : ℝ≥0, ∀ i x, ‖x‖ ≤ R →
      |f i x| ≤ M ∧ ‖fderiv ℝ (f i) x‖ ≤ M) :
    IsCompact (closure (Set.range (fun i => (⟨f i, (hf i).continuous⟩ : C(Space n, ℝ))))) := by
  let F : ι → C(Space n, ℝ) := fun i => ⟨f i, (hf i).continuous⟩
  have he : Equicontinuous f := equicontinuous_of_local_fderiv_bound hf (by
    intro R hR
    obtain ⟨M, hM⟩ := hb R hR
    exact ⟨M, fun i x hx => (hM i x hx).2⟩)
  have hc : Topology.IsClosedEmbedding
      (ContinuousMap.toUniformOnFunIsCompact : C(Space n, ℝ) →
        UniformOnFun (Space n) ℝ {K | IsCompact K}) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (F := fun g : C(Space n, ℝ) => ⇑g)
      (fun _ h => h) hc
  · intro K hK
    have hsub : Equicontinuous (fun g : Set.range F => (g : C(Space n, ℝ))) := by
      rw [equicontinuous_iff_range] at he ⊢
      have hr : Set.range (fun g : Set.range F => ⇑(g : C(Space n, ℝ))) =
          Set.range f := by
        ext g
        constructor
        · rintro ⟨⟨h, ⟨i, rfl⟩⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨⟨F i, ⟨i, rfl⟩⟩, rfl⟩
      rw [hr]
      exact he
    exact hsub.equicontinuousOn K
  · intro K hK x hx
    obtain ⟨M, hM⟩ := hb (‖x‖ + 1) (by positivity)
    refine ⟨Set.Icc (-(M : ℝ)) M, isCompact_Icc, ?_⟩
    rintro g ⟨i, rfl⟩
    exact abs_le.mp (hM i x (by linarith)).1

theorem countable_local_compactness {n : ℕ} {ι : Type*} [Countable ι]
    {f : ℕ → ι → Space n → ℝ} (hf : ∀ j i, Differentiable ℝ (f j i))
    (hb : ∀ i R, 0 < R → ∃ M : ℝ≥0, ∀ j x, ‖x‖ ≤ R →
      |f j i x| ≤ M ∧ ‖fderiv ℝ (f j i) x‖ ≤ M) :
    ∃ (a : ℕ → ℕ) (g : ι → C(Space n, ℝ)), StrictMono a ∧
      ∀ i, TendstoLocallyUniformly (fun j => f (a j) i) (g i) atTop := by
  let F : ℕ → ι → C(Space n, ℝ) := fun j i => ⟨f j i, (hf j i).continuous⟩
  let K (i : ι) := closure (Set.range (fun j => F j i))
  have hK : ∀ i, IsCompact (K i) := fun i =>
    compact_closure_of_local_bounds (fun j => hf j i) (hb i)
  have hcomp : IsCompact (Set.pi Set.univ K) := by
    simpa only [Set.pi, Set.mem_univ, forall_true_left] using isCompact_pi_infinite hK
  obtain ⟨g, hg, a, ha, hlim⟩ := hcomp.tendsto_subseq (fun j i _ => subset_closure ⟨j, rfl⟩)
  refine ⟨a, g, ha, fun i => ?_⟩
  have H : Tendsto (fun j => F (a j) i) atTop (𝓝 (g i)) :=
    (tendsto_pi_nhds.mp hlim) i
  exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp H

lemma locallyUniform_pi {X ι κ : Type*} [TopologicalSpace X]
    {f : ι → X → (κ → ℝ)} {g : X → (κ → ℝ)} {l : Filter ι}
    (h : ∀ k, TendstoLocallyUniformly (fun j x => f j x k) (fun x => g x k) l) :
    TendstoLocallyUniformly f g l := by
  rw [tendstoLocallyUniformly_iff_forall_tendsto]
  intro x
  rw [Pi.uniformity, tendsto_iInf]
  intro k
  rw [tendsto_comap_iff]
  exact (tendstoLocallyUniformly_iff_forall_tendsto.mp (h k)) x

def coordDeriv {n : ℕ} (f : Space n → ℝ) (i : Fin n) (x : Space n) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)

def coordinateDual (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Space n →L[ℝ] ℝ) :=
  ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (EuclideanSpace.proj i)

lemma coordinateDual_fderiv {n : ℕ} (f : Space n → ℝ) (x : Space n) :
    coordinateDual n (fun i => coordDeriv f i x) = fderiv ℝ f x := by
  ext v
  have hv : ∑ i : Fin n, v i • EuclideanSpace.basisFun (Fin n) ℝ i = v := by
    simpa using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  conv_rhs => rw [← hv, map_sum]
  simp only [coordinateDual, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_apply, smul_eq_mul, map_smul, coordDeriv]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_comm]

theorem first_jet_limit {n : ℕ} {f : ℕ → Space n → ℝ}
    (hf : ∀ j, Differentiable ℝ (f j))
    (g : C(Space n, ℝ)) (q : Fin n → C(Space n, ℝ))
    (hg : TendstoLocallyUniformly f g atTop)
    (hq : ∀ i, TendstoLocallyUniformly (fun j => coordDeriv (f j) i) (q i) atTop) :
    ContDiff ℝ 1 (g : Space n → ℝ) ∧
      (∀ i x, coordDeriv g i x = q i x) ∧
      TendstoLocallyUniformly (fun j => fderiv ℝ (f j)) (fderiv ℝ g) atTop := by
  let g' : Space n → (Space n →L[ℝ] ℝ) := fun x => coordinateDual n (fun i => q i x)
  have hg' : Continuous g' := (coordinateDual n).continuous.comp
    (continuous_pi (fun i => (q i).continuous))
  have hLf : TendstoLocallyUniformly (fun j => fderiv ℝ (f j)) g' atTop := by
    have hh := (coordinateDual n).uniformContinuous.comp_tendstoLocallyUniformly
      (locallyUniform_pi hq)
    simpa only [Function.comp_def, coordinateDual_fderiv] using hh
  have hfg (x : Space n) : HasFDerivAt (g : Space n → ℝ) (g' x) x := by
    apply hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hLf.tendstoLocallyUniformlyOn
      (fun j x _ => (hf j x).hasFDerivAt)
      (fun y _ => hg.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ y)) (Set.mem_univ x)
  have hfe : fderiv ℝ (g : Space n → ℝ) = g' := funext (fun x => (hfg x).fderiv)
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨g', hg', hfg⟩, ?_, ?_⟩
  · intro i x
    unfold coordDeriv
    rw [hfe]
    dsimp [g', coordinateDual]
    simp [EuclideanSpace.basisFun_apply]
  · rwa [hfe]

theorem first_jet_subsequence {n : ℕ} {ι : Type*} [Countable ι]
    {f : ℕ → ι → Space n → ℝ} (hf : ∀ j i, ContDiff ℝ 2 (f j i))
    (hb : ∀ i R, 0 < R → ∃ M : ℝ≥0, ∀ j x, ‖x‖ ≤ R →
      |f j i x| ≤ M ∧ ‖fderiv ℝ (f j i) x‖ ≤ M ∧
        ∀ k, ‖fderiv ℝ (coordDeriv (f j i) k) x‖ ≤ M) :
    ∃ (a : ℕ → ℕ) (g : ι → C(Space n, ℝ)), StrictMono a ∧
      ∀ i, ContDiff ℝ 1 (g i : Space n → ℝ) ∧
        TendstoLocallyUniformly (fun j => f (a j) i) (g i) atTop ∧
        TendstoLocallyUniformly (fun j => fderiv ℝ (f (a j) i)) (fderiv ℝ (g i)) atTop := by
  let F : ℕ → (ι × Option (Fin n)) → Space n → ℝ := fun j i =>
    match i.2 with
    | none => f j i.1
    | some k => coordDeriv (f j i.1) k
  have hF : ∀ j i, Differentiable ℝ (F j i) := by
    intro j ⟨i, k⟩
    cases k with
    | none => exact (hf j i).differentiable (by norm_num)
    | some k =>
      exact ((hf j i).fderiv_right (m := 1) (by norm_num)).clm_apply
        contDiff_const |>.differentiable (by norm_num)
  have hBF : ∀ i R, 0 < R → ∃ M : ℝ≥0, ∀ j x, ‖x‖ ≤ R →
      |F j i x| ≤ M ∧ ‖fderiv ℝ (F j i) x‖ ≤ M := by
    intro ⟨i, k⟩ R hR
    obtain ⟨M, hM⟩ := hb i R hR
    refine ⟨M, fun j x hx => ?_⟩
    cases k with
    | none => exact ⟨(hM j x hx).1, (hM j x hx).2.1⟩
    | some k =>
      refine ⟨?_, (hM j x hx).2.2 k⟩
      have H := (fderiv ℝ (f j i) x).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ k)
      have hn : ‖EuclideanSpace.basisFun (Fin n) ℝ k‖ = 1 :=
        (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one k
      simpa only [F, coordDeriv, Real.norm_eq_abs, hn, mul_one] using
        H.trans (by simpa only [hn, mul_one] using (hM j x hx).2.1)
  obtain ⟨a, g, ha, hg⟩ := countable_local_compactness hF hBF
  refine ⟨a, fun i => g (i, none), ha, fun i => ?_⟩
  have H := first_jet_limit (fun j => (hf (a j) i).differentiable (by norm_num))
    (g (i, none)) (fun k => g (i, some k)) (hg (i, none)) (fun k => hg (i, some k))
  exact ⟨H.1, hg (i, none), H.2.2⟩

lemma coordDeriv_const_mul {n : ℕ} {f : Space n → ℝ}
    (hf : Differentiable ℝ f) (c : ℝ) (k : Fin n) :
    coordDeriv (fun x => c * f x) k = fun x => c * coordDeriv f k x := by
  funext x
  simp only [coordDeriv, fderiv_const_mul (hf x), smul_apply, smul_eq_mul]

theorem normalized_first_jet_subsequence {n : ℕ} {ι : Type*} [Countable ι]
    {f : ℕ → ι → Space n → ℝ} {c : ℕ → ι → ℝ}
    (hf : ∀ j i, ContDiff ℝ 2 (f j i)) (hc : ∀ j i, 0 < c j i)
    (hb : ∀ i R, 0 < R → ∃ M : ℝ≥0, ∀ j x, ‖x‖ ≤ R →
      |f j i x| ≤ M * c j i ∧ ‖fderiv ℝ (f j i) x‖ ≤ M * c j i ∧
        ∀ k, ‖fderiv ℝ (coordDeriv (f j i) k) x‖ ≤ M * c j i) :
    ∃ (a : ℕ → ℕ) (g : ι → C(Space n, ℝ)), StrictMono a ∧
      ∀ i, ContDiff ℝ 1 (g i : Space n → ℝ) ∧
        TendstoLocallyUniformly (fun j x => (c (a j) i)⁻¹ * f (a j) i x) (g i) atTop ∧
        TendstoLocallyUniformly (fun j => fderiv ℝ (fun x => (c (a j) i)⁻¹ * f (a j) i x))
          (fderiv ℝ (g i)) atTop := by
  apply first_jet_subsequence (f := fun j i x => (c j i)⁻¹ * f j i x)
    (fun j i => contDiff_const.mul (hf j i))
  intro i R hR
  obtain ⟨M, hM⟩ := hb i R hR
  refine ⟨M, fun j x hx => ?_⟩
  have hcinv : 0 < (c j i)⁻¹ := inv_pos.mpr (hc j i)
  have mulB {b : ℝ} (h : b ≤ M * c j i) : (c j i)⁻¹ * b ≤ M := by
    have H := mul_le_mul_of_nonneg_left h hcinv.le
    have he : (c j i)⁻¹ * (M * c j i) = (M : ℝ) := by
      field_simp [ne_of_gt (hc j i)]
    rwa [he] at H
  have hd := (hf j i).differentiable (by norm_num)
  have hk (k : Fin n) : Differentiable ℝ (coordDeriv (f j i) k) :=
    ((hf j i).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const |>.differentiable (by norm_num)
  refine ⟨?_, ?_, fun k => ?_⟩
  · rw [abs_mul, abs_of_pos hcinv]
    exact mulB (hM j x hx).1
  · rw [fderiv_const_mul (hd x), norm_smul, Real.norm_eq_abs, abs_of_pos hcinv]
    exact mulB (hM j x hx).2.1
  · rw [coordDeriv_const_mul hd, fderiv_const_mul (hk k x), norm_smul,
      Real.norm_eq_abs, abs_of_pos hcinv]
    exact mulB ((hM j x hx).2.2 k)

end DeGiorgiCompactness
end

noncomputable section
namespace DeGiorgiCompactness
open Filter Set Topology
open scoped NNReal
open scoped ContDiff

abbrev JetSpace (n : ℕ) := List (Fin n) → C(Space n, ℝ)

def CoherentJets {n : ℕ} (g : JetSpace n) : Prop :=
  ∀ l, Differentiable ℝ (g l : Space n → ℝ) ∧
    ∀ i x, coordDeriv (g l) i x = g (i::l) x

lemma coherentJets_smooth {n : ℕ} {g : JetSpace n} (hg : CoherentJets g) :
    ∀ l, ContDiff ℝ ∞ (g l : Space n → ℝ) := by
  have hfin (k : ℕ) : ∀ l, ContDiff ℝ k (g l : Space n → ℝ) := by
    induction k with
    | zero => intro l; exact contDiff_zero.mpr (g l).continuous
    | succ k ih =>
      intro l
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fderiv ℝ (g l : Space n → ℝ), ?_, fun x => ((hg l).1 x).hasFDerivAt⟩
      have he : fderiv ℝ (g l : Space n → ℝ) =
          fun x => coordinateDual n (fun i => g (i::l) x) := by
        funext x
        rw [← coordinateDual_fderiv]
        simp only [(hg l).2]
      rw [he]
      exact (coordinateDual n).contDiff.comp (contDiff_pi.mpr (fun i => ih (i::l)))
  intro l
  exact contDiff_infty.mpr (fun k => hfin k l)

lemma coherentJets_closed (n : ℕ) : IsClosed {g : JetSpace n | CoherentJets g} := by
  apply IsSeqClosed.isClosed
  intro G g hG hlim l
  have hL (l) : TendstoLocallyUniformly (fun j => G j l) (g l) atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ((tendsto_pi_nhds.mp hlim) l)
  have hD (i) : TendstoLocallyUniformly (fun j => coordDeriv (G j l) i) (g (i::l)) atTop := by
    have he : (fun j => coordDeriv (G j l) i) = fun j => (G j (i::l) : Space n → ℝ) := by
      funext j x
      exact (hG j l).2 i x
    rw [he]
    exact hL (i::l)
  have H := first_jet_limit (fun j => (hG j l).1) (g l) (fun i => g (i::l)) (hL l) hD
  exact ⟨H.1.differentiable (by norm_num), H.2.1⟩

lemma fderiv_norm_le_coord_bound {n : ℕ} (f : Space n → ℝ) (x : Space n)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ i, |coordDeriv f i x| ≤ M) :
    ‖fderiv ℝ f x‖ ≤ ‖coordinateDual n‖*M := by
  rw [← coordinateDual_fderiv]
  apply (coordinateDual n).le_opNorm _ |>.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (pi_norm_le_iff_of_nonneg hM).mpr (fun i => hb i)

lemma jetSet_compact_of_local_bounds {n : ℕ} {K : Set (JetSpace n)}
    (hK : IsClosed K) (hcoh : ∀ g ∈ K, CoherentJets g)
    (hb : ∀ l R, 0 < R → ∃ M : ℝ≥0, ∀ g ∈ K, ∀ x, ‖x‖ ≤ R →
      |g l x| ≤ M ∧ ‖fderiv ℝ (g l : Space n → ℝ) x‖ ≤ M) : IsCompact K := by
  let F (l : List (Fin n)) := closure (Set.range fun g : K => g.val l)
  have hF (l) : IsCompact (F l) := by
    apply compact_closure_of_local_bounds (fun g : K => (hcoh g.val g.property l).1)
    intro R hR
    obtain ⟨M,hM⟩ := hb l R hR
    exact ⟨M, fun g x hx => hM g.val g.property x hx⟩
  have hprod : IsCompact (Set.pi Set.univ F) := by
    simpa only [Set.pi, Set.mem_univ, forall_true_left] using isCompact_pi_infinite hF
  exact hprod.of_isClosed_subset hK (fun g hg l _ => subset_closure ⟨⟨g,hg⟩, rfl⟩)

end DeGiorgiCompactness
end

end OAI
