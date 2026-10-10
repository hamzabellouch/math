import Mathlib
import OAI.Analysis.HardSphere.Bridges.Index

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma partialBridge_symm (n : ℕ) (s t : ℝ) : partialBridge n s t = partialBridge n t s := by
  simp only [partialBridge, hatKernel, mul_comm (tent _ _ s) (tent _ _ t)]

lemma partialBridge_error (n : ℕ) {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |partialBridge n s t - (min s t-s*t)| ≤ weight n := by
  rcases le_total s t with hst | hts
  · rw [min_eq_left hst]
    exact partialBridge_error_ordered n hs.1 ht.2 hst
  · rw [partialBridge_symm, min_eq_right hts, mul_comm s t]
    exact partialBridge_error_ordered n ht.1 hs.2 hts

lemma partialBridge_tendsto {s t : ℝ}
    (hs : s ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    Filter.Tendsto (fun n ↦ partialBridge n s t) Filter.atTop (𝓝 (min s t-s*t)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ partialBridge_error n hs ht)
  change Filter.Tendsto (fun n ↦ weight n) Filter.atTop (𝓝 0)
  simpa only [weight, mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)) :
      Filter.Tendsto (fun n ↦ (1/4:ℝ)*(1/2:ℝ)^n) Filter.atTop (𝓝 ((1/4:ℝ)*0)))

abbrev PartialIndex (n : ℕ) := Unit ⊕ (Σ m : Fin n, Fin (2 ^ m.val))

def partialEmbed (n : ℕ) : PartialIndex n → Index
  | .inl u => .inl u
  | .inr ⟨m,k⟩ => .inr ⟨m.val,k⟩

lemma partialEmbed_injective (n : ℕ) : Function.Injective (partialEmbed n) := by
  intro i j hij
  cases i with
  | inl u =>
    cases j with
    | inl v => exact congrArg Sum.inl (Subsingleton.elim _ _)
    | inr j => cases hij
  | inr i =>
    cases j with
    | inl u => cases hij
    | inr j =>
      obtain ⟨m,k⟩ := i
      obtain ⟨l,q⟩ := j
      simp only [partialEmbed, Sum.inr.injEq] at hij
      cases m; cases l
      cases hij
      rfl

def coefficient (n : ℕ) (t : ℝ) : PartialIndex n → ℝ
  | .inl _ => t
  | .inr ⟨m,k⟩ => amplitude m.val * tent m.val k t

def partialPath (n : ℕ) (ω : Noise) : C(Time,ℝ) :=
  ω (.inl ()) • ⟨fun t ↦ t.val, continuous_subtype_val⟩ +
    ∑ m ∈ Finset.range n, level m ω

lemma partialPath_expansion (n : ℕ) (t : Time) (ω : Noise) :
    partialPath n ω t = ∑ i : PartialIndex n, coefficient n t i * ω (partialEmbed n i) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coefficient, partialEmbed,
    Fintype.sum_unique, partialPath, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul, ContinuousMap.sum_apply, level, tentMap,
    ← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m),
    amplitude m * tent m k t * ω (.inr ⟨m,k⟩)) n]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro m _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma coefficient_covariance (n : ℕ) (s t : ℝ) :
    ∑ i : PartialIndex n, coefficient n s i * coefficient n t i =
      s*t + partialBridge n s t := by
  have hamp (m : ℕ) : amplitude m ^ 2 = weight m := by
    have hs : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    simp only [amplitude, mul_pow, weight]
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, inv_pow, hs]
    norm_num
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, coefficient, Fintype.sum_unique]
  rw [Fin.sum_univ_eq_sum_range (fun m ↦ ∑ k : Fin (2^m),
    amplitude m * tent m k s * (amplitude m * tent m k t)) n]
  congr 1
  unfold partialBridge
  apply Finset.sum_congr rfl
  intro m _
  rw [hatKernel, Finset.mul_sum, ← hamp]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma independent_coordinates : iIndepFun (fun i ω ↦ ω i) law :=
  iIndepFun_infinitePi (fun _ ↦ measurable_id)

lemma finite_coordinate_law (n : ℕ) (c : PartialIndex n → ℝ) :
    HasLaw (fun ω ↦ ∑ i, c i * ω (partialEmbed n i))
      (gaussianReal 0 (∑ i, NNReal.mk ((c i)^2) (sq_nonneg _))) law := by
  have hh (i : PartialIndex n) : HasLaw (fun ω ↦ c i * ω (partialEmbed n i))
      (gaussianReal 0 (NNReal.mk ((c i)^2) (sq_nonneg _))) law := by
    simpa only [mul_zero, mul_one] using
      gaussianReal_const_mul (coordinate_preserving (partialEmbed n i)).hasLaw (c i)
  exact hasLaw_centered_gaussian_sum hh
    ((independent_coordinates.precomp (partialEmbed_injective n)).comp
      (fun i x ↦ c i*x) (fun i ↦ by fun_prop))

lemma square_sum_covariance {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℝ) (f : ι → κ → ℝ) :
    ∑ u, (∑ i, c i*f i u)^2 = ∑ i, ∑ j, c i*c j*(∑ u, f i u*f j u) := by
  simp only [pow_two, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro u _
  ring

lemma ae_partialPath_tendsto : ∀ᵐ ω ∂law,
    Tendsto (fun n ↦ partialPath n ω) atTop (𝓝 (path ω)) := by
  filter_upwards [ae_summable_level] with ω hω
  exact tendsto_const_nhds.add hω.hasSum.tendsto_sum_nat

lemma finite_projection_expansion {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) (ω : Noise) :
    ∑ i, c i * partialPath n ω (t i) =
      ∑ u : PartialIndex n, (∑ i, c i * coefficient n (t i) u) * ω (partialEmbed n u) := by
  simp_rw [partialPath_expansion, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma finite_projection_variance {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) :
    ∑ u : PartialIndex n, (∑ i, c i * coefficient n (t i) u)^2 =
      ∑ i, ∑ j, c i*c j*((t i : ℝ)*(t j : ℝ)+partialBridge n (t i) (t j)) := by
  rw [square_sum_covariance]
  simp_rw [coefficient_covariance]

lemma finite_projection_law {ι : Type*} [Fintype ι]
    (n : ℕ) (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * partialPath n ω (t i))
      (gaussianReal 0 (Real.toNNReal
        (∑ i, ∑ j, c i*c j*((t i : ℝ)*(t j : ℝ)+partialBridge n (t i) (t j))))) law := by
  have hh := finite_coordinate_law n (fun u ↦ ∑ i, c i * coefficient n (t i) u)
  simp_rw [finite_projection_expansion]
  convert hh using 2
  rw [← finite_projection_variance]
  change Real.toNNReal (∑ u : PartialIndex n,
    ((NNReal.mk ((∑ i, c i * coefficient n (t i) u)^2) (sq_nonneg _) : ℝ≥0) : ℝ)) = _
  rw [← NNReal.coe_sum, Real.toNNReal_coe]

lemma path_projection_law {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i * path ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, c i*c j*min (t i : ℝ) (t j : ℝ)))) law := by
  refine hasLaw_gaussian_of_ae_tendsto (fun n ↦ finite_projection_law n c t) ?_
    tendsto_const_nhds ?_
  · filter_upwards [ae_partialPath_tendsto] with ω hω
    apply tendsto_finsetSum
    intro i _
    exact tendsto_const_nhds.mul ((continuous_eval_const (t i)).tendsto _ |>.comp hω)
  · apply continuous_real_toNNReal.tendsto _ |>.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    have hh := ((tendsto_const_nhds (x := (t i : ℝ)*(t j : ℝ))).add
      (partialBridge_tendsto (t i).property (t j).property)).const_mul (c i*c j)
    convert hh using 1
    congr 1
    ring

lemma finite_linear_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (x : ι → ℝ) :
    L x = ∑ i, L (Pi.single i 1) * x i := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma finite_path_gaussian {ι : Type*} [Fintype ι] (t : ι → Time) :
    HasGaussianLaw (fun ω i ↦ path ω (t i)) law := by
  classical
  have hm : Measurable (fun ω i ↦ path ω (t i)) :=
    Measurable.of_eval fun coordinate ↦
      (continuous_eval_const (t coordinate)).measurable.comp measurable_path
  refine ⟨hm.aemeasurable, ?_⟩
  apply isGaussian_of_map_eq_gaussianReal
  intro L
  refine ⟨0, Real.toNNReal (∑ i, ∑ j,
    L (Pi.single i 1)*L (Pi.single j 1)*min (t i : ℝ) (t j : ℝ)), ?_⟩
  rw [Measure.map_map L.continuous.measurable hm]
  convert (path_projection_law (fun i ↦ L (Pi.single i 1)) t).map_eq using 1
  congr 1
  funext ω
  exact finite_linear_projection L _

lemma path_isGaussianProcess : IsGaussianProcess (fun t ω ↦ path ω t) law where
  hasGaussianLaw I := finite_path_gaussian (fun t : I ↦ t.val)

lemma path_eval_law (t : Time) :
    HasLaw (fun ω ↦ path ω t) (gaussianReal 0 (Real.toNNReal t.val)) law := by
  simpa using path_projection_law (fun _ : Unit ↦ (1:ℝ)) (fun _ ↦ t)

lemma path_mean (t : Time) : ∫ ω, path ω t ∂law = 0 := by
  rw [(path_eval_law t).integral_eq, integral_id_gaussianReal]

lemma path_variance (t : Time) : Var[fun ω ↦ path ω t; law] = t.val := by
  rw [(path_eval_law t).variance_eq, variance_id_gaussianReal, Real.coe_toNNReal _ t.property.1]

lemma path_add_law (s t : Time) :
    HasLaw (fun ω ↦ path ω s + path ω t)
      (gaussianReal 0 ((s:ℝ)+(t:ℝ)+2*min (s:ℝ) (t:ℝ)).toNNReal) law := by
  have hh := path_projection_law (fun _ : Bool ↦ (1:ℝ)) (fun b ↦ if b then s else t)
  simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul, min_self] at hh
  convert hh using 1
  congr 1
  congr 1
  rw [min_comm (t:ℝ) (s:ℝ)]
  ring

lemma path_covariance (s t : Time) :
    cov[fun ω ↦ path ω s, fun ω ↦ path ω t; law] = min (s:ℝ) (t:ℝ) := by
  have hs : 0 ≤ (s:ℝ) := s.property.1
  have ht : 0 ≤ (t:ℝ) := t.property.1
  have hmin : 0 ≤ min (s:ℝ) (t:ℝ) := le_min hs ht
  have hvar := variance_fun_add (path_eval_law s).hasGaussianLaw.memLp_two
    (path_eval_law t).hasGaussianLaw.memLp_two
  rw [path_variance s, path_variance t, (path_add_law s t).variance_eq,
    variance_id_gaussianReal, Real.coe_toNNReal _ (by positivity)] at hvar
  linarith

lemma wiener_projection_law {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω : C(Time,ℝ) ↦ ∑ i, c i * ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, c i*c j*min (t i : ℝ) (t j : ℝ)))) wiener := by
  have hm : Measurable (fun ω : C(Time,ℝ) ↦ ∑ i, c i * ω (t i)) :=
    (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_eval_const (t i))).measurable
  refine ⟨hm.aemeasurable, ?_⟩
  rw [wiener, Measure.map_map hm measurable_path]
  exact (path_projection_law c t).map_eq

abbrev BridgeIndex := Σ n : ℕ, Fin (2^n)
abbrev BridgeNoise := BridgeIndex → ℝ

def linearPath : C(Time,ℝ) := ⟨fun t ↦ t.val, continuous_subtype_val⟩
def rest (ω : Noise) : BridgeNoise := fun i ↦ ω (.inr i)
def embedRest (η : BridgeNoise) : Noise := Sum.elim (fun _ ↦ 0) η
def bridgeMap (η : BridgeNoise) : C(Time,ℝ) := path (embedRest η)
def bridge (ω : Noise) : C(Time,ℝ) := bridgeMap (rest ω)

lemma measurable_bridgeMap : Measurable bridgeMap := by
  apply measurable_path.comp
  apply Measurable.of_eval
  intro i
  cases i with
  | inl u => exact measurable_const
  | inr i => exact measurable_pi_apply i

lemma measurable_rest : Measurable rest := Measurable.of_eval fun _ ↦ measurable_pi_apply _
lemma measurable_bridge : Measurable bridge := measurable_bridgeMap.comp measurable_rest

lemma independent_base_rest : IndepFun (fun ω : Noise ↦ ω (.inl ())) rest law := by
  classical
  apply IndepFun.indepFun_process (measurable_pi_apply _) (fun i ↦ measurable_pi_apply _)
  intro I
  let S : Finset Index := {.inl ()}
  let T : Finset Index := I.image Sum.inr
  have hd : Disjoint S T := by simp [S,T]
  have h := iIndepFun.indepFun_finset S T hd independent_coordinates (fun i ↦ measurable_pi_apply i)
  let a : S := ⟨.inl (), by simp [S]⟩
  let b (i : I) : T := ⟨.inr i.val, Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  exact h.comp (measurable_pi_apply a)
    (Measurable.of_eval fun coordinate ↦ measurable_pi_apply (b coordinate))

lemma independent_base_bridge : IndepFun (fun ω : Noise ↦ ω (.inl ())) bridge law :=
  independent_base_rest.comp measurable_id measurable_bridgeMap

lemma bridge_eq (ω : Noise) : bridge ω = ∑' n, level n ω := by
  simp only [bridge, bridgeMap, path, embedRest, Sum.elim_inl, zero_smul, zero_add]
  congr 1

lemma path_decomposition (ω : Noise) : path ω = ω (.inl ()) • linearPath + bridge ω := by
  rw [bridge_eq]
  rfl

lemma bridge_at_zero (ω : Noise) : bridge ω 0 = 0 := path_at_zero _
lemma bridge_at_one (ω : Noise) : bridge ω 1 = 0 := path_at_one _

def bridgeLaw : Measure C(Time,ℝ) := law.map bridge
instance : IsProbabilityMeasure bridgeLaw := by unfold bridgeLaw; infer_instance

lemma endpoint_bridge_law :
    HasLaw (fun ω : Noise ↦ (ω (.inl ()), bridge ω))
      ((gaussianReal 0 1).prod bridgeLaw) law := by
  refine ⟨((measurable_pi_apply _).prodMk measurable_bridge).aemeasurable, ?_⟩
  rw [independent_base_bridge.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
    measurable_bridge.aemeasurable, (coordinate_preserving (.inl ())).map_eq]
  rfl

lemma wiener_disintegration : wiener = ((gaussianReal 0 1).prod bridgeLaw).map
    (fun p : ℝ × C(Time,ℝ) ↦ p.1 • linearPath + p.2) := by
  rw [wiener, ← endpoint_bridge_law.map_eq,
    Measure.map_map (by fun_prop) ((measurable_pi_apply _).prodMk measurable_bridge)]
  congr 1
  funext ω
  exact path_decomposition ω

lemma bridge_apply (ω : Noise) (t : Time) : bridge ω t = path ω t - t.val * path ω 1 := by
  have h := congrArg (fun f : C(Time,ℝ) ↦ f t) (path_decomposition ω)
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, linearPath,
    ContinuousMap.coe_mk, smul_eq_mul] at h
  rw [path_at_one]
  linarith

lemma bridge_projection_algebra {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ι → Time) :
    let a : Option ι → ℝ := fun i ↦ i.elim (-∑ i, c i*(t i:ℝ)) c
    let u : Option ι → Time := fun i ↦ i.elim 1 t
    (∑ i, ∑ j, a i*a j*min (u i:ℝ) (u j:ℝ)) =
      ∑ i, ∑ j, c i*c j*(min (t i:ℝ) (t j:ℝ) - (t i:ℝ)*(t j:ℝ)) := by
  let A : ℝ := ∑ i, c i*(t i:ℝ)
  have hh : (∑ i, ∑ j, c i*c j*((t i:ℝ)*(t j:ℝ))) = A*A := by
    dsimp only [A]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h1 : (∑ i, (-A)*c i*(t i:ℝ)) = -A*A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i, c i*(-A)*(t i:ℝ)) = -A*A := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  dsimp only
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some,
    show ((1:Time):ℝ) = 1 from rfl, min_self, min_eq_right (t _).property.2,
    min_eq_left (t _).property.2, mul_one]
  simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  change (-A)*(-A) + (∑ i, (-A)*c i*(t i:ℝ)) +
    ((∑ i, c i*(-A)*(t i:ℝ)) + _) = _
  rw [h1,h2,hh]
  ring

lemma bridge_projection_law {ι : Type*} [Fintype ι] (c : ι → ℝ) (t : ι → Time) :
    HasLaw (fun ω ↦ ∑ i, c i*bridge ω (t i))
      (gaussianReal 0 (Real.toNNReal (∑ i, ∑ j, c i*c j*
        (min (t i:ℝ) (t j:ℝ) - (t i:ℝ)*(t j:ℝ))))) law := by
  have h := path_projection_law (fun i : Option ι ↦ i.elim (-∑ i, c i*(t i:ℝ)) c)
    (fun i ↦ i.elim 1 t)
  rw [bridge_projection_algebra] at h
  convert h using 1
  funext ω
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some, bridge_apply,
    mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_mul]
  simp only [mul_assoc]
  ring

def denseEval (f : C(Time,ℝ)) : ℕ → ℝ := fun n ↦ f (TopologicalSpace.denseSeq Time n)

lemma denseEval_embedding : MeasurableEmbedding denseEval := by
  apply Measurable.measurableEmbedding
  · exact Measurable.of_eval fun _ ↦ (continuous_eval_const _).measurable
  · intro f g h
    apply DFunLike.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq Time).equalizer f.continuous g.continuous h

lemma continuous_path_law_ext {X Y : Noise → C(Time,ℝ)}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ {ι : Type} [Fintype ι] (c : ι → ℝ) (t : ι → Time),
      law.map (fun ω ↦ ∑ i, c i * X ω (t i)) =
        law.map (fun ω ↦ ∑ i, c i * Y ω (t i))) :
    law.map X = law.map Y := by
  apply denseEval_embedding.map_injective
  rw [Measure.map_map denseEval_embedding.measurable hX,
    Measure.map_map denseEval_embedding.measurable hY]
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (denseEval_embedding.measurable.comp hX).aemeasurable
    (denseEval_embedding.measurable.comp hY).aemeasurable).mpr
  intro I
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  congr 1
  have hXm : Measurable (fun ω ↦ I.restrict (fun x ↦ denseEval (X ω) x)) :=
    Measurable.of_eval fun coordinate ↦ (measurable_pi_apply coordinate.val).comp
      (denseEval_embedding.measurable.comp hX)
  have hYm : Measurable (fun ω ↦ I.restrict (fun x ↦ denseEval (Y ω) x)) :=
    Measurable.of_eval fun coordinate ↦ (measurable_pi_apply coordinate.val).comp
      (denseEval_embedding.measurable.comp hY)
  simp only [Function.comp_def, Finset.restrict_def] at hXm hYm ⊢
  rw [Measure.map_map L.continuous.measurable hXm,
    Measure.map_map L.continuous.measurable hYm]
  convert h (fun i : I ↦ L (Pi.single i 1))
    (fun i : I ↦ TopologicalSpace.denseSeq Time i.val) using 1 <;>
    congr 1 <;> funext ω <;> exact finite_linear_projection L _

def prefixTime (u : Time) : C(Time,Time) where
  toFun t := ⟨(u:ℝ)*(t:ℝ), mul_nonneg u.property.1 t.property.1,
    (mul_le_of_le_one_left t.property.1 u.property.2).trans t.property.2⟩
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

def suffixTime (u : Time) : C(Time,Time) where
  toFun t := ⟨(u:ℝ)+(1-(u:ℝ))*(t:ℝ), by
    constructor
    · nlinarith [u.property.1,u.property.2,t.property.1]
    · nlinarith [u.property.1,u.property.2,t.property.1,t.property.2]⟩
  continuous_toFun := (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _

end HardSphere.Wiener
end
end
end
end
end

end OAI
