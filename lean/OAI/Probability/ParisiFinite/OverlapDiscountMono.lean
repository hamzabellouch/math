import Mathlib
import OAI.Probability.ParisiFinite.EmpiricalExpLog

namespace OAI

/-! Overlap Discount Mono. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma overlapDiscount_mono (μ : ProbabilityMeasure OverlapArray) : Monotone (overlapDiscount μ) := by
  intro x y hxy
  exact measureReal_mono (fun z hz => hz.trans hxy)

lemma overlapDiscount_le_one (μ : ProbabilityMeasure OverlapArray) (q : ℝ) : overlapDiscount μ q≤1 := by
  let := entryLaw_probability μ 0 1
  exact measureReal_le_one

lemma uniform_schedule_penalty {d : ℕ} (a : Fin d → ℝ≥0) (c : ℝ≥0) (t : ℝ) :
    penalty t (List.ofFn (fun k => (a k,c)))=
      ∑ k,(a k:ℝ)*((t+((k.val:ℝ)+1)*c)^2-(t+(k.val:ℝ)*c)^2)/4 := by
  induction d generalizing t with
  | zero => simp [penalty]
  | succ d ih =>
    rw [List.ofFn_succ,penalty,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,Nat.cast_zero,zero_add,one_mul,zero_mul,add_zero,Fin.val_succ,Nat.cast_add,Nat.cast_one]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    congr 2
    ring

def gridSchedule (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) (m : ℕ) : Schedule :=
  List.ofFn (fun k : Fin (m+1) =>
    (Real.toNNReal (overlapDiscount μ (cavityGrid m k.succ))*β,
      ⟨gridZVariance m k,gridZVariance_nonneg m k⟩))

lemma gridSchedule_admissible (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) (m : ℕ) :
    Admissible β (gridSchedule μ β m) := by
  refine ⟨?_,?_,?_⟩
  · simp only [width,gridSchedule,List.map_ofFn,List.sum_ofFn,Function.comp_def]
    change (∑ _ : Fin (m+1), (1:ℝ)/(m+1:ℕ))=1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hn : ((m+1:ℕ):ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    field_simp
  · apply List.pairwise_ofFn.mpr
    intro i j hij
    exact mul_le_mul_of_nonneg_right (Real.toNNReal_mono ((overlapDiscount_mono μ)
      ((cavityGrid_mono m) (Fin.succ_le_succ_iff.mpr hij.le)))) (by positivity : 0≤β)
  · intro l hl
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hl
    simp only [NNReal.coe_mul]
    rw [Real.coe_toNNReal _ (show 0≤overlapDiscount μ (cavityGrid m k.succ) from measureReal_nonneg)]
    have ha := overlapDiscount_le_one μ (cavityGrid m k.succ)
    nlinarith [β.coe_nonneg]

lemma gridSchedule_penalty (μ : ProbabilityMeasure OverlapArray) (β : ℝ≥0) (m : ℕ) :
    penalty 0 (gridSchedule μ β m)=
      (β:ℝ)/2*∑ k,overlapDiscount μ (cavityGrid m k.succ)*gridYVariance m k := by
  let c : ℝ≥0 := ⟨1/(m+1:ℕ),by positivity⟩
  change penalty 0 (List.ofFn (fun k : Fin (m+1) => (Real.toNNReal (overlapDiscount μ (cavityGrid m k.succ))*β,c)))=_
  rw [uniform_schedule_penalty,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [NNReal.coe_mul,zero_add]
  rw [Real.coe_toNNReal _ (show 0≤overlapDiscount μ (cavityGrid m k.succ) from measureReal_nonneg)]
  change overlapDiscount μ (cavityGrid m k.succ)*(β:ℝ)*
    ((((k.val:ℝ)+1)*(1/(m+1:ℕ)))^2-((k.val:ℝ)*(1/(m+1:ℕ)))^2)/4=
      (β:ℝ)/2*(overlapDiscount μ (cavityGrid m k.succ)*((2*(k.val:ℝ)+1)/(2*(m+1:ℕ)^2)))
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

 

theorem gridCavityMixture_tendsto {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    (m : ℕ) {β : ℝ} (hβ : 0<β) :
    Tendsto (fun r => gridCavityMixture μ m (r+1) β) atTop
      (𝓝 (β*functional β (gridSchedule μ (Real.toNNReal β) m))) := by
  let a (k : Fin (m+1)) := overlapDiscount μ (cavityGrid m k.succ)
  let s (k : Fin (m+1)) := Real.sqrt (gridZVariance m k)
  let t (k : Fin (m+1)) := Real.sqrt (gridYVariance m k)
  have hc := hierarchyField_lipschitz_tendsto hG hgg hu hex (cavityGrid m) (cavityGrid_mono m)
    (cavityGrid_root m) (cavityGrid_last m) s (lipschitz_log_cosh hβ) 0
  have ha : LipschitzWith (Real.toNNReal β) (fun x : ℝ => β*x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq,← mul_sub,abs_mul,abs_of_pos hβ,Real.coe_toNNReal β hβ.le]
    exact le_rfl
  have hy := hierarchyField_lipschitz_tendsto hG hgg hu hex (cavityGrid m) (cavityGrid_mono m)
    (cavityGrid_root m) (cavityGrid_last m) t ha 0
  have hec : scalarHierarchy a s (fun x => Real.log (2*Real.cosh (β*x))) 0=
      β*recursion β (gridSchedule μ (Real.toNNReal β) m) 0 := by
    have hh := gaussianHierarchy_cosh_schedule (fun k => Real.toNNReal (a k))
      (fun k => (⟨gridZVariance m k,gridZVariance_nonneg m k⟩ : ℝ≥0)) hβ 0
    change gaussianHierarchyRisk (fun k => (Real.toNNReal (a k):ℝ))
      (fun z => Real.log (2*Real.cosh (β*(0+∑ k,Real.sqrt (gridZVariance m k)*z k))))=
        β*recursion β (gridSchedule μ (Real.toNNReal β) m) 0 at hh
    rw [gaussianHierarchyRisk_sum (fun k => (Real.toNNReal (a k):ℝ))
      (fun k => Real.sqrt (gridZVariance m k)) (fun x => Real.log (2*Real.cosh (β*x))) 0] at hh
    have hm (k : Fin (m+1)) : (Real.toNNReal (a k):ℝ)=a k := Real.coe_toNNReal _ measureReal_nonneg
    simpa only [hm,a,s,gridSchedule] using hh
  have hey : scalarHierarchy a t (fun x => β*x) 0=
      β^2/2*∑ k,a k*gridYVariance m k := by
    have hh := scalarHierarchy_affine a t β 0 0
    simp only [add_zero,mul_zero,zero_add] at hh
    rw [hh]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [Real.sq_sqrt (gridYVariance_nonneg m k)]
  have he : scalarHierarchy a s (fun x => Real.log (2*Real.cosh (β*x))) 0-
      scalarHierarchy a t (fun x => β*x) 0=β*functional β (gridSchedule μ (Real.toNNReal β) m) := by
    rw [hec,hey,functional,gridSchedule_penalty,Real.coe_toNNReal β hβ.le]
    dsimp only [a]
    ring
  have hh := hc.sub hy
  simp only [zero_add] at hh
  have heq (r : ℕ) :
      hierarchyFieldValue μ (cavityGrid m) (r+1) (fun z => Real.log (2*Real.cosh (β*(∑ k,s k*z k))))-
      hierarchyFieldValue μ (cavityGrid m) (r+1) (fun z => β*(∑ k,t k*z k))=gridCavityMixture μ m (r+1) β :=
    (gridCavityMixture_fields μ m (Nat.succ_pos r) hβ).symm
  simp only [heq] at hh
  change Tendsto (fun r => gridCavityMixture μ m (r+1) β) atTop
    (𝓝 (scalarHierarchy a s (fun x => Real.log (2*Real.cosh (β*x))) 0-
      scalarHierarchy a t (fun x => β*x) 0)) at hh
  rw [he] at hh
  exact hh

lemma quadratic_indices_tendsto : Tendsto (fun k : ℕ => (k+1)^2) atTop atTop :=
  tendsto_atTop_mono (fun k => (by nlinarith : k≤(k+1)^2)) tendsto_id

 

theorem gridFunctional_cavity_error {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    {β v : ℝ} (hβ : 0<β) (hv : Tendsto (quadraticCavitySamples μ β) atTop (𝓝 v)) (m : ℕ) :
    |v-β*functional β (gridSchedule μ (Real.toNNReal β) m)|≤β^2*Real.pi/(m+1:ℕ) := by
  have hs := gridCavityMixture_tendsto (μ:=μ) hG hgg hu hex m hβ
  have hg : Tendsto (fun r => gridCavityMixture μ m r β) atTop
      (𝓝 (β*functional β (gridSchedule μ (Real.toNNReal β) m))) :=
    (tendsto_add_atTop_iff_nat 1).mp hs
  have hh := hg.comp quadratic_indices_tendsto
  apply le_of_tendsto (hv.sub hh).abs
  exact Eventually.of_forall fun k => gridCavityMixture_error hG hgg hu hex m (by positivity : 0<(k+1)^2) β

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiGuerra
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite SKCavity

 

theorem exists_admissible_schedule_sequence {β : ℝ} (hβ : 0<β) :
    ∃ ls : ℕ → Schedule, (∀ m,Admissible β (ls m)) ∧
      Tendsto (fun m => functional β (ls m)) atTop (𝓝 (limitingFreeEnergy β)) := by
  obtain ⟨μ,v,hG,hgg,hex,hu,hv,hbound⟩ := exists_scalar_ultrametric_cavity hβ
  let ls (m : ℕ) := gridSchedule μ (Real.toNNReal β) m
  have ha (m : ℕ) : Admissible β (ls m) := by
    simpa only [Real.coe_toNNReal β hβ.le] using gridSchedule_admissible μ (Real.toNNReal β) m
  have hl (m : ℕ) : limitingFreeEnergy β≤functional β (ls m) := by
    simpa only [Real.coe_toNNReal β hβ.le] using
      limitingFreeEnergy_le_functional (Real.toNNReal β) (Real.toNNReal_pos.mpr hβ) (ls m)
        (gridSchedule_admissible μ (Real.toNNReal β) m)
  have hupp (m : ℕ) : functional β (ls m)≤limitingFreeEnergy β+β*Real.pi/(m+1:ℕ) := by
    have hh := (abs_le.mp (gridFunctional_cavity_error hG hgg hu hex hβ hv m)).1
    change -(β^2*Real.pi/(m+1:ℕ))≤v-β*functional β (ls m) at hh
    have hdiv : β^2*Real.pi/(m+1:ℕ)=β*(β*Real.pi/(m+1:ℕ)) := by ring
    rw [hdiv] at hh
    nlinarith
  have he : Tendsto (fun m : ℕ => β*Real.pi/(m+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
    convert tendsto_succ_reciprocal.const_mul (β*Real.pi) using 1 <;> simp only [mul_zero,mul_one_div]
  refine ⟨ls,ha,?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using tendsto_const_nhds.add he) hl hupp

 

def finiteParisiValues (β : ℝ) : Set ℝ :=
  {x | ∃ ls : Schedule,Admissible β ls ∧ functional β ls=x}

def finiteParisiInfimum (β : ℝ) : ℝ := sInf (finiteParisiValues β)

lemma finiteParisiValues_nonempty {β : ℝ} (hβ : 0<β) :
    (finiteParisiValues β).Nonempty := by
  obtain ⟨ls,ha,_⟩ := exists_admissible_schedule_sequence hβ
  exact ⟨functional β (ls 0),ls 0,ha 0,rfl⟩

lemma finiteParisiValues_bddBelow {β : ℝ} (hβ : 0<β) :
    BddBelow (finiteParisiValues β) := by
  refine ⟨limitingFreeEnergy β,?_⟩
  rintro x ⟨ls,ha,rfl⟩
  simpa only [Real.coe_toNNReal β hβ.le] using
    limitingFreeEnergy_le_functional (Real.toNNReal β) (Real.toNNReal_pos.mpr hβ) ls
      (by simpa only [Real.coe_toNNReal β hβ.le] using ha)

 

theorem limitingFreeEnergy_eq_finiteParisiInfimum {β : ℝ} (hβ : 0<β) :
    limitingFreeEnergy β=finiteParisiInfimum β := by
  apply le_antisymm
  · apply le_csInf (finiteParisiValues_nonempty hβ)
    rintro x ⟨ls,ha,rfl⟩
    simpa only [Real.coe_toNNReal β hβ.le] using
      limitingFreeEnergy_le_functional (Real.toNNReal β) (Real.toNNReal_pos.mpr hβ) ls
        (by simpa only [Real.coe_toNNReal β hβ.le] using ha)
  · obtain ⟨ls,ha,ht⟩ := exists_admissible_schedule_sequence hβ
    apply ge_of_tendsto ht
    exact Eventually.of_forall fun m => csInf_le (finiteParisiValues_bddBelow hβ) ⟨ls m,ha m,rfl⟩

lemma exists_admissible_functional_lt {β ε : ℝ} (hβ : 0<β) (hε : 0<ε) :
    ∃ ls : Schedule,Admissible β ls ∧ functional β ls<limitingFreeEnergy β+ε := by
  obtain ⟨ls,ha,ht⟩ := exists_admissible_schedule_sequence hβ
  obtain ⟨m,hm⟩ := ((tendsto_order.mp ht).2 _ (lt_add_of_pos_right _ hε)).exists
  exact ⟨ls m,ha m,hm⟩

end ParisiGuerra

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma logMean_expectation_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a : ℝ} (ha : 0≤a) {f : Ω → ℝ}
    (hf : Integrable f μ) (he : Integrable (fun z => Real.exp (a*f z)) μ) :
    (∫ z,f z ∂μ)≤logMean μ a f := by
  by_cases h0 : a=0
  · simp [logMean,h0]
  have hap : 0<a := lt_of_le_of_ne ha (Ne.symm h0)
  have hh := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) (hf.const_mul a) he
  simp only [integral_const_mul] at hh
  have hp := integral_exp_pos he
  have hl := Real.log_le_log (Real.exp_pos _) hh
  rw [Real.log_exp] at hl
  simpa only [logMean,h0,↓reduceIte] using (le_div_iff₀ hap).mpr (by nlinarith)

lemma logMean_parameter_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0≤a) (hab : a≤b) {f : Ω → ℝ}
    (hf : Integrable f μ) (hea : Integrable (fun z => Real.exp (a*f z)) μ)
    (heb : Integrable (fun z => Real.exp (b*f z)) μ) :
    logMean μ a f≤logMean μ b f := by
  by_cases h0 : a=0
  · rw [h0,logMean_zero]
    exact logMean_expectation_le (ha.trans hab) hf heb
  have hap : 0<a := lt_of_le_of_ne ha (Ne.symm h0)
  have hbp : 0<b := hap.trans_le hab
  let p := a/b
  have hp0 : 0≤p := div_nonneg ha hbp.le
  have hp1 : p≤1 := (div_le_one hbp).mpr hab
  have heq (z : Ω) : (Real.exp (b*f z))^p=Real.exp (a*f z) := by
    rw [← Real.exp_mul]
    congr 1
    dsimp [p]
    field_simp
  have hi : Integrable ((fun x : ℝ => x^p) ∘ (fun z => Real.exp (b*f z))) μ := by
    simpa only [Function.comp_def,heq] using hea
  have hh := (Real.concaveOn_rpow hp0 hp1).le_map_integral
    (Real.continuous_rpow_const hp0).continuousOn isClosed_Ici
    (ae_of_all _ fun z => (Real.exp_pos (b*f z)).le) heb hi
  simp only [heq] at hh
  have hla := integral_exp_pos hea
  have hlb := integral_exp_pos heb
  have hl := Real.log_le_log hla hh
  rw [Real.log_rpow hlb] at hl
  simp only [logMean,h0,ne_of_gt hbp,↓reduceIte]
  apply (div_le_div_iff₀ hap hbp).mpr
  have he : p*Real.log (∫ z,Real.exp (b*f z) ∂μ)*b=
      Real.log (∫ z,Real.exp (b*f z) ∂μ)*a := by dsimp [p]; field_simp
  nlinarith

lemma step_parameter_mono {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {a b : ℝ} (ha : 0≤a) (hab : a≤b) (s x : ℝ) :
    step a s f x≤ step b s f x :=
  logMean_parameter_mono ha hab (integrable_shift hf x s)
    (integrable_exp_shift hf a x s) (integrable_exp_shift hf b x s)

lemma step_le_of_le {L K : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : LipschitzWith K g) {a : ℝ} (ha : 0≤a) (s x : ℝ) (hfg : ∀ y,f y≤g y) :
    step a s f x≤ step a s g x :=
  logMean_mono ha (integrable_shift hf x s) (integrable_shift hg x s)
    (integrable_exp_shift hf a x s) (integrable_exp_shift hg a x s) (fun _ => hfg _)

lemma step_stable {L K : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : LipschitzWith K g) {a : ℝ} (ha : 0≤a) (s x c : ℝ) (hfg : ∀ y,|f y-g y|≤c) :
    |step a s f x-step a s g x|≤c :=
  logMean_stable ha (integrable_shift hf x s) (integrable_shift hg x s)
    (integrable_exp_shift hf a x s) (integrable_exp_shift hg a x s) c (fun _ => hfg _)

end ParisiFinite

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

def gaussianSmallError (β s : ℝ) : ℝ :=
  logMean (gaussianReal 0 1) β (fun z => |s| * |z|)

lemma abs_scaled_lipschitz (s : ℝ) :
    LipschitzWith (Real.toNNReal |s|) (fun z : ℝ => |s| * |z|) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,← mul_sub,abs_mul,abs_abs,Real.coe_toNNReal _ (abs_nonneg s)]
  exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) (abs_nonneg s)

lemma gaussianSmallError_nonneg {β : ℝ} (hβ : 0≤β) (s : ℝ) :
    0≤gaussianSmallError β s := by
  have hi : Integrable (fun z : ℝ => |s| * |z|) (gaussianReal 0 1) := by
    simpa only [zero_add,one_mul] using integrable_shift (abs_scaled_lipschitz s) 0 1
  have he : Integrable (fun z : ℝ => Real.exp (β*(|s| * |z|))) (gaussianReal 0 1) := by
    simpa only [zero_add,one_mul] using integrable_exp_shift (abs_scaled_lipschitz s) β 0 1
  exact (integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans
    (logMean_expectation_le hβ hi he)

 

lemma step_id_error {β a : ℝ} (ha : 0≤a) (hab : a≤β) {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) (s x : ℝ) :
    |step a s f x-f x|≤gaussianSmallError β s := by
  let g (z : ℝ) := |s| * |z|
  have hgi : Integrable g (gaussianReal 0 1) := by
    simpa only [zero_add,one_mul] using integrable_shift (abs_scaled_lipschitz s) 0 1
  have hge (b : ℝ) : Integrable (fun z => Real.exp (b*g z)) (gaussianReal 0 1) := by
    simpa only [zero_add,one_mul] using integrable_exp_shift (abs_scaled_lipschitz s) b 0 1
  have hpoint (z : ℝ) : |f (x+s*z)-f x|≤g z := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,add_sub_cancel_left,abs_mul] using hf.dist_le_mul (x+s*z) x
  have hupper : step a s f x≤logMean (gaussianReal 0 1) a g+f x := by
    exact logMean_le_add ha (integrable_shift hf x s) hgi (integrable_exp_shift hf a x s)
      (hge a) (f x) (fun z => by have hh := (abs_le.mp (hpoint z)).2; linarith)
  have hmono : logMean (gaussianReal 0 1) a g≤gaussianSmallError β s :=
    logMean_parameter_mono ha hab hgi (hge a) (hge β)
  have hexp : (∫ z,f (x+s*z) ∂gaussianReal 0 1)≤ step a s f x :=
    logMean_expectation_le ha (integrable_shift hf x s) (integrable_exp_shift hf a x s)
  have hgexp : (∫ z,g z ∂gaussianReal 0 1)≤gaussianSmallError β s :=
    logMean_expectation_le (ha.trans hab) hgi (hge β)
  have hlow : f x-(∫ z,g z ∂gaussianReal 0 1)≤∫ z,f (x+s*z) ∂gaussianReal 0 1 := by
    have hh := integral_mono ((integrable_const (f x)).sub hgi) (integrable_shift hf x s)
      (fun z => by have hp := (abs_le.mp (hpoint z)).1; simp only [Pi.sub_apply]; linarith)
    simpa only [Pi.sub_apply,integral_sub (integrable_const _) hgi,integral_const,probReal_univ,one_smul] using hh
  rw [abs_le]
  constructor <;> linarith

lemma gaussianSmallError_grid_tendsto (β : ℝ) :
    Tendsto (fun m : ℕ => gaussianSmallError β (Real.sqrt (1/(m+1:ℕ)))) atTop (𝓝 0) := by
  let s (m : ℕ) := Real.sqrt (1/(m+1:ℕ))
  have hs (m : ℕ) : 0≤ s m := Real.sqrt_nonneg _
  have hs1 (m : ℕ) : s m≤1 := by
    apply Real.sqrt_le_one.mpr
    exact (div_le_one (by positivity : (0:ℝ)<(m+1:ℕ))).mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
  have ht : Tendsto s atTop (𝓝 (0:ℝ)) := by
    simpa only [Real.sqrt_zero,Function.comp_def,s] using Real.continuous_sqrt.continuousAt.tendsto.comp SKCavity.tendsto_succ_reciprocal
  have hF (m : ℕ) : LipschitzWith 1 (fun z : ℝ => |s m| * |z|) :=
    (abs_scaled_lipschitz (s m)).weaken (by simpa only [abs_of_nonneg (hs m),Real.toNNReal_le_one] using hs1 m)
  have hf : LipschitzWith 1 (fun _ : ℝ => (0:ℝ)) := (LipschitzWith.const (0:ℝ)).weaken (by norm_num)
  have hh := step_tendsto (fun k => hF k) hf (fun z => by simpa using (ht.abs).mul_const |z|) β 1 0
  simpa only [step,zero_add,one_mul,logMean_const,gaussianSmallError] using hh

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma gaussian_pair_sum_map (s t : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ×ℝ => s*p.1+t*p.2)=
      (gaussianReal 0 1).map (fun z => Real.sqrt (s^2+t^2)*z) := by
  let μ := gaussianReal (0:ℝ) 1
  have hi : IndepFun (fun p : ℝ×ℝ => s*p.1) (fun p : ℝ×ℝ => t*p.2) (μ.prod μ) :=
    indepFun_prod (by fun_prop) (by fun_prop)
  have hX : (μ.prod μ).map (fun p : ℝ×ℝ => s*p.1)=gaussianReal 0 (⟨s^2,sq_nonneg s⟩ : ℝ≥0) := by
    change (μ.prod μ).map ((fun z : ℝ => s*z) ∘ Prod.fst)=_
    rw [← Measure.map_map (by fun_prop : Measurable (fun z : ℝ => s*z)) measurable_fst]
    simp [μ,gaussianReal_map_const_mul,NNReal.mk]
    congr 1
    ext
    change s^2 * 1 = s^2
    ring
  have hY : (μ.prod μ).map (fun p : ℝ×ℝ => t*p.2)=gaussianReal 0 (⟨t^2,sq_nonneg t⟩ : ℝ≥0) := by
    change (μ.prod μ).map ((fun z : ℝ => t*z) ∘ Prod.snd)=_
    rw [← Measure.map_map (by fun_prop : Measurable (fun z : ℝ => t*z)) measurable_snd]
    simp [μ,gaussianReal_map_const_mul,NNReal.mk]
    congr 1
    ext
    change t^2 * 1 = t^2
    ring
  have hh := gaussianReal_add_gaussianReal_of_indepFun hi { map_eq := hX } { map_eq := hY }
  change (μ.prod μ).map (fun p : ℝ×ℝ => s*p.1+t*p.2)=
    gaussianReal (0+0) ((⟨s^2,sq_nonneg s⟩ : ℝ≥0)+(⟨t^2,sq_nonneg t⟩ : ℝ≥0)) at hh
  simp only [zero_add] at hh
  rw [hh,gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    change s^2+t^2 = (Real.sqrt (s^2+t^2))^2 * 1
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg s) (sq_nonneg t)),mul_one]

lemma gaussian_pair_integrable {F : ℝ → ℝ} (hF : Measurable F) (s t : ℝ)
    (hi : Integrable (fun z => F (Real.sqrt (s^2+t^2)*z)) (gaussianReal 0 1)) :
    Integrable (fun p : ℝ×ℝ => F (s*p.1+t*p.2)) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hm : Integrable F ((gaussianReal 0 1).map (fun z => Real.sqrt (s^2+t^2)*z)) :=
    (integrable_map_measure hF.aestronglyMeasurable (by fun_prop)).mpr hi
  rw [← gaussian_pair_sum_map s t] at hm
  exact hm.comp_measurable (by fun_prop)

lemma gaussian_pair_integral {F : ℝ → ℝ} (hF : Measurable F) (s t : ℝ) :
    (∫ p : ℝ×ℝ,F (s*p.1+t*p.2) ∂(gaussianReal 0 1).prod (gaussianReal 0 1))=
      ∫ z,F (Real.sqrt (s^2+t^2)*z) ∂gaussianReal 0 1 := by
  rw [← integral_map (by fun_prop : Measurable (fun p : ℝ×ℝ => s*p.1+t*p.2)).aemeasurable
    hF.aestronglyMeasurable,gaussian_pair_sum_map,
    integral_map (by fun_prop) hF.aestronglyMeasurable]

lemma exp_step {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) {a : ℝ} (ha : a≠0)
    (s x : ℝ) : Real.exp (a*step a s f x)=∫ z,Real.exp (a*f (x+s*z)) ∂gaussianReal 0 1 := by
  simp only [step,logMean,ha,↓reduceIte]
  rw [mul_div_cancel₀ _ ha,Real.exp_log (integral_exp_pos (integrable_exp_shift hf a x s))]

 
lemma step_semigroup {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (a s t x : ℝ) :
    step a s (step a t f) x=step a (Real.sqrt (s^2+t^2)) f x := by
  by_cases ha : a=0
  · subst a
    simp only [step,logMean_zero]
    have hm : Measurable (fun y => f (x+y)) := hf.continuous.measurable.comp (by fun_prop)
    have hi := gaussian_pair_integrable hm s t (integrable_shift hf x (Real.sqrt (s^2+t^2)))
    have hh := gaussian_pair_integral hm s t
    rw [integral_prod _ hi] at hh
    simpa only [add_assoc] using hh
  · have hm : Measurable (fun y => Real.exp (a*f (x+y))) := Real.measurable_exp.comp ((hf.continuous.measurable.comp (by fun_prop)).const_mul a)
    have hi := gaussian_pair_integrable hm s t (integrable_exp_shift hf a x (Real.sqrt (s^2+t^2)))
    have hh := gaussian_pair_integral hm s t
    rw [integral_prod _ hi] at hh
    simp only [step,logMean,ha,↓reduceIte]
    have he (z : ℝ) : Real.exp (a*(Real.log (∫ y,Real.exp (a*f (x+s*z+t*y)) ∂gaussianReal 0 1)/a))=
        ∫ y,Real.exp (a*f (x+s*z+t*y)) ∂gaussianReal 0 1 := by
      simpa only [step,logMean,ha,↓reduceIte] using exp_step hf ha t (x+s*z)
    simp_rw [he]
    congr 2
    simpa only [add_assoc] using hh

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

 
def evolve : Schedule → (ℝ → ℝ) → ℝ → ℝ
  | [],f => f
  | (a,d)::ls,f => step a (Real.sqrt d) (evolve ls f)

lemma evolve_lipschitz {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (ls : Schedule) :
    LipschitzWith L (evolve ls f) := by
  induction ls with
  | nil => exact hf
  | cons l ls ih => exact step_lipschitz ih l.1.coe_nonneg _

lemma recursion_eq_evolve (β : ℝ) (ls : Schedule) : recursion β ls=evolve ls (terminal β) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [recursion,evolve,ih]

lemma evolve_append (ls rs : Schedule) (f : ℝ → ℝ) :
    evolve (ls++rs) f=evolve ls (evolve rs f) := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp only [List.cons_append,evolve,ih]

lemma evolve_stable {L K : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : LipschitzWith K g) (ls : Schedule) (c : ℝ) (hfg : ∀ x,|f x-g x|≤c) :
    ∀ x,|evolve ls f x-evolve ls g x|≤c := by
  induction ls with
  | nil => exact hfg
  | cons l ls ih =>
    exact fun x => step_stable (evolve_lipschitz hf ls) (evolve_lipschitz hg ls) l.1.coe_nonneg _ x c ih

lemma evolve_mono {L K : ℝ≥0} {f g : ℝ → ℝ} (hf : LipschitzWith L f)
    (hg : LipschitzWith K g) (ls : Schedule) (hfg : ∀ x,f x≤g x) :
    ∀ x,evolve ls f x≤evolve ls g x := by
  induction ls with
  | nil => exact hfg
  | cons l ls ih =>
    exact fun x => step_le_of_le (evolve_lipschitz hf ls) (evolve_lipschitz hg ls) l.1.coe_nonneg _ x ih

 

lemma evolve_shift_error {β : ℝ} {a b d : ℝ≥0} (ha : (a:ℝ)≤β) (hb : (b:ℝ)≤β)
    (mid : Schedule) {f : ℝ → ℝ} (hf : LipschitzWith 1 f) (x : ℝ) :
    |evolve ((a,d)::mid) f x-evolve (mid++[(b,d)]) f x|≤
      2*gaussianSmallError β (Real.sqrt d) := by
  let full := (a,d)::(mid++[(b,d)])
  have hleft : |evolve full f x-evolve ((a,d)::mid) f x|≤gaussianSmallError β (Real.sqrt d) := by
    have hh := evolve_stable (step_lipschitz hf b.coe_nonneg (Real.sqrt d)) hf ((a,d)::mid)
      (gaussianSmallError β (Real.sqrt d)) (fun y => step_id_error b.coe_nonneg hb hf _ y) x
    simpa only [full,evolve_append,evolve,List.cons_append] using hh
  have hright : |evolve full f x-evolve (mid++[(b,d)]) f x|≤gaussianSmallError β (Real.sqrt d) :=
    step_id_error a.coe_nonneg ha (evolve_lipschitz hf _) _ x
  calc
    _ ≤ |evolve ((a,d)::mid) f x-evolve full f x|+|evolve full f x-evolve (mid++[(b,d)]) f x| := abs_sub_le _ _ _
    _ ≤ gaussianSmallError β (Real.sqrt d)+gaussianSmallError β (Real.sqrt d) :=
      add_le_add (by simpa only [abs_sub_comm] using hleft) hright
    _ = _ := by ring

lemma evolve_split {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    (a d e : ℝ≥0) (ls : Schedule) :
    evolve ((a,d)::(a,e)::ls) f=evolve ((a,d+e)::ls) f := by
  funext x
  change step a (Real.sqrt d) (step a (Real.sqrt e) (evolve ls f)) x=_
  rw [step_semigroup (evolve_lipschitz hf ls),Real.sq_sqrt d.coe_nonneg,Real.sq_sqrt e.coe_nonneg]
  rfl

end ParisiFinite

 

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

def dyadicSchedule (γ : ℝ≥0 → ℝ≥0) (upper : Bool) (t d : ℝ≥0) : ℕ → Schedule
  | 0 => [(γ (if upper then t+d else t),d)]
  | n+1 => dyadicSchedule γ upper t (d/2) n ++ dyadicSchedule γ upper (t+d/2) (d/2) n

def dyadicMesh (d : ℝ≥0) (n : ℕ) : ℝ≥0 := d/2^n

lemma dyadicMesh_succ (d : ℝ≥0) (n : ℕ) : dyadicMesh d (n+1)=dyadicMesh (d/2) n := by
  simp only [dyadicMesh,pow_succ,div_div]
  congr 1
  exact mul_comm _ _

lemma dyadicSchedule_nonempty (γ : ℝ≥0 → ℝ≥0) (u : Bool) (t d : ℝ≥0) (n : ℕ) :
    dyadicSchedule γ u t d n≠[] := by
  induction n generalizing t d with
  | zero => simp [dyadicSchedule]
  | succ n ih =>
    intro h
    exact ih t (d/2) (List.append_eq_nil_iff.mp h).1

lemma dyadicSchedule_shift (γ : ℝ≥0 → ℝ≥0) (t d : ℝ≥0) (n : ℕ) :
    dyadicSchedule γ false t d n++[(γ (t+d),dyadicMesh d n)]=
      (γ t,dyadicMesh d n)::dyadicSchedule γ true t d n := by
  induction n generalizing t d with
  | zero => simp [dyadicSchedule,dyadicMesh]
  | succ n ih =>
    have he : t+d/2+d/2=t+d := by ring
    simp only [dyadicSchedule,dyadicMesh_succ,List.append_assoc]
    rw [← he,ih (t+d/2) (d/2)]
    rw [← List.singleton_append,← List.append_assoc,ih t (d/2),List.cons_append]

lemma dyadicSchedule_grid_error {β : ℝ} {γ : ℝ≥0 → ℝ≥0}
    (hγ : ∀ t,(γ t:ℝ)≤β) (t d : ℝ≥0) (n : ℕ) {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) (x : ℝ) :
    |evolve (dyadicSchedule γ false t d n) f x-evolve (dyadicSchedule γ true t d n) f x|≤
      2*gaussianSmallError β (Real.sqrt (dyadicMesh d n)) := by
  have hs := dyadicSchedule_shift γ t d n
  have hn := dyadicSchedule_nonempty γ false t d n
  generalize he : dyadicSchedule γ false t d n=ls at hs hn ⊢
  cases ls with
  | nil => exact (hn rfl).elim
  | cons c mid =>
    simp only [List.cons_append,List.cons.injEq] at hs
    rw [hs.1,← hs.2]
    exact evolve_shift_error (hγ t) (hγ (t+d)) mid hf x

lemma dyadicSchedule_low_le_high {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (n : ℕ) (x : ℝ) :
    evolve (dyadicSchedule γ false t d n) f x≤evolve (dyadicSchedule γ true t d n) f x := by
  induction n generalizing t d f x with
  | zero =>
    exact step_parameter_mono hf (γ t).coe_nonneg (by exact_mod_cast hγ (le_add_of_nonneg_right (show 0≤d from zero_le))) _ x
  | succ n ih =>
    simp only [dyadicSchedule,evolve_append]
    exact (evolve_mono (evolve_lipschitz hf _) (evolve_lipschitz hf _) _
      (fun y => ih hf (t+d/2) (d/2) y) x).trans
        (ih (evolve_lipschitz hf _) t (d/2) x)

lemma dyadicSchedule_low_refine {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (n : ℕ) (x : ℝ) :
    evolve (dyadicSchedule γ false t d n) f x≤evolve (dyadicSchedule γ false t d (n+1)) f x := by
  induction n generalizing t d f x with
  | zero =>
    have he : d/2+d/2=d := by ring
    have hh := evolve_split hf (γ t) (d/2) (d/2) []
    rw [he] at hh
    change evolve [(γ t,d)] f x≤evolve [(γ t,d/2),(γ (t+d/2),d/2)] f x
    rw [← hh]
    exact step_le_of_le (step_lipschitz hf (γ t).coe_nonneg _) (step_lipschitz hf (γ (t+d/2)).coe_nonneg _)
      (γ t).coe_nonneg _ x (fun y => step_parameter_mono hf (γ t).coe_nonneg
        (by exact_mod_cast hγ (le_add_of_nonneg_right (show 0≤d/2 from zero_le))) _ y)
  | succ n ih =>
    change evolve (dyadicSchedule γ false t (d/2) n ++ dyadicSchedule γ false (t+d/2) (d/2) n) f x ≤
      evolve (dyadicSchedule γ false t (d/2) (n+1) ++ dyadicSchedule γ false (t+d/2) (d/2) (n+1)) f x
    rw [evolve_append,evolve_append]
    exact (evolve_mono (evolve_lipschitz hf _) (evolve_lipschitz hf _) _
      (fun y => ih hf (t+d/2) (d/2) y) x).trans
        (ih (evolve_lipschitz hf _) t (d/2) x)

lemma dyadicSchedule_high_refine {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f)
    {γ : ℝ≥0 → ℝ≥0} (hγ : Monotone γ) (t d : ℝ≥0) (n : ℕ) (x : ℝ) :
    evolve (dyadicSchedule γ true t d (n+1)) f x≤evolve (dyadicSchedule γ true t d n) f x := by
  induction n generalizing t d f x with
  | zero =>
    have he : d/2+d/2=d := by ring
    have ht : t+d/2+d/2=t+d := by ring
    have hh := evolve_split hf (γ (t+d)) (d/2) (d/2) []
    rw [he] at hh
    simp only [dyadicSchedule,↓reduceIte,List.singleton_append,ht]
    rw [← hh]
    exact step_parameter_mono (step_lipschitz hf (γ (t+d)).coe_nonneg _) (γ (t+d/2)).coe_nonneg
      (by exact_mod_cast hγ (show t+d/2≤t+d by gcongr; exact half_le_self (show 0≤d from zero_le))) _ x
  | succ n ih =>
    change evolve (dyadicSchedule γ true t (d/2) (n+1) ++ dyadicSchedule γ true (t+d/2) (d/2) (n+1)) f x ≤
      evolve (dyadicSchedule γ true t (d/2) n ++ dyadicSchedule γ true (t+d/2) (d/2) n) f x
    rw [evolve_append,evolve_append]
    exact (evolve_mono (evolve_lipschitz hf _) (evolve_lipschitz hf _) _
      (fun y => ih hf (t+d/2) (d/2) y) x).trans
        (ih (evolve_lipschitz hf _) t (d/2) x)

end ParisiFinite

end

end OAI
