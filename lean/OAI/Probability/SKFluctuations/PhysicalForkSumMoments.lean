import Mathlib
import OAI.Probability.SKFluctuations.ComparisonMinimumRegularRawRatio

namespace OAI

/-! Physical Fork Sum Moments. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

 theorem integral_conditionalForkTest_sum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {I : Type} (s : Finset I)
    (F : I → (P × ForwardPath (ι → ℝ) S steps.length) × (P × ForwardPath (ι → ℝ) S steps.length) → ℝ)
    (hF : ∀ i, Measurable (F i)) {R : ℝ} (hFR : ∀ i z, |F i z| ≤ R) :
    (∫ p, conditionalForkTest w φ steps x k (fun z => ∑ i ∈ s, F i z) p
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) =
      ∑ i ∈ s, ∫ p, conditionalForkTest w φ steps x k (F i) p
        ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty,conditionalForkTest,conditionalPathAverage_const hw φ steps ha]
    simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [integral_conditionalForkTest_add hw φ steps ha μ x hx k (hF i)
      (Finset.measurable_sum _ fun j _ => hF j) (hFR i)
      (fun z => (Finset.abs_sum_le_sum_abs _ _).trans
        (show ∑ j ∈ s, |F j z| ≤ (s.card:ℝ)*R by
          simpa using Finset.sum_le_sum (fun j (_ : j ∈ s) => hFR j z))),ih]

 theorem fork_sum_power_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {I : Type} (s : Finset I)
    (F : I → (P × ForwardPath (ι → ℝ) S steps.length) × (P × ForwardPath (ι → ℝ) S steps.length) → ℝ)
    (hF : ∀ i, Measurable (F i)) {R : ℝ} (hFR : ∀ i z, |F i z| ≤ R)
    (p : ℕ) (hp : 1 ≤ p) :
    (∫ q, conditionalForkTest w φ steps x k (fun z => |∑ i ∈ s, F i z|^p) q
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) ≤
      (s.card:ℝ)^(p-1) * ∑ i ∈ s,
        ∫ q, conditionalForkTest w φ steps x k (fun z => |F i z|^p) q
          ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx := by
  let H := fun z => ∑ i ∈ s, |F i z|^p
  let C : ℝ := (s.card:ℝ)^(p-1)
  have hC : 0 ≤ C := pow_nonneg (Nat.cast_nonneg _) _
  have hH : Measurable H := Finset.measurable_sum _ fun i _ => (hF i).abs.pow_const p
  have hsum : Measurable (fun z => ∑ i ∈ s, F i z) := Finset.measurable_sum _ fun i _ => hF i
  have hbnd z : |∑ i ∈ s, F i z| ≤ (s.card:ℝ)*R :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by simpa using Finset.sum_le_sum (fun i (_ : i ∈ s) => hFR i z))
  have hHbnd z : |H z| ≤ (s.card:ℝ)*R^p := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg (abs_nonneg _) _)]
    exact (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hFR i z) p).trans_eq (by simp)
  have hpt z : |∑ i ∈ s, F i z|^p ≤ C*H z := by
    have hhelp := Real.rpow_sum_le_const_mul_sum_rpow s (fun i => F i z)
      (show (1:ℝ) ≤ (p:ℝ) by exact_mod_cast hp)
    have he : (p:ℝ)-1 = ((p-1:ℕ):ℝ) := by exact_mod_cast Nat.cast_sub hp (R := ℝ)
    rw [he] at hhelp
    simp only [Real.rpow_natCast] at hhelp
    exact (pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) p).trans hhelp
  have hle : (∫ q, conditionalForkTest w φ steps x k (fun z => |∑ i ∈ s, F i z|^p) q
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) ≤
      ∫ q, conditionalForkTest w φ steps x k (fun z => C*H z) q
        ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun q => conditionalPathAverage_nonneg _ _ _ _ _
        (fun r => pow_nonneg (abs_nonneg _) _) q)
      (conditionalForkTest_integrable hw φ steps ha μ x hx k (hH.const_mul C)
        (fun z => by rw [abs_mul,abs_of_nonneg hC]; exact mul_le_mul_of_nonneg_left (hHbnd z) hC))
    exact Eventually.of_forall fun q => conditionalPathAverage_mono_bounded hw φ steps ha x k
      ((hsum.abs.pow_const p).comp measurable_prodMk_left)
      ((hH.const_mul C).comp measurable_prodMk_left)
      (fun r => by
        simp only [Function.comp_apply]
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact (pow_le_pow_left₀ (abs_nonneg _) (hbnd (q,r)) p).trans (le_max_left _ (C*((s.card:ℝ)*R^p))))
      (fun r => by
        simp only [Function.comp_apply]
        rw [abs_mul,abs_of_nonneg hC]
        exact (mul_le_mul_of_nonneg_left (hHbnd (q,r)) hC).trans (le_max_right _ _))
      (fun r => hpt (q,r)) q
  simp only [conditionalForkTest,conditionalPathAverage_const_mul,integral_const_mul] at hle
  have he := integral_conditionalForkTest_sum hw φ steps ha μ x hx k s
    (fun i z => |F i z|^p) (fun i => (hF i).abs.pow_const p)
    (fun i z => by rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]; exact pow_le_pow_left₀ (abs_nonneg _) (hFR i z) p)
  exact hle.trans_eq (congrArg (fun r => C*r) he)

 theorem fork_add_power_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x) (k : ℕ)
    {F G : (P × ForwardPath (ι → ℝ) S steps.length) × (P × ForwardPath (ι → ℝ) S steps.length) → ℝ}
    (hF : Measurable F) (hG : Measurable G) {R : ℝ}
    (hFR : ∀ z, |F z| ≤ R) (hGR : ∀ z, |G z| ≤ R) (p : ℕ) (hp : 1 ≤ p) :
    (∫ q, conditionalForkTest w φ steps x k (fun z => |F z+G z|^p) q
      ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx) ≤
      (2:ℝ)^(p-1) *
        ((∫ q, conditionalForkTest w φ steps x k (fun z => |F z|^p) q
          ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx)+
         (∫ q, conditionalForkTest w φ steps x k (fun z => |G z|^p) q
          ∂μ ⊗ₘ (hierarchyPathKernel w φ steps).comap x hx)) := by
  let H := fun (i : Fin 2) => if i=0 then F else G
  have hH i : Measurable (H i) := by dsimp [H]; split_ifs <;> assumption
  have hHR i z : |H i z| ≤ R := by dsimp [H]; split_ifs <;> [exact hFR z; exact hGR z]
  have hh := fork_sum_power_le hw φ steps ha μ x hx k Finset.univ H hH hHR p hp
  simpa [H,Fin.sum_univ_two] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalOverlapMoment (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork : ℕ) : ℝ :=
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
    (fun z => |orderedOverlap n (ForwardPath.spin steps.length z.1.2)
      (ForwardPath.spin steps.length z.2.2)|^(2*l)) p ∂physicalPathLaw μ n steps x hx

 theorem physicalOverlapMoment_le_double_sum (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (hc : OrderedSteps c steps) (hxs : 0 < xs) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (fork t : ℕ) (ht : t ≤ steps.length+1) (cs : List (ℝ × ℕ))
    (hlast : lastLayerCut cs t=steps.length+1) :
    physicalOverlapMoment n l steps μ x hx fork ≤
      (2:ℝ)^(2*l-1) *
        (2*(physicalRawRatio n l steps c xs μ x hx)^(4*l)*(xs+physicalCutMass c steps t)^(2*l) +
         ((physicalOverlapResidualPairs cs).card:ℝ)^(2*l-1) *
           ∑ ij ∈ physicalOverlapResidualPairs cs,
             ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
               (fun z => |physicalOverlapLayerTerm n steps x cs t ij z|^(2*l)) p
               ∂physicalPathLaw μ n steps x hx) := by
  let Ω := PhysicalPathState P n steps
  let F : Ω × Ω → ℝ := fun z => inner ℝ (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2)
  let G : Ω × Ω → ℝ := fun z => ∑ ij ∈ physicalOverlapResidualPairs cs,
    physicalOverlapLayerTerm n steps x cs t ij z
  have hX := actualSpinPath_measurable n steps hc x hx t
  have hF : Measurable F := (hX.comp measurable_fst).inner (hX.comp measurable_snd)
  have hG : Measurable G := Finset.measurable_sum _ fun ij _ =>
    physicalOverlapLayerTerm_measurable n steps hc x hx cs t ij
  have hFR z : |F z| ≤ 1 := by
    have hh := norm_inner_le_norm (𝕜:=ℝ) (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2)
    rw [Real.norm_eq_abs] at hh
    apply hh.trans
    calc
      _ ≤ 1*1 := mul_le_mul (actualSpinPath_norm_le n steps hc x t z.1)
        (actualSpinPath_norm_le n steps hc x t z.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hGR z : |G z| ≤ ((physicalOverlapResidualPairs cs).card:ℝ)*4 :=
    (Finset.abs_sum_le_sum_abs _ _).trans (by
      simpa using (Finset.sum_le_sum
        (fun ij (_ : ij ∈ physicalOverlapResidualPairs cs) => physicalOverlapLayerTerm_abs_le n steps hc x cs t ij z)))
  have hadd := fork_add_power_le (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork hF hG
    (fun z => (hFR z).trans (le_max_left _ (((physicalOverlapResidualPairs cs).card:ℝ)*4)))
    (fun z => (hGR z).trans (le_max_right _ _)) (2*l) (by omega)
  have hsum := fork_sum_power_le (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork
    (physicalOverlapResidualPairs cs) (physicalOverlapLayerTerm n steps x cs t)
    (physicalOverlapLayerTerm_measurable n steps hc x hx cs t)
    (physicalOverlapLayerTerm_abs_le n steps hc x cs t) (2*l) (by omega)
  have hcore := physicalProjectedOverlapMoment_le n l hl steps hc hxs μ x hx fork t ht
  have he : physicalOverlapMoment n l steps μ x hx fork =
      ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
        (fun z => |F z+G z|^(2*l)) p ∂physicalPathLaw μ n steps x hx := by
    unfold physicalOverlapMoment
    congr 1
    funext p
    apply congrArg (fun H => conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork H p)
    funext z
    rw [physicalOverlap_core_add_residual n steps x cs t hlast z]
  rw [he]
  apply le_trans hadd
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
  apply add_le_add
  · simpa only [physicalProjectedOverlapMoment,physicalPathLaw] using hcore
  · simpa only [G,physicalPathLaw] using hsum

end SKFluctuations

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem physicalCutPairPower_futureTerminal (n l : ℕ)
    (common tail pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (a b : ℕ)
    (p : PhysicalPathState P n (common++(pre++tail))) :
    physicalCutPairPower n l (common++(pre++tail)) x common.length a b
      (common.length+pre.length) ((common++(pre++tail)).length+1) p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++tail))
      x common.length (fun q => |∑ i, physicalCutIncrement n (common++(pre++tail)) x a b p i *
        physicalFutureTerminalIncrement n common tail pre x q i|^(2*l)) p := by
  unfold physicalCutPairPower
  simp_rw [show ∀ q, physicalCutIncrement n (common++(pre++tail)) x
      (common.length+pre.length) ((common++(pre++tail)).length+1) q =
      WithLp.toLp 2 (physicalFutureTerminalIncrement n common tail pre x q) from
    fun q => by
      simpa only [physicalCutIncrement,List.length_append,Nat.add_assoc] using
        (physicalFutureTerminalIncrement_eq_spinPath n common tail pre x q).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

 theorem eventually_cut_pair_terminal_full_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++tail) →
      OrderedSteps c (common++((skip++pre)++tail)) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (v w : ℕ),
      v ≤ w → w ≤ (common++((skip++pre)++tail)).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, physicalCutPairPower n (k+1) (common++((skip++pre)++tail)) x common.length v w
      (common.length+(skip++pre).length)
      ((common++((skip++pre)++tail)).length+1) p
      ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) (common++((skip++pre)++tail)) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++tail)) w) := by
  filter_upwards [eventually_common_cut_terminal_projection_moment k B] with n hn
  intro P _ common tail pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx v w hvw hw hc
  let steps := common++((skip++pre)++tail)
  let V := fun p i => physicalCutIncrement n steps x v w p i
  have hV : Measurable V := physicalCutIncrement_coe_measurable n steps hs x hx v w
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 2 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact physicalCutIncrement_norm_le n steps hs x v w p
  have hh := hn P common tail pre skip a c D ha hD hDB ho hs μ x hx V hV 2 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  rw [show 2*k+2=2*(k+1) by omega] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCutPairPower_futureTerminal] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  apply root_le_of_even_projection (Nat.succ_pos k)
    (integral_nonneg fun p => physicalCutPairPower_nonneg n (k+1) steps x _ _ _ _ _ p) hA hQ hS
  apply hh.trans
  have hM := mul_le_mul_of_nonneg_left
    (physicalRawRatio_increment_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hvw hw)
    (pow_nonneg hA (2*k+2))
  simpa only [show 2*(k+1) = 2*k+2 by omega,mul_assoc] using hM

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

 theorem physicalRawRatio_half_moment (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c xs : ℝ}
    (hc : OrderedSteps c steps) (hxs : 0 < xs)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) {t : ℕ} (ht : t ≤ steps.length+1) :
    (∫ p, ‖actualSpinPath n steps x t p‖^(2*l) ∂physicalPathLaw μ n steps x hx) ≤
      (physicalRawRatio n l steps c xs μ x hx)^(2*l)*(xs+physicalCutMass c steps t)^l := by
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) steps hc
  let ν := physicalPathLaw μ n steps x hx
  let : IsProbabilityMeasure ν := by dsimp [ν,physicalPathLaw]; infer_instance
  let Q := physicalRawRatio n l steps c xs μ x hx
  let S := xs+physicalCutMass c steps t
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hc t).1
  have hQ : 0 ≤ Q := zero_le_one.trans (physicalRawRatio_one_le n l steps c xs μ x hx)
  have hJ := integral_pow_le_mass ν
    (Eventually.of_forall fun p => pow_nonneg (norm_nonneg (actualSpinPath n steps x t p)) (2*l))
    (physicalCutNormPower_integrable n steps hc μ x hx t (2*l))
    (by omega : 0 < 2)
    (by simpa only [←pow_mul,show 2*l*2=4*l by omega] using
      physicalCutNormPower_integrable n steps hc μ x hx t (4*l))
  have hs : (∫ p, ‖actualSpinPath n steps x t p‖^(2*l) ∂ν)^2 ≤ (Q^(2*l)*S^l)^2 := by
    have he : (Q^(2*l)*S^l)^2=Q^(4*l)*S^(2*l) := by
      rw [mul_pow,←pow_mul,←pow_mul]
      congr 1 <;> congr 1 <;> omega
    rw [he]
    apply le_trans _ (physicalRawRatio_moment n l hl steps hc hxs μ x hx ht)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one,one_pow,one_mul,←pow_mul,
      show 2*l*2=4*l by omega] using hJ
  exact (sq_le_sq₀ (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _)
    (mul_nonneg (pow_nonneg hQ _) (pow_nonneg hS _))).1 hs

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalCoreLayerPower (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (c b d e : ℕ)
    (p : PhysicalPathState P n steps) : ℝ :=
  conditionalPathAverage (uniformWeight n) (finiteFeature n) steps x c
    (fun q => |inner ℝ (actualSpinPath n steps x b p)
      (physicalCutIncrement n steps x d e q)|^(2*l)) p

 theorem physicalCoreLayerPower_nonneg (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (c b d e : ℕ)
    (p : PhysicalPathState P n steps) : 0≤physicalCoreLayerPower n l steps x c b d e p :=
  conditionalPathAverage_nonneg _ _ _ _ _ (fun _ => pow_nonneg (abs_nonneg _) _) p

 theorem physicalCoreLayerPower_futurePair (n l : ℕ)
    (common tail mid pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (b : ℕ)
    (p : PhysicalPathState P n (common++(pre++(mid++tail)))) :
    physicalCoreLayerPower n l (common++(pre++(mid++tail))) x common.length b
      (common.length+pre.length) (common.length+(pre.length+mid.length)) p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++(mid++tail)))
      x common.length (fun q => |∑ i, actualSpinPath n (common++(pre++(mid++tail))) x b p i *
        physicalFuturePairIncrement n common tail mid pre x q i|^(2*l)) p := by
  unfold physicalCoreLayerPower
  simp_rw [show ∀ q, physicalCutIncrement n (common++(pre++(mid++tail))) x
      (common.length+pre.length) (common.length+(pre.length+mid.length)) q =
      WithLp.toLp 2 (physicalFuturePairIncrement n common tail mid pre x q) from
    fun q => (physicalFuturePairIncrement_eq_spinPath n common tail mid pre x q).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

 theorem eventually_core_layer_full_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail mid pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++(mid++tail)) →
      OrderedSteps c (common++((skip++pre)++(mid++tail))) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (w : ℕ),
      w ≤ (common++((skip++pre)++(mid++tail))).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, physicalCoreLayerPower n (k+1) (common++((skip++pre)++(mid++tail))) x common.length w
      (common.length+(skip++pre).length)
      (common.length+((skip++pre).length+mid.length)) p
      ∂physicalPathLaw μ n (common++((skip++pre)++(mid++tail))) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (physicalRawRatio n (k+1) (common++((skip++pre)++(mid++tail))) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++(mid++tail))) w) := by
  filter_upwards [eventually_common_cut_projection_moment k B] with n hn
  intro P _ common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx w hw hc
  let steps := common++((skip++pre)++(mid++tail))
  let V := fun p i => actualSpinPath n steps x w p i
  have hV : Measurable V :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable.comp
      (actualSpinPath_measurable n steps hs x hx w)
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 1 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact actualSpinPath_norm_le n steps hs x w p
  have hh := hn P common tail mid pre skip a c D ha hD hDB ho hs μ x hx V hV 1 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  rw [show 2*k+2=2*(k+1) by omega] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCoreLayerPower_futurePair] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  have hI : 0 ≤ ∫ p, physicalCoreLayerPower n (k+1) steps x common.length w
      (common.length+(skip++pre).length) (common.length+((skip++pre).length+mid.length)) p
      ∂physicalPathLaw μ n steps x hx :=
    integral_nonneg fun p => physicalCoreLayerPower_nonneg n (k+1) steps x _ _ _ _ p
  have hlo := mul_le_mul_of_nonneg_left
    (physicalRawRatio_half_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hw)
    (pow_nonneg hA (2*k+2))
  have he : (A^2*Q^2*S)^(k+1) = A^(2*(k+1))*Q^(2*(k+1))*S^(k+1) := by
    simp only [mul_pow,←pow_mul]
  have hm : (∫ p, physicalCoreLayerPower n (k+1) steps x common.length w
      (common.length+(skip++pre).length) (common.length+((skip++pre).length+mid.length)) p
      ∂physicalPathLaw μ n steps x hx) ≤ (A^2*Q^2*S)^(k+1) := by
    rw [he]
    apply hh.trans
    simpa only [show 2*(k+1)=2*k+2 by omega,mul_assoc] using hlo
  have hr := Real.rpow_le_rpow hI hm (inv_nonneg.2 (Nat.cast_nonneg (k+1)))
  simpa only [Real.pow_rpow_inv_natCast (by positivity : 0 ≤ A^2*Q^2*S) (Nat.succ_ne_zero k)] using hr

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 theorem physicalCoreLayerPower_futureTerminal (n l : ℕ)
    (common tail pre : List (GaussianStep (FeatureIndex n)))
    {P : Type} (x : P → FeatureIndex n → ℝ) (b : ℕ)
    (p : PhysicalPathState P n (common++(pre++tail))) :
    physicalCoreLayerPower n l (common++(pre++tail)) x common.length b
      (common.length+pre.length) ((common++(pre++tail)).length+1) p =
    conditionalPathAverage (uniformWeight n) (finiteFeature n) (common++(pre++tail))
      x common.length (fun q => |∑ i, actualSpinPath n (common++(pre++tail)) x b p i *
        physicalFutureTerminalIncrement n common tail pre x q i|^(2*l)) p := by
  unfold physicalCoreLayerPower
  simp_rw [show ∀ q, physicalCutIncrement n (common++(pre++tail)) x
      (common.length+pre.length) ((common++(pre++tail)).length+1) q =
      WithLp.toLp 2 (physicalFutureTerminalIncrement n common tail pre x q) from
    fun q => by
      simpa only [physicalCutIncrement,List.length_append,Nat.add_assoc] using
        (physicalFutureTerminalIncrement_eq_spinPath n common tail pre x q).symm]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,mul_comm]

 theorem eventually_core_layer_terminal_full_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (common tail pre skip : List (GaussianStep (FeatureIndex n)))
      (a c D xs : ℝ), 0 < a → 0 < D → D ≤ B → 0 < xs →
      OrderedSteps a (pre++tail) →
      OrderedSteps c (common++((skip++pre)++tail)) →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (w : ℕ),
      w ≤ (common++((skip++pre)++tail)).length+1 →
      (∀ V : Fin n → ℝ, AlignedFieldClock (fieldProjectionDirection n V) D pre) →
    (∫ p, physicalCoreLayerPower n (k+1) (common++((skip++pre)++tail)) x common.length w
      (common.length+(skip++pre).length)
      ((common++((skip++pre)++tail)).length+1) p
      ∂physicalPathLaw μ n (common++((skip++pre)++tail)) x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (physicalRawRatio n (k+1) (common++((skip++pre)++tail)) c xs μ x hx)^2 *
        (xs+physicalCutMass c (common++((skip++pre)++tail)) w) := by
  filter_upwards [eventually_common_cut_terminal_projection_moment k B] with n hn
  intro P _ common tail pre skip a c D xs ha hD hDB hxs ho hs μ _ x hx w hw hc
  let steps := common++((skip++pre)++tail)
  let V := fun p i => actualSpinPath n steps x w p i
  have hV : Measurable V :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).continuous.measurable.comp
      (actualSpinPath_measurable n steps hs x hx w)
  have hR : ∀ p, projectionEuclideanNorm n (V p) ≤ 1 := fun p => by
    dsimp only [V]
    rw [projectionEuclideanNorm_coe]
    exact actualSpinPath_norm_le n steps hs x w p
  have hh := hn P common tail pre skip a c D ha hD hDB ho hs μ x hx V hV 1 hR (fun p => hc (V p))
  dsimp only [V,steps] at hh
  rw [show 2*k+2=2*(k+1) by omega] at hh
  simp_rw [projectionEuclideanNorm_coe,← physicalCoreLayerPower_futureTerminal] at hh
  let A := projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D))
  let Q := physicalRawRatio n (k+1) steps c xs μ x hx
  let S := xs+physicalCutMass c steps w
  have hA : 0 ≤ A := div_nonneg (mul_nonneg (projectionLpConstant_pos k).le (sq_nonneg _))
    (mul_nonneg ha.le (Real.sqrt_nonneg _))
  have hQ : 0 ≤ Q := le_trans zero_le_one (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
  have hS : 0 ≤ S := add_nonneg hxs.le (physicalCutMass_mem steps hs w).1
  have hI : 0 ≤ ∫ p, physicalCoreLayerPower n (k+1) steps x common.length w
      (common.length+(skip++pre).length) ((common++((skip++pre)++tail)).length+1) p
      ∂physicalPathLaw μ n steps x hx :=
    integral_nonneg fun p => physicalCoreLayerPower_nonneg n (k+1) steps x _ _ _ _ p
  have hlo := mul_le_mul_of_nonneg_left
    (physicalRawRatio_half_moment n (k+1) (Nat.succ_pos k) steps hs hxs μ x hx hw)
    (pow_nonneg hA (2*k+2))
  have he : (A^2*Q^2*S)^(k+1) = A^(2*(k+1))*Q^(2*(k+1))*S^(k+1) := by
    simp only [mul_pow,←pow_mul]
  have hm : (∫ p, physicalCoreLayerPower n (k+1) steps x common.length w
      (common.length+(skip++pre).length) ((common++((skip++pre)++tail)).length+1) p
      ∂physicalPathLaw μ n steps x hx) ≤ (A^2*Q^2*S)^(k+1) := by
    rw [he]
    apply hh.trans
    simpa only [show 2*(k+1)=2*k+2 by omega,mul_assoc] using hlo
  have hr := Real.rpow_le_rpow hI hm (inv_nonneg.2 (Nat.cast_nonneg (k+1)))
  simpa only [Real.pow_rpow_inv_natCast (by positivity : 0 ≤ A^2*Q^2*S) (Nat.succ_ne_zero k)] using hr

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem eventually_physical_clock_pair_full_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D xs : ℝ),
      0 < a → 0 < D → D ≤ B → 0 < xs → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork v w d e : ℕ),
      v ≤ w → w ≤ steps.length+1 →
      PhysicalProjectionClock n steps fork d e a D →
    (∫ p, physicalCutPairPower n (k+1) steps x fork v w d e p
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) steps c xs μ x hx)^2 *
        (xs+physicalCutMass c steps w) := by
  filter_upwards [eventually_cut_pair_full_moment k B,eventually_cut_pair_terminal_full_moment k B] with n hn ht
  intro P _ steps a c D xs ha hD hDB hxs hs μ _ x hx fork v w d e hvw hw hc
  cases hc with
  | gaussian common tail mid pre skip a D ho hc =>
    exact hn P common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ x hx v w hvw hw hc
  | terminal common tail pre skip a D ho hc =>
    exact ht P common tail pre skip a c D xs ha hD hDB hxs ho hs μ x hx v w hvw hw hc

theorem eventually_physical_clock_core_layer_full_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D xs : ℝ),
      0 < a → 0 < D → D ≤ B → 0 < xs → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork w d e : ℕ),
      w ≤ steps.length+1 →
      PhysicalProjectionClock n steps fork d e a D →
    (∫ p, physicalCoreLayerPower n (k+1) steps x fork w d e p
      ∂physicalPathLaw μ n steps x hx)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (physicalRawRatio n (k+1) steps c xs μ x hx)^2 *
        (xs+physicalCutMass c steps w) := by
  filter_upwards [eventually_core_layer_full_moment k B,eventually_core_layer_terminal_full_moment k B] with n hn ht
  intro P _ steps a c D xs ha hD hDB hxs hs μ _ x hx fork w d e hw hc
  cases hc with
  | gaussian common tail mid pre skip a D ho hc =>
    exact hn P common tail mid pre skip a c D xs ha hD hDB hxs ho hs μ x hx w hw hc
  | terminal common tail pre skip a D ho hc =>
    exact ht P common tail pre skip a c D xs ha hD hDB hxs ho hs μ x hx w hw hc

end SKFluctuations

 

 

namespace SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators RealInnerProductSpace

 def physicalOverlapLayerMoment (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
    (fork t : ℕ) (i j : Fin (cs.length+1)) : ℝ :=
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
    (fun z => |physicalOverlapLayerTerm n steps x cs t (i,j) z|^(2*l)) p
      ∂physicalPathLaw μ n steps x hx

 def overlapComponentEnd (cs : List (ℝ × ℕ)) (t : ℕ) : Fin (cs.length+1) → ℕ :=
  Fin.cases t fun j => (cs.get j).2

 theorem physicalOverlapLayerMoment_nonneg (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {P : Type} [MeasurableSpace P] (μ : Measure P)
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
    (fork t : ℕ) (i j : Fin (cs.length+1)) :
    0 ≤ physicalOverlapLayerMoment n l steps μ x hx cs fork t i j :=
  integral_nonneg fun p => conditionalPathAverage_nonneg _ _ _ _ _
    (fun _ => pow_nonneg (abs_nonneg _) _) p

 theorem physicalOverlapLayerMoment_swap (n l : ℕ) (steps : List (GaussianStep (FeatureIndex n)))
    {c : ℝ} (hc : OrderedSteps c steps) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
    (fork t : ℕ) (i j : Fin (cs.length+1)) :
    physicalOverlapLayerMoment n l steps μ x hx cs fork t i j =
    physicalOverlapLayerMoment n l steps μ x hx cs fork t j i := by
  have hh := integral_conditionalForkTest_swap (uniformWeight_pos n) (finiteFeature n)
    steps hc μ x hx fork
    ((physicalOverlapLayerTerm_measurable n steps hc x hx cs t (i,j)).abs.pow_const (2*l))
    (fun z => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _)
        (physicalOverlapLayerTerm_abs_le n steps hc x cs t (i,j) z) (2*l))
  simpa only [physicalOverlapLayerMoment,physicalOverlapLayerTerm,physicalPathLaw,
    Function.comp_def,Prod.swap,real_inner_comm] using hh

 theorem eventually_physical_overlap_layer_clock_moment (k : ℕ) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ (P : Type) [MeasurableSpace P]
      (steps : List (GaussianStep (FeatureIndex n))) (a c D xs : ℝ),
      0 < a → 0 < D → D ≤ B → 0 < xs → OrderedSteps c steps →
    ∀ (μ : Measure P) [IsProbabilityMeasure μ]
      (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (cs : List (ℝ × ℕ))
      (fork t : ℕ) (i : Fin (cs.length+1)) (j : Fin cs.length),
      t ≤ steps.length+1 →
      (∀ z : Fin cs.length, cutPredecessor cs t z ≤ (cs.get z).2 ∧ (cs.get z).2 ≤ steps.length+1) →
      PhysicalProjectionClock n steps fork (cutPredecessor cs t j) (cs.get j).2 a D →
    (physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t i j.succ)^(((k+1:ℕ):ℝ)⁻¹) ≤
      (projectionLpConstant k*(Real.log (n:ℝ))^2/(a*Real.sqrt ((n:ℝ)*D)))^2 *
        (2*physicalRawRatio n (k+1) steps c xs μ x hx)^2 *
        (xs+physicalCutMass c steps (overlapComponentEnd cs t i)) := by
  filter_upwards [eventually_physical_clock_pair_full_moment k B,
    eventually_physical_clock_core_layer_full_moment k B] with n hp hc
  intro P _ steps a c D xs ha hD hDB hxs hs μ _ x hx cs fork t i j ht hends hclock
  refine Fin.cases ?_ (fun z => ?_) i
  · have hh := hc P steps a c D xs ha hD hDB hxs hs μ x hx fork t
      (cutPredecessor cs t j) (cs.get j).2 ht hclock
    change (physicalOverlapLayerMoment n (k+1) steps μ x hx cs fork t 0 j.succ)^_ ≤ _ at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _
      (add_nonneg hxs.le (physicalCutMass_mem steps hs t).1)
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have hQ := (physicalRawRatio_one_le n (k+1) steps c xs μ x hx)
    nlinarith [sq_nonneg (physicalRawRatio n (k+1) steps c xs μ x hx)]
  · exact hp P steps a c D xs ha hD hDB hxs hs μ x hx fork
      (cutPredecessor cs t z) (cs.get z).2 (cutPredecessor cs t j) (cs.get j).2
      (hends z).1 (hends z).2 hclock

end SKFluctuations

end

end OAI
