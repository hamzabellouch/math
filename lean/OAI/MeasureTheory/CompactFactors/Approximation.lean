import OAI.Analysis.PlaneSpectrum.ConditionalSpectrum
import OAI.MeasureTheory.CompactFactors.RelativeCenters

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EuclideanFiveColor.UniformEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {G Y : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableSpace Y] [Nonempty G]

omit [Nonempty G] in
theorem list_of_uniform_atoms (κ : Measure G)
    (S : Finset G) (a : ℝ≥0∞) (hmass : ∀ d ∈ S, κ {d} = a)
    (hsupp : ∀ᵐ d ∂κ, d ∈ S) (hc : (S.card : ℝ≥0∞)*a=1) :
    ∃ g : Fin S.card → G, κ = (S.card : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
  classical
  let e := S.equivFin
  let g : Fin S.card → G := fun i => (e.symm i).val
  have heq := Measure.ae_mem_finset_iff.mp hsupp
  have ha : a = (S.card : ℝ≥0∞)⁻¹ := by
    have hn : (S.card : ℝ≥0∞) ≠ 0 := by intro h; rw [h, zero_mul] at hc; exact zero_ne_one hc
    calc
      a = 1*a := by simp
      _ = ((S.card : ℝ≥0∞)⁻¹ * S.card)*a := by rw [ENNReal.inv_mul_cancel hn (by simp)]
      _ = (S.card : ℝ≥0∞)⁻¹ := by rw [mul_assoc, hc, mul_one]
  refine ⟨g, ?_⟩
  calc
    κ = ∑ d ∈ S, κ {d} • Measure.dirac d := heq
    _ = ∑ d ∈ S, (S.card : ℝ≥0∞)⁻¹ • Measure.dirac d :=
      Finset.sum_congr rfl (fun d hd => by rw [hmass d hd, ha])
    _ = (S.card : ℝ≥0∞)⁻¹ • ∑ d ∈ S, Measure.dirac d := Finset.smul_sum.symm
    _ = (S.card : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
      congr 1
      rw [← Finset.sum_coe_sort S (fun d => Measure.dirac d)]
      exact (Equiv.sum_comp e.symm (fun d : S => Measure.dirac d.val)).symm

theorem constant_uniform_lists (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ] (a : ℝ≥0∞) (ha : 0 < a)
    (hf : ∀ᵐ y ∂ν, ∃ S : Finset G, S.Nonempty ∧
      (∀ d ∈ S, κ y {d} = a) ∧ (∀ᵐ d ∂κ y, d ∈ S) ∧ (S.card : ℝ≥0∞)*a=1) :
    ∃ m : ℕ, 0 < m ∧ ∃ g : Y → Fin m → G,
      ∀ᵐ y ∂ν, κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i) := by
  classical
  obtain ⟨y₀, S₀, hS₀, _, _, hc₀⟩ := hf.exists
  let m := S₀.card
  have hm : 0 < m := Finset.card_pos.mpr hS₀
  have haT : a ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by exact_mod_cast hm.ne')] at hc₀
    exact ENNReal.top_ne_one hc₀
  have hlist : ∀ᵐ y ∂ν, ∃ g : Fin m → G,
      κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) := by
    filter_upwards [hf] with y hy
    obtain ⟨S, _hS, hSa, hSupp, hc⟩ := hy
    have hcard : S.card = m := by
      have hh : (S.card : ℝ≥0∞) = (m : ℝ≥0∞) :=
        (ENNReal.mul_right_inj ha.ne' haT).mp (by simpa only [mul_comm] using hc.trans hc₀.symm)
      exact_mod_cast hh
    obtain ⟨g, hg⟩ := list_of_uniform_atoms (κ y) S a hSa hSupp hc
    have hh : (∑ j : Fin S.card, Measure.dirac (g j)) =
        ∑ i : Fin m, Measure.dirac (g (Fin.cast hcard.symm i)) :=
      (Equiv.sum_comp (finCongr hcard.symm) (fun j => Measure.dirac (g j))).symm
    refine ⟨fun i => g (Fin.cast hcard.symm i), ?_⟩
    calc
      κ y = (S.card : ℝ≥0∞)⁻¹ • ∑ i : Fin m, Measure.dirac (g (Fin.cast hcard.symm i)) := hg.trans (congrArg ((S.card : ℝ≥0∞)⁻¹ • ·) hh)
      _ = _ := by congr 2; exact_mod_cast hcard
  let g : Y → Fin m → G := fun y => if h : ∃ g : Fin m → G,
      κ y = (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g i) then h.choose else fun _ => Classical.choice inferInstance
  refine ⟨m, hm, g, ?_⟩
  filter_upwards [hlist] with y hy
  simpa only [g, dite_eq_left hy] using hy.choose_spec

end EuclideanFiveColor.UniformEnumeration

open MeasureTheory ProbabilityTheory
namespace EuclideanFiveColor.DifferenceInvariant
variable {G Y : Type*} [CommGroup G] [MeasurableSpace G]
  [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace Y]

noncomputable def differenceLaw (ν : Measure Y) (κ : Kernel Y G) [IsMarkovKernel κ] : Measure G :=
  ((κ ×ₖ κ) ∘ₘ ν).map (fun p : G × G => p.1 / p.2)

lemma invariant (ν : Measure Y) [IsProbabilityMeasure ν]
    (κ : Kernel Y G) [IsMarkovKernel κ]
    (R : Y → Y) (hR : MeasurePreserving R ν ν)
    (T : G →* G) (hT : Measurable T)
    (he : ∀ᵐ y ∂ν, κ (R y) = (κ y).map T) :
    MeasurePreserving T (differenceLaw ν κ) (differenceLaw ν κ) := by
  have hprod : (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)) = ((κ ×ₖ κ) ∘ₘ ν) := by
    ext s hs
    rw [Measure.map_apply (hT.prodMap hT) hs,
      Measure.bind_apply ((hT.prodMap hT) hs) (κ ×ₖ κ).aemeasurable,
      Measure.bind_apply hs (κ ×ₖ κ).aemeasurable]
    calc
      (∫⁻ y, (κ ×ₖ κ) y ((Prod.map T T) ⁻¹' s) ∂ν) =
          ∫⁻ y, (κ ×ₖ κ) (R y) s ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [he] with y hy
        rw [Kernel.prod_apply, Kernel.prod_apply, hy,
          Measure.map_prod_map _ _ hT hT, Measure.map_apply (hT.prodMap hT) hs]
      _ = ∫⁻ y, (κ ×ₖ κ) y s ∂ν := hR.lintegral_comp (Kernel.measurable_coe _ hs)
  have hdiv : Measurable (fun p : G × G => p.1 / p.2) := measurable_fst.div measurable_snd
  refine ⟨hT, ?_⟩
  rw [differenceLaw, Measure.map_map hT hdiv]
  calc
    (((κ ×ₖ κ) ∘ₘ ν).map (T ∘ (fun p : G × G => p.1 / p.2))) =
        ((κ ×ₖ κ) ∘ₘ ν).map ((fun p : G × G => p.1 / p.2) ∘ Prod.map T T) := by
      congr 1
      funext p
      exact map_div T p.1 p.2
    _ = (((κ ×ₖ κ) ∘ₘ ν).map (Prod.map T T)).map (fun p : G × G => p.1 / p.2) :=
      (Measure.map_map hdiv (hT.prodMap hT)).symm
    _ = _ := by rw [hprod]

end EuclideanFiveColor.DifferenceInvariant

/-! The scalar finite bounded-module approximation in (source-4), and its
finite-vector consequence. All functions are measurable bounded representatives. -/
namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y W : Type*} [SMul K Y] [MeasurableSpace Y] [MeasurableSpace W]

def Scalar (ν : Measure Y) (q : Y → W) : Prop :=
  ∀ H : Y → ℂ, Measurable H → (∃ C : ℝ, ∀ y, ‖H y‖ ≤ C) →
  ∀ ε : ℝ, 0 < ε → ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i * Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i * Hf i y)^2 ∂ν) < ε^2

def Vector (ν : Measure Y) (q : Y → W) : Prop :=
  ∀ (m : ℕ) (H : Y → Fin m → ℂ), Measurable H →
  (∃ C : ℝ, ∀ y, ‖H y‖ ≤ C) → ∀ ε : ℝ, 0 < ε →
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2 ∂ν) < ε^2

lemma pi_dist_sq_le_sum {I : Type*} [Fintype I] (a b : I → ℂ) :
    dist a b ^ 2 ≤ ∑ i, dist (a i) (b i)^2 := by
  have hs : 0 ≤ ∑ i, dist (a i) (b i)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hn : dist a b ≤ Real.sqrt (∑ i, dist (a i) (b i)^2) := by
    rw [dist_eq_norm, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    change ‖a i - b i‖ ≤ _
    rw [← dist_eq_norm]
    apply (Real.le_sqrt (dist_nonneg) hs).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg (dist (a j) (b j))) (Finset.mem_univ i)
  nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg (∑ i, dist (a i) (b i)^2), dist_nonneg (x := a) (y := b)]

lemma vector_of_scalar (ν : Measure Y) [IsProbabilityMeasure ν]
    (q : Y → W) (hq : Measurable q) [MeasurableConstSMul K Y]
    (hs : Scalar (K := K) ν q) : Vector (K := K) ν q := by
  classical
  intro m H hH hHb ε hε
  let δ : ℝ := ε / (m+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hcoord (j : Fin m) : ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → ℂ),
      0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
      ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
        Integrable (fun y => dist (H (k • y) j) (∑ i, a (q y) i * Hf i y)^2) ν ∧
        (∫ y, dist (H (k • y) j) (∑ i, a (q y) i * Hf i y)^2 ∂ν) < δ^2 := by
    apply hs (fun y => H y j) ((measurable_pi_iff.mp hH) j) _ δ hδ
    obtain ⟨C, hC⟩ := hHb
    exact ⟨C, fun y => (norm_le_pi_norm (H y) j).trans (hC y)⟩
  choose r B C Hf hB hC hHm hHb hA using hcoord
  let I := (j : Fin m) × Fin (r j)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let V : I → Y → Fin m → ℂ := fun s y => Pi.single s.1 (Hf s.1 s.2 y)
  have hV (s : I) : Measurable (V s) := by
    apply Measurable.of_eval
    intro j
    by_cases h : s.1 = j
    · subst j
      simpa [V] using hHm s.1 s.2
    · simp only [V, Pi.single_apply, Ne.symm h, ite_false]
      exact measurable_const
  have hVnorm (s : I) (y : Y) : ‖V s y‖ ≤ ‖Hf s.1 s.2 y‖ := by
    rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro j
    by_cases h : s.1 = j
    · subst j; simp [V]
    · simp [V, h]
  refine ⟨Fintype.card I, ∑ j, B j, ∑ j, C j, fun i => V (e i),
    Finset.sum_nonneg (fun j _ => hB j), Finset.sum_nonneg (fun j _ => hC j),
    fun i => hV (e i), ?_, ?_⟩
  · intro y
    change (∑ i, (fun s : I => ‖V s y‖) (e i)) ≤ _
    rw [Equiv.sum_comp e (fun s : I => ‖V s y‖)]
    calc
      ∑ s : I, ‖V s y‖ ≤ ∑ s : I, ‖Hf s.1 s.2 y‖ := Finset.sum_le_sum (fun s _ => hVnorm s y)
      _ = ∑ j, ∑ i, ‖Hf j i y‖ := Fintype.sum_sigma _
      _ ≤ ∑ j, C j := Finset.sum_le_sum (fun j _ => hHb j y)
  · intro k
    choose a ham hab hai hae using fun j => hA j k
    let a' : W → I → ℂ := fun w s => a s.1 w s.2
    have hap (w : W) : ‖fun i => a' w (e i)‖ ≤ ∑ j, B j := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => hB j))]
      intro i
      exact ((norm_le_pi_norm (a (e i).1 w) (e i).2).trans (hab (e i).1 w)).trans
        (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_univ _))
    have ham' : Measurable (fun w i => a' w (e i)) := by
      apply Measurable.of_eval
      intro i
      exact (measurable_pi_iff.mp (ham (e i).1)) (e i).2
    let A : Y → Fin m → ℂ := fun y => ∑ s : I, a' (q y) s • V s y
    have hAeq (y : Y) (j : Fin m) : A y j = ∑ i, a j (q y) i * Hf j i y := by
      change (∑ s : I, a' (q y) s • V s y) j = _
      simp only [Finset.sum_apply, Pi.smul_apply]
      rw [Fintype.sum_sigma]
      simp [a', V, Pi.single_apply]
    have hAm : Measurable A := by
      apply Measurable.of_eval
      intro j
      simp_rw [hAeq]
      exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_iff.mp (ham j)) i |>.comp hq).mul (hHm j i))
    have hem : AEStronglyMeasurable (fun y => dist (H (k • y)) (A y)^2) ν :=
      ((hH.comp (measurable_const_smul k)).dist hAm |>.pow_const 2).aestronglyMeasurable
    have hsint : Integrable (fun y => ∑ j, dist (H (k • y) j) (A y j)^2) ν := by
      apply integrable_finsetSum
      intro j _
      simpa only [hAeq] using hai j
    have hbound (y : Y) : dist (H (k • y)) (A y)^2 ≤ ∑ j, dist (H (k • y) j) (A y j)^2 :=
      pi_dist_sq_le_sum _ _
    have hint : Integrable (fun y => dist (H (k • y)) (A y)^2) ν :=
      hsint.mono' hem (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (dist (H (k • y)) (A y)))] using hbound y))
    have hbudget : (∫ y, dist (H (k • y)) (A y)^2 ∂ν) < ε^2 := by
      calc
        _ ≤ ∫ y, ∑ j, dist (H (k • y) j) (A y j)^2 ∂ν := integral_mono hint hsint hbound
        _ = ∑ j, ∫ y, dist (H (k • y) j) (A y j)^2 ∂ν := integral_finsetSum _ (fun j _ => by simpa only [hAeq] using hai j)
        _ ≤ ∑ _j : Fin m, δ^2 := Finset.sum_le_sum (fun j _ => by simpa only [hAeq] using (hae j).le)
        _ = (m : ℝ) * δ^2 := by simp
        _ < ε^2 := by
          dsimp [δ]
          have hm : (0 : ℝ) < m+1 := by positivity
          rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (sq_pos_of_pos hm)]
          nlinarith [sq_nonneg (m : ℝ), sq_pos_of_pos hε]
    have hAe (y : Y) : (∑ i, a' (q y) (e i) • V (e i) y) = A y :=
      Equiv.sum_comp e (fun s => a' (q y) s • V s y)
    refine ⟨fun w i => a' w (e i), ham', hap, ?_, ?_⟩
    · simpa only [hAe] using hint
    · simpa only [hAe] using hbudget

end EuclideanFiveColor.CompactApproximation

namespace EuclideanFiveColor.KernelSupport
open MeasureTheory
variable {K X Y : Type*} [Group K] [MeasurableSpace X] [MeasurableSpace Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]
lemma factor_smul_preserving (μ : Measure X) [SMulInvariantMeasure K X μ]
    (p : X → Y) (hp : Measurable p)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun y : Y => k • y) (μ.map p) (μ.map p) := by
  refine ⟨measurable_const_smul k, ?_⟩
  rw [Measure.map_map (measurable_const_smul k) hp]
  calc
    μ.map ((fun y : Y => k • y) ∘ p) = μ.map (p ∘ (fun x : X => k • x)) :=
      Measure.map_congr ((hpe k).mono fun _ hx => hx.symm)
    _ = (μ.map (fun x : X => k • x)).map p :=
      (Measure.map_map hp (measurable_const_smul k)).symm
    _ = μ.map p := by rw [measurePreserving_smul k μ |>.map_eq]
end EuclideanFiveColor.KernelSupport

namespace PlaneFiveColor.Spectral
open MeasureTheory ProbabilityTheory EuclideanFiveColor
open scoped BigOperators ENNReal
variable {X Y W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace W]
  [MulAction K X] [MulAction K Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

lemma relative_difference_invariant (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure K X μ] (b : X → D) (p : X → Y)
    (hb : Measurable b) (hp : Measurable p)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) (k : K) :
    MeasurePreserving (fun d : D => k • d)
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ))
      (DifferenceFourier.differenceLaw (μ.map p) (condDistrib b p μ)) := by
  have he := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  exact DifferenceInvariant.invariant (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (KernelSupport.factor_smul_preserving μ p hp hpe k)
    (scalarHom (kCoeff k)) (measurable_const_smul k) he

lemma finite_encoding_approximation_of_compact
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace W] [Nonempty W]
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure K X μ]
    (p : X → Y) (q : Y → W) (b : X → D)
    (hp : Measurable p) (hq : Measurable q) (hb : Measurable b)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hbe : ∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x)
    (m : ℕ) (hm : 0 < m) (g : Y → Fin m → D)
    (hg : ∀ᵐ y ∂μ.map p, condDistrib b p μ y =
      (m : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (g y i))
    (hc : CompactApproximation.Scalar (K := K) (μ.map p) q) :
    FiniteEncodingApproximation μ p q b m := by
  classical
  let H₀ : Y → Fin m → ℂ := PhaseEncoding.kernelEncoding (condDistrib b p μ)
    (fun d => (eval 1 d : ℂ)) m
  have hH₀ : Measurable H₀ :=
    PhaseEncoding.measurable_kernelEncoding _ _ (measurable_eval_coe 1) m
  obtain ⟨A, hA⟩ := PhaseEncoding.exists_encoding_bound m
  have hHB : ∀ᵐ y ∂μ.map p, ‖H₀ y‖ ≤ max A 0 := by
    filter_upwards [hg] with y hy
    have he := PhaseEncoding.kernelEncoding_eq_encoding (condDistrib b p μ) (eval 1) m hm y (g y) hy
    change ‖PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval 1 d : ℂ)) m y‖ ≤ max A 0
    rw [he]
    exact (hA (fun i => eval 1 (g y i))).trans (le_max_left _ _)
  let H : Y → Fin m → ℂ := fun y => if ‖H₀ y‖ ≤ max A 0 then H₀ y else 0
  have hH : Measurable H := hH₀.piecewise (measurableSet_le hH₀.norm measurable_const) measurable_const
  have hHbound : ∀ y, ‖H y‖ ≤ max A 0 := by
    intro y
    by_cases hy : ‖H₀ y‖ ≤ max A 0
    · simpa only [H, ite_eq_left hy] using hy
    · simp only [H, ite_eq_right hy, norm_zero]
      exact le_max_right _ _
  have hHeq : H =ᵐ[μ.map p] H₀ := hHB.mono fun y hy => ite_eq_left hy
  have hv := CompactApproximation.vector_of_scalar (μ.map p) q hq hc
  intro γ hγ
  obtain ⟨r, B, C, Hf, hB, hC, _hHm, hHf, ha⟩ := hv m H hH ⟨max A 0, hHbound⟩ γ hγ
  refine ⟨r, B, C, Hf, hB, hC, hHf, ?_⟩
  intro k
  obtain ⟨a, _ham, hab, hai, hae⟩ := ha k
  have hker := KernelSupport.condDistrib_equivariant μ b p hb hp
    (MeasurableEquiv.smul k) (MeasurableEquiv.smul k) (fun d : D => k • d)
    (measurable_const_smul k) (measurePreserving_smul k μ) (hpe k) (hbe k)
  have hcov := PhaseEncoding.kernelEncoding_covariance (μ.map p) (condDistrib b p μ)
    (fun y : Y => k • y) (fun d : D => k • d) (measurable_const_smul k)
    (fun d => (eval 1 d : ℂ)) (measurable_eval_coe 1) m hker
  have heq : ∀ᵐ y ∂μ.map p, H (k • y) =
      PhaseEncoding.kernelEncoding (condDistrib b p μ) (fun d => (eval (kCoeff k) d : ℂ)) m y := by
    filter_upwards [(KernelSupport.factor_smul_preserving μ p hp hpe k).quasiMeasurePreserving.ae hHeq,
      hcov] with y hy hc'
    exact hy.trans (by simpa only [Function.comp_def, eval_smul_one] using hc')
  have he : (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) =ᵐ[μ.map p]
      (fun y => dist (PhaseEncoding.kernelEncoding (condDistrib b p μ)
        (fun d => (eval (kCoeff k) d : ℂ)) m y) (∑ i, a (q y) i • Hf i y)^2) := by
    filter_upwards [heq] with y hy
    rw [hy]
  have hai' := hai.congr he
  refine ⟨a, hab, hai'.comp_measurable hp, ?_⟩
  rw [← integral_map hp.aemeasurable hai'.aestronglyMeasurable,
    ← integral_congr_ae he]
  exact hae

/-- The complete source successor implication. The predecessor assertion is
universal in the equivariant wild map, as required by the transfinite induction. -/
theorem relative_singularity_successor
    [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
    [StandardBorelSpace W] [Nonempty W]
    [MulAction K W] [MeasurableConstSMul K W]
    (μ : Measure X) [IsProbabilityMeasure μ] [ErgodicSMul K X μ]
    (d : X → D) (p : X → Y) (q : Y → W)
    (hd : Measurable d) (hp : Measurable p) (hq : Measurable q)
    (hde : ∀ k : K, ∀ᵐ x ∂μ, d (k • x) = k • d x)
    (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x)
    (hqe : ∀ k : K, ∀ᵐ y ∂μ.map p, q (k • y) = k • q y)
    (hwild : IsWild (μ.map d))
    (hc : CompactApproximation.Scalar (K := K) (μ.map p) q)
    (hprev : ∀ b : X → D, Measurable b →
      (∀ k : K, ∀ᵐ x ∂μ, b (k • x) = k • b x) → IsWild (μ.map b) →
      DifferenceFourier.differenceLaw (μ.map (q ∘ p)) (condDistrib b (q ∘ p) μ) C = 0) :
    DifferenceFourier.differenceLaw (μ.map p) (condDistrib d p μ) C = 0 := by
  by_contra hn
  have hpos : 0 < RelativeCenters.differenceLaw (μ.map p) (condDistrib d p μ) C :=
    pos_iff_ne_zero.mpr hn
  obtain ⟨b, hb, hbe, hbw, a, ha, hf⟩ := exact_finite_center_reduction μ d p hd hp hde hpe hwild hpos
  obtain ⟨m, hm, g, hg⟩ := UniformEnumeration.constant_uniform_lists (μ.map p)
    (condDistrib b p μ) a ha (hf.mono fun y ⟨S, hS, hSa, hSupp, hcS, _⟩ =>
      ⟨S, hS, hSa, hSupp, hcS⟩)
  have hcomp : ∀ k : K, ∀ᵐ x ∂μ, (q ∘ p) (k • x) = k • (q ∘ p) x := by
    intro k
    filter_upwards [hpe k, ae_of_ae_map hp.aemeasurable (hqe k)] with x hx hy
    simp only [Function.comp_def, hx, hy]
  have hpwild : IsWild (DifferenceFourier.differenceLaw (μ.map (q ∘ p)) (condDistrib b (q ∘ p) μ)) :=
    ⟨relative_difference_invariant μ b (q ∘ p) hb (hq.comp hp) hbe hcomp,
      hprev b hb hbe hbw⟩
  exact finite_uniform_successor_contradiction μ p q b hp hq hb m hm g hg hpwild
    (finite_encoding_approximation_of_compact μ p q b hp hq hb hpe hbe m hm g hg hc)

end PlaneFiveColor.Spectral

namespace EuclideanFiveColor.CompactApproximation
open MeasureTheory
open scoped BigOperators
variable {K Y Z W : Type*} [SMul K Y] [SMul K Z]
  [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

def At (ν : Measure Y) (q : Y → W) (m : ℕ) (H : Y → Fin m → ℂ) (ε : ℝ) : Prop :=
  ∃ (r : ℕ) (B C : ℝ) (Hf : Fin r → Y → Fin m → ℂ),
    0 ≤ B ∧ 0 ≤ C ∧ (∀ i, Measurable (Hf i)) ∧ (∀ y, ∑ i, ‖Hf i y‖ ≤ C) ∧
    ∀ k : K, ∃ a : W → Fin r → ℂ, Measurable a ∧ (∀ w, ‖a w‖ ≤ B) ∧
      Integrable (fun y => dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2) ν ∧
      (∫ y, dist (H (k • y)) (∑ i, a (q y) i • Hf i y)^2 ∂ν) < ε^2

lemma lift_at
    (ν : Measure Y) [IsProbabilityMeasure ν]
    (p : Y → Z) (q : Z → W) (hp : Measurable p) (hq : Measurable q)
    [MeasurableConstSMul K Y] [MeasurableConstSMul K Z]
    (hpres : ∀ k : K, MeasurePreserving (fun y : Y => k • y) ν ν)
    (hpe : ∀ k : K, ∀ᵐ y ∂ν, p (k • y) = k • p y)
    (m : ℕ) (H : Y → Fin m → ℂ) (H₀ : Z → Fin m → ℂ)
    (hH : Measurable H) (hH₀ : Measurable H₀)
    (hB₀ : ∃ C : ℝ, ∀ z, ‖H₀ z‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε)
    (hi : Integrable (fun y => dist (H y) (H₀ (p y))^2) ν)
    (he : (∫ y, dist (H y) (H₀ (p y))^2 ∂ν) < (ε/2)^2)
    (hc : Vector (K := K) (ν.map p) q) : At (K := K) ν (q ∘ p) m H ε := by
  classical
  obtain ⟨r, B, C, Hf, hB, hC, hHm, hHf, ha⟩ := hc m H₀ hH₀ hB₀ (ε/2) (by positivity)
  refine ⟨r, B, C, fun i => Hf i ∘ p, hB, hC, fun i => (hHm i).comp hp,
    fun y => hHf (p y), ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha k
  let F : Y → Fin m → ℂ := fun y => ∑ i, a (q (p y)) i • Hf i (p y)
  have hFm : Measurable F := by
    exact Finset.measurable_sum _ (fun i _ =>
      (((measurable_pi_iff.mp ham) i).comp (hq.comp hp)).smul ((hHm i).comp hp))
  let e₁ : Y → ℝ := fun y => dist (H (k • y)) (H₀ (k • p y))^2
  let e₂ : Y → ℝ := fun y => dist (H₀ (k • p y)) (F y)^2
  have heq : (fun y => dist (H (k • y)) (H₀ (p (k • y)))^2) =ᵐ[ν] e₁ :=
    (hpe k).mono fun y hy => by simp only [e₁, hy]
  have hi₁ : Integrable e₁ ν := ((hpres k).integrable_comp hi.aestronglyMeasurable |>.mpr hi).congr heq
  have he₁ : (∫ y, e₁ y ∂ν) < (ε/2)^2 := by
    have hm : AEStronglyMeasurable (fun y => dist (H y) (H₀ (p y))^2)
        (ν.map (fun y : Y => k • y)) := by
      rw [(hpres k).map_eq]
      exact hi.aestronglyMeasurable
    rw [← integral_congr_ae heq, ← integral_map (hpres k).measurable.aemeasurable hm,
      (hpres k).map_eq]
    exact he
  have hi₂ : Integrable e₂ ν := hai.comp_measurable hp
  have he₂ : (∫ y, e₂ y ∂ν) < (ε/2)^2 := by
    change (∫ y, dist (H₀ (k • p y)) (∑ i, a (q (p y)) i • Hf i (p y))^2 ∂ν) < _
    rw [← integral_map hp.aemeasurable hai.aestronglyMeasurable]
    exact hae
  have hmajor (y : Y) : dist (H (k • y)) (F y)^2 ≤ 2*(e₁ y + e₂ y) := by
    have ht := dist_triangle (H (k • y)) (H₀ (k • p y)) (F y)
    have hx := dist_nonneg (x := H (k • y)) (y := H₀ (k • p y))
    have hy := dist_nonneg (x := H₀ (k • p y)) (y := F y)
    have hz := dist_nonneg (x := H (k • y)) (y := F y)
    dsimp [e₁, e₂]
    nlinarith [sq_nonneg (dist (H (k • y)) (H₀ (k • p y)) - dist (H₀ (k • p y)) (F y))]
  have himaj : Integrable (fun y => 2*(e₁ y + e₂ y)) ν := (hi₁.add hi₂).const_mul 2
  have hint : Integrable (fun y => dist (H (k • y)) (F y)^2) ν :=
    himaj.mono' (((hH.comp (measurable_const_smul k)).dist hFm).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs, abs_sq] using hmajor y)
  refine ⟨a, ham, hab, hint, ?_⟩
  calc
    (∫ y, dist (H (k • y)) (F y)^2 ∂ν) ≤ ∫ y, 2*(e₁ y + e₂ y) ∂ν :=
      integral_mono hint himaj hmajor
    _ = 2*((∫ y, e₁ y ∂ν) + ∫ y, e₂ y ∂ν) := by
      rw [integral_const_mul, integral_add hi₁ hi₂]
    _ < ε^2 := by nlinarith

end EuclideanFiveColor.CompactApproximation

end

end OAI
