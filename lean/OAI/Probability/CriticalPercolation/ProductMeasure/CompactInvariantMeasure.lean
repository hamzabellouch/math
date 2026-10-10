import Mathlib
import OAI.Probability.CriticalPercolation.Growth.PolynomialFolner

namespace OAI

section
noncomputable section
open Set Function Filter Finset MeasureTheory
open scoped Classical Topology BigOperators Pointwise ENNReal NNReal BoundedContinuousFunction

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

lemma orbit_wordBall_nonempty (S : Finset G) (h1 : (1:G)∈S) (n : ℕ) : (S^n).Nonempty :=
  ⟨1,Finset.one_mem_pow h1⟩

def orbitAverage (T : Finset G) (hT : T.Nonempty) (x : X) : ProbabilityMeasure X :=
  ⟨((T.card:ℝ≥0∞)⁻¹) • ∑ g∈T, Measure.dirac (g • x), by
    constructor
    simp only [Measure.smul_apply,Measure.finsetSum_apply,Measure.dirac_apply_of_mem (Set.mem_univ _),
      Finset.sum_const,nsmul_eq_mul,smul_eq_mul,mul_one]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (Finset.card_ne_zero.mpr hT)) (by simp)⟩

omit [DecidableEq G] [ContinuousConstSMul G X] in
lemma integral_orbitAverage (T : Finset G) (hT : T.Nonempty) (x : X)
    (f : X → ℝ) :
    ∫ y, f y ∂(orbitAverage T hT x:Measure X) =
      (T.card:ℝ)⁻¹ * ∑ g∈T, f (g • x) := by
  change ∫ y, f y ∂(((T.card:ℝ≥0∞)⁻¹) • ∑ g∈T, Measure.dirac (g • x))=_
  rw [integral_smul_measure,integral_finsetSum_measure (fun g _ => integrable_dirac (by finiteness))]
  simp only [integral_dirac,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]

omit [ContinuousConstSMul G X] in
lemma orbitAverage_translate_bound (S : Finset G) (h1 : (1:G)∈S)
    (n : ℕ) (x : X) (s : G) (hs : s∈S) (f : X →ᵇ ℝ) :
    |(∫ y, f (s • y) ∂(orbitAverage (S^n) (orbit_wordBall_nonempty S h1 n) x:Measure X))-
      (∫ y, f y ∂(orbitAverage (S^n) (orbit_wordBall_nonempty S h1 n) x:Measure X))| ≤
      ((S^n).card:ℝ)⁻¹ * (2*(((S^(n+1)).card:ℝ)-(S^n).card)*‖f‖) := by
  rw [integral_orbitAverage (S^n) _ x (fun y => f (s • y)),
    integral_orbitAverage (S^n) _ x f,←mul_sub,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  simpa only [mul_smul] using translated_ball_sum_bound S h1 n s hs
    (fun g => f (g • x)) ‖f‖ (norm_nonneg _) (fun g => by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (g • x))

lemma exists_invariant_probability_measure_generators [CompactSpace X]
    (S : Finset G) (h1 : (1:G)∈S) (d : ℕ) (hg : HasDegree S d) (x : X) :
    ∃ μ : ProbabilityMeasure X, ∀ s∈S, ∀ f : X →ᵇ ℝ,
      (∫ y, f (s • y) ∂(μ:Measure X))=∫ y, f y ∂(μ:Measure X) := by
  have hex : ∀ k : ℕ, ∃ n≥k,
      ((S^(n+1)).card:ℝ)-(S^n).card≤((k:ℝ)+1)⁻¹*(S^n).card := by
    intro k
    exact small_ball_increment S h1 d hg _ (by positivity) k
  choose r hr hsmall using hex
  let ν : ℕ → ProbabilityMeasure X := fun k => orbitAverage (S^(r k)) (orbit_wordBall_nonempty S h1 (r k)) x
  obtain ⟨μ,_,φ,hφ,hlim⟩ := (isCompact_univ : IsCompact (Set.univ:Set (ProbabilityMeasure X))).tendsto_subseq
    (x:=ν) (fun _ => Set.mem_univ _)
  refine ⟨μ,?_⟩
  intro s hs f
  let fs : X →ᵇ ℝ := f.compContinuous ⟨fun y => s • y,continuous_const_smul s⟩
  have he0 : Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have he : Tendsto (fun k => 2*‖f‖*((φ k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa using (he0.comp hφ.tendsto_atTop).const_mul (2*‖f‖)
  have hb (k : ℕ) :
      |(∫ y, fs y ∂(ν (φ k):Measure X))-(∫ y, f y ∂(ν (φ k):Measure X))|≤
        2*‖f‖*((φ k:ℝ)+1)⁻¹ := by
    apply (orbitAverage_translate_bound S h1 (r (φ k)) x s hs f).trans
    have hc : (0:ℝ)<(S^(r (φ k))).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1,Finset.one_mem_pow h1⟩
    have hm := mul_le_mul_of_nonneg_left (hsmall (φ k))
      (show 0≤((S^(r (φ k))).card:ℝ)⁻¹ * (2*‖f‖) by positivity)
    calc
      _ = ((S^(r (φ k))).card:ℝ)⁻¹ * (2*‖f‖) *
          (((S^(r (φ k)+1)).card:ℝ)-(S^(r (φ k))).card) := by ring
      _ ≤ ((S^(r (φ k))).card:ℝ)⁻¹ * (2*‖f‖) *
          (((φ k:ℝ)+1)⁻¹*(S^(r (φ k))).card) := hm
      _ = _ := by field_simp
  have hz : Tendsto (fun k => (∫ y, fs y ∂(ν (φ k):Measure X))-
      (∫ y, f y ∂(ν (φ k):Measure X))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using hb k) he
  have hfs := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction fs).tendsto μ |>.comp hlim
  have hf := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto μ |>.comp hlim
  exact sub_eq_zero.mp (tendsto_nhds_unique (hfs.sub hf) hz)

end CriticalPercolation.SparseGrowth

namespace CriticalPercolation.SparseGrowth
variable {G X : Type*} [Group G] [DecidableEq G]
variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MulAction G X] [ContinuousConstSMul G X]

def integralInvariantSubgroup (μ : ProbabilityMeasure X) : Subgroup G where
  carrier := {g | ∀ f : X →ᵇ ℝ, (∫ y, f (g • y) ∂(μ:Measure X))=∫ y, f y ∂(μ:Measure X)}
  one_mem' := by intro f; simp
  mul_mem' := by
    intro a b ha hb f
    let fa : X →ᵇ ℝ := f.compContinuous ⟨fun y => a • y,continuous_const_smul a⟩
    calc
      _ = ∫ y, fa (b • y) ∂(μ:Measure X) := by simp only [fa,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,mul_smul]
      _ = ∫ y, fa y ∂(μ:Measure X) := hb fa
      _ = ∫ y, f y ∂(μ:Measure X) := ha f
  inv_mem' := by
    intro a ha f
    let fi : X →ᵇ ℝ := f.compContinuous ⟨fun y => a⁻¹ • y,continuous_const_smul _⟩
    have hh := ha fi
    simpa only [fi,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk,inv_smul_smul] using hh.symm

lemma exists_invariant_probability_measure [CompactSpace X]
    (S : Finset G) (h1 : (1:G)∈S) (hgen : Subgroup.closure (S:Set G)=⊤)
    (d : ℕ) (hg : HasDegree S d) (x : X) :
    ∃ μ : ProbabilityMeasure X, ∀ g : G,
      Measure.map (fun y => g • y) (μ:Measure X)=(μ:Measure X) := by
  obtain ⟨μ,hμ⟩ := exists_invariant_probability_measure_generators S h1 d hg x
  have hle : Subgroup.closure (S:Set G) ≤ integralInvariantSubgroup μ :=
    (Subgroup.closure_le _).mpr (fun s hs => hμ s hs)
  rw [hgen] at hle
  refine ⟨μ,?_⟩
  intro g
  have hi : ∀ f : X →ᵇ ℝ, (∫ y, f (g • y) ∂(μ:Measure X))=∫ y, f y ∂(μ:Measure X) :=
    hle (Subgroup.mem_top g)
  let ν : ProbabilityMeasure X := μ.map (fun point => g • point)
  have he : ν.toFiniteMeasure=μ.toFiniteMeasure := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro f
    change (∫ y, f y ∂(Measure.map (fun y => g • y) (μ:Measure X)))=_
    rw [integral_map (continuous_const_smul g).measurable.aemeasurable f.continuous.aestronglyMeasurable]
    exact hi f
  exact congrArg FiniteMeasure.toMeasure he

end CriticalPercolation.SparseGrowth
end
end

end OAI
