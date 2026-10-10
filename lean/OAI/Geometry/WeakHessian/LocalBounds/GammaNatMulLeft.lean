import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.AddConst
import OAI.Geometry.WeakHessian.Entropy.LocalGradientParallelogram

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma gamma_nat_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (n : ℕ) :
    gamma m (fun x => (n:ℝ)*f x) g =ᵐ[m] (fun x => (n:ℝ)*gamma m f g x) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul,Pi.zero_def] using gamma_zero_left (m := m) g
  | succ n ih =>
    have e : (fun x => ((n+1:ℕ):ℝ)*f x) = (fun x => (n:ℝ)*f x+f x) := by
      funext x; push_cast; ring
    filter_upwards [gamma_add_left hfinite hpar (hf.const_mul n) hf hg,ih] with x ha hi
    rw [e,ha,hi]
    push_cast
    ring

lemma gamma_int_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (n : ℤ) :
    gamma m (fun x => (n:ℝ)*f x) g =ᵐ[m] (fun x => (n:ℝ)*gamma m f g x) := by
  obtain ⟨n,rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [Int.cast_natCast] using gamma_nat_mul_left hfinite hpar hf hg n
  · filter_upwards [gamma_nat_mul_left hfinite hpar hf hg n,
      gamma_neg_left hfinite hpar (hf.const_mul n) hg] with x hn hneg
    simpa only [Int.cast_neg,Int.cast_natCast,neg_mul,hn] using hneg

lemma gamma_rat_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (q : ℚ) :
    gamma m (fun x => (q:ℝ)*f x) g =ᵐ[m] (fun x => (q:ℝ)*gamma m f g x) := by
  have hd : (q.den:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have eq : (q.den:ℝ)*(q:ℝ) = (q.num:ℝ) := by
    rw [Rat.cast_def, mul_div_cancel₀ _ hd]
  have e : (fun x => (q.den:ℝ)*((q:ℝ)*f x)) = (fun x => (q.num:ℝ)*f x) := by
    funext x; rw [← mul_assoc,eq]
  filter_upwards [gamma_nat_mul_left hfinite hpar (hf.const_mul q) hg q.den,
    gamma_int_mul_left hfinite hpar hf hg q.num] with x hden hnum
  rw [e,hnum] at hden
  apply mul_left_cancel₀ hd
  rw [← mul_assoc,eq,hden]

lemma gamma_const_mul_left (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    gamma m (fun x => c*f x) g =ᵐ[m] (fun x => c*gamma m f g x) := by
  obtain ⟨qs,_,_,hqs⟩ := Real.exists_seq_rat_strictMono_tendsto c
  filter_upwards [gamma_const_mul_tendsto hfinite hf hg hqs,
    ae_all_iff.mpr (fun n => gamma_rat_mul_left hfinite hpar hf hg (qs n))] with x ht he
  apply tendsto_nhds_unique ht
  exact (hqs.mul_const (gamma m f g x)).congr (fun n => (he n).symm)

lemma gamma_const_mul_right (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    gamma m f (fun x => c*g x) =ᵐ[m] (fun x => c*gamma m f g x) := by
  filter_upwards [gamma_const_mul_left hfinite hpar hg hf c,
    gamma_comm (m := m) f (fun x => c*g x),gamma_comm (m := m) g f] with x hc h1 h2
  rw [h1,hc,h2]

lemma weakGradient_linear_combination_sq (hfinite : FiniteOnBoundedSets m)
    (hpar : LocalGradientParallelogram m) {f g : X → ℝ}
    (hf : LocalSobolev m f) (hg : LocalSobolev m g) (c : ℝ) :
    ∀ᵐ x ∂m, (weakGradient m (fun y => f y+c*g y) x)^2 =
      (weakGradient m f x)^2 + 2*c*gamma m f g x + c^2*(weakGradient m g x)^2 := by
  have hc := hg.const_mul c
  have hs := hf.add hfinite hc
  filter_upwards [gamma_self (m := m) (fun y => f y+c*g y),
    gamma_add_left hfinite hpar hf hc hs,
    gamma_add_right hfinite hpar hf hf hc,
    gamma_add_right hfinite hpar hc hf hc,
    gamma_const_mul_left hfinite hpar hg hf c,
    gamma_const_mul_left hfinite hpar hg hc c,
    gamma_const_mul_right hfinite hpar hf hg c,
    gamma_const_mul_right hfinite hpar hg hg c,
    gamma_self (m := m) f,gamma_self (m := m) g,gamma_comm (m := m) g f]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  rw [← h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
  ring


lemma gamma_sq_le (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, (gamma m f g x)^2 ≤ (weakGradient m f x)^2 * (weakGradient m g x)^2 := by
  filter_upwards [ae_all_iff.mpr (fun q : ℚ =>
    weakGradient_linear_combination_sq hfinite hpar hf hg (q:ℝ))] with x hx
  have hn (c : ℝ) : 0 ≤ (weakGradient m g x)^2*(c*c) + (2*gamma m f g x)*c +
      (weakGradient m f x)^2 := by
    obtain ⟨qs,_,_,ht⟩ := Real.exists_seq_rat_strictMono_tendsto c
    have hq (n : ℕ) : 0 ≤ (weakGradient m g x)^2*((qs n:ℝ)*(qs n:ℝ)) +
        (2*gamma m f g x)*(qs n:ℝ) + (weakGradient m f x)^2 := by
      have H := sq_nonneg (weakGradient m (fun y => f y+(qs n:ℝ)*g y) x)
      rw [hx (qs n)] at H
      nlinarith
    have ht' : Tendsto (fun n => (weakGradient m g x)^2*((qs n:ℝ)*(qs n:ℝ)) +
        (2*gamma m f g x)*(qs n:ℝ) + (weakGradient m f x)^2) atTop
      (𝓝 ((weakGradient m g x)^2*(c*c) + (2*gamma m f g x)*c + (weakGradient m f x)^2)) :=
      (((ht.mul ht).const_mul _).add (ht.const_mul _)).add_const _
    exact ge_of_tendsto ht' (Eventually.of_forall hq)
  have H := discrim_le_zero hn
  dsimp only [discrim] at H
  nlinarith

lemma abs_gamma_le (hfinite : FiniteOnBoundedSets m) (hpar : LocalGradientParallelogram m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    ∀ᵐ x ∂m, |gamma m f g x| ≤ weakGradient m f x * weakGradient m g x := by
  filter_upwards [gamma_sq_le hfinite hpar hf hg,weakGradient_nonneg (m := m) f,
    weakGradient_nonneg (m := m) g] with x h hn hm
  have hp : 0 ≤ weakGradient m f x*weakGradient m g x := mul_nonneg hn hm
  have he : (gamma m f g x)^2 ≤ (weakGradient m f x*weakGradient m g x)^2 := by
    nlinarith only [h]
  exact (sq_le_sq₀ (abs_nonneg _) hp).mp (by simpa only [sq_abs] using he)

lemma gamma_aestronglyMeasurable (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : LocalSobolev m f) (hg : LocalSobolev m g) :
    AEStronglyMeasurable (gamma m f g) m := by
  exact ((((weakGradient_isMinimal (hf.add hfinite hg).2).1.1.aestronglyMeasurable).pow 2).sub
    (((weakGradient_isMinimal (hf.sub hfinite hg).2).1.1.aestronglyMeasurable).pow 2)).mul_const (4⁻¹ : ℝ)

lemma integrable_gamma (hfinite : FiniteOnBoundedSets m)
    {f g : X → ℝ} (hf : Sobolev m f) (hg : Sobolev m g) : Integrable (gamma m f g) m := by
  exact (((hf.add hfinite hg).2.2.integrable_sq).sub
    ((hf.sub hfinite hg).2.2.integrable_sq)).div_const 4
end WeakHessian

end

end OAI
