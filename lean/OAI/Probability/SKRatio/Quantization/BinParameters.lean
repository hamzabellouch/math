import Mathlib
import OAI.Probability.SKRatio.Quantization.BinGeometry

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def count (σ : ι → α) (a : α) : ℕ := (Finset.univ.filter (fun i => σ i=a)).card

def binMean (σ : ι → α) (p : ι → ℝ) (a : α) : ℝ := sum σ p a/(count σ a:ℝ)

def binCentered (σ : ι → α) (p : ι → ℝ) (i : ι) : ℝ := p i-binMean σ p (σ i)

lemma sum_const_bin (σ : ι → α) (c : α → ℝ) (a : α) :
    sum σ (fun i => c (σ i)) a = (count σ a:ℝ)*c a := by
  unfold sum count
  calc
    _ = ∑ i with σ i=a, c a := Finset.sum_congr rfl (fun i hi => by dsimp only []; rw [(Finset.mem_filter.mp hi).2])
    _ = _ := by simp

lemma sum_add_bin (σ : ι → α) (p q : ι → ℝ) (a : α) :
    sum σ (fun i => p i+q i) a = sum σ p a+sum σ q a := Finset.sum_add_distrib
lemma sum_sub_bin (σ : ι → α) (p q : ι → ℝ) (a : α) :
    sum σ (fun i => p i-q i) a = sum σ p a-sum σ q a := Finset.sum_sub_distrib _ _

lemma count_mul_binMean (σ : ι → α) (p : ι → ℝ) (a : α) :
    (count σ a:ℝ)*binMean σ p a=sum σ p a := by
  by_cases h : count σ a=0
  · have he : Finset.univ.filter (fun i => σ i=a)=∅ := Finset.card_eq_zero.mp h
    simp [binMean,h,sum,he]
  · exact mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr h)

lemma binCentered_zeroSum (σ : ι → α) (p : ι → ℝ) : ZeroSum σ (binCentered σ p) := by
  intro a
  change sum σ (fun i => p i-binMean σ p (σ i)) a=0
  rw [sum_sub_bin,sum_const_bin,count_mul_binMean,sub_self]

lemma binCentered_decomp (σ : ι → α) (p : ι → ℝ) (i : ι) :
    p i=binMean σ p (σ i)+binCentered σ p i := by unfold binCentered; ring

lemma bin_orthogonal_decomposition {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u)
    (b : α → ℝ) (a : α) :
    sum σ (fun i => (b (σ i)+u i)^2) a =
      (count σ a:ℝ)*b a^2+overlap σ u u a := by
  have he : sum σ (fun i => b (σ i)*u i) a = b a*sum σ u a := by
    unfold sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only []
    rw [(Finset.mem_filter.mp hi).2]
  simp only [add_sq,sum_add_bin]
  have hcross : sum σ (fun i => 2*b (σ i)*u i) a=0 := by
    calc
      _ = 2*sum σ (fun i => b (σ i)*u i) a := by unfold sum; simp [mul_assoc,Finset.mul_sum]
      _ = 0 := by rw [he,hu a,mul_zero,mul_zero]
  rw [sum_const_bin σ (fun a => b a^2),hcross,add_zero]
  simp only [overlap,pow_two]

lemma centered_fiber_sq (σ : ι → α) (p : ι → ℝ) (a : α) :
    sum σ (fun i => p i^2) a =
      (count σ a:ℝ)*binMean σ p a^2+overlap σ (binCentered σ p) (binCentered σ p) a := by
  have he : (fun i => p i^2) = (fun i => (binMean σ p (σ i)+binCentered σ p i)^2) := by
    ext i
    rw [←binCentered_decomp]
  rw [he,bin_orthogonal_decomposition (binCentered_zeroSum σ p)]

lemma normalized_fiber_sq (σ : ι → α) (p : ι → ℝ) (a : α) :
    (sqrt (count σ a:ℝ)*binMean σ p a)^2+
      (sqrt (overlap σ (binCentered σ p) (binCentered σ p) a))^2 =
      sum σ (fun i => p i^2) a := by
  rw [mul_pow,sq_sqrt (Nat.cast_nonneg _),sq_sqrt (overlap_self_nonneg ..),centered_fiber_sq]

variable [Fintype α]

abbrev ParameterSpace (α : Type*) [Fintype α] := EuclideanSpace ℝ (α ⊕ α)

def ParameterSet (α : Type*) [Fintype α] : Set (ParameterSpace α) :=
  {z | ‖z‖=1 ∧ ∀ a, 0≤z (.inr a)}

abbrev Parameters (α : Type*) [Fintype α] := ↥(ParameterSet α)

omit [DecidableEq α] in
lemma parameterSet_compact : IsCompact (ParameterSet α) := by
  have hc : IsClosed {z : ParameterSpace α | ∀ a, 0≤z (.inr a)} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    exact isClosed_le continuous_const (EuclideanSpace.proj (Sum.inr a : α ⊕ α)).continuous
  simpa only [ParameterSet,Metric.sphere,dist_zero_right,Set.ofPred_and] using
    (isCompact_sphere (0 : ParameterSpace α) 1).inter_right hc

instance : CompactSpace (Parameters α) := isCompact_iff_compactSpace.mp parameterSet_compact

def paramB (z : Parameters α) (a : α) : ℝ := z.val (.inl a)
def paramR (z : Parameters α) (a : α) : ℝ := z.val (.inr a)

omit [DecidableEq α] in
lemma paramR_nonneg (z : Parameters α) (a : α) : 0≤paramR z a := z.property.2 a

omit [DecidableEq α] in
lemma param_sum_sq (z : Parameters α) : (∑ a, ((paramB z a)^2+(paramR z a)^2))=1 := by
  have hh := EuclideanSpace.real_norm_sq_eq z.val
  rw [z.property.1] at hh
  simpa only [one_pow,Fintype.sum_sum_type,Finset.sum_add_distrib,paramB,paramR] using hh.symm

def parametersOf (σ : ι → α) (p : ι → ℝ) (hp : ∑ i, p i^2=1) : Parameters α :=
  ⟨WithLp.toLp 2 (Sum.elim (fun a => sqrt (count σ a:ℝ)*binMean σ p a)
    (fun a => sqrt (overlap σ (binCentered σ p) (binCentered σ p) a))),by
    constructor
    · have hs : ‖WithLp.toLp 2 (Sum.elim (fun a => sqrt (count σ a:ℝ)*binMean σ p a)
          (fun a => sqrt (overlap σ (binCentered σ p) (binCentered σ p) a)))‖^2=1 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
          ←Finset.sum_add_distrib,normalized_fiber_sq,sum_fibers,hp]
      nlinarith only [hs,norm_nonneg (WithLp.toLp 2 (Sum.elim (fun a => sqrt (count σ a:ℝ)*binMean σ p a)
        (fun a => sqrt (overlap σ (binCentered σ p) (binCentered σ p) a))))]
    · intro a
      exact sqrt_nonneg _⟩

@[simp] lemma parametersOf_B (σ : ι → α) (p : ι → ℝ) (hp : ∑ i, p i^2=1) (a : α) :
    paramB (parametersOf σ p hp) a = sqrt (count σ a:ℝ)*binMean σ p a := rfl
@[simp] lemma parametersOf_R (σ : ι → α) (p : ι → ℝ) (hp : ∑ i, p i^2=1) (a : α) :
    paramR (parametersOf σ p hp) a = sqrt (overlap σ (binCentered σ p) (binCentered σ p) a) := rfl

omit [DecidableEq α] in
theorem parameters_finite_net {η : ℝ} (hη : 0<η) :
    ∃ F : Finset (Parameters α), ∀ z : Parameters α,
      ∃ z' ∈ F, ‖z.val-z'.val‖<η := by
  have hcover : (Set.univ : Set (Parameters α)) ⊆ ⋃ z : Parameters α, Metric.ball z η := by
    intro z _
    exact Set.mem_iUnion.mpr ⟨z,by simpa using hη⟩
  obtain ⟨s,hs,hsfin,hscov⟩ := isCompact_univ.elim_finite_subcover_image
    (b := (Set.univ : Set (Parameters α))) (c := fun z => Metric.ball z η)
    (fun z _ => Metric.isOpen_ball) (by simpa using hcover)
  refine ⟨hsfin.toFinset,fun z => ?_⟩
  have hz := hscov (Set.mem_univ z)
  obtain ⟨z',hz',hd⟩ := Set.mem_iUnion₂.mp hz
  exact ⟨z',by simpa using hz',by simpa only [Metric.mem_ball,Subtype.dist_eq,dist_eq_norm] using hd⟩

end SKRatio.Bins

end

end OAI
