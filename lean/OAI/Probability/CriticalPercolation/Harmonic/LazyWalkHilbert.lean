import Mathlib
import OAI.Probability.CriticalPercolation.Growth.WordLengthGeometry

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis
variable {A : Type*} [Group A]
abbrev RegularHilbert (A : Type*) := lp (fun _ : A => ℝ) 2

private lemma translate_mem (a : A) (f : RegularHilbert A) :
    Memℓp (fun x => f (a*x)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ENNReal).toReal)).mpr
  have hf : Summable (fun x : A => ‖f x‖ ^ (2:ENNReal).toReal) :=
    (lp.memℓp f).summable (by norm_num)
  exact (Equiv.mulLeft a).summable_iff.mpr hf

private def translateVector (a : A) (f : RegularHilbert A) : RegularHilbert A :=
  ⟨fun x => f (a*x), translate_mem a f⟩

private def regularLinearEquiv (a : A) : RegularHilbert A ≃ₗ[ℝ] RegularHilbert A where
  toFun := translateVector a⁻¹
  invFun := translateVector a
  left_inv f := by
    apply Subtype.ext
    funext x
    change f (a⁻¹*(a*x))=f x
    rw [inv_mul_cancel_left]
  right_inv f := by
    apply Subtype.ext
    funext x
    change f (a*(a⁻¹*x))=f x
    rw [mul_inv_cancel_left]
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' c f := by apply Subtype.ext; rfl

def regular (a : A) : RegularHilbert A ≃ₗᵢ[ℝ] RegularHilbert A :=
  (regularLinearEquiv a).isometryOfInner (by
    intro f g
    change (∑' x, inner ℝ (f (a⁻¹*x)) (g (a⁻¹*x))) = ∑' x, inner ℝ (f x) (g x)
    exact (Equiv.mulLeft a⁻¹).tsum_eq (fun x : A => inner ℝ (f x) (g x)))

@[simp] lemma regular_apply (a : A) (f : RegularHilbert A) (x : A) :
    regular a f x=f (a⁻¹*x) := rfl
@[simp] lemma regular_one (f : RegularHilbert A) : regular 1 f=f := by ext x; simp
@[simp] lemma regular_mul (a b : A) (f : RegularHilbert A) :
    regular (a*b) f=regular a (regular b f) := by ext x; simp [mul_assoc]

lemma regular_inner (a : A) (f g : RegularHilbert A) :
    inner ℝ (regular a f) g=inner ℝ f (regular a⁻¹ g) := by
  have h := (regular a).inner_map_map f (regular a⁻¹ g)
  simpa only [←regular_mul,mul_inv_cancel,regular_one] using h

namespace WordGeometry
variable (W : WordGeometry A)
def walkAverage : RegularHilbert A →ₗ[ℝ] RegularHilbert A :=
  (W.generators.card:ℝ)⁻¹ • ∑ s∈W.generators, (regular s).toLinearEquiv.toLinearMap

def lazyWalk : RegularHilbert A →ₗ[ℝ] RegularHilbert A :=
  (1/2:ℝ) • (LinearMap.id+W.walkAverage)

def walkEnergy (f : RegularHilbert A) : ℝ := inner ℝ f (f-W.lazyWalk f)

lemma generators_card_pos : 0 < W.generators.card :=
  Finset.card_pos.mpr ⟨1,W.one_mem⟩

lemma walkAverage_apply (f : RegularHilbert A) :
    W.walkAverage f = (W.generators.card:ℝ)⁻¹ • ∑ s∈W.generators, regular s f := by
  simp [walkAverage,LinearMap.sum_apply]

lemma lazyWalk_apply (f : RegularHilbert A) :
    W.lazyWalk f = (1/2:ℝ) • (f+W.walkAverage f) := rfl

lemma walkAverage_norm_le (f : RegularHilbert A) : ‖W.walkAverage f‖≤‖f‖ := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  rw [W.walkAverage_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ (W.generators.card:ℝ)⁻¹ * ∑ s∈W.generators, ‖regular s f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ = ‖f‖ := by simp [hc.ne']

lemma walkAverage_symmetric (f g : RegularHilbert A) :
    inner ℝ (W.walkAverage f) g=inner ℝ f (W.walkAverage g) := by
  simp only [W.walkAverage_apply,real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum]
  congr 1
  simp only [regular_inner]
  apply Finset.sum_bij (fun s _ => s⁻¹)
  · intro s hs
    rw [←W.inv_eq]
    exact Finset.inv_mem_inv hs
  · intro a _ b _ h; exact inv_injective h
  · intro b hb
    refine ⟨b⁻¹, ?_, inv_inv b⟩
    rw [←W.inv_eq]
    exact Finset.inv_mem_inv hb
  · intro s hs; rfl

lemma lazyWalk_symmetric (f g : RegularHilbert A) :
    inner ℝ (W.lazyWalk f) g=inner ℝ f (W.lazyWalk g) := by
  simp only [W.lazyWalk_apply,real_inner_smul_left,real_inner_smul_right,
    inner_add_left,inner_add_right,W.walkAverage_symmetric]

lemma lazyWalk_norm_le (f : RegularHilbert A) : ‖W.lazyWalk f‖≤‖f‖ := by
  rw [W.lazyWalk_apply,norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have ht := norm_add_le f (W.walkAverage f)
  have ha := W.walkAverage_norm_le f
  linarith

lemma lazyWalk_positive (f : RegularHilbert A) : 0 ≤ inner ℝ f (W.lazyWalk f) := by
  have hb := abs_real_inner_le_norm f (W.walkAverage f)
  have h := mul_le_mul_of_nonneg_left (W.walkAverage_norm_le f) (norm_nonneg f)
  have hl := (abs_le.mp (hb.trans h)).1
  simp only [W.lazyWalk_apply,real_inner_smul_right,inner_add_right,
    real_inner_self_eq_norm_sq]
  nlinarith

lemma walkEnergy_nonneg (f : RegularHilbert A) : 0≤W.walkEnergy f := by
  have hb := real_inner_le_norm f (W.lazyWalk f)
  have h := mul_le_mul_of_nonneg_left (W.lazyWalk_norm_le f) (norm_nonneg f)
  unfold walkEnergy
  rw [inner_sub_right,real_inner_self_eq_norm_sq]
  nlinarith

lemma walkEnergy_dissipation (f : RegularHilbert A) :
    ‖f-W.lazyWalk f‖^2 ≤ W.walkEnergy f-W.walkEnergy (W.lazyWalk f) := by
  have hp := W.lazyWalk_positive (f-W.lazyWalk f)
  rw [map_sub] at hp
  simp only [inner_sub_left,inner_sub_right] at hp
  rw [←W.lazyWalk_symmetric f (W.lazyWalk f)] at hp
  have hcomm : inner ℝ (W.lazyWalk f) f = inner ℝ f (W.lazyWalk f) := real_inner_comm _ _
  unfold walkEnergy
  simp only [inner_sub_right,real_inner_self_eq_norm_sq,norm_sub_sq_real]
  nlinarith [real_inner_self_eq_norm_sq (W.lazyWalk f)]

lemma walkEnergy_gradient (f : RegularHilbert A) :
    (∑ s∈W.generators, ‖regular s f-f‖^2) =
      4*(W.generators.card:ℝ)*W.walkEnergy f := by
  have hc : (W.generators.card:ℝ)≠0 := by exact_mod_cast W.generators_card_pos.ne'
  simp only [norm_sub_sq_real,LinearIsometryEquiv.norm_map,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
    nsmul_eq_mul,←Finset.mul_sum]
  unfold walkEnergy
  simp only [inner_sub_right,W.lazyWalk_apply,real_inner_smul_right,
    inner_add_right,real_inner_self_eq_norm_sq,W.walkAverage_apply,inner_sum]
  simp_rw [real_inner_comm (regular _ f) f]
  field_simp
  ring

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
