import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.LazyWalkHilbert
import OAI.Probability.CriticalPercolation.Harmonic.WalkEnergyLower

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

def projectedFunction (f : RegularHilbert A) (t : A) (x : A) : ℝ :=
  inner ℝ (regular x f-f) (regular t f-f) / (4*(W.generators.card:ℝ)*W.walkEnergy f)

lemma exists_large_generator_gradient (f : RegularHilbert A) :
    ∃ t∈W.generators, 4*W.walkEnergy f≤‖regular t f-f‖^2 := by
  by_contra! h
  have hh := Finset.sum_lt_sum_of_nonempty (show W.generators.Nonempty from ⟨1,W.one_mem⟩)
    (fun s hs => h s hs)
  rw [W.walkEnergy_gradient] at hh
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  nlinarith

lemma projectedFunction_one (f : RegularHilbert A) (t : A) :
    W.projectedFunction f t 1=0 := by simp [projectedFunction]

lemma projectedFunction_edge_bound (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : t∈W.generators) (x s : A) (hs : s∈W.generators) :
    |W.projectedFunction f t (x*s)-W.projectedFunction f t x|≤1 := by
  let q := 4*(W.generators.card:ℝ)*W.walkEnergy f
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hq : 0<q := mul_pos (mul_pos (by norm_num) hc) hf
  have hg (a : A) (ha : a∈W.generators) : ‖regular a f-f‖≤Real.sqrt q := by
    have h := W.regular_energy_displacement f 1 (by simpa [ball] using ha)
    simpa only [Nat.cast_one,one_mul] using h
  have he : (regular (x*s) f-f)-(regular x f-f)=regular x (regular s f-f) := by
    rw [regular_mul,map_sub]
    abel
  unfold projectedFunction
  rw [←sub_div,←inner_sub_left,he,abs_div,abs_of_pos hq]
  apply (div_le_one hq).mpr
  calc
    _ ≤ ‖regular x (regular s f-f)‖*‖regular t f-f‖ := abs_real_inner_le_norm _ _
    _ = ‖regular s f-f‖*‖regular t f-f‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ Real.sqrt q*Real.sqrt q := mul_le_mul (hg s hs) (hg t ht) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = q := Real.mul_self_sqrt hq.le

lemma projectedFunction_length_bound (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : t∈W.generators) (x : A) :
    |W.projectedFunction f t x|≤(W.length x:ℝ) := by
  let q := 4*(W.generators.card:ℝ)*W.walkEnergy f
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hq : 0<q := mul_pos (mul_pos (by norm_num) hc) hf
  have hx := W.regular_energy_displacement f (W.length x) (W.mem_ball_length x)
  have ht' := W.regular_energy_displacement f 1 (by simpa [ball] using ht)
  simp only [Nat.cast_one,one_mul] at ht'
  unfold projectedFunction
  rw [abs_div,abs_of_pos hq]
  apply (div_le_iff₀ hq).mpr
  calc
    _ ≤ ‖regular x f-f‖*‖regular t f-f‖ := abs_real_inner_le_norm _ _
    _ ≤ ((W.length x:ℝ)*Real.sqrt q)*Real.sqrt q :=
      mul_le_mul hx ht' (norm_nonneg _) (by positivity)
    _ = (W.length x:ℝ)*q := by rw [mul_assoc,Real.mul_self_sqrt hq.le]

lemma projectedFunction_generator_lower (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : 4*W.walkEnergy f≤‖regular t f-f‖^2) :
    (W.generators.card:ℝ)⁻¹≤W.projectedFunction f t t := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hq : 0<4*(W.generators.card:ℝ)*W.walkEnergy f := by positivity
  unfold projectedFunction
  rw [real_inner_self_eq_norm_sq]
  apply (le_div_iff₀ hq).mpr
  have he : (W.generators.card:ℝ)⁻¹*(4*(W.generators.card:ℝ)*W.walkEnergy f)=4*W.walkEnergy f := by
    field_simp
  rw [he]
  exact ht

lemma sum_walk_displacement (f : RegularHilbert A) :
    (∑ s∈W.generators, (f-regular s f))=(2*(W.generators.card:ℝ)) • (f-W.lazyWalk f) := by
  have hc : (W.generators.card:ℝ)≠0 := by exact_mod_cast W.generators_card_pos.ne'
  rw [Finset.sum_sub_distrib,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ,W.lazyWalk_apply,W.walkAverage_apply]
  simp only [smul_sub,smul_add,smul_smul]
  have h1 : (2*(W.generators.card:ℝ))*(1/2)=W.generators.card := by ring
  have h2 : (2*(W.generators.card:ℝ))*(1/2)*(W.generators.card:ℝ)⁻¹=1 := by field_simp
  rw [h1,←mul_assoc (2*(W.generators.card:ℝ)) (1/2) (W.generators.card:ℝ)⁻¹,h2,one_smul]
  module

lemma projectedFunction_residual (f : RegularHilbert A) (t x : A) :
    (∑ s∈W.generators, (W.projectedFunction f t x-W.projectedFunction f t (x*s)))=
      (2*(W.generators.card:ℝ))* inner ℝ (regular x (f-W.lazyWalk f)) (regular t f-f) /
        (4*(W.generators.card:ℝ)*W.walkEnergy f) := by
  simp only [projectedFunction,←sub_div,←Finset.sum_div,←inner_sub_left,←sum_inner]
  have he : (∑ s∈W.generators, (regular x f-f-(regular (x*s) f-f)))=
      regular x (∑ s∈W.generators, (f-regular s f)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [regular_mul,map_sub]
    abel
  rw [he,W.sum_walk_displacement,map_smul,real_inner_smul_left]

lemma projectedFunction_residual_sq (f : RegularHilbert A) (hf : 0<W.walkEnergy f)
    (t : A) (ht : t∈W.generators) (x : A) :
    (∑ s∈W.generators, (W.projectedFunction f t x-W.projectedFunction f t (x*s)))^2≤
      (W.generators.card:ℝ)*‖f-W.lazyWalk f‖^2/W.walkEnergy f := by
  have hc : (0:ℝ)<W.generators.card := by exact_mod_cast W.generators_card_pos
  have hgrad := (Finset.single_le_sum (f := fun s => ‖regular s f-f‖^2)
    (fun s hs => sq_nonneg _) ht).trans_eq (W.walkEnergy_gradient f)
  have hi := abs_real_inner_le_norm (regular x (f-W.lazyWalk f)) (regular t f-f)
  rw [LinearIsometryEquiv.norm_map] at hi
  have hisq := pow_le_pow_left₀ (abs_nonneg _) hi 2
  rw [sq_abs,mul_pow] at hisq
  have hb := mul_le_mul_of_nonneg_left hgrad (sq_nonneg ‖f-W.lazyWalk f‖)
  rw [W.projectedFunction_residual]
  rw [div_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos (show 0<4*(W.generators.card:ℝ)*W.walkEnergy f by positivity)) hf).mpr
  have hm := mul_le_mul_of_nonneg_left (hisq.trans hb)
    (show 0≤4*(W.generators.card:ℝ)^2*W.walkEnergy f by positivity)
  nlinarith only [hm]

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
