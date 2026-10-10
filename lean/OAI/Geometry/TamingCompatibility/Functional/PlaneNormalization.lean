import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeDirectionCoordinates

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def first (a : V) : V := ‖a‖⁻¹ • a

def normalPart (a b : V) : V := b - ⟪first a,b⟫ • first a

def second (a b : V) : V := ‖normalPart a b‖⁻¹ • normalPart a b

def area (a b : V) : ℝ := ‖a‖*‖normalPart a b‖

lemma norm_first {a : V} (ha : a ≠ 0) : ‖first a‖ = 1 := by
  simp only [first,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)

lemma first_reconstruct (a : V) : ‖a‖ • first a = a := by
  by_cases ha : a = 0
  · simp [ha,first]
  · rw [first,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha),one_smul]

lemma normalPart_orthogonal {a : V} (ha : a ≠ 0) (b : V) : ⟪first a,normalPart a b⟫ = 0 := by
  simp only [normalPart,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_first ha,one_pow,mul_one,sub_self]

lemma norm_second {a b : V} (hab : normalPart a b ≠ 0) : ‖second a b‖ = 1 :=
  norm_first hab

lemma first_second_orthogonal {a : V} (ha : a ≠ 0) (b : V) : ⟪first a,second a b⟫ = 0 := by
  rw [second,real_inner_smul_right,normalPart_orthogonal ha,mul_zero]

lemma second_reconstruct (a b : V) : ‖normalPart a b‖ • second a b = normalPart a b :=
  first_reconstruct _

lemma normalPart_complex_ne_zero (K : V →L[ℝ] V) (hK : ∀ v, K (K v) = -v)
    {a : V} (ha : a ≠ 0) : normalPart a (K a) ≠ 0 := by
  intro h
  have hh : K a = (⟪first a,K a⟫*‖a‖⁻¹) • a := by
    rw [normalPart,sub_eq_zero] at h
    calc
      K a = ⟪first a,K a⟫ • first a := h
      _ = _ := by rw [first,smul_smul]
  let c := ⟪first a,K a⟫*‖a‖⁻¹
  have hc : K a = c • a := hh
  have he : (-1:ℝ) • a = c^2 • a := by
    rw [neg_one_smul,← hK a,hc,map_smul,hc,smul_smul,pow_two]
  have hec : (-1:ℝ) = c^2 := (smul_left_injective ℝ ha) he
  nlinarith [sq_nonneg c]

lemma area_pos {a b : V} (ha : a ≠ 0) (hab : normalPart a b ≠ 0) : 0 < area a b :=
  mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hab)

lemma reconstruct_second (a b : V) :
    b = ⟪first a,b⟫ • first a + ‖normalPart a b‖ • second a b := by
  rw [second_reconstruct,normalPart]
  abel

lemma alternating_area (β : V [⋀^Fin 2]→L[ℝ] ℝ) (a b : V) :
    β ![a,b] = area a b * β ![first a,second a b] := by
  have hsum (u v w : V) : β ![u,v+w] = β ![u,v]+β ![u,w] := by
    rw [UnitaryFrame.alternating_swap]
    have hh := β.vecCons_add ![u] v w
    rw [hh,UnitaryFrame.alternating_swap β v u,UnitaryFrame.alternating_swap β w u]
    ring
  conv_lhs => rw [← first_reconstruct a,reconstruct_second a b]
  rw [hsum,UnitaryFrame.alternating_smul_left,UnitaryFrame.alternating_smul_left,
    UnitaryFrame.alternating_smul_right,UnitaryFrame.alternating_smul_right,
    UnitaryFrame.alternating_self]
  dsimp [area]
  ring

lemma first_continuousAt {a : V} (ha : a ≠ 0) : ContinuousAt first a :=
  (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr ha)).smul continuous_id.continuousAt

lemma normalPart_continuousAt {a b : V} (ha : a ≠ 0) :
    ContinuousAt (fun p : V × V => normalPart p.1 p.2) (a,b) := by
  have hf : ContinuousAt (fun p : V × V => first p.1) (a,b) :=
    by
      exact ContinuousAt.comp (x := (a,b)) (g := first) (f := Prod.fst)
        (first_continuousAt ha) continuous_fst.continuousAt
  exact continuous_snd.continuousAt.sub ((hf.inner continuous_snd.continuousAt).smul hf)

lemma second_continuousAt {a b : V} (ha : a ≠ 0) (hab : normalPart a b ≠ 0) :
    ContinuousAt (fun p : V × V => second p.1 p.2) (a,b) := by
  change ContinuousAt (first ∘ fun p : V × V => normalPart p.1 p.2) (a,b)
  exact ContinuousAt.comp (x := (a,b))
    (g := first) (f := fun p : V × V => normalPart p.1 p.2)
    (first_continuousAt hab) (normalPart_continuousAt (b := b) ha)

lemma area_continuousAt {a b : V} (ha : a ≠ 0) :
    ContinuousAt (fun p : V × V => area p.1 p.2) (a,b) :=
  continuous_fst.continuousAt.norm.mul (normalPart_continuousAt ha).norm
end TamingCompatibility.PlaneVariation

end
end

end OAI
