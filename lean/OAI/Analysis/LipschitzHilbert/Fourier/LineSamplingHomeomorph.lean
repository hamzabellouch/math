import OAI.Analysis.LipschitzHilbert.Fourier.LineDerivativeCommutatorL2
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-! The actual short-time line sampling map and its inverse. -/
noncomputable section
open Set
namespace LipschitzHilbert.PacketRepresentation

def lineSampling (u : ℝ → ℝ) (t y : ℝ) : ℝ := y-t*u y

theorem lineSampling_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) : LipschitzWith 2 (lineSampling u t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hu.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
  simp only [Real.dist_eq,NNReal.coe_ofNat,lineSampling]
  have he : x-t*u x-(y-t*u y)=(x-y)-t*(u x-u y) := by ring
  rw [he]
  have htri := abs_sub (x-y) (t*(u x-u y))
  rw [abs_mul] at htri
  have hm := mul_le_mul_of_nonneg_left h (abs_nonneg t)
  nlinarith [abs_nonneg (x-y)]

theorem lineSampling_antilipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (t : ℝ) (ht : |t|≤1/2) : AntilipschitzWith 2 (lineSampling u t) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have h := hu.dist_le_mul x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at h
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  have he : x-y=(lineSampling u t x-lineSampling u t y)+t*(u x-u y) := by
    unfold lineSampling
    ring
  have htri : |x-y|≤|lineSampling u t x-lineSampling u t y|+|t| *|u x-u y| := by
    conv_lhs => rw [he]
    exact (abs_add_le _ _).trans_eq (by rw [abs_mul])
  have hm := mul_le_mul_of_nonneg_left h (abs_nonneg t)
  nlinarith [abs_nonneg (x-y)]

theorem lineSampling_surjective (u : ℝ → ℝ) (hu : Continuous u) (B : ℝ)
    (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) : Function.Surjective (lineSampling u t) := by
  intro y
  let a := y-|t| *B
  let b := y+|t| *B
  have hab : a≤b := by dsimp [a,b]; nlinarith [abs_nonneg t]
  have hprod (x : ℝ) : -(|t| *B)≤t*u x ∧ t*u x≤|t| *B := by
    have hh := mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t)
    rw [←abs_mul] at hh
    exact abs_le.mp hh
  have ha : lineSampling u t a≤y := by have := (hprod a).1; dsimp [lineSampling,a]; linarith
  have hb' : y≤lineSampling u t b := by have := (hprod b).2; dsimp [lineSampling,b]; linarith
  have hc : Continuous (lineSampling u t) := continuous_id.sub (continuous_const.mul hu)
  obtain ⟨x,_,hx⟩ := intermediate_value_Icc hab hc.continuousOn ⟨ha,hb'⟩
  exact ⟨x,hx⟩

def lineSamplingHomeomorph (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) : ℝ ≃ₜ ℝ :=
  let e := Equiv.ofBijective (lineSampling u t)
    ⟨(lineSampling_antilipschitz u hu t ht).injective,lineSampling_surjective u hu.continuous B hB hb t⟩
  { e with
    continuous_toFun := (lineSampling_lipschitz u hu t ht).continuous
    continuous_invFun := ((lineSampling_antilipschitz u hu t ht).to_rightInverse e.apply_symm_apply).continuous }

theorem lineSamplingHomeomorph_apply (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) (y : ℝ) :
    lineSamplingHomeomorph u hu B hB hb t ht y=lineSampling u t y := rfl

theorem lineSamplingHomeomorph_symm_lipschitz (u : ℝ → ℝ) (hu : LipschitzWith 1 u)
    (B : ℝ) (hB : 0≤B) (hb : ∀ x, |u x|≤B) (t : ℝ) (ht : |t|≤1/2) :
    LipschitzWith 2 (lineSamplingHomeomorph u hu B hB hb t ht).symm :=
  (lineSampling_antilipschitz u hu t ht).to_rightInverse
    (lineSamplingHomeomorph u hu B hB hb t ht).apply_symm_apply

end LipschitzHilbert.PacketRepresentation

end

end OAI
