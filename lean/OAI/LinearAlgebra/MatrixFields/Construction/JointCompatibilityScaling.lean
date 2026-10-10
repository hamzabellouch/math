import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.JointAmbientRateLimit
import OAI.LinearAlgebra.MatrixFields.Entropy.JointCompatibilityEntropyBound

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.JointCompatibilityScaling

open MatrixMultiplication.Foundation JointTypeCounts JointCompatibilityIncidence
open JointCompatibilityEntropyBound Filter
open scoped BigOperators Topology

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {Shape : C → Type*}
  [∀ c, Fintype (Shape c)] [∀ c, DecidableEq (Shape c)]

def baseSize (base : ∀ c, Shape c → ℕ) (c : C) : ℕ := ∑ a, base c a

def baseTotal (base : ∀ c, Shape c → ℕ) : ℕ := ∑ c, baseSize base c

def baseEntropy (base : ∀ c, Shape c → ℕ) : ℝ :=
  ∑ c, (baseSize base c : ℝ) *
    finiteEntropy (fun a => (base c a : ℝ) / baseSize base c)

def baseGroupSize (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (g : Σ c, Option (Shape c)) : ℕ :=
  ∑ a : {a : Shape g.1 // designatedGroup (d g.1) a = g.2}, base g.1 a.val

def baseGroupedEntropy (base : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (H : (Σ c, Option (Shape c)) → ℝ) : ℝ :=
  ∑ g, (baseGroupSize base d g : ℝ) * H g

omit [DecidableEq C] [∀ c, DecidableEq (Shape c)] in
theorem baseSize_le_baseTotal (base : ∀ c, Shape c → ℕ) (c : C) :
    baseSize base c ≤ baseTotal base :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

omit [DecidableEq C] in
theorem sum_baseGroupSize (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) :
    (∑ g, baseGroupSize base d g) = baseTotal base := by
  simp only [baseGroupSize, baseTotal, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  exact Fintype.sum_fiberwise (designatedGroup (d c)) (base c)

section Repeated

variable (Pos : C → Type*)
  [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]

omit [DecidableEq C] [∀ c, DecidableEq (Shape c)] [∀ c, DecidableEq (Pos c)] in
theorem classEntropy_repeated (base : ∀ c, Shape c → ℕ) (t : ℕ) (ht : 0 < t)
    (hsize : ∀ c, Fintype.card (Pos c) = t * baseSize base c) :
    classEntropy Pos Shape (fun c a => t * base c a) = (t : ℝ) * baseEntropy base := by
  simp only [classEntropy, baseEntropy, hsize, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [show (fun a => (t : ℝ) * base c a / ((t : ℝ) * baseSize base c)) =
      (fun a => (base c a : ℝ) / baseSize base c) by
    funext a
    exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht))]
  ring

omit [Fintype C] [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem groupPos_card_repeated (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (t : ℕ)
    (w : FixedClassWords Pos Shape (fun c a => t * base c a))
    (g : Σ c, Option (Shape c)) :
    Fintype.card (GroupPos (w g.1).val (d g.1) g.2) =
      t * baseGroupSize base d g := by
  calc
    Fintype.card (GroupPos (w g.1).val (d g.1) g.2) =
        Fintype.card (Σ a : {a : Shape g.1 // designatedGroup (d g.1) a = g.2},
          {i : Pos g.1 // (w g.1).val i = a.val}) :=
      Fintype.card_congr (Equiv.sigmaSubtypeFiberEquivSubtype (w g.1).val
        (p := fun i => designatedGroup (d g.1) ((w g.1).val i) = g.2)
        (q := fun a => designatedGroup (d g.1) a = g.2) (fun _ => Iff.rfl)).symm
    _ = t * baseGroupSize base d g := by
      simp only [Fintype.card_sigma]
      change (∑ a : {a : Shape g.1 // designatedGroup (d g.1) a = g.2},
        wordPopulation (w g.1).val a.val) = _
      simp only [(w g.1).property, baseGroupSize, Finset.mul_sum]

omit [DecidableEq C] [∀ c, DecidableEq (Pos c)] in
theorem groupedEntropy_repeated (base : ∀ c, Shape c → ℕ)
    (d : ∀ c, Shape c → Prop) (t : ℕ)
    (H : (Σ c, Option (Shape c)) → ℝ)
    (w : FixedClassWords Pos Shape (fun c a => t * base c a)) :
    groupedEntropy Pos Shape (fun c a => t * base c a) d H w =
      (t : ℝ) * baseGroupedEntropy base d H := by
  simp only [JointCompatibilityEntropyBound.groupedEntropy, groupPos_card_repeated, Nat.cast_mul,
    baseGroupedEntropy, Finset.mul_sum, mul_assoc]

end Repeated

def typeErrorFactor (B t : ℕ) : ℝ := 1 + Real.log (t * B + 1 : ℕ)

theorem typeErrorFactor_nonneg (B t : ℕ) : 0 ≤ typeErrorFactor B t := by
  unfold typeErrorFactor
  have hlog : 0 ≤ Real.log (t * B + 1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (t * B)))
  linarith

def classErrorCoefficient (A : C → Type*) [∀ c, Fintype (A c)] : ℝ :=
  ∑ c, ((Fintype.card (A c) : ℝ) + 1)

def groupErrorCoefficient (Shape A : C → Type*)
    [∀ c, Fintype (Shape c)] [∀ c, Fintype (A c)] : ℝ :=
  ∑ g : Σ c, Option (Shape c), (2 * (Fintype.card (A g.1) : ℝ) + 1)

omit [DecidableEq C] in
theorem classTypeError_le (Pos A : C → Type*)
    [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (B t : ℕ) (hsize : ∀ c, Fintype.card (Pos c) ≤ t * B) :
    classTypeError Pos A ≤ classErrorCoefficient A * typeErrorFactor B t := by
  simp only [classTypeError, classErrorCoefficient, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold typeErrorFactor
  apply add_le_add le_rfl
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.succ_le_succ (hsize c)

theorem wordTypeError_le (I A : Type*) [Fintype I] [Fintype A]
    (B t : ℕ) (hsize : Fintype.card I ≤ t * B) :
    wordTypeError I A ≤ (2 * (Fintype.card A : ℝ) + 1) * typeErrorFactor B t := by
  have hlog : Real.log (Fintype.card I + 1 : ℕ) ≤ Real.log (t * B + 1 : ℕ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hsize)
  have h₁ := mul_le_mul_of_nonneg_left (add_le_add_left hlog 1)
    (by positivity : (0 : ℝ) ≤ (Fintype.card A : ℝ) + 1)
  have h₂ := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (Fintype.card A) :
    (0 : ℝ) ≤ Fintype.card A)
  unfold wordTypeError typeErrorFactor
  nlinarith [show (0 : ℝ) ≤ Fintype.card A from Nat.cast_nonneg _]

omit [DecidableEq C] in
theorem groupedTypeError_le (Pos A : C → Type*)
    [∀ c, Fintype (Pos c)] [∀ c, DecidableEq (Pos c)]
    [∀ c, Fintype (A c)] [∀ c, DecidableEq (A c)]
    (counts : ∀ c, Shape c → ℕ) (d : ∀ c, Shape c → Prop)
    (w : FixedClassWords Pos Shape counts)
    (B t : ℕ) (hsize : ∀ c, Fintype.card (Pos c) ≤ t * B) :
    groupedTypeError Pos Shape A counts d w ≤
      groupErrorCoefficient Shape A * typeErrorFactor B t := by
  simp only [groupedTypeError, groupErrorCoefficient, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro g _
  apply wordTypeError_le
  exact (Fintype.card_subtype_le _).trans (hsize g.1)

theorem tendsto_typeErrorFactor_div (B : ℕ) :
    Tendsto (fun t : ℕ => typeErrorFactor B t / (t : ℝ)) atTop (𝓝 0) := by
  have hratio : Tendsto (fun t : ℕ => ((t * B : ℕ) : ℝ) / (t : ℝ))
      atTop (𝓝 (B : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with t ht
    simp only [Nat.cast_mul]
    exact (mul_div_cancel_left₀ (B : ℝ) (Nat.cast_ne_zero.mpr ht)).symm
  have hlog := JointAmbientRateLimit.tendsto_log_succ_div_nat_of_ratio hratio
  have hinv : Tendsto (fun t : ℕ => (1 : ℝ) / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa only [typeErrorFactor, add_div, add_zero] using hinv.add hlog

theorem tendsto_mul_typeErrorFactor_div (K : ℝ) (B : ℕ) :
    Tendsto (fun t : ℕ => K * typeErrorFactor B t / (t : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_div_assoc, mul_zero] using (tendsto_typeErrorFactor_div B).const_mul K

end MatrixMultiplication.JointCompatibilityScaling

end
end

end MatrixAllFields

end OAI
