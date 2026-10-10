import OAI.Probability.ClassicalON.FiniteVolume

namespace OAI

universe uP

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ClassicalON

abbrev DiscreteTorus (L : ℕ) := ZMod L × ZMod L

def torusWave {L : ℕ} [NeZero L] (p x : DiscreteTorus L) : ℂ :=
  ZMod.stdAddChar (p.1*x.1+p.2*x.2)

variable {L : ℕ} [NeZero L]

@[simp] theorem torusWave_norm (p x : DiscreteTorus L) : ‖torusWave p x‖ = 1 :=
  AddChar.norm_apply _ _

@[simp] theorem torusWave_add (p x y : DiscreteTorus L) :
    torusWave p (x+y) = torusWave p x * torusWave p y := by
  unfold torusWave
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

@[simp] theorem torusWave_zero (p : DiscreteTorus L) : torusWave p 0 = 1 := by
  simp [torusWave]

@[simp] theorem torusWave_conj (p x : DiscreteTorus L) :
    conj (torusWave p x) = torusWave (-p) x := by
  unfold torusWave
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

theorem torusWave_mul_conj (p q x : DiscreteTorus L) :
    torusWave p x*conj (torusWave q x) = torusWave (p-q) x := by
  rw [torusWave_conj]
  unfold torusWave
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
  ring

theorem sum_stdAddChar_mul (t : ZMod L) :
    (∑ i : ZMod L, ZMod.stdAddChar (t*i)) = if t=0 then (L:ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L h)

theorem sum_torusWave (p : DiscreteTorus L) :
    (∑ x : DiscreteTorus L, torusWave p x) = if p=0 then (L:ℂ)^2 else 0 := by
  classical
  simp only [torusWave, Fintype.sum_prod_type, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul_sum, sum_stdAddChar_mul, sum_stdAddChar_mul]
  by_cases h1 : p.1=0 <;> by_cases h2 : p.2=0 <;>
    simp [h1, h2, Prod.ext_iff, pow_two]

theorem torusWave_orthogonal (p q : DiscreteTorus L) :
    (∑ x : DiscreteTorus L, torusWave p x*conj (torusWave q x)) =
      if p=q then ((L:ℝ)^2 : ℂ) else 0 := by
  simp only [torusWave_mul_conj, sum_torusWave, sub_eq_zero,
    Complex.ofReal_natCast]

theorem torusWave_orthogonal_subfamily {P : Type uP} [DecidableEq P]
    (p : P → DiscreteTorus L) (hp : Function.Injective p) (i j : P) :
    (∑ x : DiscreteTorus L, torusWave (p i) x*conj (torusWave (p j) x)) =
      if i=j then ((L:ℝ)^2 : ℂ) else 0 := by
  simp only [torusWave_orthogonal, hp.eq_iff]

theorem torusWave_intCast (p x : ℤ × ℤ) :
    torusWave (L := L) ((p.1:ZMod L),(p.2:ZMod L)) ((x.1:ZMod L),(x.2:ZMod L)) =
      Complex.exp (Complex.I * ((2*Real.pi*((p.1:ℝ)*(x.1:ℝ)+(p.2:ℝ)*(x.2:ℝ))/(L:ℝ)):ℂ)) := by
  unfold torusWave
  simp only [← Int.cast_mul, ← Int.cast_add]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem norm_stdAddChar_intCast_sub_one (p : ℤ) :
    ‖ZMod.stdAddChar (p : ZMod L)-1‖ ≤ (2*Real.pi/(L:ℝ))*|(p:ℝ)| := by
  rw [ZMod.stdAddChar_coe]
  have he : (2*Real.pi*Complex.I*(p:ℂ)/(L:ℂ)) =
      Complex.I*((2*Real.pi/(L:ℝ)*(p:ℝ):ℝ):ℂ) := by push_cast; ring
  rw [he]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi/(L:ℝ)*(p:ℝ))).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg]
  positivity

theorem torus_mode_difference (φ : DiscreteTorus L → ℂ) (p x h : DiscreteTorus L) :
    φ (x+h)*torusWave p (x+h)-φ x*torusWave p x =
      (φ (x+h)-φ x)*torusWave p x +
        φ (x+h)*torusWave p x*(torusWave p h-1) := by
  rw [torusWave_add]
  ring

end ClassicalON

end

end OAI
