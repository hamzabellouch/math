import OAI.Analysis.BoundedHochschild.PositiveKernelMatrices

namespace OAI

/-! The Hilbert-space construction for a positive scalar kernel, specialized
later to the coefficient kernel of a completely positive map. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

/-- The finite coefficient pairing of a scalar kernel. -/
def kernelForm (K : Matrix I I ℂ) (x y : I →₀ ℂ) : ℂ :=
  x.sum fun i a => y.sum fun j b => star a * K i j * b

lemma kernelForm_conj_symm (K : Matrix I I ℂ) (hK : K.IsHermitian) (x y : I →₀ ℂ) :
    star (kernelForm K y x) = kernelForm K x y := by
  classical
  simp only [kernelForm, Finsupp.sum, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hK.apply i j]
  ring

lemma kernelForm_add_left (K : Matrix I I ℂ) (x y z : I →₀ ℂ) :
    kernelForm K (x + y) z = kernelForm K x z + kernelForm K y z := by
  classical
  unfold kernelForm
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_smul_left (K : Matrix I I ℂ) (x y : I →₀ ℂ) (r : ℂ) :
    kernelForm K (r • x) y = star r * kernelForm K x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_smul_index (by intro i; simp)]
  simp only [star_mul, mul_assoc, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma kernelForm_nonneg (K : Matrix I I ℂ) (hK : K.PosSemidef) (x : I →₀ ℂ) :
    0 ≤ kernelForm K x x := hK.2 x

/-- A type copy keeps the kernel seminorm separate from any norm on the free
coefficient space. Its completion automatically removes the null vectors. -/
def PositiveKernelPreSpace (K : Matrix I I ℂ) (_hK : K.PosSemidef) : Type _ := I →₀ ℂ

instance kernelPreAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    AddCommGroup (PositiveKernelPreSpace K hK) := inferInstanceAs (AddCommGroup (I →₀ ℂ))

instance kernelPreModule (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    Module ℂ (PositiveKernelPreSpace K hK) := inferInstanceAs (Module ℂ (I →₀ ℂ))

abbrev positiveKernelCore (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (PositiveKernelPreSpace K hK) where
  inner := kernelForm K
  conj_inner_symm x y := kernelForm_conj_symm K hK.1 x y
  re_inner_nonneg x := (kernelForm_nonneg K hK x).1
  add_left := kernelForm_add_left K
  smul_left := kernelForm_smul_left K

instance kernelPreSeminormedAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    SeminormedAddCommGroup (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := positiveKernelCore K hK)

instance kernelPreInnerProductSpace (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    InnerProductSpace ℂ (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.ofCore (positiveKernelCore K hK)

/-- The separated Hilbert completion of the finite kernel vectors. -/
abbrev PositiveKernelHilbert (K : Matrix I I ℂ) (hK : K.PosSemidef) :=
  UniformSpace.Completion (PositiveKernelPreSpace K hK)

end BoundedHochschild.KadisonRingrose

end

end OAI
