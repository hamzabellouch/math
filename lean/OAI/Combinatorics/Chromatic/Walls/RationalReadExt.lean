import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalTorusFaithful

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
lemma readFiber_ext {f g : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)}
    (h : ∀m,readFiber v Ω k p hp m f=readFiber v Ω k p hp m g) : f=g := by
  apply Finsupp.ext
  intro l
  apply expandZero_injective
  apply HahnSeries.ext
  funext n
  have H:=h (n • p+(l:M))
  change (expandZero (f (off k p hp (n • p+(l:M))))).coeff (k (n • p+(l:M)))*
    (↑(v^(k (n • p+(l:M))*complementAlpha k p Ω (off k p hp (n • p+(l:M))))):K)=
    (expandZero (g (off k p hp (n • p+(l:M))))).coeff (k (n • p+(l:M)))*
    (↑(v^(k (n • p+(l:M))*complementAlpha k p Ω (off k p hp (n • p+(l:M))))):K) at H
  have hl : k (l:M)=0:=l.property
  simp only [map_add,map_zsmul,off_p,smul_zero,off_complement,zero_add,hp,
    smul_eq_mul,mul_one,hl,add_zero] at H
  exact mul_right_cancel₀ (Units.ne_zero _) H
lemma completed_readFiber_ext
    {f g : PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω))}
    (h : ∀d m,readFiber v Ω k p hp m (PowerSeries.coeff d f)=
      readFiber v Ω k p hp m (PowerSeries.coeff d g)) : f=g := by
  apply PowerSeries.ext
  intro d
  exact readFiber_ext v Ω k p hp (h d)
end
end ElementaryPositivity.RationalFiber

end

end OAI
