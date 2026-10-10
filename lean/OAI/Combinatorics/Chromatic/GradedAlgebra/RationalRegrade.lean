import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalTorusFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegradeFaithful

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus PowerSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
variable (δ : M →+ ℤ) (B : ℕ)
def rationalRegrade (f : PowerSeries (Torus v Ω)) :
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :=
  PowerSeries.map (embed v Ω hΩ k p hp) (regrade v Ω δ B f)
def rationalRegradeHom : boundedRegradeSubring v Ω δ B →+*
    PowerSeries (FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) :=
  (PowerSeries.map (embed v Ω hΩ k p hp)).comp (regradeHom v Ω δ B)
lemma rationalRegrade_mul {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g) :
    rationalRegrade v Ω hΩ k p hp δ B (f*g)=
      rationalRegrade v Ω hΩ k p hp δ B f*rationalRegrade v Ω hΩ k p hp δ B g := by
  unfold rationalRegrade
  rw [regrade_mul v Ω δ B hf hg,_root_.map_mul]
lemma rationalRegrade_one : rationalRegrade v Ω hΩ k p hp δ B 1=1 := by
  unfold rationalRegrade
  rw [regrade_one,_root_.map_one]
lemma rationalRegrade_inverse_mul {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hc : constantCoeff f=1) :
    rationalRegrade v Ω hΩ k p hp δ B (PowerSeries.invOfUnit f 1)*
      rationalRegrade v Ω hΩ k p hp δ B f=1 := by
  unfold rationalRegrade
  rw [←_root_.map_mul,regrade_inverse_mul v Ω δ B hf hc,_root_.map_one]
lemma rationalRegrade_mul_inverse {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hc : constantCoeff f=1) :
    rationalRegrade v Ω hΩ k p hp δ B f*
      rationalRegrade v Ω hΩ k p hp δ B (PowerSeries.invOfUnit f 1)=1 := by
  unfold rationalRegrade
  rw [←_root_.map_mul,regrade_mul_inverse v Ω δ B hf hc,_root_.map_one]
lemma rationalRegrade_read (τ : M →+ ℤ) {f : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hτ : FullHomogeneous v Ω τ f)
    (n : ℕ) (m : M) (hm : τ m=(n:ℤ)) :
    readFiber v Ω k p hp m (coeff (δ m).toNat
      (rationalRegrade v Ω hΩ k p hp δ B f))=coeff n f m := by
  rw [rationalRegrade,coeff_map]
  change readFiber v Ω k p hp m (embedAdd v Ω k p hp _)=_
  rw [readFiber_embedAdd,regrade_read v Ω δ B τ hf hτ n m hm]
lemma rationalRegrade_injective (τ : M →+ ℤ) {f g : PowerSeries (Torus v Ω)}
    (hf : RegradeBound v Ω δ B f) (hg : RegradeBound v Ω δ B g)
    (hτf : FullHomogeneous v Ω τ f) (hτg : FullHomogeneous v Ω τ g)
    (he : rationalRegrade v Ω hΩ k p hp δ B f=
      rationalRegrade v Ω hΩ k p hp δ B g) : f=g := by
  apply regrade_injective_homogeneous v Ω δ B τ hf hg hτf hτg
  apply PowerSeries.ext
  intro d
  apply embed_injective v Ω hΩ k p hp
  have H:=congrArg (coeff d) he
  simpa only [rationalRegrade,coeff_map] using H
end
end ElementaryPositivity.RationalFiber

end

end OAI
