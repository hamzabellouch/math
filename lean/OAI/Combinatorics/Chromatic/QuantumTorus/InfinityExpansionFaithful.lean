import Mathlib
import OAI.Combinatorics.Chromatic.Walls.FiniteFiberInfinity
import OAI.Combinatorics.Chromatic.Walls.CompletedInfinityCut

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : NonUnitalSemiring (Torus v Ω) := (Torus.instRing v Ω).toNonUnitalSemiring
local instance : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring

lemma expandFiberInfinity_monomial_coeff (l : k.ker) (a : RatFunc K) (n : ℤ) :
    (expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=
      Torus.monomial v Ω (n • (-p)+(l:M)) ((expandInfinity a).coeff n*(↑(v^(n*Ω (-p) l)):K)) := by
  change (expandFiber v Ω hΩ k (-p) (fiberReciprocalAdd v (complementOmega k Ω)
    (complementAlpha k p Ω) (complementAlpha k (-p) Ω) (FiberTorus.monomial v _ _ l a))).coeff n=_
  rw [fiberReciprocalAdd_monomial,expandFiber_monomial_coeff]
  rfl

lemma expandFiberInfinity_read_monomial (m : M) (l : k.ker) (a : RatFunc K) :
    ((expandFiberInfinity v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff (-k m)) m=
      readFiberInfinity v Ω k p hp m (FiberTorus.monomial v _ _ l a) := by
  classical
  rw [expandFiberInfinity_monomial_coeff]
  simp only [neg_smul,smul_neg,neg_neg,map_neg,AddMonoidHom.neg_apply,neg_mul_neg]
  change Finsupp.single (k m • p+(l:M))
      ((expandInfinity a).coeff (-k m)*(↑(v^(k m*Ω p l)):K)) m=
    (expandInfinity ((Finsupp.single l a) (off k p hp m))).coeff (-k m)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)
  by_cases H : l=off k p hp m
  · subst l
    rw [split_sum k p hp,Finsupp.single_eq_same,Finsupp.single_eq_same]
    rfl
  · have hm : k m • p+(l:M)≠m:=by
      intro hh
      have HO:=congrArg (off k p hp) hh
      simp only [map_add,map_zsmul,off_p,smul_zero,off_complement,zero_add] at HO
      exact H HO
    rw [Finsupp.single_eq_of_ne (Ne.symm hm),Finsupp.single_eq_of_ne (Ne.symm H),map_zero,
      HahnSeries.coeff_zero,zero_mul]
lemma expandFiberInfinity_read (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) (m : M) :
    ((expandFiberInfinity v Ω hΩ k p f).coeff (-k m)) m=readFiberInfinity v Ω k p hp m f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [_root_.map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg]
  | single l a=>exact expandFiberInfinity_read_monomial v Ω hΩ k p hp m l a

lemma readFiberInfinity_ext {f g : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)}
    (h : ∀m,readFiberInfinity v Ω k p hp m f=readFiberInfinity v Ω k p hp m g) : f=g := by
  apply Finsupp.ext
  intro l
  apply expandInfinity_injective
  apply HahnSeries.ext
  funext n
  have H:=h ((-n) • p+(l:M))
  change (expandInfinity (f (off k p hp ((-n) • p+(l:M))))).coeff (-k ((-n) • p+(l:M)))*
    (↑(v^(k ((-n) • p+(l:M))*complementAlpha k p Ω (off k p hp ((-n) • p+(l:M))))):K)=
    (expandInfinity (g (off k p hp ((-n) • p+(l:M))))).coeff (-k ((-n) • p+(l:M)))*
    (↑(v^(k ((-n) • p+(l:M))*complementAlpha k p Ω (off k p hp ((-n) • p+(l:M))))):K) at H
  have hl : k (l:M)=0:=l.property
  simp only [map_add,map_zsmul,off_p,smul_zero,off_complement,zero_add,hp,
    smul_eq_mul,mul_one,hl,add_zero,neg_neg] at H
  exact mul_right_cancel₀ (Units.ne_zero _) H

include hp in
lemma expandFiberInfinity_injective : Function.Injective (expandFiberInfinity v Ω hΩ k p) := by
  intro f g h
  apply readFiberInfinity_ext v Ω k p hp
  intro m
  rw [←expandFiberInfinity_read v Ω hΩ k p hp f m,←expandFiberInfinity_read v Ω hΩ k p hp g m,h]
include hp in
lemma completed_expandFiberInfinity_injective :
    Function.Injective (PowerSeries.map (expandFiberInfinity v Ω hΩ k p)) := by
  intro f g h
  apply PowerSeries.ext
  intro d
  apply expandFiberInfinity_injective v Ω hΩ k p hp
  have H:=congrArg (PowerSeries.coeff d) h
  simpa only [PowerSeries.coeff_map] using H
end
end ElementaryPositivity.RationalFiber

end

end OAI
