import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegrade
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalLaurentScalars
import OAI.Combinatorics.Chromatic.Walls.RationalReadExt

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus HahnSeries
noncomputable section
variable {K M : Type*} [Field K] [AddCommGroup M]
variable (v : Kˣ) (Ω : M →+ M →+ ℤ) (hΩ : ∀m,Ω m m=0)
variable (k : M →+ ℤ) (p : M) (hp : k p=1)
local instance rationalLaurentFaithfulRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rationalLaurentFaithfulNonUnitalSemiring : NonUnitalSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalSemiring
local instance rationalLaurentFaithfulNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (Torus v Ω) :=
  (Torus.instRing v Ω).toNonUnitalNonAssocSemiring
lemma expandFiber_monomial_coeff (l : k.ker) (a : RatFunc K) (n : ℤ) :
    (expandFiber v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=
      Torus.monomial v Ω (n • p+(l:M)) ((expandZero a).coeff n*(↑(v^(n*Ω p l)):K)) := by
  change (expandFiberAdd v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff n=_
  rw [expandFiberAdd_monomial,HahnSeries.coeff_mul_single_zero]
  change Torus.monomial v Ω (n • p) ((expandZero a).coeff n)*Torus.X v Ω l=_
  simp only [Torus.X,Torus.monomial_mul_monomial,mul_one,map_zsmul,AddMonoidHom.zsmul_apply,
    smul_eq_mul]
lemma expansion_embed_monomial (m : M) (a : K) :
    expandFiber v Ω hΩ k p (embed v Ω hΩ k p hp (Torus.monomial v Ω m a))=
      HahnSeries.single (k m) (Torus.monomial v Ω m a) := by
  rw [embed_monomial]
  apply HahnSeries.ext
  funext n
  rw [expandFiber_monomial_coeff,expand_centeredScalar]
  simp only [HahnSeries.coeff_single]
  by_cases H : n=k m
  · subst n
    rw [ite_eq_left rfl,ite_eq_left rfl,split_sum k p hp]
    congr 1
    change a*(↑(v^(-k m*complementAlpha k p Ω (off k p hp m))):K)*
      (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)=a
    rw [mul_assoc,←Units.val_mul,←zpow_add]
    simp
  · simp [H,Torus.monomial]
lemma expandFiber_read_monomial (m : M) (l : k.ker) (a : RatFunc K) :
    ((expandFiber v Ω hΩ k p (FiberTorus.monomial v _ _ l a)).coeff (k m)) m=
      readFiber v Ω k p hp m (FiberTorus.monomial v _ _ l a) := by
  classical
  rw [expandFiber_monomial_coeff]
  change Finsupp.single (k m • p+(l:M))
      ((expandZero a).coeff (k m)*(↑(v^(k m*Ω p l)):K)) m=
    (expandZero ((Finsupp.single l a) (off k p hp m))).coeff (k m)*
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
lemma expandFiber_read (f : FiberTorus v (complementOmega k Ω) (complementAlpha k p Ω)) (m : M) :
    ((expandFiber v Ω hΩ k p f).coeff (k m)) m=readFiber v Ω k p hp m f := by
  induction f using Finsupp.induction_linear with
  | zero=>simp
  | add f g hf hg=>simp only [_root_.map_add,HahnSeries.coeff_add,Finsupp.add_apply,hf,hg]
  | single l a=>exact expandFiber_read_monomial v Ω hΩ k p hp m l a
include hp in
lemma expandFiber_injective : Function.Injective (expandFiber v Ω hΩ k p) := by
  intro f g h
  apply readFiber_ext v Ω k p hp
  intro m
  rw [←expandFiber_read v Ω hΩ k p hp f m,←expandFiber_read v Ω hΩ k p hp g m,h]
include hp in
lemma completed_expandFiber_injective :
    Function.Injective (PowerSeries.map (expandFiber v Ω hΩ k p)) := by
  intro f g h
  apply PowerSeries.ext
  intro d
  apply expandFiber_injective v Ω hΩ k p hp
  have H:=congrArg (PowerSeries.coeff d) h
  simpa only [PowerSeries.coeff_map] using H
end
end ElementaryPositivity.RationalFiber

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ : M →+ ℤ)
local instance biSupportedRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance biSupportedAddCommMonoid : AddCommMonoid (Torus v Ω) :=
  (Torus.instRing v Ω).toAddCommMonoid
local instance biSupportedAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

def BiSupported (f : PowerSeries (Torus v Ω)) : Prop :=
  ∀n m,coeff n f m≠0 → 0≤δ m ∧ 0≤κ m ∧ (n:ℤ)=δ m+κ m
lemma BiSupported.zero : BiSupported v Ω δ κ 0 := by intro n m h; simp at h
lemma BiSupported.one : BiSupported v Ω δ κ 1 := by
  intro n m hm
  have hn : n=0:=by by_contra hn; simp [coeff_one,hn] at hm
  subst n
  have hm0 : m=0:=by
    by_contra hm0
    apply hm
    rw [coeff_one,ite_eq_left rfl]
    exact Finsupp.single_eq_of_ne hm0
  subst m
  simp
lemma BiSupported.add {f g : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f)
    (hg : BiSupported v Ω δ κ g) : BiSupported v Ω δ κ (f+g) := by
  intro n m hm
  have H : coeff n f m≠0 ∨ coeff n g m≠0:=by
    by_contra hh
    push Not at hh
    simp [hh.1,hh.2] at hm
  exact H.elim (hf n m) (hg n m)
lemma BiSupported.mul {f g : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f)
    (hg : BiSupported v Ω δ κ g) : BiSupported v Ω δ κ (f*g) := by
  intro j r hr
  obtain ⟨a,b,m,n,hab,hm,hn,rfl⟩:=series_product_nonzero v Ω f g j r hr
  obtain ⟨hdm,hkm,hem⟩:=hf a m hm
  obtain ⟨hdn,hkn,hen⟩:=hg b n hn
  simp only [map_add]
  exact ⟨add_nonneg hdm hdn,add_nonneg hkm hkn,by rw [←hab,Nat.cast_add,hem,hen]; ring⟩
lemma BiSupported.bi_vanish {f : PowerSeries (Torus v Ω)} (hf : BiSupported v Ω δ κ f)
    (d e n : ℕ) (hne : n≠d+e) : coeff e (coeff d (biHomogenize v Ω δ κ (coeff n f)))=0 := by
  ext m
  rw [biHomogenize_coeff]
  split_ifs with hh
  · by_contra hz
    obtain ⟨hd,hk,he⟩:=hf n m hz
    have hD : δ m=(d:ℤ):=by rw [hh.1,Int.toNat_of_nonneg hd]
    have hK : κ m=(e:ℤ):=by rw [hh.2,Int.toNat_of_nonneg hk]
    apply hne
    omega
  · rfl
lemma BiSupported.bi_product_vanish {f g : PowerSeries (Torus v Ω)}
    (hf : BiSupported v Ω δ κ f) (hg : BiSupported v Ω δ κ g)
    (d e a b : ℕ) (ha : d+e<a ∨ d+e<b) :
    coeff e (coeff d (biHomogenize v Ω δ κ (coeff a f)*
      biHomogenize v Ω δ κ (coeff b g)))=0 := by
  rw [coeff_mul,map_sum]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro kl hkl
  have H1:=Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have H2:=Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  rcases ha with ha|ha
  · rw [hf.bi_vanish v Ω δ κ ij.1 kl.1 a (by omega),Torus.zero_mul]
  · rw [hg.bi_vanish v Ω δ κ ij.2 kl.2 b (by omega),Torus.mul_zero]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
