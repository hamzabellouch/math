import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.RationalTorusFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.RationalCenteredAction

namespace OAI

section
namespace ElementaryPositivity.RationalFiber
open QuantumTorus WallUnits PowerSeries
noncomputable section
variable {K M:Type*} [Field K] [AddCommGroup M]
variable (v:Kˣ) (Ω:M →+ M →+ ℤ) (hΩ:∀m,Ω m m=0)
variable (k:M →+ ℤ) (p:M) (hp:k p=1)

lemma ofPowerSeries_negative (f:PowerSeries K) (j:ℤ) (hj:j<0) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff j=0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨n,_,hn⟩
  have he : (n:ℤ)=j := hn
  omega

include hΩ in
lemma read_pure_monomial_support
    (hq:∀n:ℕ,1-(↑(v^(-2:ℤ)):K)^(n+1)≠0) (b m:M)
    (hm:readFiber v Ω k p hp m
      (pureAction v (complementOmega k Ω) (complementAlpha k p Ω)
        (embed v Ω hΩ k p hp (Torus.X v Ω b)))≠0) :
    ∃j:ℕ,m=b+j • p := by
  classical
  rw [Torus.X,embed_monomial,pureAction_monomial,map_one,one_mul,
    complement_pairing Ω hΩ k p hp b] at hm
  change (expandZero ((Finsupp.single (off k p hp b)
    (centeredScalar v (k b) (Ω p b)*(pureRatio v (Ω p b):RatFunc K)))
      (off k p hp m))).coeff (k m)*
        (↑(v^(k m*complementAlpha k p Ω (off k p hp m))):K)≠0 at hm
  have ho:off k p hp b=off k p hp m:=by
    by_contra hh
    simp only [Finsupp.single_apply,ite_eq_right hh,map_zero,HahnSeries.coeff_zero,zero_mul,ne_eq,not_true_eq_false] at hm
  rw [Finsupp.single_apply,ite_eq_left ho,map_mul] at hm
  rw [show expandZero (centeredScalar v (k b) (Ω p b))=
      HahnSeries.single (k b) (↑(v^(-k b*Ω p b)):K) by
      simpa using expand_centeredScalar v (k b) (Ω p b) (1:K),
    expandedPure_ratio v hq,HahnSeries.coeff_single_mul] at hm
  have hk:0≤k m-k b:=by
    by_contra hh
    rw [ofPowerSeries_negative _ _ (lt_of_not_ge hh),mul_zero,zero_mul] at hm
    exact hm rfl
  refine ⟨(k m-k b).toNat,split_injective k p hp ?_ ?_⟩
  · simp only [map_add,map_nsmul,nsmul_eq_mul,hp,mul_one,Int.toNat_of_nonneg hk]
    omega
  · simp only [map_add,map_nsmul,off_p,smul_zero,add_zero]
    exact ho.symm
end
end ElementaryPositivity.RationalFiber

end

end OAI
