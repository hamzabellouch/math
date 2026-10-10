import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetPresentation
import OAI.Probability.CriticalPercolation.Harmonic.WeakGromovHarmonic
import OAI.Probability.CriticalPercolation.Growth.CosetImageGrowth
import OAI.Probability.CriticalPercolation.Harmonic.GraphHarmonicLinear

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A B : Type*} [Group A] [Group B]

lemma finite_image_to_integer_ker (K : Subgroup A) (f : A →* Multiplicative ℤ)
    (hf : (f '' (K:Set A)).Finite) : K≤f.ker := by
  let J := K.map f
  let : Finite J := hf.to_subtype
  intro k hk
  let j : J := ⟨f k,Subgroup.mem_map.mpr ⟨k,hk,rfl⟩⟩
  obtain ⟨n,hn,he⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite j)
  have hm : (f k)^n=1 := congrArg Subtype.val he
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hm⟩).eq_one'

lemma indicability_pullback_killing (K : Subgroup A) (f : A →* B) (hf : Surjective f)
    (hK : (f '' (K:Set A)).Finite)
    (hb : ∃ P : Subgroup B, P.FiniteIndex ∧ ∃ q : P →* Multiplicative ℤ, Surjective q) :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ K.subgroupOf H≤q.ker := by
  obtain ⟨P,hPi,q,hq⟩ := hb
  let := hPi
  let H := P.comap f
  let ψ : H →* P := (f.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Surjective ψ := by
    intro p
    obtain ⟨a,ha⟩ := hf p.val
    refine ⟨⟨a,?_⟩,Subtype.ext ha⟩
    change f a∈P
    rw [ha]
    exact p.property
  refine ⟨H,LinearGrowth.finiteIndex_comap_surjective f hf P,q.comp ψ,hq.comp hψ,?_⟩
  apply finite_image_to_integer_ker
  change ((fun h => q (ψ h)) '' (K.subgroupOf H:Set H)).Finite
  rw [←Set.image_image q ψ]
  apply Set.Finite.image
  apply Set.Finite.of_finite_image (f:=P.subtype)
  · apply hK.subset
    rintro _ ⟨p,⟨h,hh,rfl⟩,rfl⟩
    exact ⟨h.val,hh,rfl⟩
  · exact P.subtype_injective.injOn

lemma Presentation.virtually_indicable (P : Presentation A) (d : ℕ)
    (hg : HasDegree P.K P.S d) [Infinite P.X] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ P.K.subgroupOf H≤q.ker := by
  let W := P.geometry (hg.1 1)
  let ρ := (W.harmonicRepresentation 1).comp P.actionHom
  have hWg : W.HasDegree d := P.geometry_hasDegree d hg
  have htrans : ∀ x : P.X, ∃ a : A, P.actionHom a W.root=x := by
    intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨a,by change P.projection (a*1)=P.projection a; rw [mul_one]⟩
  have hInf : (Set.range ρ).Infinite := W.infinite_harmonic_linear_image P.actionHom d hWg htrans
  have hKρ : (ρ '' (P.K:Set A)).Finite := by
    apply (W.finite_stabilizer_harmonic_image d 1 hWg).subset
    rintro _ ⟨k,hk,rfl⟩
    have hstab : P.actionHom k∈W.Stab := by
      change P.projection (k*1)=P.projection 1
      apply QuotientGroup.eq.mpr
      simpa using P.K.inv_mem hk
    exact ⟨⟨P.actionHom k,hstab⟩,rfl⟩
  let f := ρ.rangeRestrict
  have hKf : (f '' (P.K:Set A)).Finite := by
    apply Set.Finite.of_finite_image (f:=ρ.range.subtype)
    · simpa only [Set.image_image] using (show ((fun x => ρ.range.subtype (f x)) '' (P.K:Set A)).Finite from hKρ)
    · exact ρ.range.subtype_injective.injOn
  have hgR := hg.image_polynomial P.one_mem P.inv_eq P.generates f ρ.rangeRestrict_surjective hKf
  let : Infinite ρ.range := hInf.to_subtype
  exact indicability_pullback_killing P.K f ρ.rangeRestrict_surjective hKf hgR.linear_virtually_indicable

lemma virtually_indicable {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hK : Bounded S (K:Set A)) (hg : HasDegree K S d) [Infinite (A ⧸ K)] :
    ∃ H : Subgroup A, H.FiniteIndex ∧ ∃ q : H →* Multiplicative ℤ,
      Surjective q ∧ K.subgroupOf H≤q.ker := by
  obtain ⟨P,hPK,hPb,hSP⟩ := normalized_generators K S h1 hi hgen hK
  have hgP : HasDegree P.K P.S d := hPK.symm ▸ hg.bounded_generators h1 hPb
  let : Infinite P.X := by change Infinite (A ⧸ P.K); rw [hPK]; infer_instance
  exact hPK ▸ P.virtually_indicable d hgP

end CriticalPercolation.RelativeGrowth
end
end

end OAI
