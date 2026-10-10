import Mathlib
import OAI.AlgebraicGeometry.Seshadri.LocalAlgebra.LocalCurvePrincipal

namespace OAI


                                          
section

namespace MaximalSeshadri.LocalCurve
noncomputable section
open IsLocalRing

theorem prime_principal_of_binary_maximal_of_not_mem {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (a b : R) (hm : maximalIdeal R = Ideal.span {a,b})
    (p : Ideal R) [hp : p.IsPrime] (ha : a ∉ p) : p.IsPrincipal := by
  classical
  let J : Ideal R := Ideal.span {a}
  have hJm : J ≤ maximalIdeal R := by
    rw [hm]
    exact Ideal.span_mono (by simp)
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJm
  let : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  let q := Ideal.Quotient.mk J
  let : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hmQ : maximalIdeal (R ⧸ J) = Ideal.span {q b} := by
    rw [← map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective,hm,Ideal.map_span]
    have hqa : q a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simp only [Set.image_insert_eq,Set.image_singleton,hqa,Ideal.span_insert_zero]
  let : IsPrincipalIdealRing (R ⧸ J) := principal_of_principal_maximal ⟨q b,hmQ⟩
  obtain ⟨c₀,hc₀⟩ := (inferInstance : (p.map q).IsPrincipal)
  change p.map q = Ideal.span {c₀} at hc₀
  have hc₀mem : c₀ ∈ p.map q := by rw [hc₀]; exact Ideal.subset_span (by simp)
  obtain ⟨c,hcp,hc⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hc₀mem
  have hp_le : p ≤ Ideal.span {c} ⊔ J • p := by
    intro z hz
    have hzq : q z ∈ Ideal.span {c₀} := by
      rw [← hc₀]
      exact Ideal.mem_map_of_mem q hz
    obtain ⟨w₀,hw₀⟩ := Ideal.mem_span_singleton.mp hzq
    obtain ⟨w,hw⟩ := Ideal.Quotient.mk_surjective w₀
    have hdiff : z-c*w ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change q (z-c*w) = 0
      rw [map_sub,map_mul,hc,hw,hw₀,sub_self]
    obtain ⟨t,ht⟩ := Ideal.mem_span_singleton.mp hdiff
    have hat : a*t ∈ p := ht ▸ p.sub_mem hz (p.mul_mem_right w hcp)
    have htp : t ∈ p := (hp.mem_or_mem hat).resolve_left ha
    have hleft : c*w ∈ Ideal.span {c} := Ideal.mem_span_singleton.mpr ⟨w,rfl⟩
    have hright : a*t ∈ J • p := by
      exact Submodule.smul_mem_smul (Ideal.subset_span (by simp)) htp
    have H := Submodule.add_mem_sup hleft hright
    have he : c*w+a*t = z := by linear_combination -ht
    exact he ▸ H
  have hple : p ≤ Ideal.span {c} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian p) (by rw [jacobson_eq_maximalIdeal _ bot_ne_top]; exact hJm) hp_le
  exact ⟨c,le_antisymm hple (Ideal.span_le.mpr (by simpa using hcp))⟩

theorem prime_principal_of_binary_maximal {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R]
    (a b : R) (hm : maximalIdeal R = Ideal.span {a,b})
    (p : Ideal R) [hp : p.IsPrime] (hne : p ≠ maximalIdeal R) : p.IsPrincipal := by
  by_cases ha : a ∈ p
  · have hb : b ∉ p := by
      intro hb
      apply hne
      apply le_antisymm (le_maximalIdeal hp.ne_top)
      rw [hm,Ideal.span_le,Set.insert_subset_iff,Set.singleton_subset_iff]
      exact ⟨ha,hb⟩
    exact prime_principal_of_binary_maximal_of_not_mem b a
      (hm.trans Ideal.span_pair_comm) p hb
  · exact prime_principal_of_binary_maximal_of_not_mem a b hm p ha
end
end MaximalSeshadri.LocalCurve

end


end OAI
