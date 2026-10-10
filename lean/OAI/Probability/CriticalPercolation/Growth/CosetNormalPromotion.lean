import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetFiniteIndex
import OAI.Probability.CriticalPercolation.Growth.CosetTransfer
import OAI.Probability.CriticalPercolation.Criticality.BoundedNormalJoins

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma conjugate_eq_of_integer_value (f : A →* Multiplicative ℤ)
    (a : A) (ha : f a=Multiplicative.ofAdd 1) (N : Subgroup A)
    (hN : f.ker≤(Subgroup.normalizer (N:Set A))) (g : A) :
    N.map (MulAut.conj g).toMonoidHom=N.map (MulAut.conj (a^Multiplicative.toAdd (f g))).toMonoidHom := by
  let z := Multiplicative.toAdd (f g)
  have hl : (a^z)⁻¹*g∈f.ker := by
    change f ((a^z)⁻¹*g)=1
    rw [map_mul,map_inv,map_zpow,ha]
    apply Multiplicative.toAdd.injective
    simp [z]
  have he : N.map (MulAut.conj ((a^z)⁻¹*g)).toMonoidHom=N :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN hl)
  have hg : g=a^z*((a^z)⁻¹*g) := by simp
  conv_lhs => rw [hg]
  rw [←conjugate_map_map,he]

lemma finite_bounded_conjugate_family (K : Subgroup A) (S : Set A)
    (hf : ∀ n, (ball K S n).Finite) (f : A →* Multiplicative ℤ) (hK : K≤f.ker)
    (a : A) (ha : f a=Multiplicative.ofAdd 1) (N : Subgroup A)
    (hN : f.ker≤(Subgroup.normalizer (N:Set A))) (n : ℕ) :
    ((fun g => N.map (MulAut.conj g).toMonoidHom) '' S^n).Finite := by
  have hKi : (f '' (K:Set A)).Finite := by
    apply (Set.finite_singleton (1:Multiplicative ℤ)).subset
    rintro _ ⟨k,hk,rfl⟩
    exact MonoidHom.mem_ker.mp (hK hk)
  have hfi := finite_image_of_finite_coset_image K f hKi (S^n) (hf n)
  apply (hfi.image (fun z => N.map (MulAut.conj (a^Multiplicative.toAdd z)).toMonoidHom)).subset
  rintro _ ⟨g,hg,rfl⟩
  exact ⟨f g,⟨g,hg,rfl⟩,(conjugate_eq_of_integer_value f a ha N hN g).symm⟩

lemma HasDegree.promote_integer_normal {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤) (hg : HasDegree K S d)
    (f : A →* Multiplicative ℤ) (hf : Surjective f) (hK : K≤f.ker)
    (N : Subgroup A) (hNL : N≤f.ker) (hLN : f.ker≤(Subgroup.normalizer (N:Set A)))
    (hNb : Bounded S (N:Set A)) (hNi : N.relIndex K≠0) :
    ∃ M : Subgroup A, M.Normal ∧ Bounded S (M:Set A) ∧ M.relIndex K≠0 := by
  let J := K⊓N
  have hJi : J.relIndex K≠0 := by simpa only [J,Subgroup.inf_relIndex_left] using hNi
  let : Finite (K ⧸ J.subgroupOf K) := Nat.finite_of_card_ne_zero hJi
  have hgJ := hg.smaller_stabilizer (show J≤K from inf_le_left)
  obtain ⟨L,hL⟩ := hNb
  obtain ⟨n,hn⟩ := exists_conjugateStage_stationary S (N:Set A) h1 hi J
    (by simpa only [Subgroup.closure_eq] using (show J≤N from inf_le_right)) d hgJ L hL
  let M := Subgroup.normalClosure (N:Set A)
  have hM : M=conjugateStage S (N:Set A) n := normalClosure_eq_conjugateStage_of_stationary S (N:Set A) h1 hi hgen n hn
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  refine ⟨M,inferInstance,?_,?_⟩
  · rw [hM,conjugateStage_eq_join]
    apply finite_normalized_join_bounded S h1 f.ker _
      (finite_bounded_conjugate_family K S hg.1 f hK a ha N hLN n)
    · rintro Q ⟨g,hg,rfl⟩
      have hh := Subgroup.map_mono hNL (f:=(MulAut.conj g).toMonoidHom)
      have he : f.ker.map (MulAut.conj g).toMonoidHom=f.ker := Subgroup.Normal.map_conj_eq f.ker g
      rwa [he] at hh
    · rintro Q ⟨g,hg,rfl⟩
      exact normalized_conjugate f.ker N hLN g
    · rintro Q ⟨g,hg,rfl⟩
      exact (show Bounded S (N:Set A) from ⟨L,hL⟩).conj h1 hi hgen g
  · exact fun he => hNi (Subgroup.relIndex_eq_zero_of_le_left (fun x hx => Subgroup.subset_normalClosure hx) he)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
