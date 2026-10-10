import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetTransfer

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma integer_kernel_coset_packing (K : Subgroup A) (S : Set A) (h1 : (1:A)∈S)
    (f : A →* Multiplicative ℤ) (hKf : K≤f.ker) (a : A) (ha : f a=Multiplicative.ofAdd 1)
    (T : Set f.ker) (L M : ℕ) (hT : f.ker.subtype '' T⊆S^L) (haS : a∈S^M)
    (n : ℕ) (hfin : (ball K S ((L+M+1)*n)).Finite) :
    n*(ball (K.subgroupOf f.ker) T n).ncard≤(ball K S ((L+M+1)*n)).ncard := by
  let Q := ball (K.subgroupOf f.ker) T n
  have hh : ∀ q∈Q, ∃ b : f.ker, b∈T^n ∧ (QuotientGroup.mk b : f.ker ⧸ K.subgroupOf f.ker)=q := fun q hq => hq
  choose b hb he using hh
  let phi : Fin n × Q → A ⧸ K := fun p => QuotientGroup.mk (a^p.1.val*(b p.2.val p.2.property).val)
  have hin (p : Fin n × Q) : phi p∈ball K S ((L+M+1)*n) := by
    refine ⟨a^p.1.val*(b p.2.val p.2.property).val,?_,rfl⟩
    have ha' : a^p.1.val∈S^(M*p.1.val) := by
      rw [pow_mul]
      exact Set.pow_mem_pow haS
    have hb' : (b p.2.val p.2.property).val∈S^(L*n) := by
      rw [pow_mul]
      apply Set.pow_subset_pow_left hT
      rw [←Set.image_pow]
      exact ⟨b p.2.val p.2.property,hb p.2.val p.2.property,rfl⟩
    apply Set.pow_subset_pow_right h1 (show M*p.1.val+L*n≤(L+M+1)*n by nlinarith [p.1.isLt])
    rw [pow_add]
    exact Set.mul_mem_mul ha' hb'
  have hphi : Injective phi := by
    rintro ⟨i,q⟩ ⟨j,r⟩ hij
    have hm := QuotientGroup.eq.mp hij
    have hf' := MonoidHom.mem_ker.mp (hKf hm)
    simp only [map_mul,map_inv,map_pow,ha,MonoidHom.mem_ker.mp (b q.val q.property).property,
      MonoidHom.mem_ker.mp (b r.val r.property).property,mul_one] at hf'
    have hi : i=j := by
      apply Fin.ext
      have hz := congrArg Multiplicative.toAdd hf'
      simp at hz
      omega
    subst j
    apply congrArg (fun s : Q => (i,s))
    apply Subtype.ext
    rw [←he q.val q.property,←he r.val r.property]
    apply QuotientGroup.eq.mpr
    change ((b q.val q.property).val)⁻¹*(b r.val r.property).val∈K
    simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hm
  let e : Fin n × Q ↪ ball K S ((L+M+1)*n) := ⟨fun p => ⟨phi p,hin p⟩,fun p q h => hphi (congrArg Subtype.val h)⟩
  let : Finite (ball K S ((L+M+1)*n)) := hfin.to_subtype
  have hc := Nat.card_le_card_of_injective e e.injective
  simpa only [Nat.card_prod,Nat.card_fin,Nat.card_coe_set_eq,Q] using hc

lemma HasDegree.integer_kernel_descent {K : Subgroup A} {S : Set A} {d : ℕ}
    (h1 : (1:A)∈S) (hi : S⁻¹=S) (hgen : Subgroup.closure S=⊤)
    (hg : HasDegree K S (d+1)) (f : A →* Multiplicative ℤ) (hf : Surjective f) (hKf : K≤f.ker)
    (T : Set f.ker) (hT : Bounded S (f.ker.subtype '' T)) :
    HasDegree (K.subgroupOf f.ker) T d := by
  have hTf := (hg.subgroup_bounded h1 f.ker T hT).1
  obtain ⟨L,hL⟩ := hT
  obtain ⟨a,ha⟩ := hf (Multiplicative.ofAdd 1)
  obtain ⟨M,hM⟩ := bounded_singleton S h1 hi hgen a
  have haS := hM (Set.mem_singleton a)
  obtain ⟨C,hC⟩ := hg.2
  let D := L+M+1
  have hD : 0<D := by dsimp [D]; omega
  refine ⟨hTf,C*(2*D)^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC (D*max R 1)
  let n := r/D
  have hnr : D*n≤r := by simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r D
  have hn : max R 1≤n := (Nat.le_div_iff_mul_le hD).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1≤n := (le_max_right R 1).trans hn
  have hrn : r≤(2*D)*n := by
    have hlt := Nat.lt_mul_div_succ r hD
    change r<D*(n+1) at hlt
    nlinarith
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : n*(ball (K.subgroupOf f.ker) T n).ncard≤n*(C*(2*D)^(d+1)*n^d) := by
    calc
      _ ≤ (ball K S (D*n)).ncard := integer_kernel_coset_packing K S h1 f hKf a ha T L M hL haS n (hg.1 _)
      _ ≤ (ball K S r).ncard := Set.ncard_le_ncard (ball_mono K S h1 hnr) (hg.1 _)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*D)*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = _ := by rw [mul_pow,pow_succ n]; ring
  exact Nat.le_of_mul_le_mul_left hb (by omega : 0<n)

end CriticalPercolation.RelativeGrowth
end
end

end OAI
