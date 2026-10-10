import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Q
import OAI.Combinatorics.RamseyFive.Entropy.SubsetMixture
import OAI.Combinatorics.RamseyFive.Entropy.BlockSelected

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α : Type*} [Fintype α]
lemma mean_exists_le (p : Law α) (f : α→ℝ) :
    ∃ a,0<p a ∧ f a≤ mean p f := by
  obtain ⟨a,ha,hh⟩:=mean_exists_ge p (fun a=> -f a)
  refine ⟨a,ha,?_⟩
  have he : mean p (fun a=> -f a)= -mean p f := by
    simp only [mean,mul_neg,Finset.sum_neg_distrib]
  rw [he] at hh
  linarith
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.ProjectiveIncidence
open Module SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem reciprocal_support_product (hdim : finrank K V=5)
    (μ : Law (Finset (ℙ K V))) (ν : Law (Finset (ℙ K (Dual K V))))
    (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (hA : ∀ A,0<μ A→a≤(A.card:ℝ)) (hB : ∀ B,0<ν B→b≤(B.card:ℝ))
    (hs : (∑ A,∑ B,μ A*ν B*relationMass Incident (uniformWeight A) (uniformWeight B))≤
      1/(4*(Nat.card K:ℝ))) :
    a*b≤16*(Nat.card K:ℝ)^5 := by
  let p:=adaptiveLaw μ (fun _=>ν)
  let f:=fun z:Finset (ℙ K V)×Finset (ℙ K (Dual K V))=>
    relationMass Incident (uniformWeight z.1) (uniformWeight z.2)
  obtain ⟨⟨A,B⟩,hp,hh⟩:=mean_exists_le p f
  have hμ : 0<μ A := by
    change 0<μ A*ν B at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h=>(μ.nonneg A).not_gt h.1) |>.1
  have hν : 0<ν B := by
    change 0<μ A*ν B at hp
    exact (mul_pos_iff.mp hp).resolve_right (fun h=>(μ.nonneg A).not_gt h.1) |>.2
  have hm : mean p f≤1/(4*(Nat.card K:ℝ)) := by
    dsimp only [p]
    rw [mean_adaptive]
    simpa only [mean,Finset.mul_sum,mul_assoc,f] using hs
  have hAc : 0<(A.card:ℝ):=ha.trans_le (hA A hμ)
  have hBc : 0<(B.card:ℝ):=hb.trans_le (hB B hν)
  have hsparse : (incidences A B:ℝ)≤(A.card:ℝ)*B.card/(4*(Nat.card K:ℝ)) := by
    have ht:=hh.trans hm
    dsimp only [f] at ht
    rw [relationMass_uniform,div_le_iff₀ (mul_pos hAc hBc)] at ht
    simpa only [incidences,div_mul_eq_mul_div,one_mul] using ht
  exact (mul_le_mul (hA A hμ) (hB B hν) hb.le hAc.le).trans
    (sparse_rectangle_size (d:=4) hdim (by decide) A B hsparse)

theorem reciprocal_u_monotone (hdim : finrank K V=5)
    (μ : Law (Finset (ℙ K V))) (ν : Law (Finset (ℙ K (Dual K V))))
    (u v k : ℝ)
    (hA : ∀ A,0<μ A→Real.exp (5*Real.log (Nat.card K)-u-k)/2≤(A.card:ℝ))
    (hB : ∀ B,0<ν B→Real.exp (v-k)/2≤(B.card:ℝ))
    (hs : (∑ A,∑ B,μ A*ν B*relationMass Incident (uniformWeight A) (uniformWeight B))≤
      1/(4*(Nat.card K:ℝ))) : v≤u+2*k+Real.log 64 := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hh:=reciprocal_support_product hdim μ ν _ _ (by positivity) (by positivity) hA hB hs
  have he : Real.exp (5*Real.log (Nat.card K)-u-k)/2*(Real.exp (v-k)/2)=
      (Nat.card K:ℝ)^5*Real.exp (v-u-2*k)/4 := by
    rw [div_mul_div_comm,←Real.exp_add]
    have heck : (5*Real.log (Nat.card K)-u-k)+(v-k)=5*Real.log (Nat.card K)+(v-u-2*k) := by ring
    have hfive : Real.exp (5*Real.log (Nat.card K))=Real.exp (Real.log (Nat.card K))^5 := by
      simpa using Real.exp_nat_mul (Real.log (Nat.card K)) 5
    rw [heck,Real.exp_add,hfive,Real.exp_log hq]
    norm_num
  rw [he] at hh
  have hexp : Real.exp (v-u-2*k)≤64 := by nlinarith [pow_pos hq 5]
  have hhlog := (Real.log_le_log (Real.exp_pos _) hexp)
  rw [Real.log_exp] at hhlog
  linarith
end
end SharpRamseyFive.ProjectiveIncidence

end OAI
