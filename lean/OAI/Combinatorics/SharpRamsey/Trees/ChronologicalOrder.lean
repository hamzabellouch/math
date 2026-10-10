import Mathlib
import OAI.Combinatorics.SharpRamsey.Reciprocal.AuxiliaryCharges

namespace OAI

section
namespace SharpLogRamsey.Selection
open Finset Real
open scoped Classical BigOperators
noncomputable section
variable {A : Type*} [Fintype A]

lemma Law.exists_mass_pos_le_of_mean_le (p : Law A) (f : A → ℝ) (c : ℝ)
    (h : (∑ a, p.mass a * f a) ≤ c) :
    ∃ a, 0 < p.mass a ∧ f a ≤ c := by
  have hp : ∃ a, 0 < p.mass a := by
    by_contra! he
    have hz : ∑ a, p.mass a = 0 := sum_eq_zero (fun a _ => (he a).antisymm (p.nonneg a))
    linarith [p.total]
  by_contra! hh
  obtain ⟨a,ha⟩ := hp
  have hle (b : A) : p.mass b * c ≤ p.mass b * f b := by
    by_cases hb : p.mass b = 0
    · simp [hb]
    · exact mul_le_mul_of_nonneg_left (hh b (lt_of_le_of_ne (p.nonneg b) (Ne.symm hb))).le (p.nonneg b)
  have hlt : (∑ b, p.mass b*c) < ∑ b, p.mass b*f b :=
    sum_lt_sum (fun b _ => hle b) ⟨a,mem_univ _,mul_lt_mul_of_pos_left (hh a ha) ha⟩
  rw [←sum_mul,p.total,one_mul] at hlt
  exact (not_lt_of_ge h) hlt

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))] in
lemma reverse_incidence_count (S : Finset (Projectivization K (Module.Dual K V)))
    (T : Finset (Projectivization K V)) :
    Incidence.incidenceCount T S = ((S ×ˢ T).filter (fun z => z.1.rep z.2.rep=0)).card := by
  simp only [Incidence.incidenceCount, Incidence.Incident, card_filter, sum_product]
  apply sum_congr rfl
  intro dualPoint _
  exact card_filter _ _

theorem auxiliary_cap_product {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K (Module.Dual K V)))
    (q : Law (Projectivization K V))
    (goodA : Finset (Projectivization K (Module.Dual K V)))
    (goodB : Finset (Projectivization K V))
    (MA MB κ : ℝ) (hMA : 0<MA) (hMB : 0<MB)
    (A : AuxiliarySupport p goodA MA κ) (B : AuxiliarySupport q goodB MB κ)
    (hsparse :
      (∑ a, ∑ b, A.law.mass a * B.law.mass b *
        (((((levelSet p a ∩ goodA) ×ˢ (levelSet q b ∩ goodB)).filter
          (fun z => z.1.rep z.2.rep=0)).card : ℝ) /
          (((levelSet p a ∩ goodA).card : ℝ) * (levelSet q b ∩ goodB).card)))
        ≤ 1/(4*(Nat.card K:ℝ))) :
    MA*MB ≤ 64*(Nat.card K:ℝ)^(n+3)*exp (2*κ) := by
  let SA := fun a : retainedLevels p goodA MA κ => levelSet p a ∩ goodA
  let SB := fun b : retainedLevels q goodB MB κ => levelSet q b ∩ goodB
  have hmean : (∑ ab, (A.law.prod B.law).mass ab *
      ((((SA ab.1 ×ˢ SB ab.2).filter (fun z => z.1.rep z.2.rep=0)).card:ℝ)/
        ((SA ab.1).card*(SB ab.2).card))) ≤ 1/(4*(Nat.card K:ℝ)) := by
    simpa only [Law.prod,Fintype.sum_prod_type] using hsparse
  obtain ⟨⟨a,b⟩,_,hs⟩ := (A.law.prod B.law).exists_mass_pos_le_of_mean_le _ _ hmean
  have ha := (A.size a).1
  have hb := (B.size b).1
  have hapos : (0:ℝ)<(SA a).card := (by positivity : 0<MA*exp (-κ)/2).trans_le ha
  have hbpos : (0:ℝ)<(SB b).card := (by positivity : 0<MB*exp (-κ)/2).trans_le hb
  have hsp : (Incidence.incidenceCount (SB b) (SA a):ℝ) ≤
      ((SB b).card:ℝ)*(SA a).card/(4*(Nat.card K:ℝ)) := by
    rw [reverse_incidence_count]
    have hh := (div_le_iff₀ (mul_pos hapos hbpos)).mp hs
    calc
      _ ≤ (1/(4*(Nat.card K:ℝ)))*((SA a).card*(SB b).card) := hh
      _ = _ := by ring
  have hm := Incidence.sparse_product_bound hdim (SB b) (SA a) hsp
  have hl : (MA*exp (-κ)/2)*(MB*exp (-κ)/2)≤
      ((SA a).card:ℝ)*(SB b).card :=
    mul_le_mul ha hb (by positivity) hapos.le
  have hex : exp (-κ)*exp (-κ)*exp (2*κ)=1 := by
    rw [←exp_add,←exp_add,show -κ + -κ + 2*κ = 0 by ring,exp_zero]
  have hh := mul_le_mul_of_nonneg_right (hl.trans (by simpa only [mul_comm] using hm))
    (exp_pos (2*κ)).le
  have he : (MA*exp (-κ)/2)*(MB*exp (-κ)/2)*exp (2*κ)=MA*MB/4 := by
    calc
      _ = MA*MB/4*(exp (-κ)*exp (-κ)*exp (2*κ)) := by ring
      _ = _ := by rw [hex,mul_one]
  rw [he] at hh
  linarith

theorem auxiliary_chronological_order {n : ℕ} (hdim : Module.finrank K V=n+3)
    (p : Law (Projectivization K (Module.Dual K V)))
    (q : Law (Projectivization K V))
    (goodA : Finset (Projectivization K (Module.Dual K V)))
    (goodB : Finset (Projectivization K V))
    (MA MB κ u v : ℝ) (hMA : 0<MA) (hMB : 0<MB)
    (hA : exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)≤MA)
    (hB : exp v≤MB)
    (A : AuxiliarySupport p goodA MA κ) (B : AuxiliarySupport q goodB MB κ)
    (hsparse :
      (∑ a, ∑ b, A.law.mass a * B.law.mass b *
        (((((levelSet p a ∩ goodA) ×ˢ (levelSet q b ∩ goodB)).filter
          (fun z => z.1.rep z.2.rep=0)).card : ℝ) /
          (((levelSet p a ∩ goodA).card : ℝ) * (levelSet q b ∩ goodB).card)))
        ≤ 1/(4*(Nat.card K:ℝ))) :
    v≤u+2*κ+log 64 := by
  have hq : (0:ℝ)<Nat.card K := by
    exact_mod_cast (show 0<Nat.card K from Nat.zero_lt_one.trans (Finite.one_lt_card : 1<Nat.card K))
  have hp := auxiliary_cap_product hdim p q goodA goodB MA MB κ hMA hMB A B hsparse
  have hlow := mul_le_mul hA hB (exp_pos v).le hMA.le
  have he : exp (((n+3:ℕ):ℝ)*log (Nat.card K)-u)*exp v=
      (Nat.card K:ℝ)^(n+3)*exp (v-u) := by
    rw [←exp_add,show ((n+3:ℕ):ℝ)*log (Nat.card K)-u+v=
      ((n+3:ℕ):ℝ)*log (Nat.card K)+(v-u) by ring,exp_add]
    congr 1
    rw [exp_nat_mul,exp_log hq]
  rw [he] at hlow
  have hcan : exp (v-u)≤64*exp (2*κ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hq _)).mp
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hlow.trans hp
  have hex : exp (v-u)≤exp (2*κ+log 64) := by
    rw [exp_add,exp_log (by norm_num : (0:ℝ)<64)]
    simpa only [mul_comm] using hcan
  have := exp_le_exp.mp hex
  linarith

end
end SharpLogRamsey.Selection

end

end OAI
