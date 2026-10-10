import OAI.Combinatorics.ContingencyTables.Rooted.TreeExteriorMass
import OAI.Combinatorics.ContingencyTables.Counting.CompanionFarMass
import OAI.Combinatorics.ContingencyTables.Transport.WeightedCellFibres

namespace OAI

/-! # The actual narrow exterior region contributes at most 4 gamma K per tree cell -/

namespace ContingencyTables.CompanionNearMass

open scoped BigOperators Classical
open CompanionFactorialApplication CompanionPhysicalNormalizer CompanionFarMass
open TreeMarginalSignature TreeExteriorPositions BalancedCellFibres ForestPenaltyApplication

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def cellPositions (A : Instance I J) (t : I×J) (gamma : ℝ) :
    Finset (Fin (cellWidth A t+1)) :=
  positions (ForestLiteralCount.lower A.T A.d A.b t.1 t.2) (A.b t.1 t.2)
    (cellWidth A t) (gamma*A.b t.1 t.2)

noncomputable def nearMass (A : Instance I J) (alpha : ℝ) (t : I×J) (gamma : ℝ) : ℝ :=
  ∑ a : Profiles (cellWidth A),if a t ∈ cellPositions A t gamma then actualWeight A alpha a else 0

lemma nearMass_eq_fibres (A : Instance I J) (alpha : ℝ) (t : I×J) (gamma : ℝ) :
    nearMass A alpha t gamma=∑ k ∈ cellPositions A t gamma,scalarExact A alpha t k.val := by
  have hh := weighted_fibre_sum (cellWidth A)
    (physicalWeight A.T A.b (ForestLiteralCount.lower A.T A.d A.b)
      (ForestLiteralCount.width A.T A.d A.b) A.r A.c alpha) t
    (fun k => if k ∈ cellPositions A t gamma then 1 else 0)
  have hs : (∑ k : Fin (cellWidth A t+1),
      if k ∈ cellPositions A t gamma then scalarExact A alpha t k.val else 0)=nearMass A alpha t gamma := by
    simp_rw [exact_eq_fibre]
    simpa only [nearMass,actualWeight,mul_ite,mul_one,mul_zero] using hh
  rw [← hs]
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using
    (Finset.sum_filter (s := Finset.univ) (fun k => k ∈ cellPositions A t gamma)
      (fun k => scalarExact A alpha t k.val)).symm

/-- This uses actual feasible endpoint tables, the proved raw marginal
signature and equality limit, and the exact count normalizer. -/
theorem near_mass_bound (A : Instance I J) (alpha gamma : ℝ) (t : I×J)
    (ht : A.T.Adj (.inl t.1) (.inr t.2)) (ha : 0 ≤ alpha) (hg : 0 < gamma)
    (hW : 20*A.d ≤ A.W) (B K : ℕ)
    (hB : (∏ a : I×J,(A.b a.1 a.2+1)) ≤ 2^B) (hBK : 2*B ≤ K) (hK : 0 < K)
    (Y0 Y1 : I → J → ℤ)
    (hY0 : ∀ i j,0 ≤ Y0 i j ∧ Y0 i j ≤ A.b i j)
    (hY1 : ∀ i j,0 ≤ Y1 i j ∧ Y1 i j ≤ A.b i j)
    (hr0 : ∀ i,(∑ j,Y0 i j)=A.r i) (hc0 : ∀ j,(∑ i,Y0 i j)=A.c j)
    (hr1 : ∀ i,(∑ j,Y1 i j)=A.r i) (hc1 : ∀ j,(∑ i,Y1 i j)=A.c j)
    (hy0 : Y0 t.1 t.2=0) (hy1 : Y1 t.1 t.2=(A.b t.1 t.2:ℤ)) :
    nearMass A alpha t gamma/physicalMass A alpha ≤ 4*gamma*K := by
  have hb : 0 < A.b t.1 t.2 := by have h := (A.hlarge _ _ (A.hTG ht)).2; omega
  have hbR : (0:ℝ) < A.b t.1 t.2 := by exact_mod_cast hb
  have hpoint (k : Fin (cellWidth A t+1)) (hk : k ∈ cellPositions A t gamma) :
      scalarExact A alpha t k.val/physicalMass A alpha ≤ (2*K:ℝ)/A.b t.1 t.2 := by
    have hh := (Finset.mem_filter.mp hk).2
    change (((ForestLiteralCount.lower A.T A.d A.b t.1 t.2+(k.val:ℤ)<0) ∧ _) ∨
      (((A.b t.1 t.2:ℤ)<ForestLiteralCount.lower A.T A.d A.b t.1 t.2+(k.val:ℤ)) ∧ _)) at hh
    simp only [ForestLiteralCount.lower,ht,ite_true] at hh
    rcases hh with hh|hh
    · apply lower_exterior_point A alpha t ht ha hW B K hB hBK hK Y1 hY1 hr1 hc1 hy1
      exact_mod_cast (show (k.val:ℤ) < (10*A.d*A.b t.1 t.2:ℕ) by omega)
    · apply upper_exterior_point A alpha t ht ha hW B K hB hBK hK Y0 hY0 hr0 hc0 hy0
      · exact_mod_cast (show (10*A.d*A.b t.1 t.2+A.b t.1 t.2:ℕ) < (k.val:ℤ) by omega)
      · exact Nat.le_of_lt_succ k.isLt
  have hcard := card_positions_le (ForestLiteralCount.lower A.T A.d A.b t.1 t.2)
    (A.b t.1 t.2) (cellWidth A t) (gamma*A.b t.1 t.2) (mul_pos hg hbR)
  calc
    _ = ∑ k ∈ cellPositions A t gamma,scalarExact A alpha t k.val/physicalMass A alpha := by
      rw [nearMass_eq_fibres,Finset.sum_div]
    _ ≤ ∑ _k ∈ cellPositions A t gamma,(2*K:ℝ)/A.b t.1 t.2 :=
      Finset.sum_le_sum (fun k hk => hpoint k hk)
    _ = ((cellPositions A t gamma).card:ℝ)*((2*K:ℝ)/A.b t.1 t.2) := by simp
    _ ≤ (2*(gamma*A.b t.1 t.2))*((2*K:ℝ)/A.b t.1 t.2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by field_simp [hbR.ne']; ring

end ContingencyTables.CompanionNearMass

end OAI
