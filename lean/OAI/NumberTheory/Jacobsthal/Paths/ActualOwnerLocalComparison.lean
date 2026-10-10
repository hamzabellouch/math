import Mathlib
import OAI.NumberTheory.Jacobsthal.Partitions.FullHypotheticalBinLower
import OAI.NumberTheory.Jacobsthal.Partitions.OriginalBinWeightRange

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosStoppedArithmetic

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem missing_weight_bound {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w : α → ℝ) (lo eta : ℝ) (hlo : 0 ≤ lo) (heta : 0 ≤ eta)
    (hNear : (1-eta)*(P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P,lo ≤ w p ∧ w p ≤ 2*lo) :
    (∑ p ∈ P \ G,w p) ≤ 2*eta*(∑ p ∈ P,w p) := by
  have hcards : ((P \ G).card : ℝ)+(G.card : ℝ)=(P.card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hGP
  have hmissing : ((P \ G).card : ℝ) ≤ eta*(P.card : ℝ) := by nlinarith
  have hsumlo : (P.card : ℝ)*lo ≤ ∑ p ∈ P,w p := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_le_sum (fun p hp => (hW p hp).1)
  calc
    _ ≤ ∑ _p ∈ P \ G,2*lo := Finset.sum_le_sum (fun p hp => (hW p (Finset.mem_sdiff.mp hp).1).2)
    _ = ((P \ G).card : ℝ)*(2*lo) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (eta*(P.card : ℝ))*(2*lo) := mul_le_mul_of_nonneg_right hmissing (by positivity)
    _ = 2*eta*((P.card : ℝ)*lo) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumlo (by positivity)

theorem near_full_owner_lower {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w T : α → ℝ) (lo eta C V : ℝ) (hlo : 0 ≤ lo) (heta : 0 ≤ eta) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hNear : (1-eta)*(P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P,lo ≤ w p ∧ w p ≤ 2*lo)
    (hAll : (39/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ P,T p)
    (hUpper : ∀ p ∈ P,T p ≤ C*V*w p) (hBudget : 2*C*eta ≤ (1/20 : ℝ)) :
    (34/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ G,T p := by
  have hw0 (p : α) (hp : p ∈ P) : 0 ≤ w p := hlo.trans (hW p hp).1
  have hsum0 : 0 ≤ ∑ p ∈ P,w p := Finset.sum_nonneg hw0
  have hmiss := missing_weight_bound P G hGP w lo eta hlo heta hNear hW
  have hmissT : (∑ p ∈ P \ G,T p) ≤ (1/20 : ℝ)*V*(∑ p ∈ P,w p) := by
    calc
      _ ≤ ∑ p ∈ P \ G,C*V*w p := Finset.sum_le_sum (fun p hp => hUpper p (Finset.mem_sdiff.mp hp).1)
      _ = C*V*(∑ p ∈ P \ G,w p) := (Finset.mul_sum _ _ _).symm
      _ ≤ C*V*(2*eta*(∑ p ∈ P,w p)) := mul_le_mul_of_nonneg_left hmiss (mul_nonneg hC hV)
      _ = (2*C*eta)*(V*(∑ p ∈ P,w p)) := by ring
      _ ≤ (1/20 : ℝ)*(V*(∑ p ∈ P,w p)) := mul_le_mul_of_nonneg_right hBudget (mul_nonneg hV hsum0)
      _ = _ := by ring
  have hsplit : (∑ p ∈ P \ G,T p)+(∑ p ∈ G,T p)=∑ p ∈ P,T p := Finset.sum_sdiff hGP
  nlinarith

theorem near_full_owner_comparison {α : Type*} (P G : Finset α) (hGP : G ⊆ P)
    (w T reference : α → ℝ) (lo eta C V : ℝ)
    (hlo : 0 ≤ lo) (heta : 0 ≤ eta) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hNear : (1-eta)*(P.card : ℝ) ≤ (G.card : ℝ))
    (hW : ∀ p ∈ P,lo ≤ w p ∧ w p ≤ 2*lo)
    (hAll : (39/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ P,T p)
    (hUpper : ∀ p ∈ P,T p ≤ C*V*w p) (hBudget : 2*C*eta ≤ (1/20 : ℝ))
    (hReference : ∀ p ∈ G,reference p ≤ (33/100 : ℝ)*V*w p) :
    (1/100 : ℝ)*V*(∑ p ∈ P,w p) ≤ ∑ p ∈ G,(T p-reference p) := by
  have howner := near_full_owner_lower P G hGP w T lo eta C V hlo heta hC hV hNear hW hAll hUpper hBudget
  have hw0 (p : α) (hp : p ∈ P) : 0 ≤ w p := hlo.trans (hW p hp).1
  have hsub : (∑ p ∈ G,w p) ≤ ∑ p ∈ P,w p :=
    Finset.sum_le_sum_of_subset_of_nonneg hGP (fun p hp _ => hw0 p hp)
  have href : (∑ p ∈ G,reference p) ≤ (33/100 : ℝ)*V*(∑ p ∈ P,w p) := by
    calc
      _ ≤ ∑ p ∈ G,(33/100 : ℝ)*V*w p := Finset.sum_le_sum hReference
      _ = (33/100 : ℝ)*V*(∑ p ∈ G,w p) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hsub (by positivity)
  rw [Finset.sum_sub_distrib]
  linarith

end ErdosStoppedArithmetic



namespace ErdosStoppedArithmetic
open ErdosStoppedTagSieve ErdosCommonMInterval ErdosInverseAlignment ErdosInversePrimeBin
  ErdosPrimeInputs.MertensStrong ErdosInverseCounts
  NumberTheoryLean.ReferenceProductsBasics

attribute [local instance] Classical.propDecidable

theorem actual_owner_local_comparison :
    ∃ eta0 : ℝ,0 < eta0 ∧ eta0 ≤ 1/4 ∧ ∃ P0 : ℕ,2 ≤ P0 ∧
      ∀ Cs : ℝ,0 ≤ Cs → ∃ K : ℝ,0 < K ∧ ∀ rho xi : ℝ,1 < rho → 0 < xi →
      ∃ w0 : ℝ,4 ≤ w0 ∧ ∀ w : ℝ,w0 ≤ w → ∀ P : ℕ,P.Prime → P0 ≤ P →
      ∀ R theta eta : ℝ,
      Real.exp (K*(Real.log w)^3) ≤ (P : ℝ) → (P : ℝ) ≤ Real.exp (rho*K*(Real.log w)^3) →
      Real.exp (w^((1:ℝ)/4)*Real.log w) ≤ R → xi/4 ≤ theta → theta ≤ 1 →
      0 ≤ eta → eta ≤ eta0 →
      ∀ Y q : ℕ,0 < Y → 0 < q → ∀ r : ℚ,∀ a : ℕ → ℕ,
      (r.den : ℝ) ≤ w^Cs → |(r.num : ℝ)| ≤ (Y : ℝ)*w^(Cs+2) →
      (∀ x ∈ Set.Icc R ((1+theta)*R),
        203/100 ≤ lengthExponent P Y x q ∧ lengthExponent P Y x q ≤ 219/100) →
      (∀ t ∈ smallPrimeSet (P : ℝ),q.Coprime t) →
      (∀ p ∈ primeBin R theta,Squarefree (p*q) ∧ r.den.Coprime p ∧
        p ∉ smallPrimeSet (P : ℝ) ∧
        (∀ t ∈ (p*q).primeFactors,t ≠ p → aligns (fun u => (a u : ℤ)) r t) ∧
        ∀ t ∈ (p*q).primeFactors,P ≤ t) →
      (1-eta)*((primeBin R theta).card : ℝ) ≤
        (((primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r)).card : ℝ) →
      ∀ reference : ℕ → ℝ,
      (∀ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
        reference p ≤ (33/100 : ℝ)*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q))) →
      (1/100 : ℝ)*primeProduct (P : ℝ)*(∑ p ∈ primeBin R theta,(Y : ℝ)/((p : ℝ)*q)) ≤
        ∑ p ∈ (primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r),
          ((modulusCount Y (smallPrimeSet (P : ℝ)) a (p*q) : ℝ)-reference p) := by
  obtain ⟨C,eta0,hC,heta0,heta01,hBudget,P0,hP0,hUpper⟩ := primeHypothetical_uniform_upper
  refine ⟨eta0,heta0,heta01,P0,hP0,?_⟩
  intro Cs hCs
  obtain ⟨K,hK,hFull⟩ := hypothetical_full_bin_lower Cs hCs
  refine ⟨K,hK,?_⟩
  intro rho xi hrho hxi
  obtain ⟨w0,hw0,hF⟩ := hFull rho xi hrho hxi
  refine ⟨w0,hw0,?_⟩
  intro w hw P hPrime hP R theta eta hPl hPu hR hThetaLo hThetaHi heta hetaU
    Y q hY hq r a hDen hNum hBand hqSmall hGeometry hNear reference hReference
  have hR0 : 0 < R := (Real.exp_pos _).trans_le hR
  have ht : 0 < theta := (div_pos hxi (by norm_num)).trans_le hThetaLo
  have hP1 : (1 : ℝ) < P := by exact_mod_cast hPrime.one_lt
  have hAll := hF w hw P R theta hPl hPu hR hThetaLo hThetaHi Y q hY hq r a hDen hNum
    hBand hqSmall (fun p hp =>
      ⟨(hGeometry p hp).1,(hGeometry p hp).2.1,(hGeometry p hp).2.2.1,(hGeometry p hp).2.2.2.1⟩)
  have hWeight := original_bin_weight_range Y q R theta (Nat.cast_nonneg Y)
    (show (0 : ℝ) < q by exact_mod_cast hq) hR0 ht.le hThetaHi
  have hPointUpper : ∀ p ∈ primeBin R theta,primeHypothetical Y (smallPrimeSet (P : ℝ)) a r q p ≤
      C*primeProduct (P : ℝ)*((Y : ℝ)/((p : ℝ)*q)) := by
    intro p hp
    obtain ⟨hpPrime,hplo,hphi⟩ := (mem_primeBin hR0.le ht.le p).mp hp
    have hb := hBand p ⟨hplo.le,hphi⟩
    have hid := reference_rpow hP1 (show (0 : ℝ) < Y by exact_mod_cast hY)
      (hR0.trans hplo) (show (0 : ℝ) < q by exact_mod_cast hq)
    have hJ : (P : ℝ)^2 ≤ (Y : ℝ)/(p*q : ℕ) := by
      have hh := Real.rpow_le_rpow_of_exponent_le hP1.le (show (2 : ℝ) ≤ lengthExponent P Y p q by linarith)
      rw [hid] at hh
      simpa only [Real.rpow_ofNat,referenceLength,Nat.cast_mul] using hh
    have hh := hUpper P hPrime hP Y q p r a hY hpPrime (hGeometry p hp).1
      (hGeometry p hp).2.2.2.2 hJ
    simpa only [Nat.cast_mul,mul_assoc,mul_left_comm,mul_comm] using hh
  have hBudget' : 2*C*eta ≤ (1/20 : ℝ) :=
    (mul_le_mul_of_nonneg_left hetaU (by positivity : 0 ≤ 2*C)).trans hBudget
  have hh := near_full_owner_comparison (primeBin R theta)
    ((primeBin R theta).filter (aligns (fun t => (a t : ℤ)) r)) (Finset.filter_subset _ _)
    (fun p => (Y : ℝ)/((p : ℝ)*q)) (primeHypothetical Y (smallPrimeSet (P : ℝ)) a r q)
    reference ((Y : ℝ)/(((1+theta)*R)*q)) eta C (primeProduct (P : ℝ))
    hWeight.1 heta hC.le (actual_primeProduct_pos _).le hNear hWeight.2 hAll hPointUpper hBudget' hReference
  convert hh using 1
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hp,ha⟩ := Finset.mem_filter.mp hp
  rw [primeHypothetical_agrees Y _ a r q p ((mem_primeBin hR0.le ht.le p).mp hp).1 ha]

end ErdosStoppedArithmetic


end Erdos970

end OAI
