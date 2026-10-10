import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.GoodRepresentative
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalLevelProducer

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]
lemma relationMass_conditioned_good_le (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β)
    (hA : (1:ℝ)/2≤eventMass p A) (hB : (1:ℝ)/2≤eventMass q B) (ρ : ℝ)
    (hρ : relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q≤ρ) :
    relationMass R (conditionOn p A (by linarith)) (conditionOn q B (by linarith))≤4*ρ := by
  rw [relationMass_conditioned_good]
  have hn:=relationMass_nonneg (fun a b=>a∈A ∧ b∈B ∧ R a b) p q p.nonneg q.nonneg
  have hab : (1:ℝ)/4≤eventMass p A*eventMass q B := by
    nlinarith [mul_le_mul hA hB (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤eventMass p A)]
  have hp : 0<eventMass p A*eventMass q B := lt_of_lt_of_le (by norm_num) hab
  apply (div_le_iff₀ hp).mpr
  have hr : 0≤ρ := hn.trans hρ
  nlinarith [mul_le_mul_of_nonneg_left hab hr]

lemma relationMass_restricted_conditionOn_right (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β) (hB : 0<eventMass q B) :
    relationMass R (fun a=>if a∈A then p a else 0) (conditionOn q B hB)=
      relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q/eventMass q B := by
  simp only [relationMass,Finset.sum_filter,conditionOn_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;> by_cases hr : R z.1 z.2 <;>
    simp only [ha,hb,hr,ite_true,ite_false,true_and,false_and,and_false,
      zero_mul,mul_zero,zero_div,mul_div_assoc]

lemma relationMass_conditionOn_left_restricted (R : α→β→Prop) (p : Law α) (q : Law β)
    (A : Finset α) (B : Finset β) (hA : 0<eventMass p A) :
    relationMass R (conditionOn p A hA) (fun b=>if b∈B then q b else 0)=
      relationMass (fun a b=>a∈A ∧ b∈B ∧ R a b) p q/eventMass p A := by
  simp only [relationMass,Finset.sum_filter,conditionOn_apply]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  by_cases ha : z.1∈A <;> by_cases hb : z.2∈B <;> by_cases hr : R z.1 z.2 <;>
    simp only [ha,hb,hr,ite_true,ite_false,true_and,false_and,and_false,
      zero_mul,mul_zero,zero_div,div_mul_eq_mul_div]

lemma div_half_bound (a m ρ : ℝ) (hm : (1:ℝ)/2 ≤ m) (ha : 0≤a) (hρ : a≤ρ) :
    a/m≤2*ρ := by
  apply (div_le_iff₀ (by linarith : 0 < m)).mpr
  have hr : 0≤ρ := ha.trans hρ
  nlinarith [mul_le_mul_of_nonneg_left hm hr]
end
end SharpRamseyFive.FiniteEntropy
namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V I : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype I] {n : ℕ}

def reciprocalGoodA (p : Law (FlagPair K V)) (u s : ℝ) : Finset (ℙ K V) :=
  goodFirstEndpoints p (32*Real.exp (5*Real.log (Nat.card K)-u)) ((Nat.card K:ℝ)^4) s

def reciprocalGoodB (p : Law (FlagPair K V)) (u s : ℝ) : Finset (ℙ K (Dual K V)) :=
  goodFirstEndpoints (swap p) (32*Real.exp u) ((Nat.card K:ℝ)^4) s

omit [FiniteDimensional K V] in
theorem reciprocal_good_mass (p : Law (FlagPair K V)) (u s d C₀ : ℝ) (hs : 0<s)
    (hA : ((support (first p)).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u))
    (hB : ((support (second p)).card:ℝ)≤32*Real.exp u)
    (hflag : ((support p).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
    (hent : 4*Real.log (Nat.card K)-entropy p≤d) (hsmall : reciprocalBadMass s d C₀≤(1:ℝ)/2) :
    (1:ℝ)/2≤eventMass (first p) (reciprocalGoodA p u s) ∧
      (1:ℝ)/2≤eventMass (second p) (reciprocalGoodB p u s) := by
  obtain ⟨ha,hb⟩:=reciprocal_bad_endpoints p u s d C₀ hs hA hB hflag hent
  have h1:=eventMass_complement (first p) (reciprocalGoodA p u s)
  have h2:=eventMass_complement (second p) (reciprocalGoodB p u s)
  change eventMass (first p) (reciprocalGoodA p u s)ᶜ≤_ at ha
  change eventMass (second p) (reciprocalGoodB p u s)ᶜ≤_ at hb
  constructor <;> linarith

omit [Finite K] in
theorem ordered_good_reference_sparse (hdim : finrank K V=5)
    (p : Law (I→FlagPair K V)) (e : I≃Fin n) (u : I→ℝ) (s ε : ℝ)
    (hcons : ∀ x,0<p x→∀ i j,e i<e j→Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
    (i j : I) (hij : e i<e j)
    (hi : (1:ℝ)/2≤eventMass (first (map p (fun x=>x i))) (reciprocalGoodA (map p (fun x=>x i)) (u i) s))
    (hj : (1:ℝ)/2≤eventMass (second (map p (fun x=>x j))) (reciprocalGoodB (map p (fun x=>x j)) (u j) s))
    (hgood : entropy (map p (fun x=>x i))+entropy (map p (fun x=>x j))-
      entropy (pair p (fun x=>x i) (fun x=>x j))+orderedCollision p e u s i j≤ε) :
    relationMass Incident
      (conditionOn (first (map p (fun x=>x i))) (reciprocalGoodA (map p (fun x=>x i)) (u i) s) (by linarith))
      (conditionOn (second (map p (fun x=>x j))) (reciprocalGoodB (map p (fun x=>x j)) (u j) s) (by linarith))≤
      320016*ε := by
  have hh:=relationMass_conditioned_good_le Incident (first (map p (fun x=>x i)))
    (second (map p (fun x=>x j))) _ _ hi hj (80004*ε)
    ((ordered_reciprocal_low_conflict hdim p e u s hcons i j hij).trans
      (mul_le_mul_of_nonneg_left hgood (by norm_num)))
  linarith
end
end SharpRamseyFive.Marking

end OAI
