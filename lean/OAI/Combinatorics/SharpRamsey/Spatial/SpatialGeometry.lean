import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialBudget
import OAI.Combinatorics.SharpRamsey.Geometry.ListSourceRadial
import OAI.Combinatorics.SharpRamsey.Geometry.ResidualSourceRadial

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section

lemma overlap_scale {σ P g N : ℝ} (hN : 0<N) (hNup : N≤exp (3*σ/2+g))
    (hσ : 0≤σ) (hP : 400≤P) :
    exp (σ+P/100-2*g)*(exp σ+1)^2≤(exp σ^3/N)^2*exp (P/50) := by
  have he : 1≤exp σ := one_le_exp hσ
  have hq : 0<exp σ := exp_pos _
  have hB : exp (3*σ/2-g)≤exp σ^3/N := by
    apply (le_div_iff₀ hN).mpr
    calc
      _ ≤ exp (3*σ/2-g)*exp (3*σ/2+g) :=
        mul_le_mul_of_nonneg_left hNup (exp_pos _).le
      _ = _ := by rw [←exp_add,←exp_nat_mul]; congr 1; ring
  have h4 : 4≤exp (P/100) := by have := add_one_le_exp (P/100); linarith
  calc
    _ ≤ exp (σ+P/100-2*g)*(4*(exp σ)^2) := by gcongr; nlinarith
    _ = 4*(exp (3*σ/2-g))^2*exp (P/100) := by
      rw [←exp_nat_mul,←exp_nat_mul]
      simp only [Nat.cast_ofNat]
      calc
        _ = 4*(exp (σ+P/100-2*g)*exp (2*σ)) := by ring
        _ = 4*exp (σ+P/100-2*g+2*σ) := by rw [←exp_add]
        _ = 4*exp (2*(3*σ/2-g)+P/100) := by congr 2; ring
        _ = _ := by rw [exp_add]; ring
    _ ≤ (exp (3*σ/2-g))^2*(exp (P/100))^2 := by
      have hh := mul_le_mul_of_nonneg_right h4 (exp_pos (P/100)).le
      have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (exp (3*σ/2-g)))
      nlinarith only [hh']
    _ ≤ (exp σ^3/N)^2*exp (P/50) := by
      have hex : (exp (P/100))^2=exp (P/50) := by rw [←exp_nat_mul]; congr 1; ring
      rw [hex]
      gcongr

lemma direction_scale {q N P : ℝ} (hq : 1≤q) (hN : 0<N)
    (hsmall : N^2≤2*q^4) (hP : 400≤P) :
    2*(q+1)≤(q^3/N)*exp (P/50) := by
  have hq0 : 0<q := by linarith
  have hNq : N≤2*q^2 := by nlinarith [sq_nonneg (N-2*q^2)]
  have hB : q≤2*(q^3/N) := by
    rw [←mul_div_assoc]
    apply (le_div_iff₀ hN).2
    nlinarith [mul_le_mul_of_nonneg_left hNq hq0.le]
  have he : 8≤exp (P/50) := by have := add_one_le_exp (P/50); linarith
  have hB0 : 0≤q^3/N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left he hB0]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialGeometry_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialGeometry_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialGeometry_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

lemma spatial_pencil_budgets (hdim : Module.finrank K V=4)
    (S O : Finset (Projectivization K V)) (hS : S.Nonempty)
    (x : Projectivization K V) (c L : ℝ≥0)
    (hc : 1/(S.card:ℝ)≤c)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (σ P g : ℝ) (R p h : ℕ)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h)
    (hqexp : exp σ=(Nat.card K:ℝ))
    (hNup : (S.card:ℝ)≤exp (3*σ/2+g))
    (hsmall : (S.card:ℝ)^2≤2*(Nat.card K:ℝ)^4)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ)))|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ))))^2)≤
      400000*((Nat.card K:ℝ)^3/S.card)*exp ((L:ℝ)/1000))
    (hcards : ((∑ i∈range 3,Nat.card K^i):ℝ)≤4*((Nat.card K:ℝ)^3/S.card)^2)
    (hdir : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*((Nat.card K:ℝ)^3/S.card))
    (hrad : ∀ i∈range (Nat.log 2 S.card+2),
      ((PreparedProjectiveGeometry.richRadials (S\(O∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤exp (σ+P/100-2*g))
    (hstrong : (PreparedProjectiveGeometry.richRadials (S\(O∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P)) :
    let B := (Nat.card K:ℝ)^3/S.card
    SecondPencil 3 R S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B 400000
      (range (Nat.log 2 S.card+2)) DyadicGrid.value ∧
    HighPencil 3 R p h S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B
      (range (Nat.log 2 S.card+2)) DyadicGrid.value := by
  let B := (Nat.card K:ℝ)^3/S.card
  have hN : (0:ℝ)<S.card := Nat.cast_pos.mpr (card_pos.mpr hS)
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hB : 0<B := by dsimp [B]; positivity
  have hsqs : 400000*B*exp ((L:ℝ)/1000)≤400000*B*exp ((L:ℝ)/100) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact exp_le_exp.mpr (by nlinarith [L.coe_nonneg])
  have hsqa : 400000*B*exp ((L:ℝ)/1000)≤B*exp (P/100) := by
    have hh := mul_le_mul_of_nonneg_left hbud.variance hB.le
    nlinarith only [hh]
  have hcs : ((∑ i∈range 3,Nat.card K^i):ℝ)≤400000*B^2 := by
    change _≤400000*((Nat.card K:ℝ)^3/S.card)^2
    nlinarith [sq_nonneg ((Nat.card K:ℝ)^3/S.card)]
  have hpair : exp (σ+P/100-2*g)*((Nat.card K:ℝ)+1)^2≤B^2*exp (P/50) := by
    simpa only [hqexp] using overlap_scale hN hNup (by linarith [hbud.sigma])
      (by linarith [hbud.large] : 400≤P)
  have hneighbor : 2*((Nat.card K:ℝ)+1)≤B*exp (P/50) :=
    direction_scale hq1 hN hsmall (by linarith [hbud.large])
  have hstrong' : (PreparedProjectiveGeometry.richRadials (S\(O∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*((Nat.card K:ℝ)+1)/(1/(100*(p:ℝ)))≤B*exp (-3*P) := by
    have heq : exp (3*σ)=(Nat.card K:ℝ)^3 := by rw [←hqexp,←exp_nat_mul]; norm_num
    simpa only [hqexp,heq] using hstrong
  exact spatial_pencils hdim R p h hbud.p_pos S O hS x c L hc A hA _ B 400000 _
    (exp (σ+P/100-2*g)) (exp_pos _).le htyp hsq hsqs
    (by simpa only [←hbud.identity] using hsqa) hcs hcards hdir hrad
    (by simpa only [←hbud.identity] using hpair)
    (by simpa only [←hbud.identity] using hneighbor)
    (by simpa only [←hbud.identity] using hstrong') hB.le
    (by simpa only [←hbud.identity] using hbud.diag)
    (by simpa only [←hbud.identity] using hbud.pow)
    (by simpa only [←hbud.identity] using hbud.sum)
    (by simpa only [←hbud.identity] using hbud.two)
    (by simpa only [←hbud.identity] using hbud.cert)
    (by simpa only [←hbud.identity] using hbud.shift)
    (by simpa only [←hbud.identity] using hbud.pb)
    (by simpa only [←hbud.identity] using hbud.ps)
    hbud.h_pos hbud.h_small hbud.h_root

end
end SharpLogRamsey.SpatialLearning

end

end OAI
