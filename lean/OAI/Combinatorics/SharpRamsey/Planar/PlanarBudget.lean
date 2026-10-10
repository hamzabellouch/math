import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.UniversalTables
import OAI.Combinatorics.SharpRamsey.Learning.RegularPreparationBounds
import OAI.Combinatorics.SharpRamsey.Planar.PlanePencils

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section

structure Budget (σ P : ℝ) (L : ℝ≥0) (R p h : ℕ) : Prop where
  sigma : 2≤σ
  large : 100000000000000≤P
  upper : P≤σ
  B : 2*exp (6*P)≤exp σ
  identity : P=(L:ℝ)*R
  Llarge : 10000≤(L:ℝ)
  Rlarge : 400≤R
  p_pos : 0<p
  p_even : Even p
  order : 10000*σ≤(p:ℝ)*P
  sparseSchedules : (R:ℝ)*exp (-(24/25:ℝ)*(L:ℝ))≤1/10
  diag : 400000*2^R≤exp (P/20)
  pow : (2*(L:ℝ)^2)^R≤exp (P/25)
  sum : (400000:ℝ)^2*exp ((L:ℝ)/50)≤exp (P/20)
  two : 2≤exp (P/20)
  variance : 400000*exp ((L:ℝ)/1000)≤exp (P/100)
  cert : MomentBudgetBridge.certificateOverhead p 0 P≤exp (2*P/25)
  shift : MomentBudgetBridge.shiftOverhead p 0≤exp (2*P/25)
  pb : (p:ℝ)^2≤exp (P/10)
  ps : 2*(p:ℝ)+3≤exp (P/10)
  h_pos : 0<h
  h_small : h≤(R/2)/400
  h_root : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2

lemma scale_B {q s P : ℝ} (hq : 0<q) (hs : 0<s) (hsmall : s^2≤2*q^3)
    (hP : 2*exp (6*P)≤q) : exp (3*P)≤q^2/s := by
  have hsq : s^2*(exp (3*P))^2≤q^4 := by
    have he : (exp (3*P))^2=exp (6*P) := by rw [←exp_nat_mul]; congr 1; ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hsmall (exp_pos (6*P)).le
    nlinarith only [hh, mul_nonneg (show 0≤q^3 by positivity) (sub_nonneg.mpr hP)]
  apply (le_div_iff₀ hs).mpr
  have hp : 0≤exp (3*P)*s := by positivity
  nlinarith [sq_nonneg (exp (3*P)*s-q^2)]

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarBudget_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarBudget_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarBudget_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarBudget_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

omit [Finite K] [FiniteDimensional K V] in
lemma sparse_mass (S : Finset (Projectivization K V))
    (T : Finset (Projectivization K (Module.Dual K V))) (c : ℝ≥0) :
    (∑ H∈T,mass S c H)=(c:ℝ)*(Incidence.incidenceCount S T:ℝ) := by
  simp only [mass,Incidence.incidenceCount,Nat.cast_sum,mul_sum, Incidence.incident_iff_submodule]

lemma plane_pencil_budgets (hdim : Module.finrank K V=3)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V))) (hA : A⊆pencil x)
    (σ P B : ℝ) (R p h : ℕ) (hbud : Budget σ P L R p h) (hB : 0<B)
    (htyp : ∀ H∈A,3/4≤outsideMass S O x c H ∧ outsideMass S O x c H≤2 ∧
      |outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ)))|≤13/100)
    (hsq : (∑ H∈A,(outsideMass S O x c H-(1-((O.card:ℝ)/(S.card:ℝ))))^2)≤
      400000*B*exp ((L:ℝ)/1000))
    (hcards : ((∑ i∈range 2,Nat.card K^i):ℝ)≤4*B^2) (hdir : (1:ℝ)≤4*B) :
    SecondPencil 2 R S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B 400000 (∅ : Finset Unit) (fun _ => 0) ∧
    HighPencil 2 R p h S O x c L A ((O.card:ℝ)/(S.card:ℝ)) B (∅ : Finset Unit) (fun _ => 0) := by
    have hsqs : 400000*B*exp ((L:ℝ)/1000)≤400000*B*exp ((L:ℝ)/100) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exp_le_exp.mpr (by nlinarith [L.coe_nonneg])
    have hsqa : 400000*B*exp ((L:ℝ)/1000)≤B*exp (P/100) := by
      have hh := mul_le_mul_of_nonneg_left hbud.variance hB.le
      nlinarith only [hh]
    have hcs : ((∑ i∈range 2,Nat.card K^i):ℝ)≤400000*B^2 := by
      nlinarith [sq_nonneg B]
    exact plane_pencils hdim R p h hbud.p_pos S O x c L A hA _ B 400000 _
      hB.le htyp hsq hsqs (by simpa only [←hbud.identity] using hsqa) hcs hcards hdir
      (by simpa only [←hbud.identity] using hbud.diag)
      (by simpa only [←hbud.identity] using hbud.pow)
      (by simpa only [←hbud.identity] using hbud.sum)
      (by simpa only [←hbud.identity] using hbud.two)
      (by simpa only [←hbud.identity] using hbud.cert)
      (by simpa only [←hbud.identity] using hbud.shift)
      (by simpa only [←hbud.identity] using hbud.pb)
      (by simpa only [←hbud.identity] using hbud.ps)
      hbud.h_pos hbud.h_small hbud.h_root

omit [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma plane_error {q B L b e X : ℝ} (hq : 0<q) (hB : 0≤B) (hL : 0≤L)
    (hX : X≤50000*B*exp (L/1000))
    (herror : 50000*exp (-(95/100:ℝ)*L)≤exp (-b-e)/800) :
    exp (-L)*X≤(q*B*exp (-b-e)/8)/(100*q) := by
  calc
    _ ≤ exp (-L)*(50000*B*exp (L/1000)) := mul_le_mul_of_nonneg_left hX (exp_pos _).le
    _ = 50000*B*exp (-L+L/1000) := by rw [exp_add]; ring
    _ ≤ 50000*B*exp (-(95/100:ℝ)*L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact exp_le_exp.mpr (by linarith only [hL])
    _ ≤ (q*B*exp (-b-e)/8)/(100*q) := by
      have hh := mul_le_mul_of_nonneg_left herror hB
      have he : (q*B*exp (-b-e)/8)/(100*q)=B*exp (-b-e)/800 := by field_simp; ring
      rw [he]
      nlinarith only [hh]

end
end SharpLogRamsey.PlanarLearning

end

end OAI
