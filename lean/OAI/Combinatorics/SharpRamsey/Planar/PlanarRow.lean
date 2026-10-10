import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanarTraining

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarRow_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarRow_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarRow_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarRow_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem short_proposal (hdim : Module.finrank K V=3)
    (S U : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hSU : S⊆U) (hST : S.card≤T.card)
    (σ P b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hproduct : (Nat.card K:ℝ)^3*exp (-b)≤(S.card:ℝ)*T.card)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card)
    (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(exp (-2*P*τ)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (PreparedDescription.good S (fun _ : Unit => ∅) [] L ((S.card:ℝ)/2) (S.card*exp (6*P)))) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^2/N
  let E := badHyperplanes S (fun _ : Unit => ∅) [] c
  let E₀ := T.filter (fun H => mass S c H≤2*τ)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := by have := (Finite.one_lt_card : 1<Nat.card K); omega
    dsimp [q]
    exact_mod_cast hh
  have hP : 0<P := by linarith [hbud.large]
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨hsp,hBbig,hcsmall,hE₀,hhalf,hE₀E,hsmallE⟩ := training hdim S T hS hT hST
    σ P τ R p h L c hqexp hc hbud hτ hτsmall hsparse hN
  obtain ⟨Ds,hDsN,hW,hown,hpencils⟩ := preparation hdim S T hS hST σ P L c R p h hc hcsmall hbud hsp
  have hZ := training_size hNs (show 0≤(E₀.card:ℝ) by positivity) b (2*P*τ)
    hproduct hhalf
  have hErr : ∀ x,x∉Ds → exp (-(L:ℝ)*(1-((own S (fun _ : Unit => ∅) [] x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤(q*B*exp (-b-2*P*τ)/8)/(100*q) := by
    intro x hx
    have hc := (hpencils x hx).1
    simp only [own,card_empty,Nat.cast_zero,zero_div,sub_zero,mul_one]
    exact plane_error hq hB.le L.coe_nonneg hc herror
  have hmean : (R:ℝ)*S.card*(L*c:ℝ≥0)=q*P := by
    push_cast
    rw [hc,hbud.identity]
    dsimp [q]
    field_simp
  have hQ : (10:ℝ)≤∑ i∈range 3,(Nat.card K:ℝ)^i := by
    have hq3 : 3≤q := by
      have hh := add_one_le_exp σ
      rw [hqexp] at hh
      linarith [hbud.sigma]
    simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one]
    nlinarith
  have hout := PreparedDescription.short_proposal 0 R p h M (by omega) hdim S S U Ds Ds hS
    Subset.rfl hSU Subset.rfl (fun _ : Unit => ∅) [] E E₀ hE₀ hE₀E c L hc hown
    σ P B 400000 b (2*P*τ) (20804*q*B) (by linarith [hbud.sigma]) hqexp
    hbud.large hbud.upper hbud.identity rfl hb (by positivity) hloss hbud.order
    (by change (Ds.card:ℝ)≤N*exp (-P/200)+N/10000; linarith [mul_nonneg hNs.le (exp_pos (-P/200)).le])
    (by change (Ds.card:ℝ)≤2*N+N*exp (5*P); nlinarith [mul_nonneg hNs.le (exp_pos (5*P)).le])
    (by nlinarith [hbud.large]) (by norm_num) hbud.Llarge hbud.Rlarge hbud.p_pos hbud.p_even
    (by simpa only [←hbud.identity] using hBbig) hQ hbud.sparseSchedules
    (fun H hH => by simpa only [←hbud.identity,mul_comm,mul_left_comm,mul_assoc] using
      sparse_training_exponent S c L R H τ (hsmallE H hH))
    (by positivity) le_rfl (by simpa only [mass,hc,inc] using hW) (by simpa only [neg_mul] using hZ) hErr
    (∅ : Finset Unit) (fun _ => 0) (fun x hx => (hpencils x hx).2.1) (fun x hx => (hpencils x hx).2.2)
    (by rw [hmean]; nlinarith only [hM])
  simp only [sized,neg_mul] at hout ⊢
  with_unfolding_all exact hout

end
end SharpLogRamsey.PlanarLearning

end

end OAI
