import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialPreparation

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real PreparedRow PreparedGeometry PreparedTypical GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialRow_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedSpatialRow_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialRow_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialRow_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem short_proposal (hdim : Module.finrank K V=4)
    (S U : Finset (Projectivization K V)) (T : Finset (Projectivization K (Module.Dual K V)))
    (hS : S.Nonempty) (hT : T.Nonempty) (hSU : S⊆U) (hST : S.card≤T.card)
    (plane : J→Finset (Projectivization K V)) (bs : List J)
    (σ P g b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/S.card)
    (hbud : Budget σ P L R (Nat.log 2 S.card+2) p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hproduct : (Nat.card K:ℝ)^4*exp (-b)≤(S.card:ℝ)*T.card)
    (hsparse : (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K)
    (hN : 100*(Nat.card K:ℝ)*P≤S.card)
    (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hNup : (S.card:ℝ)≤exp (3*σ/2+g))
    (hcell : ∀ i : Fin bs.length,((indexedCell S plane bs i).card:ℝ)/(S.card:ℝ)≤1/25)
    (D₀ D₁ : Finset (Projectivization K V))
    (hD₀ : (D₀.card:ℝ)≤S.card*exp (-P/200)) (hD₁ : (D₁.card:ℝ)≤S.card*exp (5*P))
    (hrad : ∀ x,x∉D₀ → ∀ i∈range (Nat.log 2 S.card+2),
      ((PreparedProjectiveGeometry.richRadials (S\(own S plane bs x∪{x})) x c (DyadicGrid.value i)).card:ℝ)*
        (DyadicGrid.value i)^100≤exp (σ+P/100-2*g))
    (hstrong : ∀ x,x∉D₁ → (PreparedProjectiveGeometry.richRadials (S\(own S plane bs x∪{x})) x c (1/(100*(p:ℝ)))).card=0 ∨
      2*(exp σ+1)/(1/(100*(p:ℝ)))≤(exp (3*σ)/S.card)*exp (-3*P))
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    ((S.card:ℝ)/(U.card:ℝ))^M*(exp (-2*P*τ)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (PreparedDescription.good S plane (sized S plane bs) L ((S.card:ℝ)/2) (S.card*exp (6*P)))) := by
  let q : ℝ := Nat.card K
  let N : ℝ := S.card
  let B : ℝ := q^3/N
  let E := badHyperplanes S plane bs c
  let E₀ := T.filter (fun H => mass S c H≤2*τ)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Nat.card_pos (α:=K)
  have hq2 : 2≤q := by
    have hh : 2≤Nat.card K := Finite.one_lt_card
    dsimp [q]
    exact_mod_cast hh
  have hP : 0<P := by linarith [hbud.large]
  have hNs : 0<N := by dsimp [N]; exact_mod_cast card_pos.mpr hS
  have hB : 0<B := by dsimp [B]; positivity
  obtain ⟨hsp,hBbig,hcsmall,hE₀,hhalf,hE₀E,hsmallE⟩ := training hdim S T hS hT hST
    plane bs σ P τ R p h L c hqexp hc hbud hτ hτsmall hsparse hN
  obtain ⟨Ds,Da,hsub,hDsN,hDaN,hW,hown,hsecond,hhigh⟩ := preparation hdim S T hS hST
    plane bs σ P g L c R p h hc hcsmall hbud hqexp hNup hcell hsp D₀ D₁ hD₀ hD₁ hrad hstrong
  have hZ := training_size hNs (show 0≤(E₀.card:ℝ) by positivity) b (2*P*τ)
    hproduct hhalf
  have hErr : ∀ x,x∉Ds → exp (-(L:ℝ)*(1-((own S plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤(q*B*exp (-b-2*P*τ)/8)/(100*q) := by
    intro x hx
    exact spatial_error hq hB.le L.coe_nonneg (hown x) (hsecond x hx).1 herror
  have hmean : (R:ℝ)*S.card*(L*c:ℝ≥0)=q*P := by
    push_cast
    rw [hc,hbud.identity]
    dsimp [q]
    field_simp
  have hQ : (10:ℝ)≤∑ i∈range 4,(Nat.card K:ℝ)^i := by
    have hq3 : 3≤q := by
      have hh := add_one_le_exp σ
      rw [hqexp] at hh
      linarith [hbud.sigma]
    simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one]
    nlinarith
  have hout := PreparedDescription.short_proposal 1 R p h M (by omega) hdim S S U Ds Da hS
    Subset.rfl hSU hsub plane bs E E₀ hE₀ hE₀E c L hc hown
    σ P B 400000 b (2*P*τ) (20804*q*B) (by linarith [hbud.sigma]) hqexp
    hbud.large hbud.upper hbud.identity rfl hb (by positivity) hloss hbud.order
    hDsN hDaN
    (by nlinarith [hbud.large]) (by norm_num) hbud.Llarge hbud.Rlarge hbud.p_pos hbud.p_even
    (by simpa only [←hbud.identity] using hBbig) hQ hbud.sparseSchedules
    (fun H hH => by simpa only [←hbud.identity,mul_comm,mul_left_comm,mul_assoc] using
      sparse_training_exponent S c L R H τ (hsmallE H hH))
    (by positivity) le_rfl (by simpa only [mass,hc,inc] using hW) (by simpa only [neg_mul] using hZ) hErr
    (range (Nat.log 2 S.card+2)) DyadicGrid.value (fun x hx => (hsecond x hx).2) hhigh
    (by rw [hmean]; nlinarith only [hM])
  simp only [neg_mul] at hout ⊢
  with_unfolding_all exact hout

end
end SharpLogRamsey.SpatialLearning

end

end OAI
