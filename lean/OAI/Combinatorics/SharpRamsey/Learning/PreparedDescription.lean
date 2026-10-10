import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedDecoder
import OAI.Combinatorics.SharpRamsey.Learning.PreparedPointProposals

namespace OAI

section
namespace SharpLogRamsey.PreparedDescription
open Finset MeasureTheory PreparedRow GreedyPreparation
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I B : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedDescription_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPreparedDescription_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedDescription_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedDescription_4 : Fintype (Projectivization K V) := by
  have : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

def good (S : Finset (Projectivization K V))
    (plane : B→Finset (Projectivization K V)) (bs : List (B×ℕ)) (L cap size : ℝ)
    {R : ℕ} (ω : Fin R×Projectivization K V→ℕ) : Prop :=
  ∃ z≤Fintype.card (Projectivization K (Module.Dual K V)),
    let W := PreparedDecoder.decode plane bs S.card z pencil inc L (Nat.card K) ω
    cap≤(S∩W).card ∧ (W.card:ℝ)≤ size

lemma good_of_source (S₀ S : Finset (Projectivization K V)) (hS : S⊆S₀)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E : Finset (Projectivization K (Module.Dual K V))) (L cap size : ℝ)
    {R : ℕ} (ω : Schedule S R)
    (hcap : cap≤(S∩rowTest S (own S₀ plane bs) E
      (fun x => Real.exp (-L*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))) ω).card)
    (hsize : ((rowTest S (own S₀ plane bs) E
      (fun x => Real.exp (-L*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))) ω).card:ℝ)≤ size) :
    good S plane (sized S₀ plane bs) L cap size (ambientCounts S ω) := by
  refine ⟨(emptySet S E inc ω).card,card_le_univ _,?_⟩
  dsimp only
  have he := PreparedDecoder.decode_equals_source S₀ S hS plane bs pencil inc L
    (Nat.card K) (emptySet S E inc ω).card ω
  change _ = rowTest S (own S₀ plane bs) E _ ω at he
  change cap≤(S∩PreparedDecoder.decode _ _ _ _ _ _ _ _ (PreparedDecoder.counts S ω)).card ∧
    ((PreparedDecoder.decode _ _ _ _ _ _ _ _ (PreparedDecoder.counts S ω)).card:ℝ)≤ size
  rw [he]
  exact ⟨hcap,hsize⟩

theorem geometric_proposal_probability
    (n R p h M : ℕ) (hn : n≤1) (hdim : Module.finrank K V=n+3)
    (S₀ S U Ds Da : Finset (Projectivization K V)) (hS : S.Nonempty)
    (hS₀ : S⊆S₀) (hSU : S⊆U) (hDa : Ds⊆Da)
    (plane : B→Finset (Projectivization K V)) (bs : List B)
    (E E₀ : Finset (Projectivization K (Module.Dual K V))) (hE₀ : E₀.Nonempty) (hE₀E : E₀⊆E)
    (c L : ℝ≥0) (hc : (c:ℝ)=(Nat.card K:ℝ)/(S.card:ℝ))
    (hf : ∀ x,((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)≤1/25)
    (B₀ C bE δ u zmin W tS tA : ℝ)
    (hδ : 0≤δ) (hu : 0<u) (hzmin : 0<zmin) (htS : 0<tS) (htA : 0<tA)
    (hC : 0≤C) (hL : 10000≤(L:ℝ)) (hR : 400≤R) (hp : 0<p) (hpe : Even p)
    (hB : Real.exp (3*((L:ℝ)*R))≤B₀)
    (hQ : (10:ℝ)≤∑ i∈range (n+3),(Nat.card K:ℝ)^i)
    (hα : (R:ℝ)*Real.exp (-(24/25:ℝ)*(L:ℝ))≤1/10)
    (hsmall : ∀ H∈E₀,((L*c:ℝ≥0):ℝ)*R*((S.filter (inc H)).card:ℝ)≤bE)
    (hW : (∑ H∈E,((Nat.card K:ℝ)/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤W)
    (hZ : zmin≤(E₀.card:ℝ)*Real.exp (-bE)/2)
    (herror : ∀ x,x∉Ds → Real.exp (-(L:ℝ)*(1-((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)))*
      ((pencil x∩E).card:ℝ)≤zmin/(100*(Nat.card K:ℝ)))
    (T : Finset I) (a : I→ℝ)
    (hs : ∀ x,x∉Ds → SecondPencil (n+2) R S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ C T a)
    (ha : ∀ x,x∉Da → HighPencil (n+2) R p h S (own S₀ plane bs x) x c L (pencil x\E)
      (((own S₀ plane bs x).card:ℝ)/(S.card:ℝ)) B₀ T a)
    (hM : 2*((R:ℝ)*S.card*(L*c:ℝ≥0))≤M) :
    let q : ℝ := Nat.card K
    let μmean : ℝ := (R:ℝ)*S.card*(L*c:ℝ≥0)
    let t := zmin/(10*q)
    let εs := B₀^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/t^2
    let εa := B₀^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/t^p
    let lower := Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
      (S.card:ℝ)*εs/tS-(Fintype.card (Projectivization K V):ℝ)*εa/tA-2*Real.exp (-μmean/3)
    let cap := (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)
    let size := 2*μmean+(Da.card:ℝ)+tA+100*q^(n+3)/zmin
    ((S.card:ℝ)/(U.card:ℝ))^M*lower≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*S.card*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (good S plane (sized S₀ plane bs) L cap size)) := by
  dsimp only
  let O := own S₀ plane bs
  let f := fun x => ((O x).card:ℝ)/(S.card:ℝ)
  have hr := geometric_row_probability n R p h hn hdim S Ds Da hS hDa O E E₀ hE₀ hE₀E
    c L hc f hf B₀ C bE δ u zmin W tS tA hδ hu hzmin htS htA hC hL hR hp hpe hB hQ
    hα hsmall hW hZ herror T a hs ha
  dsimp only at hr
  let P := {ω : Schedule S R | ∃ z≤Fintype.card (Projectivization K (Module.Dual K V)),
    let W₀ := PreparedDecoder.decode plane (sized S₀ plane bs) S.card z pencil inc L (Nat.card K) (ambientCounts S ω)
    (S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ)≤(S∩W₀).card ∧
    (W₀.card:ℝ)≤2*((R:ℝ)*S.card*(L*c:ℝ≥0))+(Da.card:ℝ)+tA+100*(Nat.card K:ℝ)^(n+3)/zmin}
  have hp' : Real.exp (-bE)/2-W*Real.exp (-((L:ℝ)*R)*δ)/(u*zmin)-
      (S.card:ℝ)*(B₀^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R))/(zmin/(10*(Nat.card K:ℝ)))^2)/tS-
      (Fintype.card (Projectivization K V):ℝ)*(B₀^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R)))/(zmin/(10*(Nat.card K:ℝ)))^p)/tA-
      Real.exp (-((R:ℝ)*S.card*(L*c:ℝ≥0))/3)≤
      (PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real P := by
    apply hr.trans
    apply measureReal_mono (h₂:=measure_ne_top _ _)
    intro ω hω
    exact good_of_source S₀ S hS₀ plane bs E L _ _ ω hω.2.1 hω.2.2
  have hcut := total_cutoff_intersection S R M (L*c) P hM
  have hprop := ambient_proposal_success S U hS hSU R M (by omega) (L*c)
    (good S plane (sized S₀ plane bs) L
      ((S.card:ℝ)-(Ds.card:ℝ)-tS-(10*(δ+u))*(S.card:ℝ))
      (2*((R:ℝ)*S.card*(L*c:ℝ≥0))+(Da.card:ℝ)+tA+100*(Nat.card K:ℝ)^(n+3)/zmin))
  apply le_trans _ hprop
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change _≤(PoissonSchedules.scheduleLaw (fun _ : Fin R×S => L*c)).real {ω | (∑ i,ω i)≤M ∧ ω∈P}
  linarith

end
end SharpLogRamsey.PreparedDescription

end

end OAI
