import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.PreparedRadial

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedRadialCount_1 : Finite (Projectivization K V) := by
  have : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedRadialCount_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedPreparedRadialCount_3 : Finite (Submodule K V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPreparedRadialCount_4 : Fintype (Submodule K V) := Fintype.ofFinite _

lemma planePoints_card (W : Submodule K V) :
    (planePoints W).card=∑ i∈range (Module.finrank K W),Nat.card K^i := by
  rw [planePoints,←Fintype.card_subtype,←Nat.card_eq_fintype_card,
    ←Nat.card_congr (Incidence.projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

lemma linePoints_card (W : ProjectiveLine (K:=K) (V:=V)) :
    (planePoints W.1).card=Nat.card K+1 := by
  rw [planePoints_card,W.2]
  simp [sum_range_succ,Nat.add_comm]

theorem residual_pairs_le (S : Finset (Projectivization K V))
    (X : Projectivization K V→Finset (Projectivization K V))
    (hX : ∀ x,X x⊆S) (M : ℕ) :
    ((univ : Finset (Projectivization K V × ProjectiveLine (K:=K) (V:=V))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card ≤
    (Nat.card K+1)*((univ : Finset (ProjectiveLine (K:=K) (V:=V))).filter
      (fun W => M≤(S∩planePoints W.1).card)).card := by
  let R := (univ : Finset (ProjectiveLine (K:=K) (V:=V))).filter
      (fun W => M≤(S∩planePoints W.1).card)
  have hs : (univ.filter
      (fun z : Projectivization K V × ProjectiveLine (K:=K) (V:=V) =>
        z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)) ⊆
      R.biUnion (fun W => planePoints W.1 ×ˢ {W}) := by
    intro z hz
    obtain ⟨_,hx,hrich⟩ := mem_filter.mp hz
    apply mem_biUnion.mpr
    refine ⟨z.2,mem_filter.mpr ⟨mem_univ _,hrich.trans ?_⟩,
      mem_product.mpr ⟨hx,mem_singleton_self _⟩⟩
    exact card_le_card (inter_subset_inter_right (hX z.1))
  calc
    _ ≤ (R.biUnion (fun W => planePoints W.1 ×ˢ {W})).card := card_le_card hs
    _ ≤ ∑ W∈R,(planePoints W.1 ×ˢ {W}).card := card_biUnion_le
    _ = (Nat.card K+1)*R.card := by simp [linePoints_card,mul_comm]

lemma radialFiber_eq_inter (S : Finset (Projectivization K V)) (x : Projectivization K V)
    (hx : x∉S) (W : RadialLine x) : radialFiber S x W=S∩planePoints W.1 := by
  ext y
  simp only [radialFiber,mem_filter,mem_inter,mem_planePoints]
  constructor
  · rintro ⟨hs,_,hw⟩; exact ⟨hs,hw⟩
  · rintro ⟨hs,hw⟩
    exact ⟨hs,(by intro he; exact hx (he ▸ hs)),hw⟩

end
end SharpLogRamsey.PreparedProjectiveGeometry

namespace SharpLogRamsey.PreparedRadialResidual
open Finset PreparedProjectiveGeometry
open scoped Classical BigOperators
noncomputable section
variable {q : ℕ} [Fact q.Prime]
local instance flat_JoinedPreparedRadialCount_5 : Finite (Submodule (ZMod q) (Fin 4→ZMod q)) :=
  Finite.of_injective (fun W : Submodule (ZMod q) (Fin 4→ZMod q) => (W : Set (Fin 4→ZMod q)))
    SetLike.coe_injective
local instance flat_JoinedPreparedRadialCount_6 : Fintype (Submodule (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _
local instance flat_JoinedPreparedRadialCount_7 : Fintype (Projectivization (ZMod q) (Fin 4→ZMod q)) := Fintype.ofFinite _

theorem rich_card (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (M Kp : ℕ) (hM2 : 2≤M) (hMN : M≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M)<M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M))<1/2)
    (hKM : 8*Kp≤M^2) :
    ((univ : Finset (ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
       (fun W => M≤(S∩planePoints W.1).card)).card*M≤8718*S.card := by
  let R := ((univ : Finset (ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
       (fun W => M≤(S∩planePoints W.1).card))
  have he (W : ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q)) :
      S∩planePoints W.1=S.filter (fun P => P.submodule≤W.1) := by
    ext P; simp
  have hh := RichFiniteProjective.card_mul_le hq S hS (fun W : {W // W∈R} => W.1.1)
    (fun W => W.1.2) (by intro W U h; exact Subtype.ext (Subtype.ext h)) M Kp hM2 hMN
    (fun W => by simpa only [←he] using (mem_filter.mp W.2).2)
    hcap hsmall hchar hprob hKM
  simpa only [Fintype.card_coe] using hh

theorem residual_pairs (hq : 3≤q)
    (S : Finset (Projectivization (ZMod q) (Fin 4→ZMod q))) (hS : S.Nonempty)
    (X : Projectivization (ZMod q) (Fin 4→ZMod q)→Finset (Projectivization (ZMod q) (Fin 4→ZMod q)))
    (hX : ∀ x,X x⊆S) (M Kp : ℕ) (hM2 : 2≤M) (hMN : M≤S.card)
    (hcap : ∀ f : (Fin 4→ZMod q)→ₗ[ZMod q] ZMod q, f≠0 →
       (S.filter (fun P => f P.rep=0)).card≤Kp)
    (hsmall : 198*Real.sqrt ((S.card:ℝ)/M)<M)
    (hchar : 33*Real.sqrt ((S.card:ℝ)/M)<q)
    (hprob : (S.card:ℝ)^2*Real.exp (-5*Real.sqrt ((S.card:ℝ)/M))<1/2)
    (hKM : 8*Kp≤M^2) :
    ((univ : Finset (Projectivization (ZMod q) (Fin 4→ZMod q) ×
        ProjectiveLine (K:=ZMod q) (V:=Fin 4→ZMod q))).filter
      (fun z => z.1∈planePoints z.2.1 ∧ M≤(X z.1∩planePoints z.2.1).card)).card*M ≤
      8718*(q+1)*S.card := by
  have h1 := Nat.mul_le_mul_right M (residual_pairs_le S X hX M)
  have h2 := Nat.mul_le_mul_left (q+1) (rich_card hq S hS M Kp hM2 hMN hcap hsmall hchar hprob hKM)
  have hqcard : Nat.card (ZMod q)=q := by simp
  rw [hqcard] at h1
  nlinarith

end
end SharpLogRamsey.PreparedRadialResidual

end

end OAI
