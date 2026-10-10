import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.DescriptionHeaders

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow SpatialLearning DescriptionHeaders
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype J]
local instance flat_JoinedSpatialHeaderCover_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedSpatialHeaderCover_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialHeaderCover_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialHeaderCover_4 : Fintype (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem public_header_cover (hdim : Module.finrank K V=4)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N) (hNU : N≤U.card)
    (plane : J→Finset (Projectivization K V)) (Jmax : ℕ)
    (σ P g b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R (Nat.log 2 N+2) p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    let H := (Fintype.card (Projectivization K V):ℝ)*log 2
    let a := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4+log (H+1)
    let E := 2*a+log 3+log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1)
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤N*exp (6*P)) ∧
      (∀ S,(∃ bs∈headers (α:=J) Jmax N,Input U N plane bs σ P g b τ c p S) →
        ∃ W∈caps,(N:ℝ)/2≤(S∩W).card) ∧
      (caps.card:ℝ)≤((Jmax+1:ℕ):ℝ)*
        (((Fintype.card J*(N+1)+1:ℕ):ℝ)^Jmax)*exp E := by
  dsimp only
  let H := (Fintype.card (Projectivization K V):ℝ)*log 2
  let a := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4+log (H+1)
  let E := 2*a+log 3+log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1)
  have hh (bs : List (J×ℕ)) := public_cover hdim U N hN0 hNU plane bs
    σ P g b τ L c R p h M hqexp hc hbud hb hτ hτsmall hN hloss herror hM
  choose messages hsize hcap hlen using hh
  let caps := (headers (α:=J) Jmax N).biUnion (fun bs =>
    (messages bs).image (fun z => decode U N L plane bs z.1 z.2))
  have hcount (bs : List (J×ℕ)) : ((messages bs).card:ℝ)≤exp E := by
    have ht : 0<((messages bs).card:ℝ)+1 := by positivity
    have he := exp_le_exp.mpr (hlen bs)
    rw [exp_log ht] at he
    exact (le_add_of_nonneg_right (by norm_num)).trans he
  refine ⟨caps,?_,?_,?_⟩
  · intro W hW
    obtain ⟨bs,_,hW'⟩ := mem_biUnion.mp hW
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hW'
    exact ⟨inter_subset_left,hsize bs z hz⟩
  · intro S hS
    obtain ⟨bs,hbs,hS⟩ := hS
    obtain ⟨z,hz,hzcap⟩ := hcap bs S hS
    exact ⟨_,mem_biUnion.mpr ⟨bs,hbs,mem_image.mpr ⟨z,hz,rfl⟩⟩,hzcap⟩
  · have hcc : caps.card≤∑ bs∈headers (α:=J) Jmax N,(messages bs).card := by
      apply card_biUnion_le.trans
      exact sum_le_sum (fun bs _ => card_image_le)
    have hcc' : (caps.card:ℝ)≤∑ bs∈headers (α:=J) Jmax N,((messages bs).card:ℝ) := by
      exact_mod_cast hcc
    calc
      _ ≤ ∑ bs∈headers (α:=J) Jmax N,((messages bs).card:ℝ) := hcc'
      _ ≤ ∑ _bs∈headers (α:=J) Jmax N,exp E := sum_le_sum (fun bs _ => hcount bs)
      _ = ((headers (α:=J) Jmax N).card:ℝ)*exp E := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        exact_mod_cast card_headers_le (α:=J) Jmax N

end
end SharpLogRamsey.SpatialPublic

end

end OAI
