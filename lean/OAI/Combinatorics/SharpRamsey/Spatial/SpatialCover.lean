import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialPublic

namespace OAI

section
namespace SharpLogRamsey.SpatialPublic
open Finset Real PreparedRow SpatialLearning
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V J : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedSpatialCover_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedSpatialCover_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedSpatialCover_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedSpatialCover_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

theorem public_cover (hdim : Module.finrank K V=4)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N) (hNU : N≤U.card)
    (plane : J→Finset (Projectivization K V)) (bs : List (J×ℕ))
    (σ P g b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R (Nat.log 2 N+2) p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) :
    let H := (Fintype.card (Projectivization K V):ℝ)*log 2
    let a := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4+log (H+1)
    ∃ messages : Finset (((Fin R×Projectivization K V)→Fin (M+2)) ×
        Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)),
      (∀ z∈messages,((decode U N L plane bs z.1 z.2).card:ℝ)≤N*exp (6*P)) ∧
      (∀ S,Input U N plane bs σ P g b τ c p S → ∃ z∈messages,
        (N:ℝ)/2≤(S∩decode U N L plane bs z.1 z.2).card) ∧
      log ((messages.card:ℝ)+1)≤2*a+log 3+
        log ((Fintype.card (Projectivization K (Module.Dual K V)):ℝ)+1) := by
  dsimp only
  let H := (Fintype.card (Projectivization K V):ℝ)*log 2
  let a₀ := (M:ℝ)*log ((U.card:ℝ)/N)+2*P*τ+log 4
  let a := a₀+log (H+1)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN0
  have hUr : (0:ℝ)<U.card := hNr.trans_le (by exact_mod_cast hNU)
  have hHr : 0≤H := mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by norm_num))
  have hHP : 0<H+1 := by linarith
  have hP : 0≤P := le_trans (by norm_num) hbud.large
  have ha₀ : 0≤a₀ := by
    apply add_nonneg
    · apply add_nonneg
      · exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg ((le_div_iff₀ hNr).mpr (by simpa only [one_mul] using (show (N:ℝ)≤U.card by exact_mod_cast hNU))))
      · positivity
    · exact log_nonneg (by norm_num)
  have ha : 0≤a := add_nonneg ha₀ (log_nonneg (by linarith))
  have hea : H+1≤exp a := by
    dsimp only [a]
    rw [exp_add,exp_log hHP]
    exact le_mul_of_one_le_left (le_of_lt hHP) (one_le_exp_iff.mpr ha₀)
  let Ω := (Fin R×Projectivization K V)→Fin (M+2)
  let ι := {S // Input U N plane bs σ P g b τ c p S}
  let law := PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*N*(L*c)) M
  let A : ι→Ω→Prop := fun i => PreparedProposals.accepts (coordinateSupport i.1 R) M
    (PreparedDescription.good i.1 plane bs L ((N:ℝ)/2) (N*exp (6*P)))
  have hprob : ∀ i,exp (-a)≤PublicTables.acceptProb law (A i) := by
    intro i
    have hh := input_probability hdim U N hN0 plane bs σ P g b τ L c R p h M hqexp hc hbud hb hτ hτsmall hN hloss herror hM i.1 i.2
    have he := PublicTables.sampling_exponent hNr hUr M (2*P*τ)
    simp only [neg_mul] at hh
    rw [he] at hh
    apply le_trans _ hh
    apply exp_le_exp.mpr
    dsimp only [a,a₀]
    have hh' : 0≤log (H+1) := log_nonneg (by linarith)
    linarith
  obtain ⟨messages,_,hsize,hcap,hlen⟩ := PublicTables.decoder_cover law A a H
    ((N:ℝ)/2) (N*exp (6*P))
    (Fintype.card (Projectivization K (Module.Dual K V))) (decode U N L plane bs) (fun i : ι => i.1)
    ha (input_card U N plane bs σ P g b τ c p) hea hprob
    (fun i ω hω => input_decode U N L plane bs σ P g b τ c p i.1 i.2 ω hω)
  exact ⟨messages,hsize,fun S hS => hcap ⟨S,hS⟩,hlen⟩

end
end SharpLogRamsey.SpatialPublic

end

end OAI
