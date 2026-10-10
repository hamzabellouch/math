import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PublicDecoderCover
import OAI.Combinatorics.SharpRamsey.Planar.PlanarRow

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real PreparedRow
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarPublic_1 (R : ℕ) : DecidableEq (Fin R × Projectivization K V) := Classical.decEq _
local instance flat_JoinedPlanarPublic_2 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarPublic_3 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarPublic_4 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

def Input (U : Finset (Projectivization K V)) (N : ℕ) (b τ : ℝ)
    (S : Finset (Projectivization K V)) : Prop :=
  S⊆U ∧ S.card=N ∧ ∃ T : Finset (Projectivization K (Module.Dual K V)),
    T.Nonempty ∧ S.card≤T.card ∧
    (Nat.card K:ℝ)^3*exp (-b)≤(S.card:ℝ)*T.card ∧
    (Incidence.incidenceCount S T:ℝ)≤τ*(S.card:ℝ)*T.card/Nat.card K

lemma input_card (U : Finset (Projectivization K V)) (N : ℕ) (b τ : ℝ) :
    (Fintype.card {S // Input U N b τ S}:ℝ)≤
      exp ((Fintype.card (Projectivization K V):ℝ)*log 2) := by
  have hh := Fintype.card_subtype_le (Input U N b τ)
  rw [Fintype.card_finset] at hh
  rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
  exact_mod_cast hh

lemma input_probability (hdim : Module.finrank K V=3)
    (U : Finset (Projectivization K V)) (N : ℕ) (hN0 : 0<N)
    (σ P b τ : ℝ) (L c : ℝ≥0) (R p h M : ℕ)
    (hqexp : exp σ=(Nat.card K:ℝ)) (hc : (c:ℝ)=(Nat.card K:ℝ)/N)
    (hbud : Budget σ P L R p h) (hb : 0≤b) (hτ : 0<τ) (hτsmall : τ≤1/20)
    (hN : 100*(Nat.card K:ℝ)*P≤N) (hloss : b+2*P*τ≤P/1000000)
    (herror : 50000*exp (-(95/100:ℝ)*(L:ℝ))≤exp (-b-2*P*τ)/800)
    (hM : 2*(Nat.card K:ℝ)*P≤M) (S : Finset (Projectivization K V))
    (hS : Input U N b τ S) :
    ((N:ℝ)/(U.card:ℝ))^M*(exp (-2*P*τ)/4)≤
      PublicTables.acceptProb
        (PreparedProposals.proposal (coordinateSupport U R) ((R:ℝ≥0)*N*(L*c)) M)
        (PreparedProposals.accepts (coordinateSupport S R) M
          (PreparedDescription.good S (fun _ : Unit => ∅) [] L ((N:ℝ)/2) (N*exp (6*P)))) := by
  obtain ⟨hSU,hSN,T,hT,hST,hpr,hsp⟩ := hS
  have hSn : S.Nonempty := card_pos.mp (by omega)
  have hh := short_proposal hdim S U T hSn hT hSU hST σ P b τ L c R p h M hqexp
    (by simpa only [hSN] using hc) hbud hb hτ hτsmall hpr hsp
    (by simpa only [hSN] using hN) hloss herror hM
  simpa only [hSN] using hh

def decode (U : Finset (Projectivization K V)) (N : ℕ) (L : ℝ)
    {R M : ℕ} (ω : (Fin R×Projectivization K V)→Fin (M+2))
    (z : Fin (Fintype.card (Projectivization K (Module.Dual K V))+1)) :
    Finset (Projectivization K V) :=
  U∩PreparedDecoder.decode (fun _ : Unit => ∅) [] N z pencil inc L (Nat.card K)
    (fun x => (ω x:ℕ))

lemma input_decode (U : Finset (Projectivization K V)) (N : ℕ) (L P b τ : ℝ)
    {R M : ℕ} (S : Finset (Projectivization K V)) (hS : Input U N b τ S)
    (ω : (Fin R×Projectivization K V)→Fin (M+2))
    (hω : PreparedProposals.accepts (coordinateSupport S R) M
      (PreparedDescription.good S (fun _ : Unit => ∅) [] L ((N:ℝ)/2) (N*exp (6*P))) ω) :
    ∃ z,(N:ℝ)/2≤(S∩decode U N L ω z).card ∧
      ((decode U N L ω z).card:ℝ)≤N*exp (6*P) := by
  obtain ⟨z,hz,hcap,hsize⟩ := hω.2.2
  rw [hS.2.1] at hcap hsize
  refine ⟨⟨z,by omega⟩,?_,?_⟩
  · have he : S∩decode U N L ω ⟨z,by omega⟩=
        S∩PreparedDecoder.decode (fun _ : Unit => ∅) [] N z pencil inc L (Nat.card K) (fun x => (ω x:ℕ)) := by
      ext x
      simp only [decode,mem_inter]
      exact ⟨fun hh => ⟨hh.1,hh.2.2⟩,fun hh => ⟨hh.1,hS.1 hh.1,hh.2⟩⟩
    rw [he]
    exact hcap
  · exact (show ((decode U N L ω ⟨z,by omega⟩).card:ℝ)≤
      (PreparedDecoder.decode (fun _ : Unit => ∅) [] N z pencil inc L (Nat.card K) (fun x => (ω x:ℕ))).card
        by exact_mod_cast card_le_card inter_subset_right).trans hsize

end
end SharpLogRamsey.PlanarLearning

end

end OAI
