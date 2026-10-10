import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.ReciprocalEntropy
import OAI.Combinatorics.SharpRamsey.Execution.ExecutedDecodedSize

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation ScheduledBanks PublicTables ReadyTests
  PivotGeometry ProjectiveDuality TreeDecoder FreshExecution ExecutedPotential
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]
  {I : Type*} {n : ℕ} {b τ P H : ℝ}

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma chronoFlagDomain_card (U : ChronoDomains (K:=K) (V:=V)) :
    (flagDomain (fun y x=>SharpLogRamsey.Incidence.Incident x y) U).card=
      incidenceCount U.2 U.1 := by
  simp only [flagDomain,incidenceCount,card_eq_sum_ones,sum_filter,sum_product]

omit [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem reciprocal_flagDomain_size (hdim : Module.finrank K V=n+3) (hb : 0≤b)
    (U : ChronoDomains (K:=K) (V:=V))
    (S : Finset (Projectivization K (Module.Dual K V))) (T : Finset (Projectivization K V))
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hprod : (Nat.card K:ℝ)^(n+3)*exp (-b)≤(S.card:ℝ)*T.card)
    (hA : (U.1.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/T.card)
    (hB : (U.2.card:ℝ)≤2000*(Nat.card K:ℝ)^(n+3)/S.card) :
    ((flagDomain (fun y x=>SharpLogRamsey.Incidence.Incident x y) U).card:ℝ)≤
      8000000*(Nat.card K:ℝ)^(n+2)*exp b := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Finite.card_pos : 0<Nat.card K)
  have hp := flagDomain_size (fun _ _=>True) U S T hS hT
    ((Nat.card K:ℝ)^(n+3)) 2000 b (by positivity) (by norm_num) hprod hA hB
  have hcap : (U.2.card:ℝ)*U.1.card≤(2000^2*exp b)*(Nat.card K:ℝ)^(n+3)*(1:ℝ)^2 := by
    have hp' : (U.1.card:ℝ)*U.2.card≤2000^2*(Nat.card K:ℝ)^(n+3)*exp b := by
      simpa only [flagDomain,filter_true,card_product,Nat.cast_mul] using hp
    calc
      _ = (U.1.card:ℝ)*U.2.card := by ring
      _ ≤ _ := hp'
      _ = _ := by ring
  have hB' : 1≤(2000:ℝ)^2*exp b := by nlinarith [one_le_exp hb]
  have hm := mixing_cell_scale hdim U.2 U.1 hB' (by norm_num : (0:ℝ)≤1) le_rfl hcap
  rw [chronoFlagDomain_card]
  convert hm using 1
  ring

variable (hdim : Module.finrank K V=n+3)
  (book : Book (K:=K) (V:=V) (Nat.card K) b τ P H (n+3))
  (hb : 0≤b) (hτ : 0≤τ) (hτsmall : τ≤1/40000)
include hb

theorem Book.actual_decoded_size (s : I→Original (K:=K) (V:=V) n b)
    (z : I→Banks (K:=K) (V:=V) b)
    (targets : I→List (Projectivization K (Module.Dual K V)×Projectivization K V))
    (counts : I→ℕ) (t : BinaryTree I) (U : ChronoDomains (K:=K) (V:=V)) :
    let rd := fixedRead (fun _i : I=>chronoRead (K:=K) (V:=V) b) z
    let ch := fixedChoose (fun i=>book.chronoChoose hdim hτ hτsmall (s i)) z
    ∀ D∈decode (fun y x=>SharpLogRamsey.Incidence.Incident x y) rd
      (message (fun y x=>SharpLogRamsey.Incidence.Incident x y) rd targets counts (execute rd ch t U) U) U,
      (D.card:ℝ)≤8000000*(Nat.card K:ℝ)^(n+2)*exp b := by
  apply decoded_domains_size
  intro i U c hc
  obtain ⟨x,hx,rfl⟩:=Option.map_eq_some_iff.mp hc
  have hh:=book.choose_caps hdim hτ hτsmall (s i) U.swap (z i) x hx
  apply reciprocal_flagDomain_size hdim hb _ (s i).B (s i).A (s i).nonemptyB (s i).nonemptyA
  · simpa only [mul_comm] using (s i).product
  · exact hh.2.2.2.2.2
  · exact hh.2.2.2.2.1

end
end SharpLogRamsey.ActualPivot

end

end OAI
