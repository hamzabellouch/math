import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.InitialAuto

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
variable {V : Type*} [LinearOrder V]
def StartOutput.project : StartOutput V→Finset V
  | .small o => o.project
  | .normal o => o.project
end MetricKMedianRecovery.CanonicalCoupledMerge
namespace MetricKMedianRecovery.BitMachine.BinaryInitialProject
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
attribute [local irreducible] BinaryProjection.run BinaryFiniteMachine.after
noncomputable def extract (x : List Bool) : List Bool :=
  BinaryProjection.run (BinaryFiniteMachine.after (pairBits ([],field 2 (discardPrefix x))))
noncomputable def extract_computes : PolyComputes extract :=
  ((const_computes []).pair (discardPrefix_computes.comp (field_computes 2))).comp
    (BinaryFiniteMachine.after_computes.comp BinaryProjection.run_computes)
lemma extract_output (o : StartOutput (Fin m)) : extract (BinaryInitial.output o)=BinaryFinSet.encode o.project := by
  have hz : setBits (∅ : Finset (Label (Fin m)))=[] := by
    simp only [setBits,labels,BinaryLabel.orderedSort,Finset.sort_empty,List.map_nil,encode]
  cases o <;> simp only [extract,BinaryInitial.output,discardPrefix_pairBits,BinaryCoupled.outputBits,
    field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  all_goals rw [←hz]
  all_goals rw [BinaryFiniteMachine.after_pack,BinaryProjection.run_setBits]
  all_goals rfl
noncomputable def run (v : ℚ) (C : ℕ) : List Bool→List Bool := extract ∘ BinaryInitialAuto.run v C
noncomputable def run_computes (v : ℚ) (C : ℕ) : PolyComputes (run v C) :=
  (BinaryInitialAuto.run_computes v C).comp extract_computes
lemma run_pack [PseudoMetricSpace (Fin m)] (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v M : ℚ) (C k : ℕ) (hv : 0<v) (hC : 2≤(1+v^2)^C)
    (hd : 0<d) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤d+F.card)
    (hv1 : (v:ℝ)<1/6) (hlohi : 2/((d+F.card:ℕ):ℚ)^2≤8*(d:ℚ)*M)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    run v C (BinaryInitialAuto.pack distance loc F M k)=BinaryFinSet.encode
      (start loc distance F v (2/((d+F.card:ℕ):ℚ)^2) M (d+F.card) (d+F.card)
        (HistoryPhaseBound.limit v ((M:ℝ)+8*(d:ℝ)*M)+1) k).project := by
  rw [run,Function.comp_apply,BinaryInitialAuto.run,Function.comp_apply,
    BinaryInitialAuto.initialInput_pack v M hv hM C hC]
  rw [BinaryInitial.run_pack distance loc hmetric F v _ M ((1:ℝ)/2^(d+F.card)) _ _ _ k hd
    (Nat.le_add_right _ _) hk hF hM hN (by exact_mod_cast hv) hv1 (by positivity) (by positivity)
    hlohi (by simp only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat,le_refl]) hfar hdiam,
    extract_output]
end MetricKMedianRecovery.BitMachine.BinaryInitialProject

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseOriginalLedger HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
def LowCertificate (loc : Fin d→V) (F S : Finset V) (v lo : ℝ) (k : ℕ) : Prop :=
  S⊆F ∧ S.Nonempty ∧ S.card≤k ∧ ∃ (Q : ℝ) (alpha : Fin d→ℝ),
    0≤Q ∧ (∑ j,nearestDistance (loc j) S)≤Q ∧ Dual loc F v lo alpha ∧
      (1-3*v)*Q≤∑ j,alpha j
def NormalCertificate (loc : Fin d→V) (F S : Finset V) (v lo hi eta : ℝ) (total k : ℕ) : Prop :=
  S⊆F ∧ S.Nonempty ∧ S.card≤k+3*total ∧ ∃ (lam Q : ℝ) (alpha : Fin d→ℝ),
    lo≤lam ∧ lam≤hi ∧ 0≤Q ∧ (∑ j,nearestDistance (loc j) S)≤Q ∧ Dual loc F v lam alpha ∧
      (1-3*v)*Q+(k:ℝ)*(lam-(d:ℝ)*eta)≤∑ j,alpha j
lemma start_certificate (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (eta : ℝ) (N precision k : ℕ)
    (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    let total := limit v ((M:ℝ)+8*(d:ℝ)*M)+1
    let S := (start loc distance F v lo M N precision total k).project
    LowCertificate loc F S v lo k ∨ NormalCertificate loc F S v lo (8*(d:ℝ)*M) eta total k := by
  dsimp only
  let total := limit v ((M:ℝ)+8*(d:ℝ)*M)+1
  cases he : start loc distance F v lo M N precision total k with
  | small o =>
    left
    exact start_small_certificate loc distance hmetric F v lo M N precision k o he hd hF hv hv1 hlo hM hlohi hfar hdiam
  | normal o =>
    right
    have hc := start_correct loc distance hmetric F v lo M eta N precision total k
      hd hdN hk hF hM hN hv hv1 hlo heta hlohi hprecision hfar hdiam
    have hr := start_rooted loc distance F v lo M N precision total k
    rw [he] at hc hr
    obtain ⟨hSF,hS,hcard,Q,alpha,hQ,hcost,hdual,hpay⟩ := o.normal_certificate loc F v eta lo (8*(d:ℝ)*M) M k hc hr
      (by omega) hF hv hv1 (by exact_mod_cast hlo) (by positivity) hfar hdiam
    exact ⟨hSF,hS,hcard,o.lam,Q,alpha,hc.2.1,hc.2.2.1,hQ,hcost,hdual,hpay⟩
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
