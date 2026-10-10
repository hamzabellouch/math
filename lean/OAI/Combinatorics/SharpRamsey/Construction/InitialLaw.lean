import Mathlib
import OAI.Combinatorics.SharpRamsey.Construction.InitialTools

namespace OAI

section
namespace SharpLogRamsey.InitialExperiment
open Finset Real Filter Selection Marking FiniteStreamTail RectangleStreamEvent
open scoped Classical BigOperators Topology
noncomputable section
local instance initLawFiniteDual {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Fin (d+1)→K)) :=
  Finite.of_injective ((↑) : Module.Dual K (Fin (d+1)→K)→((Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance initLawFiniteDouble {K : Type} [Field K] [Fintype K] {d : ℕ} : Finite (Module.Dual K (Module.Dual K (Fin (d+1)→K))) :=
  Finite.of_injective ((↑) : Module.Dual K (Module.Dual K (Fin (d+1)→K))→(Module.Dual K (Fin (d+1)→K)→K)) DFunLike.coe_injective
local instance initLawProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Fin (d+1)→K)) := Fintype.ofFinite _
local instance initLawDualProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Fin (d+1)→K))) := Fintype.ofFinite _
local instance initLawDoubleProjective {K : Type} [Field K] [Fintype K] {d : ℕ} : Fintype (Projectivization K (Module.Dual K (Module.Dual K (Fin (d+1)→K)))) := Fintype.ofFinite _

def occupancyConstant (i : ℕ) : ℝ := (((i+4)^2:ℕ)+5:ℝ)/log 2

lemma occupancyConstant_pos (i : ℕ) : 0 < occupancyConstant i:=by
  unfold occupancyConstant
  exact div_pos (by positivity) (log_pos (by norm_num))

variable (i q : ℕ) [Fact q.Prime] (N k : ℕ)

local instance initLawFlagNonempty : Nonempty (Flag (ZMod q) (Fin (i+4)→ZMod q)):=
  Fintype.card_pos_iff.mp (by
    have hh:=flags_card_pos (K:=ZMod q) (V:=Fin (i+4)→ZMod q) (d:=i+3) (by omega) (by simp)
    simpa only [←Nat.card_eq_fintype_card] using hh)

def goodEvent : Finset (Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q)):=
  univ.filter (fun z=>∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
    (hits (rectangle W) z:ℝ)<occupancyConstant i*log (q:ℝ))

lemma goodEvent_half (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ)) :
    (1:ℝ)/2 ≤ probability (goodEvent i q N) := by
  have hh:=simultaneous_good_probability (d:=i+3) (N:=N) (K:=ZMod q) (V:=Fin (i+4)→ZMod q)
    (by omega) (by simp) (by simpa only [Nat.card_zmod] using hN)
  have hq : 2 ≤ (q:ℝ):=by exact_mod_cast (Fact.out : q.Prime).two_le
  have hq0 : (0:ℝ) < q:=by linarith
  have hdiv : 1/(q:ℝ) ≤ 1/2:=(div_le_iff₀ hq0).mpr (by linarith)
  have hin : (1:ℝ)/2 ≤ 1-1/q:=by linarith
  apply hin.trans
  simpa only [goodEvent,occupancyConstant,Nat.card_zmod,show i+3+1=i+4 by omega,
    probability,hits,rectangle,mem_filter,mem_univ,true_and,←Fintype.card_subtype,
    ←Nat.card_eq_fintype_card] using hh

def law (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ)) : Law (goodEvent i q N):=
  uniformLaw.onEvent (goodEvent i q N) (by rw [uniformLaw_event]; have:=goodEvent_half i q N hN;linarith)

lemma law_dom (hN : (N:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ)) :
    ∀ g,((law i q N hN).map (Subtype.val : goodEvent i q N→_)).mass g ≤
      2/(Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ)^N := by
  intro g
  have hh:=uniformLaw_conditioned (goodEvent_half i q N hN) g
  convert hh using 1 <;> simp only [law,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]

variable (h : ∀ z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q),
  k ≤ (flagGraph (ZMod q) (Fin (i+4)→ZMod q) z).indepNum)

def chosen (z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q)) : Fin k↪o Fin N:=
  Classical.choose (independent_selected z (h z))

lemma chosen_consistent (z : Fin N→Flag (ZMod q) (Fin (i+4)→ZMod q)) :
    Consistent (fun j=>z (chosen i q N k h z j)):=Classical.choose_spec (independent_selected z (h z))

def tuple (z : goodEvent i q N) : Fin k→Flag (ZMod q) (Fin (i+4)→ZMod q):=
  fun j=>z.val (chosen i q N k h z.val j.rev)

lemma tuple_occurs (z : goodEvent i q N) : Occurs (reverseTuple (tuple i q N k h z)) z.val := by
  apply (occurs_iff_orderEmbedding _ _).mpr
  refine ⟨chosen i q N k h z.val,?_⟩
  intro j
  simp only [reverseTuple,tuple,Fin.rev_rev]

lemma tuple_consistent (z : goodEvent i q N) :
    ScanConsistent ((List.ofFn (fun j=>flagPair (tuple i q N k h z j))).map toScan) :=
  selected_reverse_consistent z.val (chosen i q N k h z.val) (chosen_consistent i q N k h z.val)

lemma tuple_occupancy (z : goodEvent i q N) :
    ∀ W : Submodule (ZMod q) (Fin (i+4)→ZMod q),
      ((univ.filter (fun j : Fin k=>(flagPair (tuple i q N k h z j)).swap∈
        orthogonalRectangle Projectivization.rep Projectivization.rep W)).card:ℝ) ≤
          occupancyConstant i*log (q:ℝ) := by
  intro W
  let e : Fin k↪Fin N:= (Equiv.toEmbedding (Equiv.ofBijective Fin.rev (by
    constructor
    · intro a b hab;simpa using congrArg Fin.rev hab
    · intro a;exact ⟨a.rev,by simp⟩))).trans (chosen i q N k h z.val).toEmbedding
  have hh:=hits_embedding (rectangle W) z.val e
  have hz : (hits (rectangle W) z.val:ℝ)<occupancyConstant i*log (q:ℝ):=(mem_filter.mp z.property).2 W
  apply le_trans _ hz.le
  convert (Nat.cast_le (α:=ℝ)).mpr hh using 1
  congr 1
  apply congrArg Finset.card
  ext j
  simp only [mem_filter,mem_univ,true_and,rectangle_pair_iff]
  rfl

lemma alphabet_cap {P : ℝ} (hP : 4 ≤ P) (σ : ℝ) (he : exp σ=(q:ℝ)) :
    (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ) ≤
      P*(q:ℝ)^(i+3)*exp (((i+2:ℕ):ℝ)*σ) := by
  have hq : 2 ≤ q:=(Fact.out : q.Prime).two_le
  have hh : Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)) ≤ 4*q^(i+3)*q^(i+2):=by
    rw [actualFlag_card (d:=i+3) (by simp),Nat.card_zmod]
    have h1:=InitialRectangles.sum_powers_le_two hq (show 0 < i+3+1 by omega)
    have h2:=InitialRectangles.sum_powers_le_two hq (show 0 < i+3 by omega)
    have hx:=Nat.mul_le_mul h1 h2
    simp only [Nat.add_sub_cancel,show i+3-1=i+2 by omega] at hx
    exact hx.trans_eq (by ring)
  rw [exp_nat_mul,he]
  have hh' : (Fintype.card (Flag (ZMod q) (Fin (i+4)→ZMod q)):ℝ) ≤ 4*(q:ℝ)^(i+3)*(q:ℝ)^(i+2):=by exact_mod_cast hh
  apply hh'.trans
  gcongr
end
end SharpLogRamsey.InitialExperiment

end

end OAI
