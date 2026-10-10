import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.BaseMessageCost
import OAI.Combinatorics.RamseyFive.Geometry.TwoFinitePublic

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def baseFiniteCost (U : Finset (ℙ K V)) (P τ : ℝ) (m : BaseMessage U P τ) : ℝ :=
  Real.log (Fintype.card (ℙ K V)+1:ℝ)+Real.log (Fintype.card (baseAlphabet U m.1 P τ):ℝ)

omit [Finite K] [FiniteDimensional K V] in
lemma baseFinite_sound (S U : Finset (ℙ K V)) (P τ : ℝ)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) :
    ValidCap S U ((S.card:ℝ)*Real.exp (2*P)) (t m) := by
  obtain ⟨m',hm',he⟩ := Option.map_eq_some_iff.mp hm
  unfold baseTableEncoded at hm'
  have hs := chooseMessage_sound _ t m' hm'
  simpa only [he,ValidCap,Finset.inter_comm] using hs

omit [FiniteDimensional K V] in
theorem baseFinite_cost (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1)
    (t : BaseTable U P τ) (m : BaseMessage U P τ)
    (hm : baseFiniteEncoded S U P τ t=some m) :
    baseFiniteCost U P τ m≤110*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+P) := by
  unfold baseFiniteCost
  rw [baseFinite_header S U P τ t m hm]
  exact baseMessage_cost hdim S U hS hSU P τ hP hτ hτ1
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def reversedBaseCost (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : ReversedBaseTape UT P τ H q)
    (m : ReversedBaseMessage UT P τ H q t) : ℝ :=
  baseFiniteCost UT P τ m.1+universalFreshCost (t.1 m.1) H q m.2

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] in
lemma reversedBase_prefixes (S U : Finset (ℙ K V))
    (T UT : Finset (ℙ K (Dual K V))) (P τ : ℝ) (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (t : ReversedBaseTape UT P τ H q) (m : ReversedBaseMessage UT P τ H q t)
    (hm : reversedBaseEncoded S U T UT P τ H n q MA MB t=some m) :
    baseFiniteEncoded T UT P τ t.1=some m.1 ∧
      universalFreshEncoded Incident S U (T∩t.1 m.1) (t.1 m.1) Finset.inter_subset_right
        H n q MA t.2=some m.2 := by
  unfold reversedBaseEncoded at hm
  cases hb : baseFiniteEncoded T UT P τ t.1 with
  | none => simp [hb] at hm
  | some b =>
    rw [hb] at hm
    change (if _hv : ValidCap T UT MB (t.1 b) then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hf⟩

theorem reversedBase_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (hTU : T⊆UT)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) (MA : ℝ)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2)
    (t : ReversedBaseTape UT P τ (1000*(Nat.card K)^2) (Nat.card K))
    (m : ReversedBaseMessage UT P τ (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : reversedBaseEncoded S U T UT P τ (1000*(Nat.card K)^2) ⟨_,Nat.lt_succ_of_le hn⟩
      (Nat.card K) MA ((T.card:ℝ)*Real.exp (2*P)) t=some m) :
    reversedBaseCost UT P τ (1000*(Nat.card K)^2) (Nat.card K) t m≤
      1200*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  obtain ⟨hb,hf⟩ := reversedBase_prefixes S U T UT P τ _ _ _ _ _ t m hm
  have hbase := baseFinite_cost (K:=K) (V:=Dual K V) (by simpa using hdim)
    T UT hT hTU P τ hP hτ hτ1 t.1 m.1 hb
  have hvalid := baseFinite_sound T UT P τ t.1 m.1 hb
  have hc : CaptureBound T UT (9/10) ((T.card:ℝ)*Real.exp (2*P)) (t.1 m.1) := hvalid
  have hcost := general_reverse_message_cost σ hσ hq (by omega : finrank K V≤5)
    S U hS hSU T UT (t.1 m.1) hT (9/10) 2 P (by norm_num) (by norm_num) (by norm_num) hP hc
  have hh := universalFresh_cost_exact Incident S U (T∩t.1 m.1) (t.1 m.1)
    Finset.inter_subset_right _ _ _ MA t.2 m.2 hf
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<9/10)
  norm_num at hlog
  have hcst : 1010+21*((2:ℝ)-Real.log (9/10))≤1080 := by linarith
  have hgs := (projective_enclosure_gap σ hq (by omega : finrank K V≤5) S U hS hSU).1
  have hgt := (projective_enclosure_gap σ hq (by simpa using (show finrank K V≤5 by omega)) T UT hT hTU).1
  have hpq : 0≤(Nat.card K:ℝ)*P := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcst hpq) (show 0≤Real.log ((U.card:ℝ)/S.card)+P by linarith)
  unfold reversedBaseCost
  rw [hh]
  dsimp only at hcost
  nlinarith [mul_nonneg hpq hgs,mul_nonneg hpq hgt,mul_nonneg hpq (show 0≤P by linarith)]
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap Filter ParameterHierarchy
open scoped Classical LinearAlgebra.Projectivization NNReal Topology
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

noncomputable def twoPublicCost (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (H : ℕ) (q : ℝ) (t : TwoPublicTape U UT P τ H q) :
    TwoPublicMessage U UT P τ H q t→ℝ
  | Sum.inl m => Real.log 2+baseFiniteCost U P τ m
  | Sum.inr m => Real.log 2+reversedBaseCost UT P τ H q t.2 m

theorem twoPublic_cost (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hdim : finrank K V=3)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty) (hTU : T⊆UT)
    (P τ : ℝ) (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1) (MA : ℝ)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2)
    (t : TwoPublicTape U UT P τ (1000*(Nat.card K)^2) (Nat.card K))
    (m : TwoPublicMessage U UT P τ (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : twoPublicEncoded S U T UT P τ (1000*(Nat.card K)^2) ⟨_,Nat.lt_succ_of_le hn⟩
      (Nat.card K) MA ((T.card:ℝ)*Real.exp (2*P)) t=some m) :
    twoPublicCost U UT P τ (1000*(Nat.card K)^2) (Nat.card K) t m≤
      1300*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/S.card)+Real.log ((UT.card:ℝ)/T.card)+P) := by
  let gS := Real.log ((U.card:ℝ)/S.card)
  let gT := Real.log ((UT.card:ℝ)/T.card)
  have hgs : 0≤gS := Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hS.card_pos)).mpr
    (by simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU)))
  have hgt : 0≤gT := Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hT.card_pos)).mpr
    (by simpa using (show (T.card:ℝ)≤UT.card by exact_mod_cast Finset.card_le_card hTU)))
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Nat.card_pos (α:=K))
  have hqp : 1≤(Nat.card K:ℝ)*P := one_le_mul_of_one_le_of_one_le hq1 hP
  have hall : 1≤(Nat.card K:ℝ)*P*(gS+gT+P) := one_le_mul_of_one_le_of_one_le hqp (by linarith)
  have ht := mul_nonneg (show 0≤(Nat.card K:ℝ)*P by linarith) hgt
  have hl : Real.log 2≤1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2);norm_num at this;exact this
  unfold twoPublicEncoded at hm
  split_ifs at hm with hST
  · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    have hc := baseFinite_cost hdim S U hS hSU P τ hP hτ hτ1 t.1 b hb
    change Real.log 2+baseFiniteCost U P τ b≤1300*(Nat.card K:ℝ)*P*(gS+gT+P)
    change _≤110*(Nat.card K:ℝ)*P*(gS+P) at hc
    nlinarith
  · obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    have hc := reversedBase_cost σ hσ hq hdim S U hS hSU T UT hT hTU P τ hP hτ hτ1 MA hn t.2 b hb
    change Real.log 2+reversedBaseCost UT P τ _ _ t.2 b≤1300*(Nat.card K:ℝ)*P*(gS+gT+P)
    change _≤1200*(Nat.card K:ℝ)*P*(gS+gT+P) at hc
    nlinarith
end SharpRamseyFive.ScoreGeometry

end OAI
