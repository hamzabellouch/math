import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.ThreeCoordinateCertified

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] [Fintype Ω]

abbrev GeneralReversedTape (Ω : Type*) (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype (ℙ K (Dual K V))] (H : ℕ) (q : ℝ) :=
  Ω × UniversalFresh (ℙ K (Dual K V)) H q
abbrev GeneralReversedMessage (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (H : ℕ) (q : ℝ) (t : GeneralReversedTape Ω K V H q) :=
  (m : M t.1) × UniversalFreshMessage (dec t.1 m) H q
noncomputable def generalReversedDecoded (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (U : Finset (ℙ K V)) (H : ℕ) (q : ℝ) (t : GeneralReversedTape Ω K V H q)
    (m : GeneralReversedMessage M dec H q t) : Finset (ℙ K V) :=
  U∩universalFreshDecoded Incident (dec t.1 m.1) H q t.2 m.2
noncomputable def generalReversedEncoded (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (t : GeneralReversedTape Ω K V H q) :
    Option (GeneralReversedMessage M dec H q t) :=
  (enc t.1).bind fun m=>if _hv : CaptureBound T UT c MB (dec t.1 m) then
    (universalFreshEncoded Incident S U (T∩dec t.1 m) (dec t.1 m) Finset.inter_subset_right H n q MA t.2).map
      (fun f=>⟨m,f⟩) else none
noncomputable def generalReversedCost (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (cost : ∀t,M t→ℝ) (H : ℕ) (q : ℝ) (t : GeneralReversedTape Ω K V H q)
    (m : GeneralReversedMessage M dec H q t) : ℝ :=
  cost t.1 m.1+universalFreshCost (dec t.1 m.1) H q m.2

omit [Finite K] [FiniteDimensional K V] [Fintype Ω] in
lemma generalReversed_exact (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (hc : 0<c)
    (t : GeneralReversedTape Ω K V H q) :
    (generalReversedEncoded M dec enc S U T UT H n q MA MB c t).map
      (generalReversedDecoded M dec U H q t)=
    publicGeneralReverseResult S U T UT hT H n q MA MB c hc ((enc t.1).map (dec t.1)) t.2 := by
  cases h : enc t.1 with
  | none => simp [generalReversedEncoded,h,publicGeneralReverseResult]
  | some m =>
    simp only [generalReversedEncoded,h,Option.bind_some,Option.map_some,publicGeneralReverseResult]
    split_ifs with hv
    · simp only [Option.map_map,generalReversedDecoded,Function.comp_def]
    · rfl

omit [Finite K] [FiniteDimensional K V] in
theorem generalReversed_law (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (p : Law Ω) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (hT : T.Nonempty) (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (hc : 0<c) :
    map (adaptiveLaw p (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q))
      (fun t=>(generalReversedEncoded M dec enc S U T UT H n q MA MB c t).map
        (generalReversedDecoded M dec U H q t))=
    optionCompose (map p (fun t=>(enc t).map (dec t)))
      (generalNextCapLaw S U T UT hT c hc n q MA MB) := by
  simp only [generalReversed_exact M dec enc S U T UT hT H n q MA MB c hc]
  rw [optionCompose_eq_second _ (generalNextCapLaw S U T UT hT c hc n q MA MB) (by rfl)]
  exact public_composition p (universalFreshLaw (ℙ K (Dual K V)) H q)
    (fun t=>(enc t).map (dec t))
    (publicGeneralReverseResult S U T UT hT H n q MA MB c hc)
    (generalNextCapLaw S U T UT hT c hc n q MA MB)
    (fun Y=>publicGeneralReverseResult_law S U T UT hT H n q MA MB c hc Y)

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype Ω] in
lemma generalReversed_prefixes (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (S U : Finset (ℙ K V)) (T UT : Finset (ℙ K (Dual K V)))
    (H : ℕ) (n : Fin (H+1)) (q MA MB c : ℝ) (t : GeneralReversedTape Ω K V H q)
    (m : GeneralReversedMessage M dec H q t)
    (hm : generalReversedEncoded M dec enc S U T UT H n q MA MB c t=some m) :
    enc t.1=some m.1 ∧ CaptureBound T UT c MB (dec t.1 m.1) ∧
      universalFreshEncoded Incident S U (T∩dec t.1 m.1) (dec t.1 m.1) Finset.inter_subset_right
        H n q MA t.2=some m.2 := by
  unfold generalReversedEncoded at hm
  cases hb : enc t.1 with
  | none => simp [hb] at hm
  | some b =>
    rw [hb] at hm
    change (if _hv : CaptureBound T UT c MB (dec t.1 b) then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨f,hf,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hv,hf⟩

omit [Fintype Ω] in
theorem generalReversed_cost (M : Ω→Type*) (dec : ∀t,M t→Finset (ℙ K (Dual K V)))
    (enc : ∀t,Option (M t)) (cost : ∀t,M t→ℝ)
    (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) (hdim : finrank K V≤5)
    (S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (T UT : Finset (ℙ K (Dual K V))) (hT : T.Nonempty)
    (P c B MA : ℝ) (hP : 1≤P) (hc : 0<c) (hc1 : c≤1) (hB : 0≤B)
    (hn : reverseLength (Nat.card K) (Real.log ((U.card:ℝ)/S.card))≤1000*(Nat.card K)^2)
    (t : GeneralReversedTape Ω K V (1000*(Nat.card K)^2) (Nat.card K))
    (m : GeneralReversedMessage M dec (1000*(Nat.card K)^2) (Nat.card K) t)
    (hm : generalReversedEncoded M dec enc S U T UT _ ⟨_,Nat.lt_succ_of_le hn⟩
      (Nat.card K) MA ((T.card:ℝ)*Real.exp (B*P)) c t=some m) :
    generalReversedCost M dec cost (1000*(Nat.card K)^2) (Nat.card K) t m≤
      cost t.1 m.1+(1010+21*(B-Real.log c))*(Nat.card K:ℝ)*P*
        (Real.log ((U.card:ℝ)/S.card)+P) := by
  let : Finite V := Module.finite_of_finite K
  let : Fintype V := Fintype.ofFinite _
  obtain ⟨hb,hv,hf⟩ := generalReversed_prefixes M dec enc S U T UT _ _ _ _ _ _ t m hm
  have hcost := general_reverse_message_cost σ hσ hq hdim S U hS hSU T UT (dec t.1 m.1) hT
    c B P hc hc1 hB hP hv
  have hh := universalFresh_cost_exact Incident S U (T∩dec t.1 m.1) (dec t.1 m.1)
    Finset.inter_subset_right _ _ _ MA t.2 m.2 hf
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  unfold generalReversedCost
  rw [hh]
  dsimp only at hcost
  linarith
end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining Metadata FiniteEntropy ReverseCap
open scoped Classical LinearAlgebra.Projectivization NNReal

structure FinitePredictor (A B : Type) [Fintype A] [Fintype B] where
  Tape : Type
  tapeFintype : Fintype Tape
  Message : Tape→Type
  messageFintype : ∀t,Fintype (Message t)
  tapeLaw : @Law Tape tapeFintype
  decoded : ∀t,Message t→Finset A
  encoded : Finset A→Finset B→∀t,Option (Message t)
  cost : ∀t,Message t→ℝ
attribute [instance] FinitePredictor.tapeFintype FinitePredictor.messageFintype

noncomputable def FinitePredictor.output {A B : Type} [Fintype A] [Fintype B]
    (p : FinitePredictor A B) (S : Finset A) (T : Finset B) : Law (Option (Finset A)) :=
  map p.tapeLaw (fun t=>(p.encoded S T t).map (p.decoded t))

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable instance {K : Type} [Field K] [Finite K] [Fintype K]
    [Fintype (ℙ K (Fin 4→K))] [Fintype (ℙ K (Dual K (Fin 4→K)))]
    [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K A)]
    [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K A))]
    [∀ A : Submodule K (Fin 4→K),Fintype (ℙ K (Dual K (Dual K A)))]
    (U : Finset (ℙ K (Fin 4→K))) (UT : Finset (ℙ K (Dual K (Fin 4→K))))
    (σ P τ : ℝ) (br : ThreePublicIndex K σ) (t : ThreeLocalTape U UT σ P τ br) :
    Fintype (ThreeLocalMessage U UT σ P τ br t) := by
  rcases br with b|b
  · dsimp only [ThreeLocalMessage];infer_instance
  · rcases b with b|b <;> dsimp only [ThreeLocalMessage] <;> infer_instance

noncomputable def threeFinitePredictor (hd : finrank K V=4) (σ : ℝ)
    (U : Finset (ℙ K V)) (UT : Finset (ℙ K (Dual K V)))
    (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0) : FinitePredictor (ℙ K V) (ℙ K (Dual K V)) := by
  letI : Fintype K := Fintype.ofFinite _
  letI : Finite (Dual K (Fin 4→K)) := Module.finite_of_finite K
  letI : Fintype (ℙ K (Fin 4→K)) := Fintype.ofFinite _
  letI : Fintype (ℙ K (Dual K (Fin 4→K))) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 4→K)) : Finite (Dual K A) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 4→K)) : Finite (Dual K (Dual K A)) := Module.finite_of_finite K
  letI (A : Submodule K (Fin 4→K)) : Fintype (ℙ K A) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K A)) := Fintype.ofFinite _
  letI (A : Submodule K (Fin 4→K)) : Fintype (ℙ K (Dual K (Dual K A))) := Fintype.ofFinite _
  let e := LinearEquiv.ofFinrankEq V (Fin 4→K) (by rw [Module.finrank_pi,Fintype.card_fin,hd])
  exact {
    Tape := ThreeCoordinateTape e U UT σ P τ
    tapeFintype := inferInstance
    Message := ThreeCoordinateMessage e U UT σ P τ
    messageFintype := fun _=>inferInstance
    tapeLaw := threeCoordinatePublicLaw e U UT σ P τ R L₀
    decoded := threeCoordinateDecoded e U UT σ P τ
    encoded := fun S T=>threeCoordinateEncoded e S U T UT σ P τ R L₀
    cost := threeCoordinateCost e U UT σ P τ }
end SharpRamseyFive.ScoreGeometry

end OAI
