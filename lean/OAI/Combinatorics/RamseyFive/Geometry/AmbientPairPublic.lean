import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.LocalNodeLaw
import OAI.Combinatorics.RamseyFive.Entropy.UniversalFreshCost

namespace OAI


namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
lemma public_joint_composition (p : Law α) (tape : Law β) (firstOut : α→γ)
    (out : γ→β→δ) (next : γ→Law δ)
    (hm : ∀c,map tape (out c)=next c) :
    map (adaptiveLaw p (fun _=>tape)) (fun z=>(firstOut z.1,out (firstOut z.1) z.2))=
      adaptiveLaw (map p firstOut) next := by
  apply Law.ext
  funext cd
  rcases cd with ⟨c,d⟩
  rw [adaptive_output_mass (out:=fun a b=>(firstOut a,out (firstOut a) b))]
  change _=(∑a,if firstOut a=c then p a else 0)*next c d
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : firstOut a=c
  · simp only [hc,ite_true]
    have hs : map tape (fun b=>(c,out c b)) (c,d)=map tape (out c) d := by
      simp only [map,Prod.mk.injEq,true_and]
    rw [hs,hm]
  · simp only [map,Prod.mk.injEq,hc,false_and,ite_false,Finset.sum_const_zero,mul_zero,zero_mul]
end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ProjectiveIncidence
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

noncomputable def publicAmbientSecond (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V)))
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) (t : UniversalFresh (ℙ K (Dual K V)) H q) :
    Option (Finset (ℙ K V)) :=
  match Y with
  | none => none
  | some W => if _hW : ValidCap B UB MB (UB∩W) then
      (universalFreshEncoded Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right H n q MA t).map
        (universalFreshDecoded Incident (UB∩W) H q t)
    else none
omit [Finite K] [FiniteDimensional K V] in
lemma publicAmbientSecond_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty)
    (H : ℕ) (n : Fin (H+1)) (q MA MB : ℝ)
    (Y : Option (Finset (ℙ K (Dual K V)))) :
    map (universalFreshLaw (ℙ K (Dual K V)) H q) (publicAmbientSecond A UA B UB H n q MA MB Y)=
      nextAmbientCapLaw A UA B UB hB n q MA MB Y := by
  cases Y with
  | none => exact map_const _ none
  | some W =>
    change map (universalFreshLaw (ℙ K (Dual K V)) H q)
      (fun t=>if _hW : ValidCap B UB MB (UB∩W) then
        (universalFreshEncoded Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right H n q MA t).map
          (universalFreshDecoded Incident (UB∩W) H q t) else none)=_
    dsimp only [nextAmbientCapLaw]
    split_ifs with hv
    · exact universalFreshEncoded_law Incident A UA (B∩(UB∩W)) (UB∩W) Finset.inter_subset_right
        ((hv.source_nonempty hB).mono Finset.inter_subset_right) H n q MA
    · exact map_const _ none

abbrev AmbientPairTape (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] (H : ℕ) (q : ℝ) :=
  UniversalFresh (ℙ K V) H q × UniversalFresh (ℙ K (Dual K V)) H q
noncomputable def ambientPairTapeLaw (H : ℕ) (q : ℝ) : Law (AmbientPairTape K V H q) :=
  adaptiveLaw (universalFreshLaw (ℙ K V) H q) (fun _=>universalFreshLaw (ℙ K (Dual K V)) H q)
abbrev AmbientPairMessage (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (q : ℝ) (t : AmbientPairTape K V H q) :=
  (m : UniversalFreshMessage W H q) × UniversalFreshMessage
    (UB∩universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m) H q
noncomputable def ambientPairDecoded (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (q : ℝ) (t : AmbientPairTape K V H q) (m : AmbientPairMessage UB W H q t) :
    Finset (ℙ K (Dual K V)) × Finset (ℙ K V) :=
  let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1
  (Y,universalFreshDecoded Incident (UB∩Y) H q t.2 m.2)
noncomputable def ambientPairEncoded (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q) :
    Option (AmbientPairMessage UB W H q t) :=
  (universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1).bind
    fun f=>let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 f
      if _hv : ValidCap B UB MB (UB∩Y) then
        (universalFreshEncoded Incident A UA (B∩(UB∩Y)) (UB∩Y) Finset.inter_subset_right H nA q MA t.2).map
          (fun g=>⟨f,g⟩)
      else none
noncomputable def ambientPairCost (UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (q : ℝ) (t : AmbientPairTape K V H q) (m : AmbientPairMessage UB W H q t) : ℝ :=
  universalFreshCost W H q m.1+
    universalFreshCost (UB∩universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1) H q m.2

omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_exact (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q) :
    (ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t)=
      let Y := (universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1).map
        (universalFreshDecoded (fun b a=>Incident a b) W H q t.1)
      pairOptions (Y,publicAmbientSecond A UA B UB H nA q MA MB Y t.2) := by
  cases hf : universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1 with
  | none => simp [ambientPairEncoded,hf,pairOptions]
  | some f =>
    simp only [ambientPairEncoded,hf,Option.bind_some,Option.map_some,publicAmbientSecond,pairOptions]
    split_ifs <;> simp only [Option.map_none,Option.map_map,ambientPairDecoded,Function.comp_def]

omit [Finite K] [FiniteDimensional K V] in
theorem ambientPair_law (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (W : Finset (ℙ K V)) (hW : W.Nonempty)
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) :
    map (ambientPairTapeLaw (K:=K) (V:=V) H q)
      (fun t=>(ambientPairEncoded A UA B UB W H nA nB q MA MB t).map (ambientPairDecoded UB W H q t))=
    map (adaptiveLaw (ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB q MB)
      (nextAmbientCapLaw A UA B UB hB nA q MA MB)) pairOptions := by
  simp only [ambientPair_exact]
  have hh := public_joint_composition (universalFreshLaw (ℙ K V) H q)
    (universalFreshLaw (ℙ K (Dual K V)) H q)
    (fun t=>(universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t).map
      (universalFreshDecoded (fun b a=>Incident a b) W H q t))
    (publicAmbientSecond A UA B UB H nA q MA MB)
    (nextAmbientCapLaw A UA B UB hB nA q MA MB)
    (publicAmbientSecond_law A UA B UB hB H nA q MA MB)
  rw [universalFreshEncoded_law _ _ _ _ _ _ hW] at hh
  have hm := congrArg (fun p=>map p pairOptions) hh
  simpa only [map_comp,Function.comp_def,ambientPairTapeLaw] using hm

omit [Finite K] [FiniteDimensional K V] in
lemma ambientPair_prefixes (A UA : Finset (ℙ K V))
    (B UB : Finset (ℙ K (Dual K V))) (W : Finset (ℙ K V))
    (H : ℕ) (nA nB : Fin (H+1)) (q MA MB : ℝ) (t : AmbientPairTape K V H q)
    (m : AmbientPairMessage UB W H q t)
    (hm : ambientPairEncoded A UA B UB W H nA nB q MA MB t=some m) :
    universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1=some m.1 ∧
    let Y := universalFreshDecoded (fun b a=>Incident a b) W H q t.1 m.1
    ValidCap B UB MB (UB∩Y) ∧
    universalFreshEncoded Incident A UA (B∩(UB∩Y)) (UB∩Y) Finset.inter_subset_right H nA q MA t.2=some m.2 := by
  unfold ambientPairEncoded at hm
  cases hf : universalFreshEncoded (fun b a=>Incident a b) B UB (A∩W) W Finset.inter_subset_right H nB q MB t.1 with
  | none => simp [hf] at hm
  | some f =>
    rw [hf] at hm
    change (if _hv : ValidCap B UB MB _ then _ else none)=some m at hm
    split_ifs at hm with hv
    obtain ⟨g,hg,he⟩ := Option.map_eq_some_iff.mp hm
    subst m
    exact ⟨rfl,hv,hg⟩
end SharpRamseyFive.ProjectiveIncidence

end OAI
