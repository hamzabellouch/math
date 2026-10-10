import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.SurvivingWindowCode
import OAI.Combinatorics.RamseyFive.Entropy.WindowTargetInputs

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance (priority := high) winRetPropDE (P : Prop) : Decidable P := Classical.propDecidable P
local instance winRetBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance winRetIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

lemma double_error_bound (a b c d e : ℝ) (ha : a≤c) (hb : b≤c) :
    a+b+d+e≤2*c+d+e := by linarith

theorem eventually_window_target_retention {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0 ≤ Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k s d ε C₀ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3 ≤ Nat.card K) (w n : ℕ) [Nonempty (Fin n)]
      (I : Type) [Fintype I] [DecidableEq I] [Preorder I]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
      (sel : Fin w×Bool→Fin n) (e : I→Fin w) (he : Monotone e)
      (W : ReciprocalWindows p u sel e s)
      (hcons : ∀ x,0<p x → ∀ i j,slotEmbedding i<slotEmbedding j →
        Incident (x i).1 (x j).2 → Incident (x j).1 (x i).2)
      (hA : ∀ i,((support (first (map p (fun x=>x i)))).card:ℝ) ≤
        32*Real.exp (5*Real.log (Nat.card K)-u i))
      (hB : ∀ i,((support (second (map p (fun x=>x i)))).card:ℝ) ≤32*Real.exp (u i))
      (hflag : ∀ i,((support (map p (fun x=>x i))).card:ℝ) ≤C₀*(Nat.card K:ℝ)^4)
      (hgood : ∀ i,indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (earlySlot sel (e i))=0)
      (hdrop : ∀ i,u (earlySlot sel (e i))-u (lateSlot sel (e i)) ≤ k)
      (hσ : 1 ≤ σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀ → Range η σ D R → (L₀:ℝ)=L η σ D →
      0<s → 0 ≤ ε → 0 ≤ k+2*s+Real.log 4 →
      k+2*s+Real.log 4 ≤ Cb*D*σ^(6*beta η) →
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (tree : BinaryTree I),Ordered tree → ∀ (j : Address tree) (t : Fin (2*n)),
      indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (middleSlot (e (label tree j)) t)=0 →
      orientedTargetFailure f r σ hσ hq hd.le
        (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
        W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty
        p (fun x=>(x (middleSlot (e (label tree j)) t)).1)
          (fun x=>(x (middleSlot (e (label tree j)) t)).2)
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) tree j ≤
      2*reciprocalBadMass s d C₀+
      tree.height*(20*tree.height*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)^2*(320016*ε)+((Nat.card K:ℝ)/(σ^(-1000*beta η)))*
        (4*Real.exp 1)^2*(320016*ε)+5*Real.exp (-(Nat.card K:ℝ)))+
      (20*tree.height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)*(160008*ε) := by
  filter_upwards [eventually_ordered_target_retention hη hη' Cb hCb] with σ hh
  intro D k s d ε C₀ R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 w n _ I _ _ _
    p u sel e he W hcons hA hB hflag hgood hdrop hσ hq hcard hr hL hs hε hb hbhi
  dsimp only
  intro tree hord j t ht
  have hbad:=window_bad_target p u sel (e (label tree j)) t s d ε C₀ hs
    (hA _) (hB _) (hflag _) ht
  have hright (i : I) (hi : label tree j ≤ i) :=
    W.target_right_sparse hd he d ε hcons (label tree j) i hi t ht
  have hleft (i : I) (hi : i ≤ label tree j) :=
    W.target_left_sparse hd he d ε hcons i (label tree j) hi t ht
  simp only [←map_first_value,←map_second_value] at hright hleft
  have hh':=hh D (k+2*s+Real.log 4) R L₀ q₀ K V hd hq3 I
    (fun _=>Finset (ℙ K V)) (fun _=>Finset (ℙ K (Dual K V)))
    (fun i=>(W.early i).firstLaw) (fun i=>(W.late i).secondLaw)
    W.firstSupport W.secondSupport W.first_nonempty W.second_nonempty
    W.firstReference W.secondReference (4*Real.exp 1) (320016*ε)
    (by positivity) (by positivity) W.first_domination W.second_domination
    (W.reference_sparse hd he d ε hcons hgood) hσ hq hcard hr hL hb hbhi
    (W.support_product k hdrop) tree hord j _ p
    (fun x=>(x (middleSlot (e (label tree j)) t)).1)
    (fun x=>(x (middleSlot (e (label tree j)) t)).2)
    (fun a=>a∈reciprocalGoodA (map p (fun x=>x (middleSlot (e (label tree j)) t)))
      (u (middleSlot (e (label tree j)) t)) s)
    (fun b=>b∈reciprocalGoodB (map p (fun x=>x (middleSlot (e (label tree j)) t)))
      (u (middleSlot (e (label tree j)) t)) s)
    (160008*ε) (by positivity) hright hleft
  apply hh'.trans
  apply double_error_bound
  · convert hbad.1 using 1
    congr 2
  · convert hbad.2 using 1
    congr 2

end
end

open Module SharpRamseyFive.FiniteEntropy SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.Windows
open ReverseCap ScoreGeometry BinaryTree TreeCodec PivotTree Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal Topology
noncomputable section
local instance survRetPropDE (P : Prop) : Decidable P := Classical.propDecidable P
local instance survRetBDE (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance survRetIDE (w n : ℕ) : DecidableEq (Slots w n) := Classical.decEq _

theorem eventually_surviving_target_retention {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D k s d ε C₀ : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q₀ : ℕ) (K V : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))],
    ∀ (hd : finrank K V=5) (hq3 : 3≤Nat.card K) (w n : ℕ) [Nonempty (Fin n)]
      (p : Law (Slots w n→FlagPair K V)) (u : Slots w n→ℝ)
      (sel : Fin w×Bool→Fin n) (E : Finset (Fin w)) (hE : E.Nonempty)
      (W : ReciprocalWindows p u sel (survivingOriginal E hE) s)
      (hcons : ∀x,0<p x→∀i j,slotEmbedding i<slotEmbedding j→
        Incident (x i).1 (x j).2→Incident (x j).1 (x i).2)
      (hinc : ∀x,0<p x→∀i,Incident (x i).1 (x i).2)
      (hA : ∀i,((support (first (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (5*Real.log (Nat.card K)-u i))
      (hB : ∀i,((support (second (map p (fun x=>x i)))).card:ℝ)≤32*Real.exp (u i))
      (hflag : ∀i,((support (map p (fun x=>x i))).card:ℝ)≤C₀*(Nat.card K:ℝ)^4)
      (hgood : ∀v∈E,indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (earlySlot sel v)=0)
      (hdrop : ∀v∈E,u (earlySlot sel v)-u (lateSlot sel v)≤k)
      (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K),
      Nat.card K=q₀→Range η σ D R→(L₀:ℝ)=L η σ D→
      0<s→0≤ε→0≤k+2*s+Real.log 4→k+2*s+Real.log 4≤Cb*D*σ^(6*beta η)→
      let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
        (P η σ D R) (σ^(-800*beta η)) R L₀
      let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
        (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
        (P η σ D R) (σ^(-800*beta η)) R L₀
      ∀ (v : Fin w) (hv : v∈E) (t : Fin (2*n)),
      indexBad (4*Real.log (Nat.card K)) d ε p
        (orderedCollision p (slotEquiv w n) u s) sel (middleSlot v t)=0→
      survivingTargetFailure f r p u sel E hE W σ hσ hq hd.le
        (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) v t≤
      2*reciprocalBadMass s d C₀+
      (finiteBalanced E.card).height*(20*(finiteBalanced E.card).height*
        (50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)^2*(320016*ε)+((Nat.card K:ℝ)/(σ^(-1000*beta η)))*
        (4*Real.exp 1)^2*(320016*ε)+5*Real.exp (-(Nat.card K:ℝ)))+
      (20*(finiteBalanced E.card).height+2)*(50*(Nat.card K:ℝ)/(9*((9/100000)*(9/10))))*
        (4*Real.exp 1)*(160008*ε) := by
  filter_upwards [eventually_window_target_retention hη hη' Cb hCb] with σ hh
  intro D k s d ε C₀ R L₀ q₀ K V _ _ _ _ _ _ _ _ _ hd hq3 w n _ p u sel E hE W
    hcons hinc hA hB hflag hgood hdrop hσ hq hcard hr hL hs hε hb hbhi
  dsimp only
  intro v hv t ht
  let f := fun C : PivotContext K V=>fourFinitePredictor hd σ C.1 C.2
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let r := fun C : PivotContext K V=>fourFinitePredictor (K:=K) (V:=Dual K V)
    (by simpa using hd) σ C.2 (C.1.map bidualPoint.toEmbedding)
    (P η σ D R) (σ^(-800*beta η)) R L₀
  let j : Fin E.card:=⟨(survivorRank E v).val,survivorRank_mem_lt E v hv⟩
  have heq : survivingOriginal E hE (label (finiteBalanced E.card) ((finiteRankEquiv E.card).symm j))=v := by
    rw [survivingOriginal_address]
    exact survivorRank_original E v hv
  rw [survivingTargetFailure_eq f r p u sel E hE W σ hσ hq hd.le
    (9/100000) (9/10) (σ^(-1000*beta η)) (P η σ D R) (by norm_num) hinc v hv t]
  have hh':=hh D k s d ε C₀ R L₀ q₀ K V hd hq3 w n (Fin (E.card+1)) p u sel
    (survivingOriginal E hE) (survivingOriginal_monotone E hE) W hcons hA hB hflag
    (fun i=>hgood _ (survivingOriginal_mem E hE i))
    (fun i=>hdrop _ (survivingOriginal_mem E hE i)) hσ hq hcard hr hL hs hε hb hbhi
    (finiteBalanced E.card) (finiteBalanced_ordered E.card) ((finiteRankEquiv E.card).symm j) t
  simp only [heq] at hh'
  exact hh' ht
end

end SharpRamseyFive.Marking

end OAI
