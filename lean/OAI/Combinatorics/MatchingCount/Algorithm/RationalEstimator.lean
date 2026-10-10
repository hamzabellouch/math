import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.RationalObservables
import OAI.Combinatorics.MatchingCount.Algorithm.RationalScale

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport

variable {V : Type*} [LinearOrder V]
def sampleAverage {Ω : Type*} {S : ℕ} (f : Ω → ℚ) (x : Fin S → Ω) : ℚ :=
  (∑ i,f (x i))/(S:ℚ)
lemma sampleAverage_cast {Ω : Type*} {S : ℕ} (f : Ω → ℚ) (x : Fin S → Ω) :
    (sampleAverage f x:ℝ)=Enlargement.sampleAverage (fun a=>(f a:ℝ)) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast]
def probeMatrix (z : LogicalEdge V → ℚ) (i j : V) : ℚ :=
  if hij : i=j then 0 else z (pairEdge i j hij)
lemma probeMatrix_cast (z : LogicalEdge V → ℚ) (i j : V) :
    (probeMatrix z i j:ℝ)=Enlargement.probeMatrix (fun e=>(z e:ℝ)) i j := by
  simp only [probeMatrix,Enlargement.probeMatrix]
  split_ifs <;> norm_cast
lemma probeMatrix_symm (z : LogicalEdge V → ℚ) (i j : V) : probeMatrix z i j=probeMatrix z j i := by
  apply Rat.cast_injective (α:=ℝ)
  rw [probeMatrix_cast,probeMatrix_cast,Enlargement.probeMatrix_symm]
def estimateMatrix (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) : ℚ :=
  Counting.upperEstimate D dbar (probeMatrix zbar i j)
lemma estimateMatrix_cast (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    (estimateMatrix D dbar zbar i j:ℝ)=Enlargement.estimateMatrix D dbar (fun e=>(zbar e:ℝ)) i j := by
  rw [estimateMatrix,Counting.upperEstimate_cast,probeMatrix_cast]
  rfl
lemma estimateMatrix_symm (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    estimateMatrix D dbar zbar i j=estimateMatrix D dbar zbar j i := by
  rw [estimateMatrix,estimateMatrix,probeMatrix_symm]
lemma estimateMatrix_bounds (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    Counting.alpha≤estimateMatrix D dbar zbar i j ∧ estimateMatrix D dbar zbar i j≤3 := by
  unfold estimateMatrix Counting.upperEstimate
  split_ifs
  · exact ⟨le_max_left _ _,max_le (by norm_num [Counting.alpha]) (min_le_left _ _)⟩
  · norm_num [Counting.alpha]

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    Fintype (Transport.BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) := Fintype.ofFinite _

def sourceD (K : ℕ) : ℕ :=
  100*Fintype.card (SourceVertex (Fin G.n) K)^2*(100000000*(G.n+1)^4)
omit [Nontrivial (Fin G.n)] in
lemma sourceD_eq (K : ℕ) : sourceD (G:=G) K=Enlargement.sourceD (V:=Fin G.n) K := by
  simp only [sourceD,Enlargement.sourceD,Fintype.card_fin]

def ScaleState.matrix (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) :
    Fin G.n → Fin G.n → ℚ :=
  estimateMatrix (sourceD (G:=G) K)
    (sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x)
    (fun e=>sampleAverage (RationalSource.observableProbe s.activity s.nextActivity K e) x)
lemma ScaleState.matrix_bounds (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) (a b : Fin G.n) :
    Counting.alpha ≤ s.matrix x a b ∧ s.matrix x a b≤3 := estimateMatrix_bounds _ _ _ _ _
lemma ScaleState.matrix_symm (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) (a b : Fin G.n) :
    s.matrix x a b=s.matrix x b a := estimateMatrix_symm _ _ _ _ _
def ScaleState.updateVector (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) : Fin G.n → ℚ :=
  Counting.scalingTrace hn (s.matrix x) G.n
lemma ScaleState.updateVector_bounds (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) (i : Fin G.n) :
    0<s.updateVector hn x i ∧ s.updateVector hn x i≤2 := by
  have h:=(Counting.scalingTrace_invariant hn (s.matrix x) (s.matrix_symm x)
    (fun a b _=>s.matrix_bounds x a b) G.n).1
  exact ⟨h.pos i,h.upper i⟩
def ScaleState.update (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) : ScaleState G (j+1) where
  scale i:=s.scale i*s.updateVector hn x i
  positive i:=mul_pos (s.positive i) (s.updateVector_bounds hn x i).1
  upper i:=by
    rw [pow_succ]
    exact mul_le_mul (s.upper i) (s.updateVector_bounds hn x i).2 (s.updateVector_bounds hn x i).1.le (by positivity)
lemma ScaleState.update_activity (hn : 2≤G.n) (s : ScaleState G j)
    (x : Fin S → RationalSource.Marked s.activity K) :
    (s.update hn x).activity=(fun a b=>s.nextActivity a b*s.updateVector hn x a*s.updateVector hn x b) := by
  funext a b
  simp only [ScaleState.activity,ScaleState.update,ScaleState.nextActivity]
  ring

def ScaleState.ratioEstimate (s : ScaleState G j) (x : Fin S → RationalSource.Marked s.activity K) : ℚ :=
  Counting.ratioEstimate (sampleAverage (RationalSource.observableA s.activity K) x)
    (sampleAverage (RationalSource.observableD s.activity s.nextActivity K) x)

lemma average_A (w : Fin G.n → Fin G.n → ℚ) (K : ℕ)
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableA w K) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableA (fun a b=>(w a b:ℝ)) K) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableA_cast]
lemma average_D (w w₁ : Fin G.n → Fin G.n → ℚ) (K : ℕ)
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableD w w₁ K) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(w a b:ℝ)) (fun a b=>(w₁ a b:ℝ)) K) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableD_cast]
lemma average_Probe (w w₁ : Fin G.n → Fin G.n → ℚ) (K : ℕ) (e : LogicalEdge (Fin G.n))
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableProbe w w₁ K e) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(w a b:ℝ)) (fun a b=>(w₁ a b:ℝ)) K e) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableProbe_cast]
lemma ScaleState.matrix_cast (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    (fun a b=>(s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ))=
      Enlargement.estimateMatrix (sourceD (G:=G) K)
        (Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K) x)
        (fun e=>Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K e) x) := by
  funext a b
  simp only [ScaleState.matrix,estimateMatrix_cast,average_D,average_Probe]
lemma ScaleState.ratioEstimate_cast (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    (s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x):ℝ)=
      RealStage.ratioEstimate
        (Enlargement.sampleAverage (Enlargement.observableA (fun a b=>(s.activity a b:ℝ)) K) x)
        (Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K) x) := by
  simp only [ScaleState.ratioEstimate,Counting.ratioEstimate_cast,average_A,average_D]
end MatchingFPRAS.FiniteTrial

end OAI
