import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailWeights
import OAI.NumberTheory.DirichletL.Inversion.InitialHighFrequencyTailKernel

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialHighFrequencyTail
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialPhysicalMeasure
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def sourceKey (x : Point ι) : Fin 5→Finset ι :=
  ![x.common,x.divisor,x.overlap,x.left,x.right]

def sourcePoint (k : Fin 5→Finset ι) (h : O) : Point ι :=
  ⟨k 0,k 1,k 2,k 3,k 4,h⟩

omit [DecidableEq ι] in
theorem sourcePoint_key (x : Point ι) : sourcePoint (sourceKey x) x.frequency=x := by
  cases x
  rfl

def sourceKeys (S : Finset (Point ι)) : Finset (Fin 5→Finset ι) := S.image sourceKey

def sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) : Finset O :=
  (S.filter (fun x=>sourceKey x=k)).image Point.frequency

theorem mem_sourceFrequencies (S : Finset (Point ι)) (k : Fin 5→Finset ι) (h : O) :
    h∈sourceFrequencies S k ↔ sourcePoint k h∈S := by
  constructor
  · intro hh
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hh
    obtain ⟨hx,hk⟩ := Finset.mem_filter.mp hx
    rw [←hk,←he,sourcePoint_key]
    exact hx
  · intro hh
    apply Finset.mem_image.mpr
    refine ⟨sourcePoint k h,Finset.mem_filter.mpr ⟨hh,?_⟩,rfl⟩
    funext i
    fin_cases i <;> rfl

theorem source_sum_fibers (S : Finset (Point ι)) (f : Point ι→ℂ) :
    ∑x∈S,f x = ∑k∈sourceKeys S,∑h∈sourceFrequencies S k,f (sourcePoint k h) := by
  rw [←Finset.sum_fiberwise_of_maps_to (s:=S) (t:=sourceKeys S) (g:=sourceKey)
    (fun x hx=>Finset.mem_image.mpr ⟨x,hx,rfl⟩) f]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sourceFrequencies,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [←(Finset.mem_filter.mp hx).2,sourcePoint_key]
  · intro x hx y hy hxy
    have hk := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
    rw [←sourcePoint_key x,←sourcePoint_key y,hk,hxy]

theorem sourceKeys_card
    (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (S : Finset (Point ι)) (L : ℝ) (hL : 1≤L)
    (hpool : ∀x∈S,∀i,sourceKey x i⊆pool)
    (hnorm : ∀x∈S,∀i,primeProductNorm p (sourceKey x i)≤L) :
    ((sourceKeys S).card:ℝ)≤(128*L)^5 := by
  let T := boundedPrimeSupports p pool L
  have hsub : sourceKeys S⊆Fintype.piFinset (fun _ : Fin 5=>T) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hk
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hpool x hx i),hnorm x hx i⟩
  have hc := Finset.card_le_card hsub
  have hcast : ((sourceKeys S).card:ℝ)≤(T.card:ℝ)^5 := by
    exact_mod_cast (by simpa using hc)
  exact hcast.trans (pow_le_pow_left₀ (by positivity)
    (boundedPrimeSupports_card p hinj pool L hL) 5)

end SevenEighths.InverseInitialHighFrequencyTail

end

end OAI
