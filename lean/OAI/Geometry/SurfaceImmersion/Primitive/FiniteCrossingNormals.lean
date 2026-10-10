import OAI.Geometry.SurfaceImmersion.Primitive.LocalCrossingChoice
import OAI.Geometry.SurfaceImmersion.Geometry.FiniteDisjointAdjustment

namespace OAI

/-! Simultaneous normal adjustments at the finitely many later crossings.
Disjoint supports preserve the other curves and the exterior normal exactly. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

theorem finite_crossing_normals {U : Set E} (hU : IsOpen U)
    {n : E → Vec} (hn : ContDiffOn ℝ ∞ n U)
    (hunit : ∀ y ∈ U, n y ⬝ᵥ n y = 1)
    (v : κ → E → Vec) (hv : ∀ k, ContDiffOn ℝ ∞ (v k) U)
    (left right : ι → κ) (x : ι → E) (hx : ∀ i, x i ∈ U)
    (O : ι → Set E) (hO : ∀ i, IsOpen (O i)) (hxo : ∀ i, x i ∈ O i)
    (hdisj : Pairwise fun i j => Disjoint (O i) (O j))
    (C : κ → Set E)
    (hcurves : ∀ i k y, y ∈ O i → y ∈ C k → k = left i ∨ k = right i)
    (hchoice : ∀ i,
      (0 < v (left i) (x i) ⬝ᵥ n (x i) ∧ 0 < v (right i) (x i) ⬝ᵥ n (x i)) ∨
      (0 < v (left i) (x i) ⬝ᵥ v (right i) (x i) ∧
        ∃ w : Vec, n (x i) ⬝ᵥ w = 0 ∧
          0 < v (left i) (x i) ⬝ᵥ w ∧ 0 < v (right i) (x i) ⬝ᵥ w)) :
    ∃ g : E → Vec, ContDiffOn ℝ ∞ g U ∧
      (∀ y ∈ U, g y ⬝ᵥ g y = 1) ∧
      (∀ y ∈ U, (∀ i, y ∉ O i) → g y = n y) ∧
      (∀ k y, y ∈ U → y ∈ C k → n y ≠ -normalize (v k y) →
        g y ≠ -normalize (v k y)) ∧
      (∀ y ∈ U, ∀ w : Vec, w ⬝ᵥ n y = 0 →
        (∀ k, w ⬝ᵥ v k y = 0) → w ⬝ᵥ g y = 0) ∧
      ∀ i, 0 < v (left i) (x i) ⬝ᵥ g (x i) ∧
        0 < v (right i) (x i) ⬝ᵥ g (x i) := by
  classical
  choose f hfs hfu hfe hfl hfr hfn hfp using fun i =>
    local_crossing_adjustment_of_choice hU (hO i) hn (hv (left i)) (hv (right i))
      hunit (hx i) (hxo i) (hchoice i)
  let f' : ι → E → Vec := fun i y => if y ∈ U then f i y else n y
  have hfeq (i : ι) {y : E} (hy : y ∈ U) : f' i y = f i y := by simp only [f',hy,ite_true]
  have hfext : ∀ i ∈ (Finset.univ : Finset ι), ∀ y ∉ O i, f' i y = n y := by
    intro i _ y hy
    by_cases hyU : y ∈ U
    · rw [hfeq i hyU]
      exact hfe i y hyU hy
    · simp only [f',hyU,ite_false]
  have hd : ((Finset.univ : Finset ι) : Set ι).Pairwise fun i j => Disjoint (O i) (O j) :=
    fun i _ j _ hij => hdisj hij
  let g := finiteDisjointAdjustment Finset.univ n f'
  have heq (i : ι) {y : E} (hy : y ∈ U) (hyO : y ∈ O i) : g y = f i y :=
    (finiteDisjointAdjustment_of_mem hd hfext (Finset.mem_univ i) hyO).trans (hfeq i hy)
  have hprop {P : E → Vec → Prop} (hnP : ∀ y ∈ U, P y (n y))
      (hfP : ∀ i y, y ∈ U ∩ O i → P y (f i y)) : ∀ y ∈ U, P y (g y) := by
    apply finiteDisjointAdjustment_property hd hfext hnP
    intro i _ y hy
    rw [hfeq i hy.1]
    exact hfP i y hy
  refine ⟨g,?_,?_,?_,?_,?_,?_⟩
  · apply finiteDisjointAdjustment_smoothOn hn
    intro i _
    apply (hfs i).congr
    intro y hy
    exact hfeq i hy
  · exact hprop (P := fun _ a => a ⬝ᵥ a = 1) hunit (fun i y hy => hfu i y hy.1)
  · intro y _ hy
    exact finiteDisjointAdjustment_of_exterior hfext (fun i _ => hy i)
  · intro k y hy hyC hanti
    apply hprop (P := fun z a => z ∈ C k → n z ≠ -normalize (v k z) → a ≠ -normalize (v k z))
      (fun _ _ _ h => h) ?_ y hy hyC hanti
    intro i z hz hzC hzanti
    rcases hcurves i k z hz.2 hzC with rfl | rfl
    · exact hfl i z hz.1 hzanti
    · exact hfr i z hz.1 hzanti
  · intro y hy w hwn hwv
    exact hprop (P := fun z a => w ⬝ᵥ n z = 0 → (∀ k, w ⬝ᵥ v k z = 0) → w ⬝ᵥ a = 0)
      (fun _ _ h _ => h)
      (fun i z hz h hzv => hfn i z hz.1 w h (hzv (left i))) y hy hwn hwv
  · intro i
    rw [heq i (hx i) (hxo i)]
    exact hfp i

end ClosedSurfaceR4.VelocityFrame

end

end OAI
