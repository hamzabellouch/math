import OAI.Analysis.TreePotential.TreeTests

namespace OAI

noncomputable section
open Set
open scoped ENNReal
namespace BoundedTreePotentials

section CompletedHeads
open scoped Classical
variable {I : Type*}

def coordinateFunctional (K : TestFamily I) (i : I) : TestCompletion K →L[ℝ] ℝ :=
  completedTestFunctional K ⟨_, K.singleton_mem i⟩

@[simp] lemma coordinateFunctional_coe (K : TestFamily I) (i : I) (x : TestVector K) :
    coordinateFunctional K i (x : TestCompletion K) = (testVectorEquiv K x) i := by
  rw [coordinateFunctional, completedTestFunctional_coe]
  change finitePairing _ ((testVectorEquiv K) x) = _
  convert finitePairing_single_test ((testVectorEquiv K) x) i using 1

def coordinateVector (K : TestFamily I) (i : I) : TestCompletion K :=
  ((testVectorEquiv K).symm (Finsupp.single i 1) : TestVector K)

@[simp] lemma norm_coordinateVector (K : TestFamily I) (i : I) :
    ‖coordinateVector K i‖ = 1 := by
  simp only [coordinateVector, UniformSpace.Completion.norm_coe, norm_test_single]

@[simp] lemma coordinateFunctional_vector (K : TestFamily I) (i j : I) :
    coordinateFunctional K i (coordinateVector K j) = if i = j then 1 else 0 := by
  simp only [coordinateVector, coordinateFunctional_coe, LinearEquiv.apply_symm_apply]
  simp [Finsupp.single_apply, eq_comm]

def completedHead (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] TestCompletion K :=
  ∑ i ∈ B, (coordinateFunctional K i).smulRight (coordinateVector K i)

@[simp] lemma completedHead_apply (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    completedHead K B x = ∑ i ∈ B, coordinateFunctional K i x • coordinateVector K i := by
  simp [completedHead]

lemma coordinate_completedHead (K : TestFamily I) (B : Finset I) (x : TestCompletion K) (i : I) :
    coordinateFunctional K i (completedHead K B x) = if i ∈ B then coordinateFunctional K i x else 0 := by
  simp only [completedHead_apply, map_sum, map_smul, coordinateFunctional_vector, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ B <;> simp [hi]

lemma finiteHead_eq_sum (B : Finset I) (x : I →₀ ℝ) :
    Finsupp.filter (fun i => i ∈ B) x = ∑ i ∈ B, x i • Finsupp.single i 1 := by
  ext j
  simp only [Finsupp.filter_apply
    ]
  by_cases hj : j ∈ B <;> simp [Finsupp.single_apply, hj, eq_comm]

lemma completedHead_coe (K : TestFamily I) (B : Finset I) (x : TestVector K) :
    completedHead K B (x : TestCompletion K) =
      ((testVectorEquiv K).symm (Finsupp.filter (fun i => i ∈ B) (testVectorEquiv K x)) : TestCompletion K) := by
  rw [finiteHead_eq_sum]
  simp only [map_sum, map_smul]
  change completedHead K B (x : TestCompletion K) =
    (UniformSpace.Completion.toComplL : TestVector K →L[ℝ] TestCompletion K) (∑ i ∈ B, (testVectorEquiv K x) i • (testVectorEquiv K).symm (Finsupp.single i 1))
  simp only [map_sum, map_smul, completedHead_apply, coordinateFunctional_coe, coordinateVector]
  rfl

def headCoordinates (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] (B → ℝ) :=
  ContinuousLinearMap.pi (fun i => coordinateFunctional K i.val)

/-- Closed finite-codimensional coordinate tail, with no topological assumption
    on an arbitrary algebraic complement. -/
def coordinateTail (K : TestFamily I) (B : Finset I) : Submodule ℝ (TestCompletion K) :=
  (headCoordinates K B).ker

lemma mem_coordinateTail (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    x ∈ coordinateTail K B ↔ ∀ i ∈ B, coordinateFunctional K i x = 0 := by
  change (headCoordinates K B x = 0) ↔ _
  simp only [headCoordinates, ContinuousLinearMap.pi_apply, funext_iff, Pi.zero_apply, Subtype.forall]

lemma coordinateTail_closed (K : TestFamily I) (B : Finset I) :
    IsClosed (coordinateTail K B : Set (TestCompletion K)) :=
  (headCoordinates K B).isClosed_ker

instance coordinateTail_finiteCodim (K : TestFamily I) (B : Finset I) :
    Module.Finite ℝ (TestCompletion K ⧸ coordinateTail K B) :=
  Module.Finite.equiv (headCoordinates K B).toLinearMap.quotKerEquivRange.symm

def completedTail (K : TestFamily I) (B : Finset I) : TestCompletion K →L[ℝ] TestCompletion K :=
  ContinuousLinearMap.id ℝ (TestCompletion K) - completedHead K B

@[simp] lemma completedTail_apply (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    completedTail K B x = x - completedHead K B x := rfl

lemma completedTail_mem (K : TestFamily I) (B : Finset I) (x : TestCompletion K) :
    completedTail K B x ∈ coordinateTail K B := by
  rw [mem_coordinateTail]
  intro i hi
  simp only [completedTail_apply, map_sub, coordinate_completedHead, ite_eq_left hi, sub_self]

lemma completedTail_eq_self (K : TestFamily I) (B : Finset I) (x : TestCompletion K)
    (hx : x ∈ coordinateTail K B) : completedTail K B x = x := by
  rw [mem_coordinateTail] at hx
  rw [completedTail_apply, completedHead_apply]
  have hz : (∑ i ∈ B, coordinateFunctional K i x • coordinateVector K i) = 0 :=
    Finset.sum_eq_zero (fun i hi => by rw [hx i hi, zero_smul])
  rw [hz, sub_zero]

lemma completedTail_coe (K : TestFamily I) (B : Finset I) (x : TestVector K) :
    completedTail K B (x : TestCompletion K) =
      ((testVectorEquiv K).symm ((testVectorEquiv K x) - Finsupp.filter (fun i => i ∈ B) (testVectorEquiv K x)) : TestCompletion K) := by
  simp only [completedTail_apply, completedHead_coe, map_sub, LinearEquiv.symm_apply_apply,
    UniformSpace.Completion.coe_sub]

/-- Density transfer with a continuous tail projection. -/
lemma completion_norm_pair_bound (K : TestFamily I)
    (P : TestCompletion K →L[ℝ] TestCompletion K) (x : TestVector K) (a b t : ℝ)
    (h : ∀ w : TestVector K, a * ‖x‖ + b * ‖P (w : TestCompletion K)‖ ≤
      (‖(x : TestCompletion K) + t • P (w : TestCompletion K)‖ +
        ‖(x : TestCompletion K) - t • P (w : TestCompletion K)‖) / 2)
    (z : TestCompletion K) :
    a * ‖x‖ + b * ‖P z‖ ≤
      (‖(x : TestCompletion K) + t • P z‖ + ‖(x : TestCompletion K) - t • P z‖) / 2 := by
  have hc := P.continuous
  have hc1 : Continuous (fun z : TestCompletion K => a * ‖x‖ + b * ‖P z‖) :=
    continuous_const.add (continuous_const.mul hc.norm)
  have hc2 : Continuous (fun z : TestCompletion K =>
      (‖(x : TestCompletion K) + t • P z‖ + ‖(x : TestCompletion K) - t • P z‖) / 2) :=
    ((continuous_const.add (hc.const_smul t)).norm.add
      (continuous_const.sub (hc.const_smul t)).norm).div_const 2
  exact UniformSpace.Completion.induction_on z (isClosed_le hc1 hc2) h

end CompletedHeads

namespace TreeCalculus
open scoped Classical

def coordinateHead (r : Bool) (D : Finset Node) : Finset (TreeCoordinate r) :=
  D.subtype (fun s => r = true ∨ s ≠ [])

@[simp] lemma mem_coordinateHead (r : Bool) (D : Finset Node) (s : TreeCoordinate r) :
    s ∈ coordinateHead r D ↔ s.val ∈ D := by simp [coordinateHead]

def initialHull {r : Bool} (x : TreeCoordinate r →₀ ℝ) : Finset Node :=
  insert [] (x.support.biUnion (fun s => s.val.inits.toFinset))

lemma root_mem_initialHull {r : Bool} (x : TreeCoordinate r →₀ ℝ) :
    [] ∈ initialHull x := Finset.mem_insert_self _ _

lemma support_mem_initialHull {r : Bool} (x : TreeCoordinate r →₀ ℝ) (s : TreeCoordinate r)
    (hs : x s ≠ 0) : s.val ∈ initialHull x := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  exact ⟨s, Finsupp.mem_support_iff.mpr hs, by simp⟩

lemma initialHull_initial {r : Bool} (x : TreeCoordinate r →₀ ℝ) :
    Initial (initialHull x : Set Node) := by
  intro s u hs hus
  change s ∈ initialHull x at hs
  rw [initialHull, Finset.mem_insert] at hs
  rcases hs with rfl | hs
  · have hu : u = [] := List.prefix_nil.mp hus
    subst u
    exact root_mem_initialHull x
  · obtain ⟨i, hi, his⟩ := Finset.mem_biUnion.mp hs
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨i, hi, ?_⟩
    exact List.mem_toFinset.mpr ((List.mem_inits u i.val).mpr (hus.trans ((List.mem_inits s i.val).mp (List.mem_toFinset.mp his))))

lemma paired_vector_inequality {r : Bool} {k : QuadraticKind} {D : Set Node}
    (hD : Initial D) (hroot : [] ∈ D)
    (x y : TestVector (treeTestFamily r k))
    (hx : ∀ s, (testVectorEquiv _ x) s ≠ 0 → s.val ∈ D)
    (hy : ∀ s, s.val ∈ D → (testVectorEquiv _ y) s = 0)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * ‖x‖ + (t * θ / 2) * ‖y‖ ≤ (‖x + t • y‖ + ‖x - t • y‖) / 2 := by
  simp only [norm_testVector_equiv, map_add, map_sub, map_smul]
  exact paired_finite_inequality hD hroot _ _ hx hy ha ha1 hθ hθ1 ht hsquare

lemma paired_projected_inequality {r : Bool} {k : QuadraticKind} {D : Finset Node}
    (hD : Initial (D : Set Node)) (hroot : [] ∈ D)
    (x w : TestVector (treeTestFamily r k))
    (hx : ∀ s, (testVectorEquiv _ x) s ≠ 0 → s.val ∈ D)
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * ‖x‖ + (t * θ / 2) * ‖completedTail (treeTestFamily r k) (coordinateHead r D) w‖ ≤
      (‖(x : TestCompletion (treeTestFamily r k)) +
          t • completedTail (treeTestFamily r k) (coordinateHead r D) w‖ +
        ‖(x : TestCompletion (treeTestFamily r k)) -
          t • completedTail (treeTestFamily r k) (coordinateHead r D) w‖) / 2 := by
  rw [completedTail_coe]
  rw [← UniformSpace.Completion.coe_smul, ← UniformSpace.Completion.coe_add,
    ← UniformSpace.Completion.coe_sub]
  simp only [UniformSpace.Completion.norm_coe]
  apply paired_vector_inequality hD hroot _ _ hx ?_ ha ha1 hθ hθ1 ht hsquare
  intro s hs
  simp only [LinearEquiv.apply_symm_apply, Finsupp.sub_apply, Finsupp.filter_apply]
  rw [ite_eq_left ((mem_coordinateHead r D s).mpr hs), sub_self]

/-- The paired inequality on the actual completion. Finite tails are obtained
    by applying a continuous finite-coordinate tail projection to dense arrays. -/
theorem paired_completed_inequality {r : Bool} {k : QuadraticKind} {D : Finset Node}
    (hD : Initial (D : Set Node)) (hroot : [] ∈ D)
    (x : TestVector (treeTestFamily r k)) (y : TestCompletion (treeTestFamily r k))
    (hx : ∀ s, (testVectorEquiv _ x) s ≠ 0 → s.val ∈ D)
    (hy : y ∈ coordinateTail (treeTestFamily r k) (coordinateHead r D))
    {a θ t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/2)
    (ht : 0 ≤ t) (hsquare : a^2 + θ^2 ≤ 1) :
    a * ‖x‖ + (t * θ / 2) * ‖y‖ ≤
      (‖(x : TestCompletion (treeTestFamily r k)) + t • y‖ +
        ‖(x : TestCompletion (treeTestFamily r k)) - t • y‖) / 2 := by
  have h := completion_norm_pair_bound (treeTestFamily r k)
    (completedTail (treeTestFamily r k) (coordinateHead r D)) x a (t*θ/2) t
    (fun w => paired_projected_inequality hD hroot x w hx ha ha1 hθ hθ1 ht hsquare) y
  simpa only [completedTail_eq_self _ _ y hy] using h

end TreeCalculus


end BoundedTreePotentials

end

end OAI
