import Mathlib
import OAI.Geometry.CAT0Fillings.Slicing.Superlevels
import OAI.Geometry.CAT0Fillings.Slices.BorelAction

namespace OAI

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

def NormalApprox (k : ℕ) (T : Functional X k) : Prop :=
  ∃ C : ℕ, ∃ Ts : ℕ → Functional X k,
    (∀ j, IsIntegral k (Ts j)) ∧
    (∀ j, mass (Ts j) ≤ C) ∧ (∀ j, mass (boundary (Ts j)) ≤ C) ∧
    ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))

lemma normalApprox_of_weak_limit {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {k : ℕ} {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsIntegral k (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundary (Ts j)) ≤ N)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    NormalApprox k T := by
  obtain ⟨C,hC⟩ := exists_nat_gt (max (M : ℝ) N)
  exact ⟨C,Ts,hTs,fun j => (hM j).trans ((le_max_left _ _).trans hC.le),
    fun j => (hN j).trans ((le_max_right _ _).trans hC.le),hlim⟩

noncomputable def denseCurrentTest (k K : ℕ) : ℕ → TestClass (X := X) k K :=
  (exists_dense_seq (TestClass (X := X) k K)).choose

lemma denseCurrentTest_dense {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] (k K : ℕ) : DenseRange (denseCurrentTest (X := X) k K) :=
  (exists_dense_seq (TestClass (X := X) k K)).choose_spec

noncomputable def currentCoordinates (k : ℕ) (T : Functional X k) : (ℕ × ℕ) → ℝ :=
  fun ij => TestClass.eval T (denseCurrentTest k ij.1 ij.2)

noncomputable def normalApproxClosed (k C : ℕ) : Set ((ℕ × ℕ) → ℝ) :=
  closure (currentCoordinates k ''
    {T : Functional X k | IsIntegral k T ∧ mass T ≤ C ∧ mass (boundary T) ≤ C})

lemma lipschitz_of_dense_limit {Z : Type*} [PseudoMetricSpace Z]
    {q : ℕ → Z} (hq : DenseRange q) {f : ℕ → Z → ℝ} {F : Z → ℝ}
    {C : ℝ≥0} (hf : ∀ j, LipschitzWith C (f j)) (hF : Continuous F)
    (hlim : ∀ i, Tendsto (fun j => f j (q i)) atTop (𝓝 (F (q i)))) :
    LipschitzWith C F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact hq.induction_on₂
    (isClosed_le ((hF.comp continuous_fst).dist (hF.comp continuous_snd))
      (continuous_const.mul (continuous_fst.dist continuous_snd)))
    (fun i j => le_of_tendsto ((hlim i).dist (hlim j))
      (Eventually.of_forall fun a => (hf a).dist_le_mul (q i) (q j))) x y

lemma IsMetricCurrent.testClass_lipschitz_zero {T : Functional X 0}
    (hT : IsMetricCurrent T) (M : ℝ≥0) (hM : mass T ≤ M) (K : ℕ) :
    LipschitzWith M (TestClass.eval (K := K) T) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hπ : (fun i => (p.val.2 i : X → ℝ)) = fun i => (q.val.2 i : X → ℝ) :=
    funext fun i => Fin.elim0 i
  have hb : ∀ x, |p.val.1 x - q.val.1 x| ≤ (nndist p q : ℝ≥0) := by
    intro x
    exact (ContinuousMap.dist_apply_le_dist (f := p.val.1) (g := q.val.1) x).trans
      (le_max_left (dist p.val.1 q.val.1) (dist p.val.2 q.val.2))
  have hh := IsMetricCurrent.first_difference_bound hT p.boundedLip q.boundedLip
    (fun i => p.val.2 i) K p.property.2.2 (nndist p q) hb
  have hh' : |T p.val.1 (fun i => p.val.2 i) - T q.val.1 (fun i => q.val.2 i)| ≤
      dist p q * mass T := by
    simpa only [hπ,pow_zero,one_mul,coe_nndist] using hh
  exact hh'.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hM (dist_nonneg : 0 ≤ dist p q))

lemma IsIntegral.uniform_testClass_lipschitz {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) (M N : ℝ≥0)
    (hM : mass T ≤ M) (hN : mass (boundary T) ≤ N) (K : ℕ) :
    LipschitzWith ((K : ℝ≥0)^k*M + k*((K : ℝ≥0)+K)^(k-1)*(K*N+K*M))
      (TestClass.eval (K := K) T) := by
  cases k with
  | zero => simpa using IsMetricCurrent.testClass_lipschitz_zero hT.1 M hM K
  | succ k => simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using
      IntegerRectifiable.testClass_lipschitz hT.2.1 hT.1 hT.2.2.1 M N hM hN K

lemma weak_limit_of_coordinate_limit {k : ℕ}
    {Ts : ℕ → Functional X k} {T : Functional X k}
    (hTs : ∀ j, IsIntegral k (Ts j)) (M N : ℝ≥0)
    (hM : ∀ j, mass (Ts j) ≤ M) (hN : ∀ j, mass (boundary (Ts j)) ≤ N)
    (hOff : ∀ b π, ¬Admissible b π → T b π = 0)
    (hCont : ∀ K, Continuous (TestClass.eval (K := K) T))
    (hlim : Tendsto (fun j => currentCoordinates k (Ts j)) atTop
      (𝓝 (currentCoordinates k T))) :
    ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π)) := by
  have hall (K : ℕ) (p : TestClass (X := X) k K) :
      Tendsto (fun j => TestClass.eval (Ts j) p) atTop (𝓝 (TestClass.eval T p)) := by
    let C : ℝ≥0 := (K : ℝ≥0)^k*M +
      k*((K : ℝ≥0)+K)^(k-1)*(K*N+K*M)
    have hL (j : ℕ) : LipschitzWith C (TestClass.eval (K := K) (Ts j)) :=
      IsIntegral.uniform_testClass_lipschitz (hTs j) M N (hM j) (hN j) K
    have hd (i : ℕ) : Tendsto
        (fun j => TestClass.eval (Ts j) (denseCurrentTest k K i)) atTop
        (𝓝 (TestClass.eval T (denseCurrentTest k K i))) :=
      tendsto_pi_nhds.mp hlim (K,i)
    have hLT := lipschitz_of_dense_limit (denseCurrentTest_dense k K) hL (hCont K) hd
    exact tendsto_of_lipschitz_dense hL hLT (denseCurrentTest_dense k K) hd p
  have hcur j : IsMetricCurrent (Ts j) := by
    cases k <;> exact (hTs j).1
  intro b π
  by_cases hab : Admissible b π
  · obtain ⟨K,p,hb,hπ⟩ := admissible_mem_testClass hab
    simpa only [TestClass.eval,hb,hπ] using hall K p
  · simpa only [(fun j => (hcur j).offDomain b π hab),hOff b π hab] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem normalApprox_iff_coordinates {k : ℕ} {T : Functional X k}
    (hOff : ∀ b π, ¬Admissible b π → T b π = 0)
    (hCont : ∀ K, Continuous (TestClass.eval (K := K) T)) :
    NormalApprox k T ↔
      ∃ C : ℕ, currentCoordinates k T ∈ normalApproxClosed (X := X) k C := by
  classical
  constructor
  · rintro ⟨C,Ts,hTs,hM,hN,hlim⟩
    refine ⟨C, isClosed_closure.mem_of_tendsto
      (tendsto_pi_nhds.mpr fun ij => hlim _ _) ?_⟩
    exact Eventually.of_forall fun j => subset_closure ⟨Ts j,⟨hTs j,hM j,hN j⟩,rfl⟩
  · rintro ⟨C,hC⟩
    obtain ⟨ys,hys,hlim⟩ := mem_closure_iff_seq_limit.mp hC
    choose Ts hTs heq using hys
    have hlim' : Tendsto (fun j => currentCoordinates k (Ts j)) atTop
        (𝓝 (currentCoordinates k T)) := by
      simpa only [heq] using hlim
    refine ⟨C,Ts,fun j => (hTs j).1,fun j => (hTs j).2.1,fun j => (hTs j).2.2,?_⟩
    exact weak_limit_of_coordinate_limit (fun j => (hTs j).1) C C
      (fun j => (hTs j).2.1) (fun j => (hTs j).2.2) hOff hCont hlim'

lemma measurableSet_normalApprox {A : Type*} [MeasurableSpace A] {k : ℕ}
    (T : A → Functional X k)
    (hOff : ∀ a b π, ¬Admissible b π → T a b π = 0)
    (hCont : ∀ a K, Continuous (TestClass.eval (K := K) (T a)))
    (hMeas : ∀ b π, Measurable (fun a => T a b π)) :
    MeasurableSet {a | NormalApprox k (T a)} := by
  have he : {a | NormalApprox k (T a)} =
      ⋃ C : ℕ, (fun a => currentCoordinates k (T a)) ⁻¹' normalApproxClosed (X := X) k C := by
    ext a
    simpa only [mem_ofPred_eq,mem_iUnion,mem_preimage] using
      normalApprox_iff_coordinates (hOff a) (hCont a)
  rw [he]
  apply MeasurableSet.iUnion
  intro C
  exact isClosed_closure.measurableSet.preimage (Measurable.of_eval fun index =>
    hMeas (denseCurrentTest k index.1 index.2).val.1
      (fun coordinate => (denseCurrentTest k index.1 index.2).val.2 coordinate))

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction SmoothCutoff

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma continuous_profile_action {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {u : X → ℝ} (hu : BoundedLip u)
    (a : ℝ≥0) {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Continuous (fun t : ℝ => T (fun x => profile a t (u x) * b x) π) := by
  apply continuous_iff_seqContinuous.mpr
  intro ts t ht
  let f (s : ℝ) (x : X) := profile a s (u x) * b x
  have hf (s : ℝ) : BoundedLip (f s) := (profile_comp_boundedLip hu a s).mul hab.1
  obtain ⟨B,hB⟩ := hab.1.2
  have hbound (s : ℝ) (x : X) : |f s x| ≤ B := by
    dsimp [f]
    rw [abs_mul,abs_of_nonneg (profile_bounds a s (u x)).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (profile_bounds a s (u x)).2).trans (hB x)
  have hlim (x : X) : Tendsto (fun j => f (ts j) x) atTop (𝓝 (f t x)) := by
    have hp : Continuous (fun s : ℝ => profile a s (u x)) := by
      unfold profile
      fun_prop
    exact ((hp.tendsto t).comp ht).mul_const (b x)
  have h := borelAction_tendsto_of_bounded_pointwise hT (currentMassMeasure hT)
    (currentMassMeasure_controls hT) (hf t).continuous.measurable
    (fun j => (hf (ts j)).continuous.measurable) B (fun j => hbound (ts j)) hlim π hab.2
  simpa only [borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hf _,hab.2⟩,
    f, Function.comp_def] using h

variable {A : Type*} [MeasurableSpace A]

lemma measurable_profile_action_family {k : ℕ} (T : A → Functional X k)
    (hT : ∀ a, IsMetricCurrent (T a))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (c : ℝ≥0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    Measurable (fun p : ℝ × A => T p.2 (fun x => profile c p.1 (u x) * b x) π) := by
  exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun a => continuous_profile_action (hT a) hu c hab)
    (fun t => (hTm (fun x => profile c t (u x)*b x) π).stronglyMeasurable)).measurable

lemma measurable_restriction_family {k : ℕ} (T : A → Functional X k)
    (hT : ∀ a, IsMetricCurrent (T a))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (b : X → ℝ) (π : Fin k → X → ℝ) :
    Measurable (fun p : ℝ × A => restrictCurrent (hT p.2) {x | p.1 < u x} b π) := by
  classical
  by_cases hab : Admissible b π
  · have hlim (p : ℝ × A) : Tendsto
        (fun n : ℕ => T p.2 (fun x => profile ((n:ℝ≥0)+1) p.1 (u x)*b x) π) atTop
        (𝓝 (restrictCurrent (hT p.2) {x | p.1 < u x} b π)) := by
      have h := profile_current_tendsto (hT p.2) hu p.1 b π hab
      have he (n : ℕ) : weightedCurrent (currentMassMeasure (hT p.2)) (hT p.2)
          (profile ((n:ℝ≥0)+1) p.1 ∘ u) b π =
          T p.2 (fun x => profile ((n:ℝ≥0)+1) p.1 (u x)*b x) π := by
        rw [weightedCurrent,ite_eq_left hab]
        exact borelAction_eq _ (hT p.2) (currentMassMeasure_controls (hT p.2))
          ⟨(profile_comp_boundedLip hu _ _).mul hab.1,hab.2⟩
      simpa only [he] using h
    exact measurable_of_tendsto_metrizable
      (fun n => measurable_profile_action_family T hT hTm hu ((n:ℝ≥0)+1) hab) (tendsto_pi_nhds.mpr hlim)
  · have he (p : ℝ × A) : restrictCurrent (hT p.2) {x | p.1 < u x} b π = 0 := by
      simp only [restrictCurrent,ite_eq_right hab]
    simpa only [he] using (measurable_const : Measurable (fun _ : ℝ × A => (0:ℝ)))

theorem measurable_superlevelSlice_family {k : ℕ} (T : A → Functional X (k+1))
    (hT : ∀ a, IsMetricCurrent (T a))
    (hB : ∀ a, IsMetricCurrent (boundarySucc (T a)))
    (hTm : ∀ b π, Measurable (fun a => T a b π))
    {u : X → ℝ} (hu : BoundedLip u) (b : X → ℝ) (π : Fin k → X → ℝ) :
    Measurable (fun p : ℝ × A => superlevelSlice (hT p.2) (hB p.2) u p.1 b π) := by
  classical
  have hBm (b : X → ℝ) (π : Fin k → X → ℝ) :
      Measurable (fun a => boundarySucc (T a) b π) := by
    by_cases h : Admissible b π
    · simpa only [boundarySucc,ite_eq_left h] using hTm (fun _ => 1) (Matrix.vecCons b π)
    · simp only [boundarySucc,ite_eq_right h]
      exact measurable_const
  by_cases hab : Admissible b π
  · have hleft := measurable_restriction_family (fun a => boundarySucc (T a)) hB hBm hu b π
    have hright := measurable_restriction_family T hT hTm hu (fun _ => 1) (Matrix.vecCons b π)
    convert hleft.sub hright using 1
    funext p
    simp only [superlevelSlice,Pi.sub_apply,boundarySucc,ite_eq_left hab]
  · have he (p : ℝ × A) : superlevelSlice (hT p.2) (hB p.2) u p.1 b π = 0 := by
      simp only [superlevelSlice,Pi.sub_apply,restrictCurrent,boundarySucc,ite_eq_right hab,sub_zero]
    simpa only [he] using (measurable_const : Measurable (fun _ : ℝ × A => (0:ℝ)))

end CAT0Fillings.Slicing
end

end OAI
