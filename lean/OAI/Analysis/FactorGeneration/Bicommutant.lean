import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import OAI.Analysis.FactorGeneration.Target

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

abbrev FiniteHilbert (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

def diagonalOperator (T : H →L[ℂ] H) : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i)))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_apply (T : H →L[ℂ] H) (x : FiniteHilbert ι H) (i : ι) :
    diagonalOperator T x i=T (x i) := rfl

theorem diagonalOperator_star (T : H →L[ℂ] H) :
    diagonalOperator (ι := ι) (star T)=star (diagonalOperator (ι := ι) T) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply,diagonalOperator_apply,
    ContinuousLinearMap.adjoint_inner_right]

def tupleOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    S →ₗ[ℂ] FiniteHilbert ι H where
  toFun a := diagonalOperator a.val x
  map_add' a b := by ext i; rfl
  map_smul' c a := by ext i; rfl

def tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    Submodule ℂ (FiniteHilbert ι H) := (tupleOrbitMap S x).range.topologicalClosure

instance tupleOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : CompleteSpace (tupleOrbitClosure S x) :=
  inferInstanceAs (CompleteSpace (tupleOrbitMap S x).range.topologicalClosure)

theorem mem_tupleOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) : x ∈ tupleOrbitClosure S x := by
  apply Submodule.le_topologicalClosure
  refine ⟨1,?_⟩
  ext i
  rfl

theorem tupleOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) {y : FiniteHilbert ι H}
    (hy : y ∈ tupleOrbitClosure S x) : diagonalOperator a.val y ∈ tupleOrbitClosure S x := by
  have h : (tupleOrbitMap S x).range.topologicalClosure ≤
      (tupleOrbitClosure S x).comap (diagonalOperator a.val).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨a*b,?_⟩
      ext i
      rfl
    · exact (Submodule.isClosed_topologicalClosure _).preimage (diagonalOperator a.val).continuous
  exact h hy

theorem starProjection_commutes_of_invariant (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hT : ∀ x ∈ K,T x ∈ K) (hstar : ∀ x ∈ K,star T x ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext x
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (K.starProjection_apply_mem x)
  · intro y hy
    change inner ℂ (T x-T (K.starProjection x)) y=0
    rw [← map_sub]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact K.starProjection_inner_eq_zero x _ (hstar y hy)

theorem tupleOrbitProjection_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : FiniteHilbert ι H) (a : S) :
    (tupleOrbitClosure S x).starProjection*diagonalOperator a.val=
      diagonalOperator a.val*(tupleOrbitClosure S x).starProjection := by
  apply starProjection_commutes_of_invariant
  · exact fun y hy => tupleOrbitClosure_invariant S x a hy
  · rw [← diagonalOperator_star]
    exact fun y hy => tupleOrbitClosure_invariant S x (star a) hy

variable [DecidableEq ι]

def tupleSingle (i : ι) : H →L[ℂ] FiniteHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem tupleSingle_apply (i j : ι) (x : H) :
    tupleSingle i x j=(Pi.single i x : ι → H) j := rfl

omit [CompleteSpace H] in
theorem tuple_eq_sum_single (x : FiniteHilbert ι H) :
    x=∑ i,tupleSingle i (x i) := by
  ext j
  simp [WithLp.ofLp_sum,tupleSingle_apply,Pi.single_apply]

omit [CompleteSpace H] [Fintype ι] in
theorem diagonalOperator_single (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonalOperator T (tupleSingle i x)=tupleSingle i (T x) := by
  ext j
  by_cases h : j=i <;> simp [h]

def operatorEntry (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (Q.comp (tupleSingle j))

omit [Fintype ι] in
theorem operatorEntry_mem_centralizer (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (hQ : ∀ a : S,Q*diagonalOperator a.val=diagonalOperator a.val*Q) (i j : ι) :
    operatorEntry Q i j ∈ Set.centralizer (S : Set (H →L[ℂ] H)) := by
  intro a ha
  ext z
  change a (Q (tupleSingle j z) i)=Q (tupleSingle j (a z)) i
  have h := congrArg (fun T : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H =>
    T (tupleSingle j z) i) (hQ ⟨a,ha⟩)
  simpa only [mul_apply_eq_comp,diagonalOperator_apply,
    diagonalOperator_single] using h.symm

omit [CompleteSpace H] in
theorem diagonalOperator_commutes_of_entries (T : H →L[ℂ] H)
    (Q : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H)
    (h : ∀ i j,operatorEntry Q i j*T=T*operatorEntry Q i j) :
    Q*diagonalOperator T=diagonalOperator T*Q := by
  ext x i
  rw [tuple_eq_sum_single x]
  simp only [map_sum,mul_apply_eq_comp,diagonalOperator_single]
  simp only [WithLp.ofLp_sum,Finset.sum_apply,diagonalOperator_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : H →L[ℂ] H => a (x j)) (h i j)

theorem bicommutant_tuple_mem_closure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (x : FiniteHilbert ι H) : diagonalOperator T x ∈ tupleOrbitClosure S x := by
  let Q := (tupleOrbitClosure S x).starProjection
  have hcomm : Q*diagonalOperator T=diagonalOperator T*Q :=
    diagonalOperator_commutes_of_entries T Q (fun i j => hT _
      (operatorEntry_mem_centralizer S Q (tupleOrbitProjection_commutes S x) i j))
  apply Submodule.starProjection_eq_self_iff.mp
  have h := congrArg (fun a : FiniteHilbert ι H →L[ℂ] FiniteHilbert ι H => a x) hcomm
  change Q (diagonalOperator T x)=diagonalOperator T (Q x) at h
  rw [show Q x=x from Submodule.starProjection_eq_self_iff.mpr (mem_tupleOrbitClosure S x)] at h
  exact h

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem bicommutant_finite_strong_approximation (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : S,∀ x ∈ s,‖T x-a.val x‖ < ε := by
  classical
  let x : FiniteHilbert s H := WithLp.toLp 2 (fun i : s => i.val)
  have h := bicommutant_tuple_mem_closure S T hT x
  obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp h ε hε
  refine ⟨a,?_⟩
  intro y hy
  have hb := PiLp.norm_apply_le (diagonalOperator T x-tupleOrbitMap S x a) (⟨y,hy⟩ : s)
  exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

theorem bicommutant_exists_strong_net (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))) :
    ∃ a : Finset H × ℕ → S,∀ x : H,
      Tendsto (fun d => (a d).val x) atTop (𝓝 (T x)) := by
  classical
  have hex (d : Finset H × ℕ) := bicommutant_finite_strong_approximation S T hT d.1
    (1/((d.2 : ℝ)+1)) (by positivity)
  choose a ha using hex
  refine ⟨a,?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun d : Finset H × ℕ => d.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun d => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H),0)] with d hd
  rw [dist_comm,dist_eq_norm]
  exact (ha d x (hd.1 (Finset.mem_singleton_self x))).le

theorem wotClosed_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H)))=S := by
  classical
  apply Set.Subset.antisymm
  · intro T hT
    obtain ⟨a,ha⟩ := bicommutant_exists_strong_net S T hT
    have hw : Tendsto (fun d => ContinuousLinearMapWOT.ofCLM (a d).val) atTop
        (𝓝 (ContinuousLinearMapWOT.ofCLM T)) := by
      apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
      intro x y
      exact (continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha x)
    exact hS.mem_of_tendsto hw (Eventually.of_forall (fun d => (a d).property))
  · intro T hT a ha
    exact (ha T hT).symm

def vonNeumannOfWOTClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    VonNeumannAlgebra H where
  toStarSubalgebra := S
  centralizer_centralizer' := wotClosed_bicommutant S hS

theorem wotClosed_normClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S) :
    IsClosed (S : Set (H →L[ℂ] H)) :=
  hS.preimage ContinuousLinearMapWOT.continuous_ofCLM

end

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

theorem countable_monoid_closure {A : Type*} [Monoid A] {s : Set A}
    (hs : s.Countable) : (Submonoid.closure s : Set A).Countable := by
  let : Countable s := hs.to_subtype
  let : Countable (FreeMonoid s) := inferInstanceAs (Countable (List s))
  rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
  exact Set.countable_range _

theorem separable_countable_star_adjoin {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] [TopologicalSpace A]
    [ContinuousAdd A] [ContinuousSMul ℂ A] {s : Set A} (hs : s.Countable) :
    TopologicalSpace.IsSeparable (StarAlgebra.adjoin ℂ s : Set A) := by
  change TopologicalSpace.IsSeparable
    ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
  rw [StarAlgebra.adjoin_eq_span]
  apply TopologicalSpace.IsSeparable.span
  apply Set.Countable.isSeparable
  apply countable_monoid_closure
  exact hs.union (by simpa only [Set.image_star] using hs.image star)

end Generator

end

end OAI
