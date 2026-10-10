import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Topology.Semicontinuity.Basic
import OAI.Analysis.FactorGeneration.Bicommutant
import OAI.Analysis.FactorGeneration.CornerTrace

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/
namespace Tracial
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem tendsto_vector_iff_norm₂ {I : Type*} (l : Filter I)
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra) :
    Tendsto (fun i => (a i : H →L[ℂ] H) τ.vector) l (𝓝 ((b : H →L[ℂ] H) τ.vector)) ↔
    Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0) := by
  simpa only [dist_eq_norm,TracialRepresentation.norm₂_sub] using
    (tendsto_iff_dist_tendsto_zero (f := fun i => (a i : H →L[ℂ] H) τ.vector)
      (a := (b : H →L[ℂ] H) τ.vector))

theorem norm₂_limit_unique {I : Type*} {l : Filter I} [l.NeBot]
    (a : I → M.toStarSubalgebra) {b c : M.toStarSubalgebra}
    (hb : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0))
    (hc : Tendsto (fun i => τ.norm₂ (a i-c)) l (𝓝 0)) : b=c := by
  have he := tendsto_nhds_unique ((tendsto_vector_iff_norm₂ τ l a b).mpr hb)
    ((tendsto_vector_iff_norm₂ τ l a c).mpr hc)
  apply sub_eq_zero.mp
  apply τ.separating
  change (b : H →L[ℂ] H) τ.vector-(c : H →L[ℂ] H) τ.vector=0
  exact sub_eq_zero.mpr he

theorem norm₂_limit_star {I : Type*} {l : Filter I} (a : I → M.toStarSubalgebra)
    (b : M.toStarSubalgebra) (h : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => τ.norm₂ (star (a i)-star b)) l (𝓝 0) := by
  simpa only [← star_sub,τ.norm₂_star] using h

theorem norm₂_limit_mul {I : Type*} {l : Filter I}
    (a c : I → M.toStarSubalgebra) (b d : M.toStarSubalgebra)
    (C : ℝ) (hC : ∀ i, ‖a i‖ ≤ C)
    (ha : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0))
    (hc : Tendsto (fun i => τ.norm₂ (c i-d)) l (𝓝 0)) :
    Tendsto (fun i => τ.norm₂ (a i*c i-b*d)) l (𝓝 0) := by
  have hbound : ∀ i, τ.norm₂ (a i*c i-b*d) ≤ C*τ.norm₂ (c i-d)+τ.norm₂ (a i-b)*‖d‖ := by
    intro i
    have he : a i*c i-b*d = a i*(c i-d)+(a i-b)*d := by
      simp only [mul_sub,sub_mul]; abel
    rw [he]
    exact (τ.norm₂_add_le _ _).trans (add_le_add
      ((τ.norm₂_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _)))
      (τ.norm₂_mul_le_right _ _))
  apply squeeze_zero (fun i => norm_nonneg _) hbound
  simpa using (hc.const_mul C).add (ha.mul_const ‖d‖)

theorem norm₂_limit_trace {I : Type*} {l : Filter I}
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra)
    (h : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => τ.trace (a i)) l (𝓝 (τ.trace b)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  apply squeeze_zero (fun i => norm_nonneg _)
    (fun i => ?_) h
  rw [← trace_sub]
  exact τ.norm_trace_le_norm₂ _

end Tracial

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : S →ₗ[ℂ] H where
  toFun a := a.val ξ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (vectorOrbitMap S ξ).range.topologicalClosure

instance vectorOrbitClosure_complete (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (vectorOrbitClosure S ξ) :=
  inferInstanceAs (CompleteSpace (vectorOrbitMap S ξ).range.topologicalClosure)

theorem mem_vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    ξ ∈ vectorOrbitClosure S ξ :=
  Submodule.le_topologicalClosure _ ⟨1,rfl⟩

theorem vectorOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (a : S) {y : H} (hy : y ∈ vectorOrbitClosure S ξ) : a.val y ∈ vectorOrbitClosure S ξ := by
  have h : (vectorOrbitMap S ξ).range.topologicalClosure ≤
      (vectorOrbitClosure S ξ).comap a.val.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨a*b,rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage a.val.continuous
  exact h hy

theorem vectorOrbitProjection_commutes (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (a : S) : (vectorOrbitClosure S ξ).starProjection*a.val=
      a.val*(vectorOrbitClosure S ξ).starProjection := by
  apply starProjection_commutes_of_invariant
  · exact fun y hy => vectorOrbitClosure_invariant S ξ a hy
  · exact fun y hy => vectorOrbitClosure_invariant S ξ (star a) hy

theorem commutant_orbitClosure_eq_top (M : VonNeumannAlgebra H) (ξ : H)
    (hξ : ∀ a : M.toStarSubalgebra,a.val ξ=0 → a=0) :
    vectorOrbitClosure M.commutant.toStarSubalgebra ξ=⊤ := by
  let K := vectorOrbitClosure M.commutant.toStarSubalgebra ξ
  have hQ : K.starProjection ∈ M := by
    have h : K.starProjection ∈ M.commutant.commutant := by
      apply VonNeumannAlgebra.mem_commutant_iff.mpr
      intro a ha
      exact (vectorOrbitProjection_commutes M.commutant.toStarSubalgebra ξ ⟨a,ha⟩).symm
    simpa only [M.commutant_commutant] using h
  have he : (1-K.starProjection) ξ=0 := by
    change ξ-K.starProjection ξ=0
    rw [Submodule.starProjection_eq_self_iff.mpr (mem_vectorOrbitClosure _ _),sub_self]
  have hzero := hξ ⟨1-K.starProjection,M.toStarSubalgebra.sub_mem M.one_mem hQ⟩ he
  have h1 : K.starProjection=1 := by
    have h := congrArg Subtype.val hzero
    exact (sub_eq_zero.mp h).symm
  apply top_unique
  intro y _
  apply Submodule.starProjection_eq_self_iff.mp
  rw [show (vectorOrbitClosure M.commutant.toStarSubalgebra ξ).starProjection=1 from h1]
  rfl

theorem commutant_orbit_dense (M : VonNeumannAlgebra H) (ξ : H)
    (hξ : ∀ a : M.toStarSubalgebra,a.val ξ=0 → a=0) :
    Dense (Set.range (fun a : M.commutant.toStarSubalgebra => a.val ξ)) := by
  intro y
  have h : y ∈ vectorOrbitClosure M.commutant.toStarSubalgebra ξ := by
    rw [commutant_orbitClosure_eq_top M ξ hξ]
    trivial
  exact h

end

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/
namespace Tracial

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

abbrev traceCyclicSpace := vectorOrbitClosure M.toStarSubalgebra τ.vector

def traceCyclicVector : traceCyclicSpace τ := ⟨τ.vector,mem_vectorOrbitClosure _ _⟩

def traceCyclicOperator (a : M.toStarSubalgebra) :
    traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ :=
  a.val.restrict (fun _ hy => vectorOrbitClosure_invariant _ _ a hy)

@[simp] theorem traceCyclicOperator_apply (a : M.toStarSubalgebra) (y : traceCyclicSpace τ) :
    (traceCyclicOperator τ a y).val=a.val y.val := rfl

theorem traceCyclicOperator_star (a : M.toStarSubalgebra) :
    traceCyclicOperator τ (star a)=star (traceCyclicOperator τ a) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y.val (star a.val x.val)=inner ℂ y (star (traceCyclicOperator τ a) x)
  simp only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  rfl

def traceCyclicHom : M.toStarSubalgebra →⋆ₐ[ℂ]
    (traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ) where
  toFun := traceCyclicOperator τ
  map_one' := by ext y; rfl
  map_mul' _ _ := by ext y; rfl
  map_zero' := by ext y; rfl
  map_add' _ _ := by ext y; rfl
  commutes' _ := by ext y; rfl
  map_star' := traceCyclicOperator_star τ

theorem traceCyclicHom_injective : Function.Injective (traceCyclicHom τ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply τ.separating
  have h := congrArg (fun T : traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ =>
    (T (traceCyclicVector τ)).val) hab
  exact sub_eq_zero.mpr h

theorem traceCyclicHom_norm (a : M.toStarSubalgebra) : ‖traceCyclicHom τ a‖=‖a‖ := by
  let : CStarAlgebra M.toStarSubalgebra := {}
  let : CStarAlgebra (traceCyclicSpace τ →L[ℂ] traceCyclicSpace τ) := {}
  exact NonUnitalStarAlgHom.norm_map (traceCyclicHom τ) (traceCyclicHom_injective τ) a

theorem traceCyclicHom_isometry : Isometry (traceCyclicHom τ) :=
  AddMonoidHomClass.isometry_of_norm (traceCyclicHom τ) (traceCyclicHom_norm τ)

theorem traceCyclicVector_norm : ‖traceCyclicVector τ‖=1 := τ.norm_vector

theorem traceCyclicHom_trace (a : M.toStarSubalgebra) :
    inner ℂ (traceCyclicVector τ) (traceCyclicHom τ a (traceCyclicVector τ))=τ.trace a := rfl

theorem traceCyclicHom_norm₂ (a : M.toStarSubalgebra) :
    ‖traceCyclicHom τ a (traceCyclicVector τ)‖=τ.norm₂ a := rfl

theorem traceCyclicHom_cyclic :
    Dense (Set.range (fun a : M.toStarSubalgebra => traceCyclicHom τ a (traceCyclicVector τ))) := by
  intro y
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨z,⟨a,rfl⟩,ha⟩ := Metric.mem_closure_iff.mp y.property ε hε
  exact ⟨traceCyclicHom τ a (traceCyclicVector τ),⟨a,rfl⟩,ha⟩

theorem traceCyclicSpace_separable
    (hsep : TopologicalSpace.IsSeparable
      (Set.range (fun a : M.toStarSubalgebra => a.val τ.vector))) :
    TopologicalSpace.SeparableSpace (traceCyclicSpace τ) :=
  hsep.closure.separableSpace

end

/-! The faithful cyclic restriction sends actual algebra balls to compact
weak-operator balls. On each bounded ball it is a closed topological embedding. -/
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def cyclicBallMap (C : ℝ) (T : weakOperatorBall M C) :
    traceCyclicSpace τ →WOT[ℂ] traceCyclicSpace τ :=
  ContinuousLinearMapWOT.ofCLM (traceCyclicHom τ ⟨T.val.toCLM,T.property.1⟩)

theorem cyclicBallMap_continuous (C : ℝ) : Continuous (cyclicBallMap τ C) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  change Continuous (fun T : weakOperatorBall M C => inner ℂ y.val (T.val x.val))
  exact ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val x.val y.val

theorem cyclicBallMap_injective (C : ℝ) : Function.Injective (cyclicBallMap τ C) := by
  intro a b hab
  have he : traceCyclicHom τ ⟨a.val.toCLM,a.property.1⟩=
      traceCyclicHom τ ⟨b.val.toCLM,b.property.1⟩ :=
    congrArg ContinuousLinearMapWOT.toCLM hab
  have he' := congrArg Subtype.val (traceCyclicHom_injective τ he)
  apply Subtype.ext
  exact congrArg ContinuousLinearMapWOT.ofCLM he'

theorem cyclicBallMap_isClosedEmbedding (C : ℝ) :
    Topology.IsClosedEmbedding (cyclicBallMap τ C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  exact (cyclicBallMap_continuous τ C).isClosedEmbedding (cyclicBallMap_injective τ C)

def cyclicWeakOperatorBall (C : ℝ) : Set (traceCyclicSpace τ →WOT[ℂ] traceCyclicSpace τ) :=
  {T | ∃ a : M.toStarSubalgebra,‖a‖ ≤ C ∧ ContinuousLinearMapWOT.ofCLM (traceCyclicHom τ a)=T}

theorem cyclicWeakOperatorBall_eq_range (C : ℝ) :
    cyclicWeakOperatorBall τ C=Set.range (cyclicBallMap τ C) := by
  ext T
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨ContinuousLinearMapWOT.ofCLM a.val,⟨a.property,ha⟩⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    exact ⟨⟨a.val.toCLM,a.property.1⟩,a.property.2,rfl⟩

theorem cyclicWeakOperatorBall_isCompact (C : ℝ) : IsCompact (cyclicWeakOperatorBall τ C) := by
  let : CompactSpace (weakOperatorBall M C) :=
    isCompact_iff_compactSpace.mp (weakOperatorBall_isCompact M C)
  rw [cyclicWeakOperatorBall_eq_range]
  exact isCompact_range (cyclicBallMap_continuous τ C)

theorem cyclicWeakOperatorBall_isClosed (C : ℝ) : IsClosed (cyclicWeakOperatorBall τ C) :=
  (cyclicWeakOperatorBall_isCompact τ C).isClosed

end Tracial

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology
namespace Tracial
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem traceVector_weak_continuous (C : ℝ) :
    Continuous (fun T : weakOperatorBall M C => toWeakSpace ℂ H (T.val τ.vector)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  exact (ContinuousLinearMapWOT.continuous_dual_apply τ.vector f).comp continuous_subtype_val

def traceFunctionalSlice (f : M.toStarSubalgebra →L[ℝ] ℝ) (r : ℝ) : Set H :=
  {ξ | ∃ a : M.toStarSubalgebra, ‖a‖ ≤ 1 ∧ f a ≤ r ∧ a.val τ.vector = ξ}

theorem traceFunctionalSlice_convex (f : M.toStarSubalgebra →L[ℝ] ℝ) (r : ℝ) :
    Convex ℝ (traceFunctionalSlice τ f r) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨a, ha, hfa, rfl⟩ := hx
  obtain ⟨b, hb, hfb, rfl⟩ := hy
  refine ⟨s • a + t • b, ?_, ?_, rfl⟩
  · calc
      ‖s • a + t • b‖ ≤ ‖s • a‖ + ‖t • b‖ := norm_add_le _ _
      _ = s * ‖a‖ + t * ‖b‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hs, Real.norm_of_nonneg ht]
      _ ≤ s * 1 + t * 1 := _root_.add_le_add
        (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
      _ = 1 := by simpa only [mul_one] using hst
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    calc
      s*f a+t*f b ≤ s*r+t*r := _root_.add_le_add
        (mul_le_mul_of_nonneg_left hfa hs) (mul_le_mul_of_nonneg_left hfb ht)
      _ = r := by rw [← add_mul, hst, one_mul]

theorem traceFunctionalSlice_isClosed (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra),
      (∀ n, ‖a n‖ ≤ 1) → Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0) →
      Tendsto (fun n => f (a n)) atTop (𝓝 (f b))) (r : ℝ) :
    IsClosed (traceFunctionalSlice τ f r) := by
  apply IsSeqClosed.isClosed
  intro ξ z hz hlim
  choose a ha hfa he using hz
  have hva : Tendsto (fun n => (a n).val τ.vector) atTop (𝓝 z) := by
    simpa only [he] using hlim
  obtain ⟨b, hb, hbe⟩ := bounded_trace_limit τ a 1 zero_le_one ha z hva
  refine ⟨b, hb, ?_, hbe⟩
  apply le_of_tendsto (hf a b ha ?_) (Eventually.of_forall hfa)
  apply (tendsto_vector_iff_norm₂ τ atTop a b).mp
  rwa [hbe]

theorem unitBall_functional_sublevel_isClosed (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra),
      (∀ n, ‖a n‖ ≤ 1) → Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0) →
      Tendsto (fun n => f (a n)) atTop (𝓝 (f b))) (r : ℝ) :
    IsClosed {T : weakOperatorBall M 1 | f ⟨T.val.toCLM, T.property.1⟩ ≤ r} := by
  have hclosed := traceFunctionalSlice_isClosed τ f hf r
  have hconvex := traceFunctionalSlice_convex τ f r
  have hw : IsClosed ((toWeakSpace ℂ H) '' traceFunctionalSlice τ f r) := by
    rw [← closure_eq_iff_isClosed, ← hconvex.toWeakSpace_closure ℂ, hclosed.closure_eq]
  have hpre := hw.preimage (traceVector_weak_continuous τ 1)
  convert hpre using 1
  ext T
  constructor
  · intro h
    exact ⟨T.val τ.vector, ⟨⟨T.val.toCLM, T.property.1⟩, T.property.2, h, rfl⟩, rfl⟩
  · rintro ⟨ξ, ⟨a, _, hfa, ha⟩, he⟩
    have hv : a.val τ.vector = T.val τ.vector := ha.trans ((toWeakSpace ℂ H).injective he)
    have heq : a = (⟨T.val.toCLM, T.property.1⟩ : M.toStarSubalgebra) := by
      apply sub_eq_zero.mp
      apply τ.separating
      change a.val τ.vector - T.val τ.vector = 0
      exact sub_eq_zero.mpr hv
    change f ⟨T.val.toCLM, T.property.1⟩ ≤ r
    simpa only [heq] using hfa

theorem unitBall_functional_continuous_of_norm₂ (f : M.toStarSubalgebra →L[ℝ] ℝ)
    (hf : ∀ (a : ℕ → M.toStarSubalgebra) (b : M.toStarSubalgebra),
      (∀ n, ‖a n‖ ≤ 1) → Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0) →
      Tendsto (fun n => f (a n)) atTop (𝓝 (f b))) :
    Continuous (fun T : weakOperatorBall M 1 => f ⟨T.val.toCLM, T.property.1⟩) := by
  apply continuous_iff_lower_upperSemicontinuous.mpr
  constructor
  · exact lowerSemicontinuous_iff_isClosed_preimage.mpr
      (unitBall_functional_sublevel_isClosed τ f hf)
  · apply upperSemicontinuous_iff_isClosed_preimage.mpr
    intro r
    have hn := unitBall_functional_sublevel_isClosed τ (-f)
      (fun a b ha ht => (hf a b ha ht).neg) (-r)
    change IsClosed {T : weakOperatorBall M 1 | r ≤ f ⟨T.val.toCLM, T.property.1⟩}
    simpa only [neg_apply, neg_le_neg_iff] using hn

end Tracial

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem bounded_operators_tendsto_of_dense {I : Type*} {l : Filter I}
    (a : I → H →L[ℂ] H) (b : H →L[ℂ] H) (C : ℝ)
    (ha : ∀ i,‖a i‖ ≤ C) (s : Set H) (hs : Dense s)
    (hlim : ∀ y ∈ s,Tendsto (fun i => a i y) l (𝓝 (b y))) :
    ∀ y : H,Tendsto (fun i => a i y) l (𝓝 (b y)) := by
  intro y
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let D := |C|+‖b‖+1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨z,hz,hyz⟩ := Metric.mem_closure_iff.mp (hs y) (ε/(2*D)) (by positivity)
  have hzlim := Metric.tendsto_nhds.mp (hlim z hz) (ε/2) (by positivity)
  filter_upwards [hzlim] with i hi
  have he : a i y-b y=(a i-b) (y-z)+(a i z-b z) := by
    simp only [sub_apply,map_sub]; abel
  have hn : ‖a i-b‖ ≤ D := by
    calc
      ‖a i-b‖ ≤ ‖a i‖+‖b‖ := norm_sub_le _ _
      _ ≤ |C|+‖b‖ := _root_.add_le_add ((ha i).trans (le_abs_self C)) le_rfl
      _ ≤ D := le_add_of_nonneg_right zero_le_one
  have hd : D*‖y-z‖ < ε/2 := by
    have h := (mul_lt_mul_iff_right₀ hD).mpr hyz
    rw [dist_eq_norm] at h
    have heq : D*(ε/(2*D))=ε/2 := by field_simp
    rw [heq] at h
    exact h
  rw [dist_eq_norm,he]
  have hbound := ((a i-b).le_opNorm (y-z)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hi' : ‖a i z-b z‖ < ε/2 := by simpa only [dist_eq_norm] using hi
  exact (norm_add_le _ _).trans_lt (by linarith)

namespace Tracial
open UltrapowerBridge
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_limit_strong {I : Type*} {l : Filter I}
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra) (C : ℝ)
    (ha : ∀ i,‖a i‖ ≤ C)
    (hlim : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    ∀ y : H,Tendsto (fun i => (a i).val y) l (𝓝 (b.val y)) := by
  apply bounded_operators_tendsto_of_dense (fun i => (a i).val) b.val C ha
    (Set.range (fun c : M.commutant.toStarSubalgebra => c.val τ.vector))
    (commutant_orbit_dense M τ.vector τ.separating)
  rintro _ ⟨c,rfl⟩
  have he (d : M.toStarSubalgebra) : d.val (c.val τ.vector)=c.val (d.val τ.vector) :=
    congrArg (fun T : H →L[ℂ] H => T τ.vector)
      (VonNeumannAlgebra.mem_commutant_iff.mp c.property d.val d.property)
  simp only [he]
  exact c.val.continuous.continuousAt.tendsto.comp
    ((tendsto_vector_iff_norm₂ τ l a b).mpr hlim)

theorem norm₂_limit_strong_star {I : Type*} {l : Filter I}
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra) (C : ℝ)
    (ha : ∀ i,‖a i‖ ≤ C)
    (hlim : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    ∀ y : H,Tendsto (fun i => (star (a i)).val y) l (𝓝 ((star b).val y)) :=
  norm₂_limit_strong τ (fun i => star (a i)) (star b) C
    (fun i => by
      change ‖star ((a i).val)‖ ≤ C
      rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint.norm_map]
      exact ha i) (norm₂_limit_star τ a b hlim)

theorem bounded_strong_iff_norm₂ {I : Type*} {l : Filter I}
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra) (C : ℝ)
    (ha : ∀ i,‖a i‖ ≤ C) :
    (∀ y : H,Tendsto (fun i => (a i).val y) l (𝓝 (b.val y))) ↔
      Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0) :=
  ⟨fun h => (tendsto_vector_iff_norm₂ τ l a b).mp (h τ.vector),
    norm₂_limit_strong τ a b C ha⟩

end Tracial

end Generator

end

end OAI
