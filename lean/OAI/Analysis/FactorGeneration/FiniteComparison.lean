import OAI.Analysis.FactorGeneration.ProjectionComparison

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def projectionOrbitVectors (p : AlgebraProjection M) : Set H :=
  {y | ∃ a : M.toStarSubalgebra, ∃ x : H, y=a.val (p.val.val x)}

def projectionOrbitClosure (p : AlgebraProjection M) : Submodule ℂ H :=
  (Submodule.span ℂ (projectionOrbitVectors p)).topologicalClosure

instance projectionOrbitClosure_complete (p : AlgebraProjection M) :
    CompleteSpace (projectionOrbitClosure p) :=
  inferInstanceAs (CompleteSpace (Submodule.span ℂ (projectionOrbitVectors p)).topologicalClosure)

theorem projectionOrbitClosure_invariant_of_vectors (p : AlgebraProjection M)
    (T : H →L[ℂ] H)
    (hT : ∀ y ∈ projectionOrbitVectors p, T y ∈ projectionOrbitVectors p) :
    ∀ y ∈ projectionOrbitClosure p, T y ∈ projectionOrbitClosure p := by
  have h : projectionOrbitClosure p ≤ (projectionOrbitClosure p).comap T.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro y hy
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span (hT y hy))
    · exact (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  exact fun y hy => h hy

theorem projectionOrbitClosure_invariant (p : AlgebraProjection M) (a : M.toStarSubalgebra) :
    ∀ y ∈ projectionOrbitClosure p, a.val y ∈ projectionOrbitClosure p := by
  apply projectionOrbitClosure_invariant_of_vectors
  rintro y ⟨b,x,rfl⟩
  exact ⟨a*b,x,rfl⟩

theorem projectionOrbitClosure_commutant_invariant (p : AlgebraProjection M)
    (T : H →L[ℂ] H) (hT : T ∈ M.commutant) :
    ∀ y ∈ projectionOrbitClosure p, T y ∈ projectionOrbitClosure p := by
  apply projectionOrbitClosure_invariant_of_vectors
  rintro y ⟨a,x,rfl⟩
  refine ⟨a,T x,?_⟩
  have ha := VonNeumannAlgebra.mem_commutant_iff.mp hT a.val a.property
  have hp := VonNeumannAlgebra.mem_commutant_iff.mp hT p.val.val p.val.property
  have hea := congrArg (fun R : H →L[ℂ] H => R (p.val.val x)) ha
  have hep := congrArg (fun R : H →L[ℂ] H => R x) hp
  change a.val (T (p.val.val x))=T (a.val (p.val.val x)) at hea
  change p.val.val (T x)=T (p.val.val x) at hep
  exact hea.symm.trans (congrArg a.val hep.symm)

theorem projectionOrbitProjection_mem (p : AlgebraProjection M) :
    (projectionOrbitClosure p).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro T hT
  rw [Submodule.range_starProjection]
  exact projectionOrbitClosure_commutant_invariant p T hT

def centralSupport (p : AlgebraProjection M) : AlgebraProjection M :=
  ⟨⟨(projectionOrbitClosure p).starProjection, projectionOrbitProjection_mem p⟩, by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := projectionOrbitClosure p)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection (U := projectionOrbitClosure p)).isSelfAdjoint.star_eq⟩

theorem centralSupport_commutes (p : AlgebraProjection M) (a : M.toStarSubalgebra) :
    a*(centralSupport p).val=(centralSupport p).val*a := by
  apply Subtype.ext
  exact (Generator.starProjection_commutes_of_invariant (projectionOrbitClosure p) a.val
    (projectionOrbitClosure_invariant p a)
    (projectionOrbitClosure_invariant p (star a))).symm

theorem le_centralSupport (p : AlgebraProjection M) : p ≤ centralSupport p := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨1,x,rfl⟩

theorem centralSupport_le (p q : AlgebraProjection M)
    (hcomm : ∀ a : M.toStarSubalgebra, a*q.val=q.val*a) (hpq : p ≤ q) :
    centralSupport p ≤ q := by
  have hK : projectionOrbitClosure p ≤ (q.val.val-1).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨a,x,rfl⟩
      change q.val.val (a.val (p.val.val x))-a.val (p.val.val x)=0
      have he : q.val*a*p.val=a*p.val := by
        rw [← hcomm a, mul_assoc, hpq]
      exact sub_eq_zero.mpr (congrArg (fun R : M.toStarSubalgebra => R.val x) he)
    · exact (q.val.val-1).isClosed_ker
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact sub_eq_zero.mp (hK ((projectionOrbitClosure p).starProjection_apply_mem x))

theorem mul_centralSupport_eq_zero_of_no_links (p q : AlgebraProjection M)
    (hlink : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0) :
    q.val*(centralSupport p).val=0 := by
  have hK : projectionOrbitClosure p ≤ q.val.val.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro y ⟨a,x,rfl⟩
      exact congrArg (fun R : M.toStarSubalgebra => R.val x) (hlink a)
    · exact q.val.val.isClosed_ker
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact hK ((projectionOrbitClosure p).starProjection_apply_mem x)

/-- Scalar center forces every nonzero projection to have full central support. -/
theorem centralSupport_eq_one_of_factor
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p : AlgebraProjection M) (hp : p.val≠0) : (centralSupport p).val=1 := by
  obtain ⟨z,hz⟩ := hfactor (centralSupport p).val (centralSupport_commutes p)
  have he := le_centralSupport p
  change (centralSupport p).val*p.val=p.val at he
  rw [hz,smul_mul_assoc,one_mul] at he
  have hz1 : z=1 := (smul_left_injective ℂ hp) (he.trans (one_smul ℂ p.val).symm)
  rw [hz,hz1,one_smul]

theorem traceFree_projection_eq_zero_or_eq_zero_of_no_links
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) (hlink : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0) :
    p.val=0 ∨ q.val=0 := by
  by_cases hp : p.val=0
  · exact Or.inl hp
  · right
    have h := mul_centralSupport_eq_zero_of_no_links p q hlink
    rwa [centralSupport_eq_one_of_factor hfactor p hp,mul_one] at h

end

/-! Trace-free upper bounds of arbitrary directed nets of partial isometries.
A weak operator ultralimit suffices: extension identities with each fixed net
member force the limit to satisfy b b* b = b. No trace or countability is used. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Left multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_left {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((c*a i).val x)) l
      (𝓝 (inner ℂ y ((c*b).val x))) := by
  intro x y
  change Tendsto (fun i => inner ℂ y (c.val ((a i).val x))) l
    (𝓝 (inner ℂ y (c.val (b.val x))))
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    using ht x (star c.val y)

/-- Right multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_right {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i*c).val x)) l
      (𝓝 (inner ℂ y ((b*c).val x))) := fun x y => ht (c.val x) y

/-- Matrix coefficients determine an element of the concrete algebra. -/
theorem wot_limit_unique {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x))))
    (hc : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (c.val x)))) : b=c := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact ext_inner_left ℂ (fun y => tendsto_nhds_unique (hb x y) (hc x y))

namespace PartialIsometry

/-- Every monotone directed net has a partial-isometry upper bound, retaining
any prescribed bounds on its initial and final projections. -/
theorem traceFree_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p q : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ q) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  refine ⟨v, hbp, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul q).mpr
    apply wot_limit_unique (fun i => q.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul q).mp (hq i)] using hb

end PartialIsometry
end

/-! Trace-free chain upper bounds and maximal partial isometries, with prescribed
initial and final projection bounds. The index set may be uncountable. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem traceFree_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p q : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ q) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v, h, le_rfl⟩
    · exact ⟨u, le_rfl, h⟩⟩
  obtain ⟨v, hv, hvp, hvq⟩ := traceFree_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p q
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
  exact ⟨v, fun w hw => hv ⟨w,hw⟩, hvp, hvq⟩

theorem traceFree_exists_maximal_between (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ q → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) := {v | v.support ≤ p ∧ v.target ≤ q}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v, hcv, hvp, hvq⟩ := traceFree_chain_upper_bound c hchain hne p q
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2)
      exact ⟨v, ⟨hvp, hvq⟩, hcv⟩
    · refine ⟨zero, ⟨?_, ?_⟩, ?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul q).mpr
        exact mul_zero _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2,fun w hp hq h => hv.2 ⟨hp,hq⟩ h⟩

end PartialIsometry
end

/-! Projection comparison from scalar center, without a supplied trace.
The maximal partial isometry, central support and polar linking are constructed. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfactor in
theorem traceFree_exists_nonzero_partialIsometry_between_projections
    (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val≠0) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧ v.support.val≠0 := by
  have hex : ∃ a : M.toStarSubalgebra, q.val*a*p.val≠0 := by
    by_contra hn
    have hz : ∀ a : M.toStarSubalgebra, q.val*a*p.val=0 := by
      simpa only [not_exists,not_not] using hn
    exact (traceFree_projection_eq_zero_or_eq_zero_of_no_links hfactor p q hz).elim hp hq
  obtain ⟨a,ha⟩ := hex
  apply exists_partialIsometry_of_link p q (q.val*a*p.val)
  · rw [mul_assoc,p.property.isIdempotentElem.eq]
  · rw [← mul_assoc,← mul_assoc,q.property.isIdempotentElem.eq]
  · exact ha

include hfactor in
theorem traceFree_exists_partialIsometry_comparison (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      (v.support=p ∨ v.target=q) := by
  obtain ⟨v,hvp,hvq,hmax⟩ := PartialIsometry.traceFree_exists_maximal_between p q
  let r : AlgebraProjection M :=
    ⟨p.val-v.support.val,v.support.property.sub_of_mul_eq_right p.property hvp⟩
  let s : AlgebraProjection M :=
    ⟨q.val-v.target.val,v.target.property.sub_of_mul_eq_right q.property hvq⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-v.support.val)=p.val-v.support.val
    rw [mul_sub,p.property.isIdempotentElem.eq,hvp]
  have hsq : s ≤ q := by
    change q.val*(q.val-v.target.val)=q.val-v.target.val
    rw [mul_sub,q.property.isIdempotentElem.eq,hvq]
  have hzero : r.val=0 ∨ s.val=0 := by
    by_contra hn
    have hr : r.val≠0 := fun h => hn (Or.inl h)
    have hs : s.val≠0 := fun h => hn (Or.inr h)
    obtain ⟨w,hwr,hws,hw0⟩ :=
      traceFree_exists_nonzero_partialIsometry_between_projections hfactor r s hr hs
    have hpw : v.support.val*w.support.val=0 := by
      calc _ = v.support.val*(r.val*w.support.val) := by rw [hwr]
           _ = (v.support.val*r.val)*w.support.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.support.val*(p.val-v.support.val))*w.support.val=0
             rw [mul_sub,projection_mul_of_le hvp,v.support.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    have hqw : v.target.val*w.target.val=0 := by
      calc _ = v.target.val*(s.val*w.target.val) := by rw [hws]
           _ = (v.target.val*s.val)*w.target.val := (mul_assoc _ _ _).symm
           _ = 0 := by
             change (v.target.val*(q.val-v.target.val))*w.target.val=0
             rw [mul_sub,projection_mul_of_le hvq,v.target.property.isIdempotentElem.eq,
               sub_self,zero_mul]
    let u := PartialIsometry.patch v w hpw hqw
    have hup : u.support ≤ p := by
      change p.val*(v.support.val+w.support.val)=v.support.val+w.support.val
      rw [mul_add,hvp,show p.val*w.support.val=w.support.val from hwr.trans hrp]
    have huq : u.target ≤ q := by
      apply (u.target_le_iff_mul q).mpr
      change q.val*(v.val+w.val)=v.val+w.val
      rw [mul_add,(v.target_le_iff_mul q).mp hvq,
        (w.target_le_iff_mul q).mp (hws.trans hsq)]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)
  refine ⟨v,hvp,hvq,?_⟩
  rcases hzero with hr | hs
  · exact Or.inl (Subtype.ext (sub_eq_zero.mp hr).symm)
  · exact Or.inr (Subtype.ext (sub_eq_zero.mp hs).symm)

end Tracial

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- The identity partial isometry on a projection. -/
def onProjection (p : AlgebraProjection M) : PartialIsometry M :=
  ⟨p, p.val, by rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]⟩

theorem onProjection_target (p : AlgebraProjection M) : (onProjection p).target=p := by
  apply Subtype.ext
  change p.val*star p.val=p.val
  rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]

/-- A finite algebra has no partial isometry from a projection onto a proper
subprojection of itself. Finiteness is used on v + (1 - p). -/
theorem target_eq_support_of_finite
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.target ≤ v.support) : v.target=v.support := by
  let r : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let w := onProjection r
  have hp : v.support.val*w.support.val=0 := by
    change v.support.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,v.support.property.isIdempotentElem.eq,sub_self]
  have hq : v.target.val*w.target.val=0 := by
    rw [show w.target=r from onProjection_target r]
    change v.target.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,projection_mul_of_le hv,sub_self]
  let u := patch v w hp hq
  have hu : star u.val*u.val=1 := by
    rw [u.initial]
    change v.support.val+(1-v.support.val)=1
    abel
  have huf := hfinite u.val hu
  change u.target.val=1 at huf
  rw [patch_target,show w.target=r from onProjection_target r] at huf
  apply Subtype.ext
  change v.target.val+(1-v.support.val)=1 at huf
  have he : v.target.val+(1-v.support.val)=v.support.val+(1-v.support.val) := by
    rw [huf]
    abel
  exact add_right_cancel he

/-- Finiteness also excludes a proper enlargement equivalent to a projection. -/
theorem target_eq_support_of_finite_of_le
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.support ≤ v.target) : v.target=v.support := by
  have he : v.adjoint.target=v.support := by
    apply Subtype.ext
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial]
  have h := target_eq_support_of_finite hfinite v.adjoint (by
    change v.adjoint.target ≤ v.target
    rw [he]
    exact hv)
  change v.adjoint.target=v.target at h
  rw [he] at h
  exact h.symm

end PartialIsometry
end Tracial

/-- Comparison in the exact original concrete algebra, packaged by its proved
bicommutant property. The underlying operators and star subalgebra are unchanged. -/
theorem isII1Factor_projection_comparison
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S)
    (p q : Tracial.AlgebraProjection (vonNeumannOfWOTClosed S hS.weaklyClosed)) :
    ∃ v : Tracial.PartialIsometry (vonNeumannOfWOTClosed S hS.weaklyClosed),
      v.support ≤ p ∧ v.target ≤ q ∧ (v.support=p ∨ v.target=q) := by
  apply Tracial.traceFree_exists_partialIsometry_comparison
  intro c hc
  obtain ⟨z,hz⟩ := hS.factor c hc
  exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩

/-- The exact original finite-isometry field makes every projection finite. -/
theorem isII1Factor_no_proper_self_equivalence
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S)
    (v : Tracial.PartialIsometry (vonNeumannOfWOTClosed S hS.weaklyClosed))
    (hv : v.target ≤ v.support) : v.target=v.support :=
  Tracial.PartialIsometry.target_eq_support_of_finite hS.finite v hv

end

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/
namespace Tracial
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Orthogonality passes to subprojections in both variables. -/
theorem projection_orthogonal_of_le {p q r s : AlgebraProjection M}
    (h : p.val*q.val=0) (hr : r ≤ p) (hs : s ≤ q) : r.val*s.val=0 := by
  calc _ = (r.val*p.val)*(q.val*s.val) := by rw [projection_mul_of_le hr,hs]
       _ = r.val*(p.val*q.val)*s.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

namespace PartialIsometry

theorem target_mono {v w : PartialIsometry M} (h : v ≤ w) : v.target ≤ w.target := by
  apply (v.target_le_iff_mul w.target).mpr
  calc _ = w.target.val*(w.val*v.support.val) := by rw [h]
       _ = v.val := by rw [← mul_assoc,w.target_mul,h]

/-- A directed increasing family of square-zero partial isometries has an
upper bound with orthogonal initial/final projections inside p. -/
theorem traceFree_orthogonal_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ p)
    (ho : ∀ i, (a i).support.val*(a i).target.val=0) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  have hcross (i j : ι) : (a i).val*(a j).val=0 := by
    obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
    exact (a i).mul_eq_zero (a j)
      (projection_orthogonal_of_le (ho k) (support_mono (ha hik)) (target_mono (ha hjk)))
  have hbi (i : ι) : b*(a i).val=0 := by
    apply wot_limit_unique (fun j => (a j).val*(a i).val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [hcross] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  have hbb : b*b=0 := by
    apply wot_limit_unique (fun i => b*(a i).val) _ _ (wot_limit_mul_left _ _ _ hb)
    simpa only [hbi] using (fun x y : H =>
      (tendsto_const_nhds : Tendsto (fun _ : ι => inner ℂ y ((0 : M.toStarSubalgebra).val x))
        (ω : Filter ι) (𝓝 (inner ℂ y ((0 : M.toStarSubalgebra).val x)))))
  refine ⟨v, hbp, ?_, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => p.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul p).mp (hq i)] using hb
  · change (star b*b)*(b*star b)=0
    calc _ = star b*(b*b)*star b := by simp only [mul_assoc]
         _ = 0 := by rw [hbb,mul_zero,zero_mul]

theorem traceFree_orthogonal_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ p)
    (ho : ∀ v ∈ c, v.support.val*v.target.val=0) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v,h,le_rfl⟩
    · exact ⟨u,le_rfl,h⟩⟩
  obtain ⟨v,hv,hvp,hvq,hvo⟩ := traceFree_orthogonal_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
    (fun w => ho w.val w.property)
  exact ⟨v,fun w hw => hv ⟨w,hw⟩,hvp,hvq,hvo⟩

theorem traceFree_exists_maximal_orthogonal (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ p ∧
      v.support.val*v.target.val=0 ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ p →
        w.support.val*w.target.val=0 → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) :=
    {v | v.support ≤ p ∧ v.target ≤ p ∧ v.support.val*v.target.val=0}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v,hcv,hvp,hvq,hvo⟩ := traceFree_orthogonal_chain_upper_bound c hchain hne p
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2.1) (fun w hw => (hc hw).2.2)
      exact ⟨v,⟨hvp,hvq,hvo⟩,hcv⟩
    · refine ⟨zero,⟨?_,?_,?_⟩,?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul p).mpr
        exact mul_zero _
      · exact zero_mul _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2.1,hv.1.2.2,fun w hp hq ho h => hv.2 ⟨hp,hq,ho⟩ h⟩

/-! Simultaneous least initial and final support bounds for arbitrary directed
partial-isometry nets. The actual ultralimit is chosen once for all bounds. -/

/-- The initial and final projections of this upper bound are the respective
least upper bounds of the net's initial and final projections. -/
theorem traceFree_monotone_least_supports
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧
      (∀ p : AlgebraProjection M, (∀ i, (a i).support ≤ p) → v.support ≤ p) ∧
      (∀ q : AlgebraProjection M, (∀ i, (a i).target ≤ q) → v.target ≤ q) := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  refine ⟨v, hbp, ?_, ?_⟩
  · intro p hp
    apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · intro q hq
    apply (v.target_le_iff_mul q).mpr
    apply wot_limit_unique (fun i => q.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul q).mp (hq i)] using hb

end PartialIsometry
end Tracial

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance unitaryPolarCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance unitaryPolarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance unitaryPolarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hfinite in
theorem PartialIsometry.exists_unitary_extension (v : PartialIsometry M) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*v.support.val=v.val := by
  let p : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let q : AlgebraProjection M := ⟨1-v.target.val,v.target.property.one_sub⟩
  obtain ⟨w,hwp,hwq,hw⟩ := traceFree_exists_partialIsometry_comparison hfactor p q
  have hp : v.support.val*w.support.val=0 := by
    calc _ = v.support.val*(p.val*w.support.val) := by rw [hwp]
      _ = (v.support.val*p.val)*w.support.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.support.val*(1-v.support.val))*w.support.val=0
        rw [v.support.property.mul_one_sub_self,zero_mul]
  have hq : v.target.val*w.target.val=0 := by
    calc _ = v.target.val*(q.val*w.target.val) := by rw [hwq]
      _ = (v.target.val*q.val)*w.target.val := (mul_assoc _ _ _).symm
      _ = 0 := by
        change (v.target.val*(1-v.target.val))*w.target.val=0
        rw [v.target.property.mul_one_sub_self,zero_mul]
  let a := v.patch w hp hq
  have hi : star a.val*a.val=1 := by
    rcases hw with hw | hw
    · rw [a.initial]
      change v.support.val+w.support.val=1
      rw [hw]
      change v.support.val+(1-v.support.val)=1
      abel
    · have hf : a.val*star a.val=1 := by
        change a.target.val=1
        rw [PartialIsometry.patch_target,hw]
        change v.target.val+(1-v.target.val)=1
        abel
      have h := hfinite (star a.val) (by simpa only [star_star] using hf)
      simpa only [star_star] using h
  exact ⟨⟨a.val,⟨hi,hfinite a.val hi⟩⟩,v.le_patch w hp hq⟩

include hfactor hfinite in
theorem exists_unitary_polar_decomposition (x : M.toStarSubalgebra) :
    ∃ u : unitary M.toStarSubalgebra, (u : M.toStarSubalgebra)*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hvx,hvi,_⟩ := exists_polar_decomposition x
  let a := CFC.sqrt (star x*x)
  let w : PartialIsometry M := ⟨rangeProjection a,v,hvi⟩
  obtain ⟨u,hu⟩ := w.exists_unitary_extension hfactor hfinite
  have ha : w.support.val*a=a := rangeProjection_mul a
  refine ⟨u,?_⟩
  calc (u : M.toStarSubalgebra)*a = (u : M.toStarSubalgebra)*(w.support.val*a) := by rw [ha]
    _ = w.val*a := by rw [← mul_assoc,hu]
    _ = x := hvx

end Tracial

end Generator

end

end OAI
