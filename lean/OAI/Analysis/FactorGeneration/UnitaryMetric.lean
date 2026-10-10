import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Metrizable.Basic
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Bounded self-adjoint least-distance elements in a von Neumann subalgebra. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def selfAdjointTraceBall (τ : TracialRepresentation N) (R : ℝ) : Set H :=
  {ξ | ∃ a : N.toStarSubalgebra, IsSelfAdjoint a ∧ ‖a‖ ≤ R ∧ baseVector τ a=ξ}

theorem selfAdjointTraceBall_closed (τ : TracialRepresentation N) (R : ℝ) :
    IsClosed (selfAdjointTraceBall τ R) := by
  apply IsSeqClosed.isClosed
  intro ξ z hz hlim
  choose a ha hR he using hz
  have hlimA : Tendsto (fun n => baseVector τ (a n)) atTop (𝓝 z) := by
    convert hlim using 1
    exact funext he
  obtain ⟨b,hb,hbz⟩ := bounded_trace_limit τ a R ((norm_nonneg _).trans (hR 0)) hR z
    hlimA
  have hvec : Tendsto (fun n => (a n : H →L[ℂ] H) τ.vector) atTop
      (𝓝 ((b : H →L[ℂ] H) τ.vector)) := by rw [hbz]; exact hlimA
  have h := (tendsto_vector_iff_norm₂ τ atTop a b).mp hvec
  have hs := norm₂_limit_star τ a b h
  simp only [(ha _).star_eq] at hs
  have hsb : star b=b := norm₂_limit_unique τ a hs h
  exact ⟨b,hsb,hb,hbz⟩

theorem selfAdjointTraceBall_convex (τ : TracialRepresentation N) (R : ℝ) :
    Convex ℝ (selfAdjointTraceBall τ R) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨a,ha,hRa,rfl⟩ := hx
  obtain ⟨b,hb,hRb,rfl⟩ := hy
  refine ⟨s • a+t • b,((IsSelfAdjoint.all s).smul ha).add
    ((IsSelfAdjoint.all t).smul hb),?_,rfl⟩
  calc ‖s • a+t • b‖ ≤ ‖s • a‖+‖t • b‖ := norm_add_le _ _
       _ = s*‖a‖+t*‖b‖ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg hs,Real.norm_of_nonneg ht]
       _ ≤ s*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hRa hs)
          (mul_le_mul_of_nonneg_left hRb ht)
       _ = R := by rw [← add_mul,hst,one_mul]

theorem exists_selfAdjoint_ball_minimum (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : N.toStarSubalgebra, IsSelfAdjoint c ∧ ‖c‖ ≤ R ∧
      ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
        τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a) := by
  let τN := restrictedTrace τ hNM
  let K := selfAdjointTraceBall τN R
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨ξ,hξ,hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (show K.Nonempty from ⟨0,0,IsSelfAdjoint.zero _,by simpa using hR,rfl⟩)
    (selfAdjointTraceBall_closed τN R).isComplete (selfAdjointTraceBall_convex τN R)
    (baseVector τ x)
  obtain ⟨c,hc,hRc,rfl⟩ := hξ
  refine ⟨c,hc,hRc,?_⟩
  intro a ha hRa
  have h := ciInf_le (show BddBelow (Set.range (fun w : K => ‖baseVector τ x-w.val‖)) from
    ⟨0,by rintro _ ⟨w,rfl⟩; exact norm_nonneg _⟩)
    (⟨baseVector τN a,a,ha,hRa,rfl⟩ : K)
  rw [← hmin] at h
  exact h

theorem exists_selfAdjoint_ball_variational (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : N.toStarSubalgebra, IsSelfAdjoint c ∧ ‖c‖ ≤ R ∧
      (∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
        τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) ∧
      ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
        (inner ℂ (baseVector τ (x-coordinateInclusion hNM c))
          (baseVector τ (coordinateInclusion hNM (a-c)))).re ≤ 0 := by
  let τN := restrictedTrace τ hNM
  let K := selfAdjointTraceBall τN R
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨ξ,hξ,hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (show K.Nonempty from ⟨0,0,IsSelfAdjoint.zero _,by simpa using hR,rfl⟩)
    (selfAdjointTraceBall_closed τN R).isComplete (selfAdjointTraceBall_convex τN R)
    (baseVector τ x)
  obtain ⟨c,hc,hRc,rfl⟩ := hξ
  refine ⟨c,hc,hRc,?_,?_⟩
  · intro a ha hRa
    have h := ciInf_le (show BddBelow (Set.range (fun w : K => ‖baseVector τ x-w.val‖)) from
      ⟨0,by rintro _ ⟨w,rfl⟩; exact norm_nonneg _⟩)
      (⟨baseVector τN a,a,ha,hRa,rfl⟩ : K)
    rw [← hmin] at h
    exact h
  · intro a ha hRa
    have h := (norm_eq_iInf_iff_real_inner_le_zero (selfAdjointTraceBall_convex τN R)
      (show baseVector τN c ∈ K from ⟨c,hc,hRc,rfl⟩)).mp hmin
      (baseVector τN a) ⟨a,ha,hRa,rfl⟩
    exact h

end

/-! Countable determination of a relative commutant from actual L2
separability. Operator norm separability is not required. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem commute_of_norm₂_limit (a : ℕ → M.toStarSubalgebra)
    (b c : M.toStarSubalgebra)
    (ha : Tendsto (fun n => τ.norm₂ (a n-b)) atTop (𝓝 0))
    (hc : ∀ n,Commute (a n) c) : Commute b c := by
  have hr : Tendsto (fun n => τ.norm₂ (a n*c-b*c)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using ha.mul_const ‖c‖)
    rw [← sub_mul]
    exact τ.norm₂_mul_le_right _ _
  have hl : Tendsto (fun n => τ.norm₂ (a n*c-c*b)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using ha.const_mul ‖c‖)
    rw [(hc n).eq,← mul_sub]
    exact τ.norm₂_mul_le _ _
  exact norm₂_limit_unique τ (fun n => a n*c) hr hl

theorem exists_countable_commutant_family (S : Set M.toStarSubalgebra)
    (hne : S.Nonempty) (hsep : TopologicalSpace.IsSeparable (baseVector τ '' S)) :
    ∃ a : ℕ → M.toStarSubalgebra,(∀ n,a n ∈ S) ∧
      ∀ c : M.toStarSubalgebra,(∀ n,Commute (a n) c) ↔ ∀ b ∈ S,Commute b c := by
  let T := baseVector τ '' S
  let : TopologicalSpace.SeparableSpace T := hsep.separableSpace
  let : Nonempty T := ⟨⟨baseVector τ hne.choose,Set.mem_image_of_mem _ hne.choose_spec⟩⟩
  obtain ⟨v,hv⟩ := TopologicalSpace.exists_dense_seq (α := T)
  have hex (n : ℕ) : ∃ a ∈ S,baseVector τ a=(v n).val := (v n).property
  choose a ha he using hex
  refine ⟨a,ha,fun c => ⟨?_,fun h n => h (a n) (ha n)⟩⟩
  intro hc b hb
  let z : T := ⟨baseVector τ b,Set.mem_image_of_mem _ hb⟩
  obtain ⟨w,hw,hlim⟩ := mem_closure_iff_seq_limit.mp (hv z)
  choose k hk using hw
  have ht : Tendsto (fun n => baseVector τ (a (k n))) atTop (𝓝 (baseVector τ b)) := by
    have h := continuous_subtype_val.continuousAt.tendsto.comp hlim
    convert h using 1
    funext n
    exact (he (k n)).trans (congrArg Subtype.val (hk n))
  exact commute_of_norm₂_limit τ (fun n => a (k n)) b c
    ((tendsto_vector_iff_norm₂ τ atTop _ b).mp ht) (fun n => hc (k n))

end

/-! The unitary metric induced by a faithful trace vector, distinguishing the trace two-norm topology from the operator norm topology. -/
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

structure TraceUnitary (τ : TracialRepresentation M) where
  toUnitary : unitary M.toStarSubalgebra

namespace TraceUnitary

def algebra (u : TraceUnitary τ) : M.toStarSubalgebra := u.toUnitary

def vector (u : TraceUnitary τ) : H := (u.algebra τ).val τ.vector

theorem vector_injective : Function.Injective (vector τ) := by
  intro u v h
  have he : u.algebra τ = v.algebra τ := by
    apply sub_eq_zero.mp
    apply τ.separating
    exact sub_eq_zero.mpr h
  cases u
  cases v
  congr 1
  exact Subtype.ext he

instance : MetricSpace (TraceUnitary τ) :=
  MetricSpace.induced (vector τ) (vector_injective τ) inferInstance

theorem vector_isometry : Isometry (vector τ) := fun _ _ => rfl

@[simp] theorem dist_eq (u v : TraceUnitary τ) :
    dist u v = τ.norm₂ (u.algebra τ-v.algebra τ) := by
  change dist (vector τ u) (vector τ v) = _
  rw [dist_eq_norm]
  rfl

theorem algebra_norm_le (u : TraceUnitary τ) : ‖u.algebra τ‖ ≤ 1 :=
  unitary_norm_le _ u.toUnitary.property.1

theorem unitary_of_limit (u : ℕ → TraceUnitary τ) (a : M.toStarSubalgebra)
    (ha : Tendsto (fun n => τ.norm₂ ((u n).algebra τ-a)) atTop (𝓝 0)) :
    a ∈ unitary M.toStarSubalgebra := by
  have hs := norm₂_limit_star τ (fun n => (u n).algebra τ) a ha
  have hleft := norm₂_limit_mul τ (fun n => star ((u n).algebra τ))
    (fun n => (u n).algebra τ) (star a) a 1
    (fun n => by
      change ‖star ((u n).algebra τ).val‖ ≤ 1
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint.norm_map]
      exact algebra_norm_le τ (u n)) hs ha
  have hright := norm₂_limit_mul τ (fun n => (u n).algebra τ)
    (fun n => star ((u n).algebra τ)) a (star a) 1
    (fun n => algebra_norm_le τ (u n)) ha hs
  have hconst : Tendsto (fun _ : ℕ => τ.norm₂ ((1 : M.toStarSubalgebra)-1))
      atTop (𝓝 0) := by simpa only [sub_self,τ.norm₂_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hl (n : ℕ) : star ((u n).algebra τ)*(u n).algebra τ=1 :=
    (u n).toUnitary.property.1
  have hr (n : ℕ) : (u n).algebra τ*star ((u n).algebra τ)=1 :=
    (u n).toUnitary.property.2
  simp only [hl] at hleft
  simp only [hr] at hright
  exact ⟨norm₂_limit_unique τ _ hleft hconst, norm₂_limit_unique τ _ hright hconst⟩

theorem vector_range_closed : IsClosed (Set.range (vector τ)) := by
  apply IsSeqClosed.isClosed
  intro x y hx hxy
  choose u hu using hx
  obtain ⟨a,_,hay⟩ := bounded_trace_limit τ (fun n => (u n).algebra τ) 1 zero_le_one
    (fun n => algebra_norm_le τ (u n)) y (by change Tendsto (fun n => vector τ (u n)) atTop (𝓝 y); simpa only [hu] using hxy)
  have ht : Tendsto (fun n => τ.norm₂ ((u n).algebra τ-a)) atTop (𝓝 0) := by
    apply (tendsto_vector_iff_norm₂ τ atTop _ a).mp
    change Tendsto (fun n => vector τ (u n)) atTop (𝓝 (a.val τ.vector))
    simpa only [hu,hay] using hxy
  exact ⟨⟨⟨a,unitary_of_limit τ u a ht⟩⟩,hay⟩

instance : CompleteSpace (TraceUnitary τ) :=
  (completeSpace_iff_isComplete_range (vector_isometry τ).isUniformInducing).mpr
    (vector_range_closed τ).isComplete

/-- Convergence in the constructed metric is exactly trace two-norm convergence. -/
theorem tendsto_iff {I : Type*} (l : Filter I) (u : I → TraceUnitary τ)
    (v : TraceUnitary τ) :
    Tendsto u l (𝓝 v) ↔ Tendsto (fun i => τ.norm₂ ((u i).algebra τ-v.algebra τ)) l (𝓝 0) := by
  simpa only [dist_eq] using (tendsto_iff_dist_tendsto_zero (f := u) (a := v) (x := l))

end TraceUnitary

end Generator.Tracial

end

end OAI
