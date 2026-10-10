import Mathlib
import OAI.Analysis.Commutator.ProjectionLifts
import OAI.Analysis.Commutator.TracialUltrapowerTransfer

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS HilbertSequence

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def mapSequence (f : A →⋆ₐ[ℂ] B) : (ℕ →ᵇ A) →⋆ₐ[ℂ] (ℕ →ᵇ B) where
  toFun a := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => f (a i))
    ‖a‖ (fun i => (NonUnitalStarAlgHom.norm_apply_le f (a i)).trans (a.norm_coe_le_norm i))
  map_one' := by ext i; exact map_one f
  map_mul' a b := by ext i; exact map_mul f (a i) (b i)
  map_zero' := by ext i; exact map_zero f
  map_add' a b := by ext i; exact map_add f (a i) (b i)
  commutes' z := by ext i; exact AlgHom.commutes f.toAlgHom z
  map_star' a := by ext i; exact map_star f (a i)

@[simp] lemma mapSequence_apply (f : A →⋆ₐ[ℂ] B) (a : ℕ →ᵇ A) (i : ℕ) :
    mapSequence f a i=f (a i) := rfl

variable [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma leftRestricted_eq_of_eventuallyEq {a b : ℕ →ᵇ A}
    (hab : (a : ℕ → A)=ᶠ[ω] b) : leftRestricted τ ω a=leftRestricted τ ω b := by
  apply sub_eq_zero.mp
  rw [←map_sub,leftRestricted_eq_zero_iff τ ω hτ]
  change ((vectorPre τ ω (a-b)) : Space ω τ.GNS)=0
  apply (coe_eq_zero_iff ω τ.GNS _).mpr
  apply tendsto_const_nhds.congr'
  filter_upwards [hab] with i hi
  simp only [vectorPre_seq,BoundedContinuousFunction.sub_apply,hi,sub_self,
    map_zero,norm_zero]

def cutSequence {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (q : ℕ →ᵇ N)
    (good : ℕ → Prop) : ℕ →ᵇ N :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => if good i then q i else 0) ‖q‖ (fun i => by
      split_ifs
      · exact q.norm_coe_le_norm i
      · simpa only [norm_zero] using norm_nonneg q)

@[simp] lemma cutSequence_apply {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (q : ℕ →ᵇ N)
    (good : ℕ → Prop) (i : ℕ) :
    cutSequence N q good i=if good i then q i else 0 := rfl

lemma projection_operator_lift {G K : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (N : VonNeumannAlgebra G) (φ : (ℕ →ᵇ N) →⋆ₐ[ℂ] (K →L[ℂ] K))
    {e : K →L[ℂ] K} (he : IsStarProjection e) (her : e∈Set.range φ) :
    ∃ q : ℕ →ᵇ N, (∀ i, IsStarProjection (q i)) ∧ φ q=e :=
  ProjectionLifts.projection_lift (ι:=ℕ) (B:=(K →L[ℂ] K)) N φ he her

lemma projection_rep_lift {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
    {e : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (he : IsStarProjection e)
    (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f))) :
    ∃ q : ℕ →ᵇ N, (∀ i, IsStarProjection (q i)) ∧ leftRestricted τ ω (mapSequence f q)=e :=
  projection_operator_lift N
    ((leftRestricted τ ω).comp (mapSequence f)) he her

include hτ in
theorem small_projection_lift {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
    {b : ℝ} (hb : 0≤b)
    {e : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (he : IsStarProjection e)
    (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f)))
    (het : (sequenceTrace τ ω e).re<b) :
    ∃ r : ℕ →ᵇ N, (∀ i, IsStarProjection (r i)) ∧
      (∀ i, (τ (f (r i))).re≤b) ∧ leftRestricted τ ω (mapSequence f r)=e := by
  classical
  obtain ⟨q,hq,hqe⟩ := projection_rep_lift τ ω N f he her
  have ht := Complex.continuous_re.tendsto _ |>.comp (tendsto_trace τ ω (mapSequence f q))
  change Tendsto (fun i => (τ (f (q i))).re) (ω : Filter ℕ)
    (𝓝 (sequenceTrace τ ω (leftRestricted τ ω (mapSequence f q))).re) at ht
  have hlim : (sequenceTrace τ ω (leftRestricted τ ω (mapSequence f q))).re < b :=
    lt_of_eq_of_lt (congrArg (fun T => (sequenceTrace τ ω T).re) hqe) het
  have hg : ∀ᶠ i in (ω : Filter ℕ), (τ (f (q i))).re≤b :=
    (ht.eventually (gt_mem_nhds hlim)).mono (fun _ h => h.le)
  let r := cutSequence N q (fun i => (τ (f (q i))).re≤b)
  have hrq : (r : ℕ → N)=ᶠ[ω] q := by
    filter_upwards [hg] with i hi
    exact ite_eq_left hi
  have hre : leftRestricted τ ω (mapSequence f r)=e := by
    exact (leftRestricted_eq_of_eventuallyEq τ ω hτ
      (a := mapSequence f r) (b := mapSequence f q)
      (hrq.mono (fun _ hi => congrArg f hi))).trans hqe
  have hr (i : ℕ) : IsStarProjection (r i) := by
    change IsStarProjection (if _ then q i else 0)
    split_ifs
    · exact hq i
    · exact IsStarProjection.zero _
  have hrt (i : ℕ) : (τ (f (r i))).re≤b := by
    change (τ (f (if _ then q i else 0))).re≤b
    split_ifs with hi
    · exact hi
    · simpa only [map_zero,Complex.zero_re] using hb
  exact ⟨r,hr,hrt,hre⟩

include hτ in
theorem small_corner_bound {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (N : VonNeumannAlgebra G) (f : N →⋆ₐ[ℂ] A)
    (hω : (ω : Filter ℕ)≤atTop)
    (S : τ.GNS →L[ℂ] τ.GNS) {b c : ℝ} (hb : 0≤b) (hc : 0≤c)
    (hS : ∀ (q : N), IsStarProjection q → (τ (f q)).re≤b →
      ∀ a : A, f q*a*f q=a →
        ‖S*τ.gnsStarAlgHom a-τ.gnsStarAlgHom a*S‖≤c*‖a‖)
    {e T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (he : IsStarProjection e)
    (her : e∈Set.range ((leftRestricted τ ω).comp (mapSequence f)))
    (het : (sequenceTrace τ ω e).re<b)
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (heT : e*T*e=T) :
    ‖compressed τ ω S*T-T*compressed τ ω S‖≤c*‖T‖ := by
  obtain ⟨r,hr,hrt,hre⟩ := small_projection_lift τ ω hτ N f hb he her het
  obtain ⟨a,hna,haT⟩ := bicommutant_norm_lift τ ω hτ hω hT
  let z := mapSequence f r*a*mapSequence f r
  have hzT : leftRestricted τ ω z=T := by
    simp only [z,map_mul,hre,haT,heT]
  rw [←hzT]
  apply commutator_bound τ ω S z
  intro i
  have hfi : IsStarProjection (f (r i)) := (hr i).map f
  have hz : f (r i)*z i*f (r i)=z i := by
    change f (r i)*(f (r i)*a i*f (r i))*f (r i)=f (r i)*a i*f (r i)
    simp only [←mul_assoc,hfi.isIdempotentElem.eq]
    rw [mul_assoc _ (f (r i)) (f (r i)),hfi.isIdempotentElem.eq]
  have hn : ‖z i‖≤‖T‖ := by
    change ‖f (r i)*a i*f (r i)‖≤‖T‖
    calc
      _ ≤ ‖f (r i)‖*‖a i‖*‖f (r i)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖a i‖*1 := by gcongr <;> exact hfi.norm_le _
      _ ≤ ‖T‖ := by simpa only [one_mul,mul_one] using (a.norm_coe_le_norm i).trans hna
  exact (hS (r i) (hr i) (hrt i) (z i) hz).trans
    (by rw [hzT]; exact mul_le_mul_of_nonneg_left hn hc)

end Kadison.TracialSequence

end

end OAI
