import Mathlib
import OAI.Analysis.Commutator.ConvexIsometryFix
import OAI.Analysis.Commutator.NormalGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace Kadison.NormalRelativeCommutant

open TracialGNS NormalGNS

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra D]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (π : D →⋆ₐ[ℂ] M)

def liftedUnitary (u : unitary D) : unitary M := ⟨π (u:D), Unitary.map_mem π u.property⟩

def orbit (a : M) : Set τ.GNS :=
  Set.range (fun u : unitary D => algebraVector τ (π (u:D)*a*star (π (u:D))))

lemma orbit_self (a : M) : algebraVector τ a∈orbit M τ π a := by
  refine ⟨1,?_⟩
  simp

lemma conjugation_orbit (a : M) (u : unitary D) :
    ∀ x∈orbit M τ π a, conjugation τ hτ (liftedUnitary M π u) x∈orbit M τ π a := by
  rintro x ⟨v,rfl⟩
  refine ⟨u*v,?_⟩
  simp only [algebraVector_apply,conjugation_coe,liftedUnitary,Submonoid.coe_mul,
    map_mul,star_mul,mul_assoc]

lemma vector_injective (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) :
    Function.Injective (algebraVector τ) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply hfaith
  have hv : algebraVector τ (a-b)=0 := by rw [map_sub,hab,sub_self]
  rw [←inner_algebraVector,hv,inner_zero_left]

lemma vector_unitball_convex :
    Convex ℝ {x : τ.GNS | ∃ a : M, ‖a‖≤1 ∧ algebraVector τ a=x} := by
  have hh := (convex_closedBall (0:M) 1).linear_image ((algebraVector τ).restrictScalars ℝ)
  simpa only [Metric.closedBall,dist_zero_right,LinearMap.coe_restrictScalars,Set.mem_ofPred_eq,
    Set.image,exists_prop] using hh

lemma hull_bounded (hnormal : BoundedWOTContinuous M τ) (a : M) (ha : ‖a‖≤1) :
    closedConvexHull ℝ (orbit M τ π a) ⊆
      {x : τ.GNS | ∃ b : M, ‖b‖≤1 ∧ algebraVector τ b=x} := by
  apply closedConvexHull_min _ (vector_unitball_convex M τ) (vector_unitball_isClosed M τ hnormal)
  rintro x ⟨u,rfl⟩
  refine ⟨π (u:D)*a*star (π (u:D)),?_,rfl⟩
  have hn : ‖π (u:D)*a*star (π (u:D))‖=‖a‖ := by
    exact (CStarRing.norm_mul_coe_unitary _ (star (liftedUnitary M π u))).trans
      (CStarRing.norm_coe_unitary_mul (liftedUnitary M π u) a)
  rwa [hn]

include hτ in
lemma hull_trace (a : M) :
    ∀ x∈closedConvexHull ℝ (orbit M τ π a), inner ℂ (vacuum τ) x=τ a := by
  apply closedConvexHull_min
  · rintro x ⟨u,rfl⟩
    change inner ℂ (vacuum τ) (algebraVector τ (π (u:D)*a*star (π (u:D))))=τ a
    rw [inner_vacuum_algebraVector,hτ,←mul_assoc]
    have hu : star (π (u:D))*π (u:D)=1 := (liftedUnitary M π u).property.1
    rw [hu,one_mul]
  · exact (convex_singleton (τ a)).linear_preimage ((innerSL ℂ (vacuum τ)).toLinearMap.restrictScalars ℝ)
  · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

lemma commutes_of_fixed (b : M) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hfix : ∀ u : unitary D,
      conjugation τ hτ (liftedUnitary M π u) (algebraVector τ b)=algebraVector τ b) :
    ∀ a : D, π a*b=b*π a := by
  have hu (u : unitary D) : π (u:D)*b=b*π (u:D) := by
    have hh0 := hfix u
    rw [algebraVector_apply,conjugation_coe] at hh0
    have he : π (u:D)*b*star (π (u:D))=b := vector_injective M τ hfaith hh0
    have hh := congrArg (fun x : M => x*π (u:D)) he
    have hut : star (π (u:D))*π (u:D)=1 := (liftedUnitary M π u).property.1
    simpa only [mul_assoc,hut,mul_one] using hh
  intro a
  have ha : a∈Submodule.span ℂ (unitary D:Set D) := by rw [CStarAlgebra.span_unitary]; trivial
  induction ha using Submodule.span_induction with
  | mem a ha => exact hu ⟨a,ha⟩
  | zero => simp
  | add a b ha hb h1 h2 => simp only [map_add,add_mul,mul_add,h1,h2]
  | smul c a ha h1 => simp only [map_smul,smul_mul_assoc,mul_smul_comm,h1]

include hτ in
theorem scalar_mem_hull_contraction
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ a : D, π a*b=b*π a) → ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) :
    (τ a) • vacuum τ∈closedConvexHull ℝ (orbit M τ π a) := by
  obtain ⟨z,hz,hfix⟩ := ConvexIsometry.exists_fixed (closedConvexHull ℝ (orbit M τ π a))
    ⟨algebraVector τ a,subset_closedConvexHull (orbit_self M τ π a)⟩
    isClosed_closedConvexHull convex_closedConvexHull
  obtain ⟨b,_,hb⟩ := hull_bounded M τ π hnormal a ha hz
  have hf : ∀ u : unitary D,
      conjugation τ hτ (liftedUnitary M π u) (algebraVector τ b)=algebraVector τ b := by
    intro u
    rw [hb]
    exact hfix _ (ConvexIsometry.maps_closedConvexHull _ _ (conjugation_orbit M τ hτ π a u))
  obtain ⟨c,hc⟩ := hirr b (commutes_of_fixed M τ hτ π b hfaith hf)
  have htc : τ b=c := by rw [hc,Algebra.algebraMap_eq_smul_one,map_smul,hone,smul_eq_mul,mul_one]
  have hta : τ b=τ a := by rw [←inner_vacuum_algebraVector,hb]; exact hull_trace M τ hτ π a z hz
  have hz' : z=(τ a) • vacuum τ := by
    rw [←hb,hc,Algebra.algebraMap_eq_smul_one,map_smul,←hta,htc]
    rfl
  rwa [hz'] at hz

include hτ in
theorem scalar_distance_le
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ a : D, π a*b=b*π a) → ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) (c : ℝ)
    (hc : ∀ u : unitary D,
      ‖algebraVector τ (π (u:D)*a*star (π (u:D))-a)‖≤c) :
    ‖algebraVector τ (a-algebraMap ℂ M (τ a))‖≤c := by
  have hh : closedConvexHull ℝ (orbit M τ π a) ⊆
      Metric.closedBall (algebraVector τ a) c := by
    apply closedConvexHull_min _ (convex_closedBall _ _) Metric.isClosed_closedBall
    rintro x ⟨u,rfl⟩
    simpa only [Metric.mem_closedBall,dist_eq_norm,map_sub] using hc u
  have hm := hh (scalar_mem_hull_contraction M τ hτ π hnormal hfaith hone hirr a ha)
  rw [Metric.mem_closedBall,dist_comm,dist_eq_norm] at hm
  simpa only [map_sub,Algebra.algebraMap_eq_smul_one,map_smul,algebraVector_apply,vacuum] using hm

include hτ in
theorem exists_unitary_witness
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ a : D, π a*b=b*π a) → ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : M) (ha : ‖a‖≤1) :
    ∃ u : unitary D,
      ‖algebraVector τ (a-algebraMap ℂ M (τ a))‖≤
        2*‖algebraVector τ (π (u:D)*a*star (π (u:D))-a)‖ := by
  by_cases hz : ‖algebraVector τ (a-algebraMap ℂ M (τ a))‖=0
  · exact ⟨1,by rw [hz]; positivity⟩
  by_contra hn
  push Not at hn
  have hb : ∀ u : unitary D,
      ‖algebraVector τ (π (u:D)*a*star (π (u:D))-a)‖≤
        ‖algebraVector τ (a-algebraMap ℂ M (τ a))‖/2 := by
    intro u
    have hi := hn u
    linarith
  have hh := scalar_distance_le M τ hτ π hnormal hfaith hone hirr a ha _ hb
  have hp := (norm_nonneg (algebraVector τ (a-algebraMap ℂ M (τ a)))).lt_of_ne' hz
  linarith

end Kadison.NormalRelativeCommutant

end

end
end

end OAI
