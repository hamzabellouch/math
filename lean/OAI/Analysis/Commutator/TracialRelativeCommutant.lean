import Mathlib
import OAI.Analysis.Commutator.TracialSmallCorners
import OAI.Analysis.Commutator.NormalRelativeCommutant

namespace OAI

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open TracialGNS NormalGNS NormalRelativeCommutant

variable {H D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [CStarAlgebra D]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)
  (hτ : ∀ a b : M, τ (a*b)=τ (b*a)) (π : D →⋆ₐ[ℂ] M) (ω : Ultrafilter ℕ)

def unitarySequence (u : ℕ → unitary D) : ℕ →ᵇ D :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => (u i:D)) 1
    (fun i => by
      cases subsingleton_or_nontrivial D with
      | inl hs => exact le_trans (le_of_eq (by rw [Subsingleton.elim (u i:D) 0,norm_zero])) zero_le_one
      | inr hn => exact (CStarRing.norm_coe_unitary (u i)).le)

@[simp] lemma unitarySequence_apply (u : ℕ → unitary D) (i : ℕ) :
    unitarySequence u i=(u i:D) := rfl

lemma unitarySequence_star_mul (u : ℕ → unitary D) :
    star (unitarySequence u)*unitarySequence u=1 := by
  ext i
  exact (u i).property.1

lemma unitarySequence_mul_star (u : ℕ → unitary D) :
    unitarySequence u*star (unitarySequence u)=1 := by
  ext i
  exact (u i).property.2

lemma conjugate_difference_map_zero {A B : Type*} [Ring A] [Ring B]
    [StarRing A] (f : A →+* B) (a b : A) (hb : b*star b=1)
    (hc : f b*f a=f a*f b) : f (b*a*star b-a)=0 := by
  rw [map_sub,map_mul,map_mul,hc,mul_assoc,←map_mul,hb,map_one,mul_one,sub_self]

lemma algHom_eq_smul_one_of_sub {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (a : A) (c : ℂ) (h : f (a-c • 1)=0) : f a=c • 1 := by
  simpa only [map_sub,map_smul,map_one,sub_eq_zero] using h

private lemma norm_map_sub_smul_le {A E : Type*} [AddCommGroup A] [Module ℂ A]
    [SeminormedAddCommGroup E] [NormedSpace ℂ E] (f : A →ₗ[ℂ] E)
    (x u : A) (c d : ℂ) :
    ‖f (x - c • u)‖ ≤ ‖f (x - d • u)‖ + ‖d - c‖ * ‖f u‖ := by
  have h : f (x - c • u) = f (x - d • u) + (d - c) • f u := by
    simp only [map_sub, map_smul, sub_smul]
    abel
  calc
    _ = ‖f (x - d • u) + (d - c) • f u‖ := congrArg norm h
    _ ≤ ‖f (x - d • u)‖ + ‖(d - c) • f u‖ := norm_add_le _ _
    _ = _ := congrArg (‖f (x - d • u)‖ + ·) (norm_smul _ _)

include hτ in
theorem commutant_contraction_sequence
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ a : D, π a*b=b*π a) → ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : ℕ →ᵇ M) (ha : ‖a‖≤1)
    (hcomm : ∀ b : ℕ →ᵇ D,
      leftRestricted τ ω (mapSequence π b)*leftRestricted τ ω a=
        leftRestricted τ ω a*leftRestricted τ ω (mapSequence π b)) :
    leftRestricted τ ω a=(sequenceTrace τ ω (leftRestricted τ ω a)) • 1 := by
  have hw (i : ℕ) := exists_unitary_witness M τ hτ π hnormal hfaith hone hirr
    (a i) ((a.norm_coe_le_norm i).trans ha)
  choose u hu using hw
  let b := mapSequence π (unitarySequence u)
  have hb : b*star b=1 := by
    change mapSequence π (unitarySequence u)*star (mapSequence π (unitarySequence u))=1
    rw [←map_star,←map_mul,unitarySequence_mul_star,map_one]
  have hc : leftRestricted τ ω (b*a*star b-a)=0 :=
    conjugate_difference_map_zero (leftRestricted τ ω).toAlgHom.toRingHom a b hb (hcomm _)
  have hlim := (vector_eq_zero_iff τ ω _).mp
    ((leftRestricted_eq_zero_iff τ ω hτ _).mp hc)
  have hcenter : Tendsto (fun i => ‖algebraVector τ (a i-algebraMap ℂ M (τ (a i)))‖)
      (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => hu i)
    simpa only [b,BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.mul_apply,
      BoundedContinuousFunction.star_apply,mapSequence_apply,unitarySequence_apply,mul_zero]
      using tendsto_const_nhds.mul hlim
  let c := sequenceTrace τ ω (leftRestricted τ ω a)
  have htrace : Tendsto (fun i => ‖τ (a i)-c‖*‖vacuum τ‖)
      (ω : Filter ℕ) (𝓝 0) := by
    have hh := ((tendsto_trace τ ω a).sub (tendsto_const_nhds (x:=c))).norm.mul_const ‖vacuum τ‖
    simpa only [c,sub_self,norm_zero,zero_mul] using hh
  have hnorm (i : ℕ) :
      ‖algebraVector τ (a i-c • (1:M))‖≤
        ‖algebraVector τ (a i-algebraMap ℂ M (τ (a i)))‖+
          ‖τ (a i)-c‖*‖vacuum τ‖ := by
    have hv : algebraVector τ (1 : M) = vacuum τ := rfl
    simpa only [Algebra.algebraMap_eq_smul_one, hv] using
      norm_map_sub_smul_le (algebraVector τ) (a i) (1 : M) c (τ (a i))
  have hlim0 : Tendsto (fun i => ‖algebraVector τ (a i-c • (1:M))‖)
      (ω : Filter ℕ) (𝓝 0) := by
    exact squeeze_zero (fun i => norm_nonneg (algebraVector τ (a i-c • (1:M))))
      hnorm (by simpa only [zero_add] using hcenter.add htrace)
  have hlim' : Tendsto (fun i => ‖algebraVector τ ((a-c • 1) i)‖)
      (ω : Filter ℕ) (𝓝 0) := by
    simpa only [BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.smul_apply,
      BoundedContinuousFunction.coe_one,Pi.one_apply] using hlim0
  have hz : leftRestricted τ ω (a-c • 1)=0 :=
    (leftRestricted_eq_zero_iff τ ω hτ _).mpr ((vector_eq_zero_iff τ ω _).mpr hlim')
  exact algHom_eq_smul_one_of_sub (leftRestricted τ ω).toAlgHom a c hz

lemma algHom_commutes_smul {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (a b : A) (c : ℂ) (h : f b*f a=f a*f b) :
    f b*f (c • a)=f (c • a)*f b := by
  simp only [map_smul,mul_smul_comm,smul_mul_assoc,h]

lemma algHom_scalar_of_smul {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (a : A) {r : ℂ} (hr : r≠0) (c : ℂ)
    (h : f (r • a)=c • 1) : ∃ d : ℂ, f a=d • 1 := by
  refine ⟨r⁻¹*c,?_⟩
  have hh := congrArg (fun t : B => r⁻¹ • t) h
  simpa only [map_smul,smul_smul,inv_mul_cancel₀ hr,one_smul] using hh

lemma scalar_of_contractions {A B ι : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (g : ι → B)
    (h : ∀ a : A, ‖a‖≤1 → (∀ i, g i*f a=f a*g i) → ∃ c : ℂ, f a=c • 1)
    (a : A) (ha : ∀ i, g i*f a=f a*g i) : ∃ c : ℂ, f a=c • 1 := by
  by_cases hz : a=0
  · exact ⟨0,by rw [hz,map_zero,zero_smul]⟩
  let r : ℂ := (‖a‖:ℂ)⁻¹
  have hr : r≠0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))
  have hn : ‖r • a‖≤1 := (norm_smul_inv_norm (𝕜:=ℂ) hz).le
  have hc : ∀ i, g i*f (r • a)=f (r • a)*g i := by
    intro i
    simp only [map_smul,mul_smul_comm,smul_mul_assoc,ha i]
  obtain ⟨c,hc⟩ := h (r • a) hn hc
  exact algHom_scalar_of_smul f a hr c hc

lemma scalar_of_range {A B ι : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (g : ι → B)
    (h : ∀ a : A, (∀ i, g i*f a=f a*g i) → ∃ c : ℂ, f a=c • 1)
    (T : B) (hT : T∈Set.range f) (hcomm : ∀ i, g i*T=T*g i) : ∃ c : ℂ, T=c • 1 := by
  obtain ⟨a,rfl⟩ := hT
  exact h a hcomm

include hτ in
theorem commutant_sequence_scalar
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ a : D, π a*b=b*π a) → ∃ c : ℂ, b=algebraMap ℂ M c)
    (a : ℕ →ᵇ M)
    (hcomm : ∀ b : ℕ →ᵇ D,
      leftRestricted τ ω (mapSequence π b)*leftRestricted τ ω a=
        leftRestricted τ ω a*leftRestricted τ ω (mapSequence π b)) :
    ∃ c : ℂ, leftRestricted τ ω a=c • 1 := by
  apply scalar_of_contractions (leftRestricted τ ω).toAlgHom
    (fun b : ℕ →ᵇ D => leftRestricted τ ω (mapSequence π b)) _ a hcomm
  intro a ha hc
  exact ⟨_,commutant_contraction_sequence M τ hτ π ω hnormal hfaith hone hirr a ha hc⟩

include hτ in
theorem full_relative_commutant_scalar
    (hnormal : BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (hone : τ 1=1)
    (hirr : ∀ b : M, (∀ a : D, π a*b=b*π a) → ∃ c : ℂ, b=algebraMap ℂ M c)
    (hω : (ω : Filter ℕ)≤atTop)
    {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hcomm : ∀ b : ℕ →ᵇ D,
      leftRestricted τ ω (mapSequence π b)*T=T*leftRestricted τ ω (mapSequence π b)) :
    ∃ c : ℂ, T=c • 1 := by
  have hr : T∈Set.range (leftRestricted τ ω) := by
    exact (congrArg (fun operators => T ∈ operators) (range_bicommutant τ ω hτ hω)).mp hT
  exact scalar_of_range (leftRestricted τ ω).toAlgHom
    (fun b : ℕ →ᵇ D => leftRestricted τ ω (mapSequence π b))
    (commutant_sequence_scalar M τ hτ π ω hnormal hfaith hone hirr) T hr hcomm

end Kadison.TracialSequence
end

end OAI
