import Mathlib
import OAI.Analysis.BoundedHochschild.ExponentialLifts
import OAI.Analysis.BoundedHochschild.SpectralProjections

namespace OAI

/-! Unitary lifts and coordinate realizations of free path moments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
namespace HochschildUnitaryLift
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma norm_sub_one_lt_two (u : unitary M) (hu : 0 ≤ (u : M)+star (u : M)) :
    ‖(u : M)-1‖ < 2 := by
  have hh : star ((u : M)-1)*((u : M)-1)=2-((u : M)+star (u : M)) := by
    rw [star_sub,star_one,sub_mul,mul_sub,mul_sub,Unitary.star_mul_self_of_mem u.prop]
    simp only [one_mul,mul_one,← one_add_one_eq_two]
    abel
  have hn : ‖star ((u : M)-1)*((u : M)-1)‖ ≤ 2 := by
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (by norm_num : (0 : ℝ) ≤ 2) (star_mul_self_nonneg _)).mpr
    rw [hh]
    simpa only [map_ofNat] using sub_le_self (2 : M) hu
  rw [CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg ((u : M)-1)]

lemma exists_symmetry_cut (u : unitary M)
    (hsupport : ∀ a : M, 0 ≤ a → ∃ p : M, IsSupportProjection a p) :
    ∃ s : unitary M, IsSelfAdjoint (s : M) ∧
      0 ≤ ((s*u : unitary M) : M)+star ((s*u : unitary M) : M) := by
  let c : M := (selfAdjointPart ℝ (u : M) : M)
  have hc : IsSelfAdjoint c := (selfAdjointPart ℝ (u : M)).property
  have hcu : Commute c (u : M) := by
    dsimp [c]
    rw [selfAdjointPart_apply_coe]
    apply Commute.smul_left
    apply Commute.add_left (Commute.refl _)
    rw [commute_iff_eq,Unitary.star_mul_self_of_mem u.prop,Unitary.mul_star_self_of_mem u.prop]
  obtain ⟨p,hp⟩ := hsupport c⁻ (CFC.negPart_nonneg c)
  have hpu : Commute p (u : M) :=
    hp.commute (IsSelfAdjoint.of_nonneg (CFC.negPart_nonneg c)) (hcu.cfcₙ_real _)
  have hpp : p*p=p := hp.proj.isIdempotentElem.eq
  have hps : star p=p := hp.proj.isSelfAdjoint.star_eq
  have hpplus : p*c⁺=0 := hp.annihilate _ (CFC.negPart_mul_posPart c)
  have hpc : p*c= -c⁻ := by
    nth_rw 1 [← CFC.posPart_sub_negPart c hc]
    rw [mul_sub,hpplus,hp.left,zero_sub]
  have hs : IsSelfAdjoint (1-2*p : M) := by
    change star (1-2*p : M)=1-2*p
    simp only [star_sub,star_one,star_mul,star_ofNat,hps]
    noncomm_ring
  have hss : (1-2*p : M)*(1-2*p)=1 := by
    calc
      _ = 1-4*p+4*(p*p) := by noncomm_ring
      _ = 1 := by rw [hpp]; noncomm_ring
  let s : unitary M := ⟨1-2*p,by rw [Unitary.mem_iff,hs.star_eq]; exact ⟨hss,hss⟩⟩
  have hs' : IsSelfAdjoint (s : M) := hs
  have hsc : (s : M)*c=c⁺+c⁻ := by
    change (1-2*p)*c=_
    rw [sub_mul,one_mul,mul_assoc,hpc]
    nth_rw 1 [← CFC.posPart_sub_negPart c hc]
    noncomm_ring
  have hsu : Commute (s : M) (u : M) := by
    change Commute (1-2*p) (u : M)
    exact (Commute.one_left _).sub_left ((Commute.ofNat_left _ _).mul_left hpu)
  have hsu' : Commute (s : M) (star (u : M)) := by
    simpa only [hs'.star_eq] using hsu.star_star
  have hsum : (u : M)+star (u : M)=2*c := by
    dsimp [c]
    rw [selfAdjointPart_apply_coe]
    rw [mul_smul_comm,two_mul,← two_smul ℝ,smul_smul]
    norm_num
  refine ⟨s,hs',?_⟩
  have he : ((s*u : unitary M) : M)+star ((s*u : unitary M) : M)=2*(c⁺+c⁻) := by
    change (s : M)*(u : M)+star ((s : M)*(u : M))=_
    rw [star_mul,hs'.star_eq,← hsu'.eq,← mul_add,hsum]
    calc
      _ = 2*((s : M)*c) := by noncomm_ring
      _ = _ := by rw [hsc]
  rw [he,two_mul]
  exact add_nonneg (add_nonneg (CFC.posPart_nonneg c) (CFC.negPart_nonneg c))
    (add_nonneg (CFC.posPart_nonneg c) (CFC.negPart_nonneg c))

 

theorem exists_three_exponentials (u : unitary M)
    (hsupport : ∀ a : M, 0 ≤ a → ∃ p : M, IsSupportProjection a p) :
    ∃ a b c : selfAdjoint M,
      selfAdjoint.expUnitary a*selfAdjoint.expUnitary b*selfAdjoint.expUnitary c=u := by
  obtain ⟨s,hs,hpos⟩ := exists_symmetry_cut u hsupport
  have hI : Complex.I ∈ unitary ℂ := by simp [Unitary.mem_iff]
  have hnegI : -Complex.I ∈ unitary ℂ := by simp [Unitary.mem_iff]
  let r : unitary M := ⟨Complex.I • (s : M),Unitary.smul_mem_of_mem hI s.prop⟩
  let t : unitary M := ⟨(-Complex.I) • (1 : M),Unitary.smul_mem_of_mem hnegI (one_mem _)⟩
  have hr : 0 ≤ (r : M)+star (r : M) := by
    change 0 ≤ Complex.I • (s : M)+star (Complex.I • (s : M))
    simp [star_smul,hs.star_eq]
  have ht : 0 ≤ (t : M)+star (t : M) := by
    change 0 ≤ (-Complex.I) • (1 : M)+star ((-Complex.I) • (1 : M))
    simp [star_smul]
  refine ⟨Unitary.argSelfAdjoint r,Unitary.argSelfAdjoint t,
    Unitary.argSelfAdjoint (s*u),?_⟩
  rw [expUnitary_argSelfAdjoint (norm_sub_one_lt_two r hr),
    expUnitary_argSelfAdjoint (norm_sub_one_lt_two t ht),
    expUnitary_argSelfAdjoint (norm_sub_one_lt_two (s*u) hpos)]
  have hrt : r*t=s := by
    apply Subtype.ext
    change (Complex.I • (s : M))*((-Complex.I) • (1 : M))=(s : M)
    rw [smul_mul_smul_comm,mul_one]
    simp
  rw [hrt,← mul_assoc]
  have hss : s*s=1 := by
    apply Subtype.ext
    change (s : M)*(s : M)=1
    nth_rw 1 [← hs.star_eq]
    rw [Unitary.star_mul_self_of_mem s.prop]
  rw [hss,one_mul]

end HochschildUnitaryLift

namespace HochschildUltrapower
open Filter
open scoped BoundedContinuousFunction
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : A, τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ) ≤ atTop)

include hω

 

theorem exists_unitary_lift (u : unitary (Ultrapower τ h1 ω htr)) :
    ∃ v : unitary (ℕ →ᵇ A), quotientHom τ h1 ω htr (v : ℕ →ᵇ A)=
      (u : Ultrapower τ h1 ω htr) := by
  obtain ⟨a,b,c,habc⟩ := HochschildUnitaryLift.exists_three_exponentials u
    (exists_support_projection τ h1 ω htr hω)
  obtain ⟨v,hv⟩ := exists_expUnitary_lift τ h1 ω htr a
  obtain ⟨w,hw⟩ := exists_expUnitary_lift τ h1 ω htr b
  obtain ⟨z,hz⟩ := exists_expUnitary_lift τ h1 ω htr c
  refine ⟨v*w*z,?_⟩
  change quotientHom τ h1 ω htr ((v : ℕ →ᵇ A)*(w : ℕ →ᵇ A)*(z : ℕ →ᵇ A))=_
  rw [map_mul,map_mul,hv,hw,hz]
  exact congrArg Subtype.val habc

 

theorem exists_unitary_coordinates {D : Type*}
    (h : D → unitary (Ultrapower τ h1 ω htr)) :
    ∃ u : ℕ → D → unitary A, ∀ d,
      quotientFamily τ h1 ω htr (fun j => FreeGroup.lift (u j)) (FreeGroup.of d) =
        (h d : Ultrapower τ h1 ω htr) := by
  choose v hv using fun d => exists_unitary_lift τ h1 ω htr hω (h d)
  let u : ℕ → D → unitary A := fun j d =>
    Unitary.map { (sequenceEval (A := A) j).toMonoidHom with
      map_star' := fun _ => rfl } (v d)
  refine ⟨u,fun d => ?_⟩
  rw [← hv d]
  apply congrArg (quotientHom τ h1 ω htr)
  ext j
  simp only [boundedHom_apply,FreeGroup.lift_apply_of,u,Unitary.coe_map]
  rfl

end HochschildUltrapower

 

open Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildPaths
open HochschildUltrapower HochschildRare
variable {M C D : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (ω : Ultrafilter ℕ)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hω : (ω : Filter ℕ) ≤ atTop)
include hω

 

theorem simultaneous_paths_of_free_unitaries
    (v : C → unitary M) (h : D → unitary (Ultrapower τ h1 ω htr))
    (B : Subalgebra ℂ (Ultrapower τ h1 ω htr)) (b : C → Bˣ)
    (hb : ∀ c, ((b c : B) : Ultrapower τ h1 ω htr)=constant τ h1 ω htr (v c : M))
    (hu : ∀ g : FreeGroup D, g ≠ 1 →
      quotientTrace τ h1 ω htr
        (freshEvaluation (fun d => Unitary.toUnits (h d)) g)=0)
    (hfree : HochschildFreeMoments.FreeCoefficients B
      (freshEvaluation (fun d => Unitary.toUnits (h d)))
      (quotientTrace τ h1 ω htr).toLinearMap)
    {T : Type*} [Finite T] (r n : T → ℕ)
    (w : ∀ t, Fin (r t) × Fin (n t) → (C ⊕ D) × Bool)
    (q : ∀ t, FreeGroup (Fin (r t))) (hq : ∀ t, q t ≠ 1)
    (hletters : ∀ t, ∃ (s : Fin (r t) → Fin (n t)) (a : Fin (r t) → D),
      (∀ i, (w t (i,s i)).1=Sum.inr (a i)) ∧
      (∀ i z, (w t z).1=Sum.inr (a i) → z=(i,s i)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : D → unitary M, ∀ t,
      ‖τ (FreeGroup.lift (pathValue (Sum.elim v u) (w t)) (q t) : M)‖ < ε := by
  obtain ⟨u,hu'⟩ := exists_unitary_coordinates τ h1 ω htr hω h
  have he : freshUnits τ h1 ω htr u =
      fun d => Unitary.toUnits (h d) := by
    funext d
    apply Units.ext
    exact hu' d
  have hhu : ∀ g : FreeGroup D, g ≠ 1 →
      quotientTrace τ h1 ω htr (freshEvaluation (freshUnits τ h1 ω htr u) g)=0 := by
    simpa only [he] using hu
  have hhfree : HochschildFreeMoments.FreeCoefficients B
      (freshEvaluation (freshUnits τ h1 ω htr u))
      (quotientTrace τ h1 ω htr).toLinearMap := by
    simpa only [he] using hfree
  obtain ⟨j,hj⟩ := simultaneous_paths_of_free_lifts τ h1 ω htr v u B b hb
    hhu hhfree r n w q hq hletters ε hε
  exact ⟨u j,hj⟩

end HochschildPaths
end

end OAI
