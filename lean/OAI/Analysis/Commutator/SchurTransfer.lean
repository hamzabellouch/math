import Mathlib
import OAI.Analysis.Commutator.TwoByTwoPositive

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder ContinuousFunctionalCalculus Topology

open Filter

namespace Kadison.CStarBlock

variable {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

omit [PartialOrder A] [StarOrderedRing A] in
lemma conjugate_diagonal (a b c d u v : A) :
    star (block u 0 0 v)*block a b c d*block u 0 0 v=
      block (star u*a*u) (star u*b*v) (star v*c*u) (star v*d*v) := by
  simp [star_block,block_mul]

omit [PartialOrder C] [StarOrderedRing C] in
lemma transfer_unit_square (φ : C →⋆ₐ[ℂ] A) (ψ : C →⋆ₐ[ℂ] B)
    (f : A →ₗ[ℂ] B) (hf : ∀ a,‖f a‖≤‖a‖)
    (hmod : ∀ c a d,f (φ c*a*φ d)=ψ c*f a*ψ d)
    (u v : Cˣ) (x : A)
    (hx : 0 ≤ block (φ (star (u:C)*u)) x (star x) (φ (star (v:C)*v))) :
    0 ≤ block (ψ (star (u:C)*u)) (f x) (star (f x)) (ψ (star (v:C)*v)) := by
  have hcancelφ (w : Cˣ) : star (φ (↑w⁻¹))*star (φ (w:C))=1 := by
    rw [←star_mul,←map_mul]; simp
  have hcancelψ (w : Cˣ) : star (ψ (w:C))*star (ψ (↑w⁻¹))=1 := by
    rw [←star_mul,←map_mul]; simp
  let ui : A := φ (↑u⁻¹)
  let vi : A := φ (↑v⁻¹)
  let y := star ui*x*vi
  have he : star (block ui 0 0 vi)*block (φ (star (u:C)*u)) x (star x)
      (φ (star (v:C)*v))*block ui 0 0 vi=block 1 y (star y) 1 := by
    rw [conjugate_diagonal]
    dsimp [ui,vi,y]
    simp only [map_mul,map_star,star_mul,star_star]
    congr 1
    · simp only [←mul_assoc]
      rw [hcancelφ,one_mul,←map_mul]; simp
    · simp [mul_assoc]
    · simp only [←mul_assoc]
      rw [hcancelφ,one_mul,←map_mul]; simp
  have hy : 0 ≤ block 1 y (star y) 1 := by
    rw [←he]
    exact star_left_conjugate_nonneg hx _
  have hfy : ‖f y‖≤1 := (hf y).trans (contraction_of_block_nonneg y hy)
  have hp := contraction_block_nonneg (f y) hfy
  have hm : f y=star (ψ (↑u⁻¹))*f x*ψ (↑v⁻¹) := by
    simpa only [y,ui,vi,←map_star] using hmod (star (↑u⁻¹)) x (↑v⁻¹)
  have hr : star (block (ψ (u:C)) 0 0 (ψ (v:C)))*block 1 (f y) (star (f y)) 1*
      block (ψ (u:C)) 0 0 (ψ (v:C))=
      block (ψ (star (u:C)*u)) (f x) (star (f x)) (ψ (star (v:C)*v)) := by
    rw [conjugate_diagonal,hm]
    simp only [mul_one,map_mul,map_star,star_mul,star_star]
    congr 1
    · simp only [←mul_assoc]
      rw [hcancelψ,one_mul,mul_assoc,←map_mul]; simp
    · simp only [←mul_assoc]
      rw [hcancelψ,one_mul,mul_assoc,←map_mul]; simp
  rw [←hr]
  exact star_left_conjugate_nonneg hp _

lemma transfer_strictlyPositive (φ : C →⋆ₐ[ℂ] A) (ψ : C →⋆ₐ[ℂ] B)
    (f : A →ₗ[ℂ] B) (hf : ∀ a,‖f a‖≤‖a‖)
    (hmod : ∀ c a d,f (φ c*a*φ d)=ψ c*f a*ψ d)
    (p q : C) (hp : IsStrictlyPositive p) (hq : IsStrictlyPositive q) (x : A)
    (hx : 0 ≤ block (φ p) x (star x) (φ q)) :
    0 ≤ block (ψ p) (f x) (star (f x)) (ψ q) := by
  have hup := (CFC.isUnit_sqrt_iff p hp.nonneg).mpr hp.isUnit
  have huq := (CFC.isUnit_sqrt_iff q hq.nonneg).mpr hq.isUnit
  have he (r : C) (hr : 0≤r) (hu : IsUnit (CFC.sqrt r)) : star (hu.unit:C)*hu.unit=r := by
    rw [hu.unit_spec,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg r)).star_eq]
    exact CFC.sqrt_mul_sqrt_self r hr
  simpa only [he p hp.nonneg hup,he q hq.nonneg huq] using
    transfer_unit_square φ ψ f hf hmod hup.unit huq.unit x
      (by simpa only [he p hp.nonneg hup,he q hq.nonneg huq] using hx)

omit [PartialOrder A] [StarOrderedRing A] in
lemma block_add_scalar (a b c d : A) (r : ℝ) :
    block (a+r • 1) b c (d+r • 1)=block a b c d+r • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block]

lemma transfer_nonneg (φ : C →⋆ₐ[ℂ] A) (ψ : C →⋆ₐ[ℂ] B)
    (f : A →ₗ[ℂ] B) (hf : ∀ a,‖f a‖≤‖a‖)
    (hmod : ∀ c a d,f (φ c*a*φ d)=ψ c*f a*ψ d)
    (p q : C) (hp : 0≤p) (hq : 0≤q) (x : A)
    (hx : 0 ≤ block (φ p) x (star x) (φ q)) :
    0 ≤ block (ψ p) (f x) (star (f x)) (ψ q) := by
  have hφ (a : C) (r : ℝ) : φ (a+r • 1)=φ a+r • 1 := by
    change (φ.restrictScalars ℝ) (a+r • 1)=_
    simp only [map_add,map_smul,map_one]
    rfl
  have hψ (a : C) (r : ℝ) : ψ (a+r • 1)=ψ a+r • 1 := by
    change (ψ.restrictScalars ℝ) (a+r • 1)=_
    simp only [map_add,map_smul,map_one]
    rfl
  have he (r : ℝ) (hr : 0<r) :
      0 ≤ block (ψ p) (f x) (star (f x)) (ψ q)+r • 1 := by
    have hpr : IsStrictlyPositive (p+r • 1) :=
      IsStrictlyPositive.nonneg_add hp (isStrictlyPositive_one.smul hr)
    have hqr : IsStrictlyPositive (q+r • 1) :=
      IsStrictlyPositive.nonneg_add hq (isStrictlyPositive_one.smul hr)
    have hxr : 0 ≤ block (φ (p+r • 1)) x (star x) (φ (q+r • 1)) := by
      rw [hφ,hφ,block_add_scalar]
      exact add_nonneg hx (smul_nonneg hr.le zero_le_one)
    simpa only [hψ,block_add_scalar] using
      transfer_strictlyPositive φ ψ f hf hmod (p+r • 1) (q+r • 1) hpr hqr x hxr
  have hc : Continuous (fun r : ℝ => block (ψ p) (f x) (star (f x)) (ψ q)+r • 1) := by
    fun_prop
  have hl := hc.continuousAt.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hh := ge_of_tendsto hl (show ∀ᶠ r in 𝓝[>] (0:ℝ),
      0 ≤ block (ψ p) (f x) (star (f x)) (ψ q)+r • 1 from
        Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ r in 𝓝[>] (0:ℝ),r∈Set.Ioi 0) (fun r hr => he r hr))
  simpa using hh

end Kadison.CStarBlock

end

end
end

end OAI
