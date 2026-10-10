import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.StrongDenseEigenvalues
import OAI.Probability.CriticalPercolation.LinearGroups.PeriodicSpectrum
import OAI.Probability.CriticalPercolation.LinearGroups.ProjectivePeriodicity

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K G n : Type} [Field K] [CharZero K] [Countable K] [IsAlgClosed K]
variable [Group G] [DecidableEq G] [Fintype n] [DecidableEq n] [Nonempty n]
variable {degree : ℕ}

lemma scalar_power_of_strongFullMatrixSpan (ρ : G →* GL n K)
    (hρ : StrongFullMatrixSpan ρ) (hg : SparseGrowth.HasPolynomialDegree G degree) (g : G) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : K, a≠0 ∧ (ρ g).val^m=a • (1:Matrix n n K) := by
  let A := (matrixRepresentation ρ g).toLinearMap
  obtain ⟨a,ha⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v,hv⟩ := ha.exists_hasEigenvector
  have hav : (ρ g).val.mulVec v=a • v := hv.apply_eq_smul
  have ha0 : a≠0 := by
    intro he
    exact hv.2 ((matrixRepresentation ρ g).injective (by
      change (ρ g).val.mulVec v=(ρ g).val.mulVec 0
      simpa only [he,zero_smul,Matrix.mulVec_zero] using hav))
  obtain ⟨m,hm,hni⟩ := exists_scalar_unipotent_power A a ha0 (by
    intro r hr
    obtain ⟨w,hw⟩ := (Module.End.hasEigenvalue_of_isRoot hr).exists_hasEigenvector
    exact eigenvalue_ratio_root_of_unity_of_strongFullMatrixSpan ρ hρ hg g hw.2 hv.2
      hw.apply_eq_smul hav)
  let : Uncountable ℂ := Arithmetic.uncountable_complete_normed_field ℂ
  obtain ⟨f'⟩ := Arithmetic.exists_algHom_of_countable (k:=ℚ) (K:=K) (F:=ℂ)
  let f := f'.toRingHom
  let τ := (Matrix.GeneralLinearGroup.map f).comp ρ
  have hτ := hρ.transfer f (RingHom.id ℂ) ρ τ (fun _ _ _ => rfl)
  let E : Matrix n n ℂ ≃ₐ[ℂ] ((n → ℂ) →L[ℂ] (n → ℂ)) :=
    Matrix.toLinAlgEquiv'.trans continuousEndAlgEquiv
  let φ : Matrix n n K →+* ((n → ℂ) →L[ℂ] (n → ℂ)) := E.toRingHom.comp f.mapMatrix
  have hφs (c : K) : φ (c • (1:Matrix n n K))=f c • 1 := by
    have hmat : f.mapMatrix (c • (1:Matrix n n K))=f c • (1:Matrix n n ℂ) := by
      ext i j
      simp only [RingHom.mapMatrix_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul]
      congr 1
      exact congrArg (fun M : Matrix n n ℂ => M i j) f.mapMatrix.map_one
    change E (f.mapMatrix (c • (1:Matrix n n K)))=_
    rw [hmat,map_smul,map_one]
  let T := φ (ρ g).val
  have hniM : IsNilpotent ((ρ g).val^m-a^m • (1:Matrix n n K)) := by
    have hh := hni.map (LinearMap.toMatrixAlgEquiv'.toRingHom)
    have hA : LinearMap.toMatrixAlgEquiv' A=(ρ g).val :=
      Matrix.toLinAlgEquiv'.symm_apply_apply _
    change IsNilpotent (LinearMap.toMatrixAlgEquiv' (A^m-a^m • 1)) at hh
    simpa only [map_sub,map_pow,map_smul,map_one,hA] using hh
  have hniT : IsNilpotent (T^m-(f a)^m • 1) := by
    have hh := hniM.map φ
    simpa only [map_sub,map_pow,hφs,T] using hh
  obtain ⟨S,h1,hi,hgen,hgS⟩ := (SparseGrowth.hasPolynomialDegree_iff degree).mp hg
  obtain ⟨δ,hδ,hb⟩ := projective_bound_of_strongFullSpan (matrixRepresentation τ)
    (hτ.strongFullSpan τ) S h1 hgen degree hgS
  have hTpow (k : ℕ) : (continuousRepresentation (matrixRepresentation τ) (g^k)).toContinuousLinearMap=T^k := by
    induction k with
    | zero => ext x i; simp only [pow_zero,map_one]; rfl
    | succ k ih =>
      rw [pow_succ,map_mul,ContinuousLinearEquiv.toContinuousLinearMap_mul,ih,pow_succ]
      rfl
  have hbT (k : ℕ) (x : n → ℂ) : δ*‖T^k‖*‖x‖≤‖(T^k) x‖ := by
    rw [←hTpow]
    exact hb (g^k) x
  let v' : n → ℂ := f ∘ v
  have hv' : v'≠0 := eigenvector_transfer_ne_zero f (RingHom.id ℂ) v v' (fun _ => rfl) hv.2
  have hav' : T v'=f a • v' := eigenvector_transfer f (RingHom.id ℂ)
    (ρ g).val (τ g).val (fun _ _ => rfl) v v' (fun _ => rfl) a (f a) rfl hav
  have hfa : f a≠0 := fun h => ha0 (f.injective (h.trans f.map_zero.symm))
  have hs := scalar_power_of_projective_bound T δ hδ hbT hv' hfa hav' m hniT
  refine ⟨m,hm,a^m,pow_ne_zero m ha0,?_⟩
  have hφinj : Function.Injective φ := by
    intro B C h
    have he := E.injective h
    ext i j
    apply f.injective
    exact congrArg (fun M : Matrix n n ℂ => M i j) he
  apply hφinj
  rw [map_pow,hφs,map_pow]
  exact hs

end CriticalPercolation.LinearGrowth
end
end

end OAI
