import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.ComponentB

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial ElementaryPositivity.Homogeneity
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem gradeB_internal (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    DirectSum.IsInternal (gradeB a μ d) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
      (gradeB_finite_independent a μ d)
  · apply top_unique
    intro f hf
    obtain ⟨s,hs,heq⟩ := componentB_finite_decomposition a μ d f
    rw [← heq]
    apply Submodule.sum_mem
    intro k hk
    apply (le_iSup (gradeB a μ d) k)
    exact ⟨f,rfl⟩

lemma gradeB_homogeneous_representative (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    (d : I → ℕ) (k : ℤ) (f : B a μ d) (hf : f∈gradeB a μ d k) :
    ∃ g : S d, g.val.IsWeightedHomogeneous (fun _=>(1:ℤ)) k ∧
      (destabilizingSpace a μ d).mkQ g=f := by
  obtain ⟨x,rfl⟩ := hf
  obtain ⟨g,rfl⟩ := (destabilizingSpace a μ d).mkQ_surjective x
  exact ⟨componentS d k g,componentS_homogeneous d k g,rfl⟩

theorem shuffleB_graded (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0<c i)
    (d e : I → ℕ) (hs : SlopeArithmetic.slope c η d = SlopeArithmetic.slope c η e)
    (m n : ℤ) (f : B a (SlopeArithmetic.slope c η) d)
    (g : B a (SlopeArithmetic.slope c η) e)
    (hf : f∈gradeB a (SlopeArithmetic.slope c η) d m)
    (hg : g∈gradeB a (SlopeArithmetic.slope c η) e n) :
    shuffleB a c η hc d e hs f g ∈
      gradeB a (SlopeArithmetic.slope c η) (d+e) (m+n-eulerForm a d e) := by
  obtain ⟨f,hfp,rfl⟩ := gradeB_homogeneous_representative a _ d m f hf
  obtain ⟨g,hgp,rfl⟩ := gradeB_homogeneous_representative a _ e n g hg
  rw [shuffleB_mk,mem_gradeB_iff,componentB_mk,
    componentS_of_homogeneous _ _ (shufflePolynomial_homogeneous a f g hfp hgp),ite_eq_left rfl]

lemma intWeight_eq_natWeight {σ : Type*} (x : σ →₀ ℕ) :
    Finsupp.weight (fun _=>(1:ℤ)) x = (Finsupp.weight (fun _=>(1:ℕ)) x : ℤ) := by
  classical
  simp [Finsupp.weight_apply,Finsupp.sum]

lemma homogeneous_int_nat {σ : Type*} (p : MvPolynomial σ ℚ) (k : ℕ) :
    p.IsWeightedHomogeneous (fun _=>(1:ℤ)) (k:ℤ) ↔
      p.IsWeightedHomogeneous (fun _=>(1:ℕ)) k := by
  simp only [IsWeightedHomogeneous,intWeight_eq_natWeight,Nat.cast_inj]

omit [DecidableEq I] in
lemma componentS_range_finite (d : I → ℕ) (k : ℤ) :
    Module.Finite ℚ (LinearMap.range (componentS d k)) := by
  classical
  by_cases hk : k<0
  · have hr : LinearMap.range (componentS d k)=⊥ := by
      apply bot_unique
      rintro x ⟨f,rfl⟩
      exact Subtype.ext (homogeneous_negative_eq_zero _ (componentS_homogeneous d k f) hk)
    rw [hr]
    infer_instance
  · have hk0 : 0≤k := le_of_not_gt hk
    let H := weightedHomogeneousSubmodule ℚ (fun _ : Σ i,Fin (d i)=>(1:ℕ)) k.toNat
    let : Module.Finite ℚ H := Module.Finite.of_fg
      (weightedHomogeneousSubmodule_fg ℚ _ (fun _=>one_ne_zero) _)
    let L : LinearMap.range (componentS d k) →ₗ[ℚ] H :=
      (((symmetricSpace d).val.toLinearMap).comp (LinearMap.range (componentS d k)).subtype).codRestrict H (by
        rintro ⟨f,⟨g,rfl⟩⟩
        apply (homogeneous_int_nat _ _).mp
        rw [Int.toNat_of_nonneg hk0]
        exact componentS_homogeneous d k g)
    have hL : Function.Injective L := by
      intro x y h
      have hv : x.val.val=y.val.val := congrArg (fun z : H=>z.val) h
      exact Subtype.ext (Subtype.ext hv)
    exact Module.Finite.of_injective L hL

theorem gradeB_finite (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) (k : ℤ) :
    Module.Finite ℚ (gradeB a μ d k) := by
  classical
  let := componentS_range_finite d k
  let Q := destabilizingSpace a μ d
  let L : LinearMap.range (componentS d k) →ₗ[ℚ] gradeB a μ d k :=
    (Q.mkQ.comp (LinearMap.range (componentS d k)).subtype).codRestrict _ (by
      rintro ⟨f,⟨g,rfl⟩⟩
      exact ⟨Q.mkQ g,rfl⟩)
  apply Module.Finite.of_surjective L
  rintro ⟨f,hf⟩
  obtain ⟨x,rfl⟩ := hf
  obtain ⟨g,rfl⟩ := Q.mkQ_surjective x
  exact ⟨⟨componentS d k g,⟨g,rfl⟩⟩,rfl⟩

end ElementaryPositivity.RawShuffle

end

end OAI
