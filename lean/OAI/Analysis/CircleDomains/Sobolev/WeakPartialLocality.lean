import OAI.Analysis.CircleDomains.Sobolev.PartitionTestDecomposition
import OAI.Analysis.CircleDomains.Sobolev.LocalSobolevSmoothing

namespace OAI

/-! Weak partial derivatives are local on an open plane domain. The
proof decomposes each compact test into finitely many actual smooth
partition products; it does not assume a global Sobolev gluing theorem. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem weakPartial_test_on_superset {u g : EuclideanPlane → ℝ} {i : Fin 2}
    {V Ω : Set EuclideanPlane} (hVΩ : V ⊆ Ω)
    (hw : DeGiorgi.HasWeakPartialDeriv i g u V)
    {φ : EuclideanPlane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ V) :
    (∫ x in Ω, u x*fderiv ℝ φ x (EuclideanSpace.single i 1)) = -(∫ x in Ω, g x*φ x) := by
  have heq (S : Set EuclideanPlane) (hVS : V ⊆ S) :
      (∫ x in S, u x*fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, u x*fderiv ℝ φ x (EuclideanSpace.single i 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      (fun hh => hx (hVS (hsub (tsupport_fderiv_apply_subset ℝ _ hh)))) ,mul_zero]
  have geq (S : Set EuclideanPlane) (hVS : V ⊆ S) :
      (∫ x in S, g x*φ x) = ∫ x, g x*φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hVS (hsub hh))),mul_zero]
  rw [heq Ω hVΩ,geq Ω hVΩ,← heq V Subset.rfl,← geq V Subset.rfl]
  exact hw φ hφ hs hsub

 theorem weakPartial_test_finite_sum {u g : EuclideanPlane → ℝ} {i : Fin 2}
    {Ω : Set EuclideanPlane} (hu : LocallyIntegrable u (volume.restrict Ω))
    (hg : LocallyIntegrable g (volume.restrict Ω)) {ι : Type*}
    (F : Finset ι) (ψ : ι → EuclideanPlane → ℝ)
    (hψ : ∀ j ∈ F, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hs : ∀ j ∈ F, HasCompactSupport (ψ j))
    (hw : ∀ j ∈ F, (∫ x in Ω, u x*fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) =
      -(∫ x in Ω, g x*ψ j x)) :
    (∫ x in Ω, u x*fderiv ℝ (fun y => ∑ j ∈ F, ψ j y) x (EuclideanSpace.single i 1)) =
      -(∫ x in Ω, g x*(∑ j ∈ F, ψ j x)) := by
  have hIu (j : ι) (hj : j ∈ F) : Integrable
      (fun x => u x*fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) (volume.restrict Ω) := by
    simpa only [smul_eq_mul] using hu.integrable_smul_right_of_hasCompactSupport
      (((hψ j hj).continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hs j hj).fderiv_apply (𝕜 := ℝ) _)
  have hIg (j : ι) (hj : j ∈ F) : Integrable (fun x => g x*ψ j x) (volume.restrict Ω) := by
    simpa only [smul_eq_mul] using hg.integrable_smul_right_of_hasCompactSupport
      (hψ j hj).continuous (hs j hj)
  have hd (x : EuclideanPlane) :
      fderiv ℝ (fun y => ∑ j ∈ F, ψ j y) x (EuclideanSpace.single i 1) =
        ∑ j ∈ F, fderiv ℝ (ψ j) x (EuclideanSpace.single i 1) := by
    rw [fderiv_fun_sum (fun j hj => (hψ j hj).differentiable (by simp) x)]
    simp only [sum_apply]
  simp_rw [hd,Finset.mul_sum]
  rw [integral_finsetSum _ hIu,integral_finsetSum _ hIg]
  calc
    _ = ∑ j ∈ F, -(∫ x in Ω, g x*ψ j x) := Finset.sum_congr rfl hw
    _ = -(∑ j ∈ F, ∫ x in Ω, g x*ψ j x) := Finset.sum_neg_distrib _

 theorem weakPartial_of_local {u g : EuclideanPlane → ℝ} {i : Fin 2}
    {Ω : Set EuclideanPlane} (hΩ : IsOpen Ω)
    (hu : LocallyIntegrable u (volume.restrict Ω))
    (hg : LocallyIntegrable g (volume.restrict Ω))
    (hloc : ∀ x ∈ Ω, ∃ V : Set EuclideanPlane, IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧
      DeGiorgi.HasWeakPartialDeriv i g u V) :
    DeGiorgi.HasWeakPartialDeriv i g u Ω := by
  classical
  let O : TopologicalSpace.Opens EuclideanPlane := ⟨Ω,hΩ⟩
  choose V hV hxV hVΩ hw using (fun x : O => hloc x x.property)
  obtain ⟨ι,_,ρ,c,hsub⟩ := exists_openPlanePartition O
    (fun x => Subtype.val ⁻¹' V x) (fun x => (hV x).preimage continuous_subtype_val |>.mem_nhds (hxV x))
  intro φ hφ hs hφΩ
  obtain ⟨F,hF⟩ := ρ.finite_test_decomposition hs hφΩ
  let ψ : ι → EuclideanPlane → ℝ := fun j x => ρ.weight j x*φ x
  have hψ (j : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ j) := (ρ.smooth j).mul hφ
  have hsψ (j : ι) : HasCompactSupport (ψ j) := (ρ.compact j).mul_right
  have hψV (j : ι) : tsupport (ψ j) ⊆ V (c j) := by
    apply tsupport_mul_subset_left.trans
    intro x hx
    obtain ⟨p,hp,rfl⟩ := hsub j hx
    exact hp
  have hid (j : ι) : (∫ x in Ω, u x*fderiv ℝ (ψ j) x (EuclideanSpace.single i 1)) =
      -(∫ x in Ω, g x*ψ j x) :=
    weakPartial_test_on_superset (hVΩ (c j)) (hw (c j)) (hψ j) (hsψ j) (hψV j)
  have htest := weakPartial_test_finite_sum hu hg F ψ
    (fun j _ => hψ j) (fun j _ => hsψ j) (fun j _ => hid j)
  change (∫ x in Ω, u x*fderiv ℝ φ x (EuclideanSpace.single i 1)) = -(∫ x in Ω, g x*φ x)
  have hsum : (fun y => ∑ j ∈ F, ψ j y) = φ := hF.symm
  rw [hsum] at htest
  simpa only [congrFun hsum] using htest

end CircleDomainRigidity

end

end OAI
