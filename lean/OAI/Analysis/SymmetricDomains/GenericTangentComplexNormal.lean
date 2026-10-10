import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicSupportIndependent

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set
open scoped Classical

theorem independent_functionals_surjective {𝕜 E ι : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E] [Fintype ι]
    (l : ι → Module.Dual 𝕜 E) (hi : LinearIndependent 𝕜 l) :
    Function.Surjective (LinearMap.pi l) := by
  classical
  have hexp (L : Module.Dual 𝕜 (ι → 𝕜)) (v : ι → 𝕜) :
      L v = ∑ i, v i * L (Pi.single i 1) := by
    have hv : v = ∑ i : ι, v i • Pi.single i (1 : 𝕜) := by
      ext i
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul,smul_eq_mul]
  apply LinearMap.dualMap_injective_iff.mp
  intro L Q hLQ
  have hzero : ∑ i, (L-Q) (Pi.single i 1) • l i = 0 := by
    ext x
    have he := congrArg (fun D : Module.Dual 𝕜 E => D x) hLQ
    change L (fun i => l i x) = Q (fun i => l i x) at he
    have hz : (L-Q) (fun i => l i x) = 0 := sub_eq_zero.mpr he
    rw [hexp] at hz
    simpa only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
      mul_comm,LinearMap.zero_apply] using hz
  have hc := Fintype.linearIndependent_iff.mp hi _ hzero
  apply LinearMap.ext
  intro v
  apply sub_eq_zero.mp
  change (L-Q) v = 0
  rw [hexp]
  simp only [hc,mul_zero,Finset.sum_const_zero]

theorem exists_scalar_continuousLinearEquiv_prod_ker
    {𝕜 E X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X]
    (A : E →L[𝕜] X) (hA : Function.Surjective A) :
    ∃ e : E ≃L[𝕜] X × LinearMap.ker A.toLinearMap, ∀ v, (e v).1 = A v := by
  obtain ⟨R,hR⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hA
  let K := LinearMap.ker A.toLinearMap
  let L : E →ₗ[𝕜] X × K :=
    { toFun := fun v => (A v,⟨v-R (A v),by change A (v-R (A v)) = 0; rw [map_sub,hR,sub_self]⟩)
      map_add' := by intro v w; ext <;> simp [map_add]; abel
      map_smul' := by intro c v; ext <;> simp [map_smul,smul_sub] }
  have hinj : Function.Injective L := by
    intro v w he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun p : X × K => (p.2 : E)) he
    change A v = A w at h1
    change v-R (A v) = w-R (A w) at h2
    rw [h1] at h2
    exact sub_left_injective h2
  have hsurj : Function.Surjective L := by
    rintro ⟨x,k⟩
    refine ⟨R x+k,?_⟩
    have hk : A k = 0 := k.property
    have ha : A (R x+k) = x := by rw [map_add,hR,hk,add_zero]
    apply Prod.ext
    · exact ha
    · apply Subtype.ext
      change R x+(k : E)-R (A (R x+k)) = k
      rw [ha]
      abel
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj,hsurj⟩).toContinuousLinearEquiv,fun _ => rfl⟩

lemma submodule_basis_independent {𝕜 E ι : Type*} [Field 𝕜]
    [AddCommGroup E] [Module 𝕜 E] (S : Submodule 𝕜 E)
    (b : Module.Basis ι 𝕜 S) : LinearIndependent 𝕜 (fun i => (b i : E)) := by
  exact b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)

lemma real_conormal_basis_complex_independent {n k : ℕ}
    (S : Submodule ℝ (Affine n)) (hS : Submodule.span ℂ (S : Set (Affine n)) = ⊤)
    (b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator) :
    LinearIndependent ℂ (fun i => (b i).val.extendRCLike (𝕜 := ℂ)) := by
  have hreal (i : Fin k) : Complex.reCLM.toLinearMap.comp
      (((b i).val.extendRCLike (𝕜 := ℂ)).restrictScalars ℝ) = (b i).val := by
    apply LinearMap.ext
    intro x
    exact Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x
  apply complex_independent_of_generic_real_conormals (S : Set (Affine n)) hS
    (fun i => (b i).val.extendRCLike)
  · intro i x hx
    exact (Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x).trans
      ((Submodule.mem_dualAnnihilator _).mp (b i).property x hx)
  · have hb := submodule_basis_independent S.dualAnnihilator b
    simpa only [hreal] using hb

lemma real_conormal_basis_vanishing_iff {n k : ℕ}
    (S : Submodule ℝ (Affine n))
    (b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator) (x : Affine n) :
    x ∈ S ↔ ∀ i, (b i).val x = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_dualAnnihilator _).mp (b i).property x hx
  · intro h
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := S)]
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro Q hQ
    let q : S.dualAnnihilator := ⟨Q,hQ⟩
    have heq := b.sum_repr q
    have heq' := congrArg (fun v : S.dualAnnihilator => v.val x) heq
    simpa only [Submodule.coe_sum,Submodule.coe_smul_of_tower,
      LinearMap.sum_apply,LinearMap.smul_apply,h,smul_zero,Finset.sum_const_zero] using heq'.symm

theorem generic_tangent_complex_normal_form {n : ℕ}
    (S : Submodule ℝ (Affine n)) (hS : Submodule.span ℂ (S : Set (Affine n)) = ⊤) :
    ∃ r : ℕ, ∃ e : Affine n ≃L[ℂ]
      (Affine r × Affine (Module.finrank ℝ S.dualAnnihilator)),
      r + Module.finrank ℝ S.dualAnnihilator = n ∧
      ∀ x, x ∈ S ↔ ∀ i, ((e x).2 i).im = 0 := by
  let _ : Module.Free ℝ ↥S.dualAnnihilator := Module.Free.of_divisionRing ℝ ↥S.dualAnnihilator
  let k := Module.finrank ℝ S.dualAnnihilator
  let b : Module.Basis (Fin k) ℝ ↥S.dualAnnihilator := Module.finBasis ℝ ↥S.dualAnnihilator
  let l : Fin k → Module.Dual ℂ (Affine n) := fun i => (b i).val.extendRCLike
  have hi : LinearIndependent ℂ l := real_conormal_basis_complex_independent S hS b
  let L : Affine n →L[ℂ] Affine k := (LinearMap.pi l).toContinuousLinearMap
  let A : Affine n →L[ℂ] Affine k := Complex.I • L
  have hA : Function.Surjective A := by
    intro y
    obtain ⟨x,hx⟩ := independent_functionals_surjective l hi ((-Complex.I) • y)
    refine ⟨x,?_⟩
    change Complex.I • L x = y
    change L x = (-Complex.I) • y at hx
    rw [hx,smul_smul]
    simp
  obtain ⟨e,he⟩ := exists_scalar_continuousLinearEquiv_prod_ker A hA
  let r := Module.finrank ℂ (LinearMap.ker A.toLinearMap)
  let c : LinearMap.ker A.toLinearMap ≃L[ℂ] Affine r :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [r,Affine])
  let f := (e.trans ((ContinuousLinearEquiv.refl ℂ (Affine k)).prodCongr c)).trans
    (ContinuousLinearEquiv.prodComm ℂ (Affine k) (Affine r))
  have hf (x : Affine n) : (f x).2 = A x := he x
  have hdim : r+k=n := by
    have hh := f.toLinearEquiv.finrank_eq
    simpa only [Module.finrank_prod,Affine,Module.finrank_pi,
      Fintype.card_fin] using hh.symm
  refine ⟨r,f,hdim,?_⟩
  intro x
  have hx (i : Fin k) : ((f x).2 i).im = (b i).val x := by
    rw [hf]
    change (Complex.I * l i x).im = (b i).val x
    simp only [Complex.I_mul_im]
    exact Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) (b i).val x
  simp only [hx]
  exact real_conormal_basis_vanishing_iff S b x
end Release061

end

end OAI
