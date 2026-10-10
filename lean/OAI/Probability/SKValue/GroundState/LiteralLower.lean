import Mathlib
import OAI.Probability.SKValue.Equations.LiteralNormalizer
import OAI.Probability.SKValue.Control.Regularity
import OAI.Probability.SKValue.GroundState.RoundingSpin

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

theorem shiftedCoefficientSum_le_groundState (W : BrownianSpace) (γ : OrderParameter)
    {T : ℝ} (hT : 0≤T) (hT1 : T<1) {N : ℕ} (hN : 0<N)
    (hpos : ∀ j<N,0<∫ z,(rawCoefficient W γ T N j z)^2 ∂gaussianProduct (Fin (N+1))) :
    shiftedCoefficientSum W γ T N≤groundStateValue := by
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩ := sourceStripRegularity W γ T ⟨hT,hT1⟩
  rw [literal_shiftedCoefficientSum]
  exact normalized_shifted_sum_le_groundState
    (fun j : Fin N ↦ meshRaw T N γ.coeff (gradient W γ) j)
    (meshTerminal T N γ.coeff (gradient W γ))
    (fun j ↦ mesh_raw_measurable hT hG hN j.isLt.le)
    (fun j ↦ mesh_raw_depends T j.isLt.le γ.coeff (gradient W γ))
    (fun j ↦ mesh_raw_memLp hT hG hDb hN j.isLt.le)
    (fun j ↦ hpos j j.isLt)
    (mesh_terminal_measurable hT hG hN) (mesh_terminal_depends T N γ.coeff (gradient W γ))

end SKValue

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma finiteMaximum_prod_add {ι Λ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype Λ] [Nonempty Λ] (f : ι → ℝ) (g : Λ → ℝ) :
    finiteMaximum (fun p : ι×Λ ↦ f p.1+g p.2)=finiteMaximum f+finiteMaximum g := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := exists_finiteMaximum (fun p : ι×Λ ↦ f p.1+g p.2)
    rw [←hp]
    exact add_le_add (le_finiteMaximum f p.1) (le_finiteMaximum g p.2)
  · obtain ⟨i,hi⟩ := exists_finiteMaximum f
    obtain ⟨a,ha⟩ := exists_finiteMaximum g
    rw [←hi,←ha]
    exact le_finiteMaximum (fun p : ι×Λ ↦ f p.1+g p.2) (i,a)

lemma finiteMaximum_prod_curry {ι Λ : Type*} [Fintype ι] [Nonempty ι]
    [Fintype Λ] [Nonempty Λ] (f : ι×Λ → ℝ) :
    finiteMaximum f=finiteMaximum (fun a ↦ finiteMaximum (fun i ↦ f (i,a))) := by
  apply le_antisymm
  · obtain ⟨p,hp⟩ := exists_finiteMaximum f
    rw [←hp]
    exact (le_finiteMaximum (fun i ↦ f (i,p.2)) p.1).trans
      (le_finiteMaximum (fun a ↦ finiteMaximum (fun i ↦ f (i,a))) p.2)
  · obtain ⟨a,ha⟩ := exists_finiteMaximum (fun a ↦ finiteMaximum (fun i ↦ f (i,a)))
    obtain ⟨i,hi⟩ := exists_finiteMaximum (fun i ↦ f (i,a))
    rw [←ha,←hi]
    exact le_finiteMaximum f (i,a)

lemma spinMaximum_eq_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    finiteMaximum (fun σ : ι → Bool ↦ ∑ i, spin (σ i)*x i)=∑ i, |x i| := by
  classical
  apply le_antisymm
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum (fun σ : ι → Bool ↦ ∑ i, spin (σ i)*x i)
    rw [←hσ]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |spin (σ i)*x i| := le_abs_self _
      _ = _ := by rw [abs_mul,abs_spin,one_mul]
  · let σ : ι → Bool := fun i ↦ decide (0≤x i)
    have he (i : ι) : spin (σ i)*x i=|x i| := by
      by_cases h : 0≤x i
      · simp [σ,spin,h,abs_of_nonneg h]
      · simp [σ,spin,h,abs_of_neg (lt_of_not_ge h)]
    simpa only [he] using le_finiteMaximum (fun σ : ι → Bool ↦ ∑ i, spin (σ i)*x i) σ

noncomputable def leafField {Λ κ : Type*} [Fintype κ] {n : ℕ}
    (v : Λ → κ → ℝ) (z : Fin n×κ → ℝ) (α : Λ) (i : Fin n) : ℝ :=
  ∑ k, v α k*z (i,k)

lemma linearProcess_leafField {Λ κ : Type*} [Fintype κ] (n : ℕ)
    (v : Λ → κ → ℝ) (z : Fin n×κ → ℝ) (p : (Fin n → Bool)×Λ) :
    linearProcess (leafFieldCoeff n v) z p=∑ i, spin (p.1 i)*leafField v z p.2 i := by
  simp only [linearProcess,leafFieldCoeff,Fintype.sum_prod_type,leafField,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma leafField_max {Λ κ : Type*} [Fintype Λ] [Nonempty Λ] [Fintype κ]
    (n : ℕ) (v : Λ → κ → ℝ) (d : Λ → ℝ) (z : Fin n×κ → ℝ) :
    finiteMaximum (fun p ↦ linearProcess (leafFieldCoeff n v) z p+d p.2)=
      finiteMaximum (fun α ↦ (∑ i, |leafField v z α i|)+d α) := by
  rw [finiteMaximum_prod_curry]
  simp only [linearProcess_leafField,finiteMaximum_add_const,spinMaximum_eq_sum_abs]

lemma expected_guerra_max {Λ κ : Type*} [Fintype Λ] [Nonempty Λ] [Fintype κ]
    (n : ℕ) (v : Λ → κ → ℝ) (d : Λ → ℝ) :
    (∫ z, finiteMaximum (fun p ↦ linearProcess (guerraCoeff n v) z p+d p.2)
      ∂gaussianProduct ((Fin n×Fin n)⊕(κ×κ))) = expectedMaximum n+
      ∫ z, finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z α+d α)
        ∂gaussianProduct (κ×κ) := by
  have he := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin n×Fin n)⊕(κ×κ) ↦ standardGaussian)
  change (∫ z, finiteMaximum (fun p ↦ linearProcess (guerraCoeff n v) z p+d p.2)
    ∂Measure.pi (fun _ : (Fin n×Fin n)⊕(κ×κ) ↦ standardGaussian)) = _
  rw [←he.integral_comp' (fun z ↦ finiteMaximum (fun p ↦ linearProcess (guerraCoeff n v) z p+d p.2))]
  have hlin (z : ((Fin n×Fin n) → ℝ)×((κ×κ) → ℝ)) :
      (fun p ↦ linearProcess (guerraCoeff n v)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin n×Fin n)⊕(κ×κ) ↦ ℝ)).symm z) p+d p.2) =
      (fun p ↦ linearProcess (hamCoeff n) z.1 p.1+(linearProcess (leafAuxCoeff n v) z.2 p.2+d p.2)) := by
    funext p
    simp [linearProcess,guerraCoeff,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm,add_assoc]
  have hm (z : ((Fin n×Fin n) → ℝ)×((κ×κ) → ℝ)) :
      finiteMaximum (fun p : (Fin n → Bool)×Λ ↦ linearProcess (hamCoeff n) z.1 p.1+
        (linearProcess (leafAuxCoeff n v) z.2 p.2+d p.2)) =
      finiteMaximum (linearProcess (hamCoeff n) z.1)+
        finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z.2 α+d α) :=
    finiteMaximum_prod_add (linearProcess (hamCoeff n) z.1)
      (fun α ↦ linearProcess (leafAuxCoeff n v) z.2 α+d α)
  simp only [hlin,hm]
  change (∫ z, finiteMaximum (linearProcess (hamCoeff n) z.1)+
    finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z.2 α+d α)
      ∂(gaussianProduct (Fin n×Fin n)).prod (gaussianProduct (κ×κ))) = _
  rw [integral_add ((finiteMaximum_integrable (hamCoeff n)).comp_fst _)
    ((affineMaximum_integrable (leafAuxCoeff n v) d).comp_snd _),
    integral_fun_fst (fun z ↦ finiteMaximum (linearProcess (hamCoeff n) z)),
    integral_fun_snd (fun z ↦ finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z α+d α))]
  simp [expectedMaximum]

theorem finite_guerra_upper {Λ κ : Type*} [Fintype Λ] [Nonempty Λ] [Fintype κ]
    {n : ℕ} (hn : 0<n) (v : Λ → κ → ℝ)
    (hv : ∀ α, ∑ k, (v α k)^2=1) (d : Λ → ℝ) :
    expectedMaximum n+
      (∫ z, finiteMaximum (fun α ↦ linearProcess (leafAuxCoeff n v) z α+d α)
        ∂gaussianProduct (κ×κ)) ≤
      ∫ z, finiteMaximum (fun α ↦ (∑ i, |leafField v z α i|)+d α)
        ∂gaussianProduct (Fin n×κ) := by
  have h := expected_affine_max_le (guerraCoeff n v) (leafFieldCoeff n v)
    (fun p ↦ d p.2) (guerra_metric_le hn v hv)
  simpa only [expected_guerra_max,leafField_max] using h

end SKValueG

end

end OAI
