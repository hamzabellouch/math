import OAI.Analysis.LiebThirring.SpectralTrials

namespace OAI

universe u180


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 ConstantProof MeasureTheory Set Filter
open scoped Topology

lemma real_family_bound_sorted {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (hWn : ∀ᵐ x, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (u : Fin N → C1L2) (k : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) (horder : Antitone k) :
    (∑ i, k i^(1+2*σ))*betaAction σ ≤ actionYoungConstant σ*∫ x, W x^(1+σ) := by
  have hc : ContinuousAt (fun t : ℝ ↦ ∑ i, (t*k i)^(1+2*σ)*betaAction σ) 1 := by
    apply tendsto_finsetSum
    intro i _
    exact (((continuousAt_id.mul_const (k i)).rpow_const
      (Or.inl (by simpa using (hk i).ne'))).mul_const _)
  have ht : Tendsto (fun t : ℝ ↦ ∑ i, (t*k i)^(1+2*σ)*betaAction σ) (𝓝[<] 1)
      (𝓝 ((∑ i, k i^(1+2*σ))*betaAction σ)) := by
    simpa only [one_mul,Finset.sum_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht0
  have hκ (i : Fin N) : 0 < t*k i ∧ t*k i < k i :=
    ⟨mul_pos ht0 (hk i),by simpa using mul_lt_mul_of_pos_right (show t < 1 from ht) (hk i)⟩
  obtain ⟨q,hqo,hqc,hqe⟩ := exists_compact_negative_flag hW u k (fun i ↦ t*k i)
    ho he hk hκ horder
  have h := compact_trial_bound hσ₀ hσ₁ hW hWn hWp (fun i ↦ t*k i)
    (fun i ↦ (hκ i).1) q hqo hqc hqe
  simpa only [boundary_action_scaling hσ₀ (hκ _).1] using h

lemma real_family_action_bound {N : ℕ} {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (hWn : ∀ᵐ x, 0 ≤ W x) (hWp : Integrable (fun x ↦ W x^(1+σ)))
    (u : Fin N → C1L2) (k : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) :
    (∑ i, k i^(1+2*σ))*betaAction σ ≤ actionYoungConstant σ*∫ x, W x^(1+σ) := by
  let e := Tuple.sort (fun i ↦ -k i)
  have horder : Antitone (fun i ↦ k (e i)) := by
    intro i j hij
    have h := Tuple.monotone_sort (fun i ↦ -k i) hij
    dsimp at h
    linarith
  have h := real_family_bound_sorted hσ₀ hσ₁ hW hWn hWp
    (fun i ↦ u (e i)) (fun i ↦ k (e i)) (ho.comp e e.injective)
    (fun i ↦ he (e i)) (fun i ↦ hk (e i)) horder
  simpa only [Equiv.sum_comp e (fun i ↦ k i^(1+2*σ))] using h

lemma action_constant_eq_sharp {σ : ℝ} (hσ : 0 < σ) :
    actionYoungConstant σ / betaAction σ = sharpConstant (σ+1/2) := by
  rw [actionYoungConstant,young_over_beta hσ,sharpConstant,semiclassicalConstant]
  have h1 : σ+1/2-1/2 = σ := by ring
  have h2 : σ+1/2+1/2 = σ+1 := by ring
  have h3 : σ+1/2+1 = σ+3/2 := by ring
  have h4 : σ+1/2+3/2 = σ+2 := by ring
  rw [h1,h2,h3,h4]
  ring

lemma real_family_bound {ι : Type u180} [Fintype ι] {γ : ℝ}
    (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (hWn : ∀ᵐ x, 0 ≤ W x)
    (hWp : Integrable (fun x ↦ W x^(γ+1/2)))
    (u : ι → C1L2) (k : ι → ℝ) (ho : Orthonormal ℝ u)
    (he : ∀ i, (u i).IsEigen W (k i)) (hk : ∀ i, 0 < k i) :
    (∑ i, k i^(2*γ)) ≤ sharpConstant γ*∫ x, W x^(γ+1/2) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hσ₀ : 0 < γ-1/2 := by linarith
  have hσ₁ : γ-1/2 < 1 := by linarith
  have he2 : 1+(γ-1/2) = γ+1/2 := by ring
  have h := real_family_action_bound hσ₀ hσ₁ hW hWn
    (by simpa only [he2] using hWp)
    (fun i ↦ u (e i)) (fun i ↦ k (e i)) (ho.comp e e.injective)
    (fun i ↦ he (e i)) (fun i ↦ hk (e i))
  rw [Equiv.sum_comp e (fun i ↦ k i^(1+2*(γ-1/2)))] at h
  have he1 : 1+2*(γ-1/2) = 2*γ := by ring
  rw [he1,he2] at h
  have hh := (le_div_iff₀ (betaAction_pos hσ₀)).mpr h
  rw [mul_div_right_comm,action_constant_eq_sharp hσ₀,sub_add_cancel] at hh
  exact hh

end SharpLiebThirring.SpectralProof

end


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Module

/-- Finite realification, retaining all complex multiplicities at each energy. -/
lemma realify_finite_family {ι : Type} [Fintype ι] [DecidableEq ι]
    {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (k : ι → ℝ)
    (hk : ∀ i, 0 < k i) (a b : ι → C1L2)
    (ha : ∀ i, (a i).IsEigen W (k i)) (hb : ∀ i, (b i).IsEigen W (k i))
    (hr : ∀ i j, inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = if i=j then 1 else 0)
    (hi : ∀ i j, inner ℝ (a i) (b j)-inner ℝ (b i) (a j) = 0)
    (p : ℝ) :
    ∃ (J : Type) (_ : Fintype J) (v : J → C1L2) (l : J → ℝ),
      Orthonormal ℝ v ∧ (∀ j, (v j).IsEigen W (l j)) ∧ (∀ j, 0 < l j) ∧
      (∑ i, k i^p) ≤ ∑ j, l j^p := by
  classical
  let T := range k
  let : Fintype T := (finite_range k).fintype
  let I := fun t : T ↦ {i : ι // k i = t.val}
  let g := fun (t : T) (z : I t × Bool) ↦ if z.2 then b z.1 else a z.1
  let E := fun t : T ↦ Submodule.span ℝ (range (g t))
  have (t : T) : FiniteDimensional ℝ (E t) := FiniteDimensional.span_of_finite ℝ (finite_range _)
  have hE (t : T) : E t ≤ eigenSubmodule hW t.val := by
    apply Submodule.span_le.mpr
    rintro v ⟨⟨i,c⟩,rfl⟩
    change (if c then b i else a i).IsEigen W t.val
    cases c
    · simpa only [i.property,Bool.false_eq_true,ite_false] using ha i
    · simpa only [i.property,ite_true] using hb i
  let ar := fun (t : T) (i : I t) ↦ (⟨a i,Submodule.subset_span (mem_range.mpr ⟨(i,false),rfl⟩)⟩ : E t)
  let br := fun (t : T) (i : I t) ↦ (⟨b i,Submodule.subset_span (mem_range.mpr ⟨(i,true),rfl⟩)⟩ : E t)
  have hdim (t : T) : Fintype.card (I t) ≤ finrank ℝ (E t) := by
    apply complex_family_card_le_real_dimension (ar t) (br t)
    · intro i j
      change inner ℝ (a i) (a j)+inner ℝ (b i) (b j) = _
      rw [hr]
      congr 1
      exact propext Subtype.ext_iff.symm
    · intro i j
      exact hi i j
  let B := fun t : T ↦ stdOrthonormalBasis ℝ (E t)
  let J := (t : T) × Fin (finrank ℝ (E t))
  let v : J → C1L2 := fun z ↦ (B z.1 z.2).val
  let l : J → ℝ := fun z ↦ z.1.val
  have hl (t : T) : 0 < t.val := by obtain ⟨i,he⟩ := t.property; rw [← he]; exact hk i
  have hv (j : J) : (v j).IsEigen W (l j) := hE j.1 (B j.1 j.2).property
  refine ⟨J,inferInstance,v,l,?_,hv,fun j ↦ hl j.1,?_⟩
  · rw [orthonormal_iff_ite]
    rintro ⟨t,i⟩ ⟨s,j⟩
    by_cases hts : t=s
    · subst s
      have hh := (B t).orthonormal
      have heq := orthonormal_iff_ite.mp hh i j
      change inner ℝ (B t i) (B t j) = _
      rw [heq]
      congr 1
      apply propext
      constructor
      · intro h; subst j; rfl
      · intro h
        exact eq_of_heq (Sigma.mk.inj h).2
    · have hneq : t.val^2 ≠ s.val^2 := by
        intro he
        have hval : t.val = s.val := by nlinarith [hl t,hl s]
        exact hts (Subtype.ext hval)
      rw [eigen_orthogonal (hv ⟨t,i⟩) (hv ⟨s,j⟩) hW hneq,ite_eq_right]
      exact fun h ↦ hts (congrArg Sigma.fst h)
  · have heq : (∑ i, k i^p) = ∑ t : T, (Fintype.card (I t) : ℝ)*t.val^p := by
      let f : ι ≃ (t : T) × I t :=
        { toFun := fun i ↦ ⟨⟨k i,mem_range_self i⟩,⟨i,rfl⟩⟩
          invFun := fun z ↦ z.2.val
          left_inv := fun _ ↦ rfl
          right_inv := by rintro ⟨⟨t,ht⟩,⟨i,hi⟩⟩; dsimp at hi; subst t; rfl }
      calc
        (∑ i, k i^p) = ∑ z : (t : T) × I t, z.1.val^p :=
          Equiv.sum_comp f (fun z ↦ z.1.val^p)
        _ = _ := by
          rw [Fintype.sum_sigma]
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [heq,Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro t _
    simp only [l,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdim t) (Real.rpow_nonneg (hl t).le _)

end SharpLiebThirring.SpectralProof

end

end OAI
