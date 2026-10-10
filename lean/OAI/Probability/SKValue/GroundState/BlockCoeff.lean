import Mathlib
import OAI.Probability.SKValue.GroundState.RotatedCoefficients

namespace OAI

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma hamCoeff_distance {n : ℕ} (hn : 0 < n) (σ τ : Fin n → Bool) :
    (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
    (n : ℝ) - (∑ i, spin (σ i)*spin (τ i))^2 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt := Real.sq_sqrt hn'.le
  have hn0 := ne_of_gt hn'
  have hs0 := Real.sqrt_ne_zero'.mpr hn'
  have hu := twice_upper_sum (fun i j ↦ (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2)
    (fun i j ↦ by ring) (fun i ↦ by rw [← sq,← sq,spin_sq,spin_sq]; norm_num)
  have he : (∑ i, ∑ j, (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2) =
      2*(n : ℝ)^2 - 2*(∑ i, spin (σ i)*spin (τ i))^2 := by
    simp_rw [spin_pair_difference,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum,← Finset.sum_mul]
    ring
  have hc : (∑ k, (hamCoeff n σ k-hamCoeff n τ k)^2) =
      (Real.sqrt (n : ℝ))⁻¹^2 *
      ∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0 := by
    simp only [Fintype.sum_prod_type, Finset.mul_sum,hamCoeff]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [hc,inv_pow,hsqrt]
  rw [he] at hu
  have ht : (∑ i, ∑ j, if i < j then (spin (σ i)*spin (σ j)-spin (τ i)*spin (τ j))^2 else 0) =
      (n : ℝ)^2 - (∑ i, spin (σ i)*spin (τ i))^2 := by linarith
  rw [ht]
  field_simp

noncomputable def blockCoeff (n m : ℕ) (σ : Fin (n+m) → Bool) :
    (Fin n × Fin n) ⊕ (Fin m × Fin m) → ℝ :=
  Sum.elim (hamCoeff n (fun i ↦ σ (Fin.castAdd m i)))
    (hamCoeff m (fun i ↦ σ (Fin.natAdd n i)))

lemma weighted_square_div_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    (x+y)^2/(a+b) ≤ x^2/a+y^2/b := by
  have hab : 0 < a+b := add_pos ha hb
  have he : x^2/a+y^2/b = (b*x^2+a*y^2)/(a*b) := by
    field_simp
  rw [he]
  apply (div_le_div_iff₀ hab (mul_pos ha hb)).2
  nlinarith [sq_nonneg (b*x-a*y)]

lemma blockCoeff_distance_le {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (σ τ : Fin (n+m) → Bool) :
    (∑ k, (blockCoeff n m σ k-blockCoeff n m τ k)^2) ≤
      ∑ k, (hamCoeff (n+m) σ k-hamCoeff (n+m) τ k)^2 := by
  simp only [Fintype.sum_sum_type,blockCoeff,Sum.elim_inl,Sum.elim_inr]
  rw [hamCoeff_distance hn,hamCoeff_distance hm,hamCoeff_distance (by omega)]
  rw [Fin.sum_univ_add,Nat.cast_add]
  have hh := weighted_square_div_le (by exact_mod_cast hn : (0 : ℝ) < n)
    (by exact_mod_cast hm : (0 : ℝ) < m)
    (∑ i : Fin n, spin (σ (Fin.castAdd m i))*spin (τ (Fin.castAdd m i)))
    (∑ i : Fin m, spin (σ (Fin.natAdd n i))*spin (τ (Fin.natAdd n i)))
  linarith

lemma finiteMaximum_append_sum {n m : ℕ} (f : (Fin n → Bool) → ℝ)
    (g : (Fin m → Bool) → ℝ) :
    finiteMaximum (fun σ : Fin (n+m) → Bool ↦
      f (fun i ↦ σ (Fin.castAdd m i))+g (fun i ↦ σ (Fin.natAdd n i))) =
    finiteMaximum f + finiteMaximum g := by
  apply le_antisymm
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum (fun σ : Fin (n+m) → Bool ↦
      f (fun i ↦ σ (Fin.castAdd m i))+g (fun i ↦ σ (Fin.natAdd n i)))
    rw [← hσ]
    exact add_le_add (le_finiteMaximum _ _) (le_finiteMaximum _ _)
  · obtain ⟨σ,hσ⟩ := exists_finiteMaximum f
    obtain ⟨τ,hτ⟩ := exists_finiteMaximum g
    have hh := le_finiteMaximum (fun η : Fin (n+m) → Bool ↦
      f (fun i ↦ η (Fin.castAdd m i))+g (fun i ↦ η (Fin.natAdd n i))) (Fin.append σ τ)
    simpa only [Fin.append_left,Fin.append_right,hσ,hτ] using hh

lemma expected_max_block (n m : ℕ) :
    (∫ J, finiteMaximum (linearProcess (blockCoeff n m) J)
      ∂gaussianProduct ((Fin n × Fin n) ⊕ (Fin m × Fin m))) =
    expectedMaximum n + expectedMaximum m := by
  have he := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ standardGaussian)
  change (∫ J, finiteMaximum (linearProcess (blockCoeff n m) J)
    ∂Measure.pi (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ standardGaussian)) = _
  rw [← he.integral_comp' (fun J ↦ finiteMaximum (linearProcess (blockCoeff n m) J))]
  have hlin (p : ((Fin n × Fin n) → ℝ) × ((Fin m × Fin m) → ℝ)) :
      linearProcess (blockCoeff n m)
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : (Fin n × Fin n) ⊕ (Fin m × Fin m) ↦ ℝ)).symm p) =
      (fun σ ↦ linearProcess (hamCoeff n) p.1 (fun i ↦ σ (Fin.castAdd m i))+
        linearProcess (hamCoeff m) p.2 (fun i ↦ σ (Fin.natAdd n i))) := by
    funext σ
    simp [linearProcess,blockCoeff,Fintype.sum_sum_type,MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  simp only [hlin,finiteMaximum_append_sum]
  change (∫ p, finiteMaximum (linearProcess (hamCoeff n) p.1)+
    finiteMaximum (linearProcess (hamCoeff m) p.2)
      ∂(gaussianProduct (Fin n × Fin n)).prod (gaussianProduct (Fin m × Fin m))) = _
  rw [integral_add ((finiteMaximum_integrable (hamCoeff n)).comp_fst _)
    ((finiteMaximum_integrable (hamCoeff m)).comp_snd _),
    integral_fun_fst (fun J ↦ finiteMaximum (linearProcess (hamCoeff n) J)),
    integral_fun_snd (fun J ↦ finiteMaximum (linearProcess (hamCoeff m) J))]
  simp [expectedMaximum]

lemma expectedMaximum_zero : expectedMaximum 0 = 0 := by
  have hh (J : (Fin 0 × Fin 0) → ℝ) : linearProcess (hamCoeff 0) J = fun _ ↦ 0 := by
    funext σ
    simp [linearProcess]
  simp [expectedMaximum,hh,finiteMaximum]

lemma expectedMaximum_superadditive (n m : ℕ) : expectedMaximum n + expectedMaximum m ≤ expectedMaximum (n+m) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [expectedMaximum_zero]
  rcases m.eq_zero_or_pos with rfl | hm
  · simp [expectedMaximum_zero]
  exact (expected_max_block n m).symm.le.trans
    (expected_max_le_of_pair_distances (blockCoeff n m) (hamCoeff (n+m)) (blockCoeff_distance_le hn hm))

lemma integrable_exp_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    Integrable (fun z ↦ Real.exp (linearProcess c z i)) (gaussianProduct κ) := by
  simpa only [gaussianProduct,standardGaussian,linearProcess,Real.exp_sum] using
    Integrable.fintype_prod (fun k : κ ↦ integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (c i k))

lemma integral_exp_linearProcess {ι κ : Type*} [Fintype κ] (c : ι → κ → ℝ) (i : ι) :
    (∫ z, Real.exp (linearProcess c z i) ∂gaussianProduct κ) = Real.exp ((∑ k, (c i k)^2)/2) := by
  simp only [gaussianProduct,linearProcess,Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun k x ↦ Real.exp (c i k*x))]
  have hg (r : ℝ) : (∫ x, Real.exp (r*x) ∂standardGaussian) = Real.exp (r^2/2) := by
    simpa [mgf,standardGaussian] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) r
  simp_rw [hg]
  rw [← Real.exp_sum,Finset.sum_div]

lemma integral_logPartition_upper {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (c : ι → κ → ℝ) :
    (∫ z, logPartition (linearProcess c z) ∂gaussianProduct κ) ≤
      Real.log (∑ i, Real.exp ((∑ k, (c i k)^2)/2)) := by
  let Z := fun z ↦ ∑ i, Real.exp (linearProcess c z i)
  let E := ∑ i, Real.exp ((∑ k, (c i k)^2)/2)
  have hZ : Integrable Z (gaussianProduct κ) := integrable_finsetSum _ (fun i _ ↦ integrable_exp_linearProcess c i)
  have hE : (∫ z, Z z ∂gaussianProduct κ) = E := by
    rw [integral_finsetSum _ (fun i _ ↦ integrable_exp_linearProcess c i)]
    simp only [integral_exp_linearProcess,E]
  have hEp : 0 < E := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hZp (z) : 0 < Z z := Finset.sum_pos (fun i _ ↦ Real.exp_pos _) Finset.univ_nonempty
  have hlog (z) : logPartition (linearProcess c z) ≤ Z z/E-1+Real.log E := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hZp z) hEp)
    rw [Real.log_div (hZp z).ne' hEp.ne'] at hh
    exact sub_le_iff_le_add.mp hh
  have hh := integral_mono (logPartition_integrable c)
    (((hZ.div_const E).sub (integrable_const 1)).add (integrable_const (Real.log E))) hlog
  change (∫ z, logPartition (linearProcess c z) ∂gaussianProduct κ) ≤
    (∫ z, (Z z/E-1)+Real.log E ∂gaussianProduct κ) at hh
  rw [integral_add (f := fun z ↦ Z z/E-1) (g := fun _ ↦ Real.log E)
    ((hZ.div_const E).sub (integrable_const 1)) (integrable_const _),
    integral_sub (f := fun z ↦ Z z/E) (g := fun _ ↦ 1) (hZ.div_const E) (integrable_const 1),
    integral_div,hE] at hh
  simpa only [div_self hEp.ne',integral_const,probReal_univ,one_smul,sub_self,zero_add] using hh

lemma upper_triangle_count_bound (n : ℕ) :
    2*(∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0) ≤ (n : ℝ)^2 := by
  have h := twice_upper_sum (fun i j : Fin n ↦ if i=j then (0 : ℝ) else 1)
    (fun i j ↦ by simp only [eq_comm]) (fun i ↦ by simp)
  have he : (∑ i : Fin n, ∑ j : Fin n, if i < j then (if i=j then (0 : ℝ) else 1) else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [hij,ne_of_lt hij]
    · simp [hij]
  rw [he] at h
  rw [h]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> norm_num
    _ = _ := by simp; ring

lemma hamCoeff_variance_bound (n : ℕ) (σ : Fin n → Bool) :
    (∑ k, (hamCoeff n σ k)^2) ≤ (n : ℝ)/2 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (∑ k, (hamCoeff n σ k)^2) = (n : ℝ)⁻¹ *
      ∑ i : Fin n, ∑ j : Fin n, if i < j then (1 : ℝ) else 0 := by
    simp only [hamCoeff,Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs
    · rw [mul_pow,mul_pow,spin_sq,spin_sq,inv_pow,Real.sq_sqrt hn'.le]
      ring
    · ring
  rw [he,← div_eq_inv_mul]
  apply (div_le_iff₀ hn').2
  have hh := upper_triangle_count_bound n
  nlinarith

lemma expectedMaximum_upper (n : ℕ) :
    expectedMaximum n ≤ (n : ℝ)*(Real.log 2+1/4) := by
  have hmax (J) : finiteMaximum (linearProcess (hamCoeff n) J) ≤
      logPartition (linearProcess (hamCoeff n) J) := by
    obtain ⟨σ,hσ⟩ := exists_finiteMaximum (linearProcess (hamCoeff n) J)
    rw [← hσ]
    exact le_logPartition _ _
  have hsum : (∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2)) ≤
      (2 : ℝ)^n * Real.exp ((n : ℝ)/4) := by
    calc
      _ ≤ ∑ σ : Fin n → Bool, Real.exp ((n : ℝ)/4) := by
        apply Finset.sum_le_sum
        intro σ _
        apply Real.exp_le_exp.mpr
        have hh := hamCoeff_variance_bound n σ
        linarith
      _ = _ := by simp
  have hsumpos : (0 : ℝ) < ∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2) :=
    Finset.sum_pos (fun _ _ ↦ Real.exp_pos _) Finset.univ_nonempty
  calc
    expectedMaximum n ≤ ∫ J, logPartition (linearProcess (hamCoeff n) J) ∂gaussianProduct (Fin n × Fin n) :=
      integral_mono (finiteMaximum_integrable (hamCoeff n)) (logPartition_integrable (hamCoeff n)) hmax
    _ ≤ Real.log (∑ σ : Fin n → Bool, Real.exp ((∑ k, (hamCoeff n σ k)^2)/2)) :=
      integral_logPartition_upper (hamCoeff n)
    _ ≤ Real.log ((2 : ℝ)^n*Real.exp ((n : ℝ)/4)) := Real.log_le_log hsumpos hsum
    _ = _ := by rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (Real.exp_ne_zero _),Real.log_pow,Real.log_exp]; ring

theorem groundStateSequence_tendsto :
    Tendsto groundStateSequence atTop (𝓝 groundStateValue) := by
  let u : ℕ → ℝ := fun n ↦ -expectedMaximum n
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [expectedMaximum_superadditive n m]
  have hC : 0 ≤ Real.log 2+1/4 := by positivity
  have hb : BddBelow (range (fun n : ℕ ↦ u n/n)) := by
    refine ⟨-(Real.log 2+1/4), ?_⟩
    rintro y ⟨n,rfl⟩
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [Nat.cast_zero,div_zero]
      linarith
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hh : expectedMaximum n/n ≤ Real.log 2+1/4 := by
      apply (div_le_iff₀ hn').2
      simpa only [mul_comm] using expectedMaximum_upper n
    dsimp [u]
    rw [neg_div]
    linarith
  apply tendsto_nhds_limUnder
  refine ⟨-hu.lim, ?_⟩
  have hh := (hu.tendsto_lim hb).neg
  convert hh using 1
  funext n
  simp [groundStateSequence_eq,u,div_eq_mul_inv,mul_comm]

end SKValueG

end

end OAI
