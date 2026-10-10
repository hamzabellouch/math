import OAI.Analysis.TriangularHilbert.HeatBound

namespace OAI

universe uι uE uF

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Topology
open Filter MeasureTheory
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def gramGradientAt (R P : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (3 : ℝ) • traceRealCLM.comp ((ContinuousLinearMap.mul ℝ _) ((R * CFC.sqrt P)ᴴ))

@[simp] lemma gramGradientAt_apply (R P D : Matrix ι ι ℂ) :
    gramGradientAt R P D = 3 * hsReal (R * CFC.sqrt P) D := rfl

lemma regularized_energyGram_hasFDerivAt (R : Matrix ι ι ℂ) {η : ℝ} (hη : 0 < η) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (regularize (Xᴴ * X) η))
      (gramGradientAt R (regularize (Rᴴ * R) η)) R := by
  have hg := (((hasFDerivAt_id R (𝕜 := ℝ)).star).mul' (hasFDerivAt_id R)).add_const
    (η • (1 : Matrix ι ι ℂ))
  have hp := regularize_posDef (Matrix.posSemidef_conjTranspose_mul_self R) hη
  have hn : ∀ᶠ X : Matrix ι ι ℂ in 𝓝 R, 0 ≤ regularize (Xᴴ * X) η :=
    Eventually.of_forall fun X =>
      (regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self X) hη.le).nonneg
  have hh := (energy_hasFDerivWithinAt hp).comp_hasFDerivAt R hg hn
  convert! hh using 1
  ext D
  simp only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, id_eq,
    ContinuousLinearEquiv.coe_coe, starL'_apply, smul_eq_mul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Matrix.star_eq_conjTranspose]
  rw [energyGradient_gram, gramGradientAt_apply]

lemma continuousAt_tendstoUniformlyOnFilter {E : Type uE} {F : Type uF} [TopologicalSpace E]
    [UniformSpace F] {H : ℝ × E → F} {x : E}
    (hH : ContinuousAt H (0, x)) :
    TendstoUniformlyOnFilter (fun η y => H (η, y)) (fun y => H (0, y))
      (𝓝[>] 0) (𝓝 x) := by
  apply tendstoUniformlyOnFilter_iff_tendsto.mpr
  have hp : (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x ≤ 𝓝 (0, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have h₂ : Tendsto H ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.mono_left hp
  have h₁ : Tendsto (fun p : ℝ × E => H (0, p.2))
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) (𝓝 (H (0, x))) :=
    hH.tendsto.comp (tendsto_const_nhds.prodMk_nhds tendsto_snd)
  exact (h₁.prodMk_nhds h₂).mono_right (nhds_le_uniformity _)

def gramRegularization (η : ℝ) (R : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  regularize (Rᴴ * R) (η^2)

lemma continuous_gramRegularization : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramRegularization p.1 p.2) := by
  unfold gramRegularization regularize
  fun_prop

lemma gramRegularization_posSemidef (η : ℝ) (R : Matrix ι ι ℂ) :
    (gramRegularization η R).PosSemidef :=
  regularize_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _) (sq_nonneg _)

@[simp] lemma gramRegularization_zero (R : Matrix ι ι ℂ) :
    gramRegularization 0 R = Rᴴ * R := by simp [gramRegularization, regularize]

lemma continuous_regularizedGradient : Continuous
    (fun p : ℝ × Matrix ι ι ℂ => gramGradientAt p.2 (gramRegularization p.1 p.2)) := by
  unfold gramGradientAt
  have hs : Continuous (fun p : ℝ × Matrix ι ι ℂ => CFC.sqrt (gramRegularization p.1 p.2)) :=
    continuous_sqrt_matrix continuous_gramRegularization
      (fun p => gramRegularization_posSemidef p.1 p.2)
  have hr : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ) := (continuous_snd.mul hs).star
  have hm : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ)) :=
    (ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ)).continuous.comp hr
  have ht : Continuous (fun p : ℝ × Matrix ι ι ℂ =>
      traceRealCLM.comp ((ContinuousLinearMap.mul ℝ (Matrix ι ι ℂ))
        ((p.2 * CFC.sqrt (gramRegularization p.1 p.2))ᴴ))) :=
    (ContinuousLinearMap.compL ℝ (Matrix ι ι ℂ) (Matrix ι ι ℂ) ℝ
      traceRealCLM).continuous.comp hm
  exact ht.const_smul (3 : ℝ)

lemma eventually_regularizedEnergy_deriv (R : Matrix ι ι ℂ) :
    ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R,
      HasFDerivAt (fun X => energy (gramRegularization p.1 X))
        (gramGradientAt p.2 (gramRegularization p.1 p.2)) p.2 := by
  have hp0 : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
  have hh : ∀ᶠ p : ℝ × Matrix ι ι ℂ in (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 R, 0 < p.1 :=
    hp0.prod_inl _
  filter_upwards [hh] with p hp
  exact regularized_energyGram_hasFDerivAt p.2 (sq_pos_of_pos hp)

lemma continuous_regularizedEnergy_single (R : Matrix ι ι ℂ) :
    Continuous (fun η : ℝ => energy (gramRegularization η R)) := by
  have hp : Continuous (fun η : ℝ => gramRegularization η R) := by
    unfold gramRegularization regularize
    fun_prop
  exact traceRealCLM.continuous.comp (hp.mul (continuous_sqrt_matrix hp
    (fun η => gramRegularization_posSemidef η R)))

lemma tendsto_regularizedEnergy (R : Matrix ι ι ℂ) :
    Tendsto (fun η => energy (gramRegularization η R))
      (𝓝[>] 0) (𝓝 (energy (Rᴴ * R))) := by
  have ht := (continuous_regularizedEnergy_single R).tendsto (0 : ℝ)
  rw [gramRegularization_zero] at ht
  exact ht.mono_left nhdsWithin_le_nhds

theorem energyGram_hasFDerivAt (R : Matrix ι ι ℂ) :
    HasFDerivAt (fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
      (gramGradientAt R (Rᴴ * R)) R := by
  have hh := hasFDerivAt_of_tendstoUniformlyOnFilter (𝕜 := ℝ) (x := R)
    (f := fun (η : ℝ) (X : Matrix ι ι ℂ) => energy (gramRegularization η X))
    (f' := fun (η : ℝ) (X : Matrix ι ι ℂ) => gramGradientAt X (gramRegularization η X))
    (g := fun X : Matrix ι ι ℂ => energy (Xᴴ * X))
    (g' := fun X : Matrix ι ι ℂ => gramGradientAt X (gramRegularization 0 X))
    (continuousAt_tendstoUniformlyOnFilter
      (continuous_regularizedGradient.continuousAt (x := (0, R))))
    (eventually_regularizedEnergy_deriv R)
    (Eventually.of_forall (fun X => tendsto_regularizedEnergy X))
  simpa only [gramRegularization_zero] using hh

end
end TriangularHilbert.MatrixEnergy
end

end OAI
