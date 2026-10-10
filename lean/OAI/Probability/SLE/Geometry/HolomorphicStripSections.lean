import OAI.Probability.SLE.Geometry.ComplexDirichletSlices

namespace OAI

/-! Low-energy angular sections of a holomorphic map on a logarithmic strip. -/
noncomputable section
open Set Filter Metric Function MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

lemma holomorphic_angular_deriv_norm {f : ℂ → ℂ} {v θ : ℝ}
    (hf : DifferentiableAt ℂ f ((v:ℂ)+(θ:ℂ)*Complex.I)) :
    ‖deriv (fun s : ℝ => f ((v:ℂ)+(s:ℂ)*Complex.I)) θ‖ =
      ‖deriv f ((v:ℂ)+(θ:ℂ)*Complex.I)‖ := by
  have hp : HasDerivAt (fun s : ℝ => (v:ℂ)+(s:ℂ)*Complex.I) Complex.I θ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I).const_add (v:ℂ)
  have hd := (hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt θ hp
  change ‖deriv (f ∘ fun s : ℝ => (v:ℂ)+(s:ℂ)*Complex.I) θ‖ = _
  rw [hd.deriv]
  simp [ContinuousLinearMap.toSpanSingleton_apply]

lemma exists_holomorphic_energy_section {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z | 0<z.im ∧ z.im<Real.pi}) (q : ℝ)
    (he : (∫⁻ z in {z : ℂ | q<z.re ∧ z.re<q+1 ∧ 0<z.im ∧ z.im<Real.pi},
      ENNReal.ofReal (‖deriv f z‖^2))<∞) :
    ∃ v∈Ioo q (q+1),
      MemLp (deriv (fun θ : ℝ => f ((v:ℂ)+(θ:ℂ)*Complex.I))) 2
        (volume.restrict (Ioo 0 Real.pi)) ∧
      (∫ θ in Ioo 0 Real.pi, ‖deriv (fun s : ℝ => f ((v:ℂ)+(s:ℂ)*Complex.I)) θ‖^2) ≤
        ∫ z in {z : ℂ | q<z.re ∧ z.re<q+1 ∧ 0<z.im ∧ z.im<Real.pi}, ‖deriv f z‖^2 := by
  let S : Set ℂ := {z | 0<z.im ∧ z.im<Real.pi}
  let T : Set ℂ := {z | q<z.re ∧ z.re<q+1 ∧ 0<z.im ∧ z.im<Real.pi}
  let J := Ioo q (q+1)
  let K := Ioo (0:ℝ) Real.pi
  let e := Complex.measurableEquivRealProd.symm
  have hS : IsOpen S := (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)
  have hT : IsOpen T := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter hS)
  have hTS : T⊆S := fun _ hz => hz.2.2
  have hpre : e ⁻¹' T=J ×ˢ K := by ext z; simp [e,T,J,K,and_assoc]
  have hmp : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have hgT := deriv_memLp_two_of_energy hT (hf.mono hTS) he
  have hiT : IntegrableOn (fun z => ‖deriv f z‖^2) T := hgT.norm.integrable_sq
  have hip : Integrable (fun p : ℝ×ℝ => ‖deriv f (e p)‖^2)
      ((volume.restrict J).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict]
    exact hpre ▸ (hmp.integrableOn_comp_preimage e.measurableEmbedding).mpr hiT
  have hgm : AEStronglyMeasurable (fun p : ℝ×ℝ => deriv f (e p))
      ((volume.restrict J).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict, ← hpre]
    exact hgT.aestronglyMeasurable.comp_quasiMeasurePreserving
      (hmp.quasiMeasurePreserving.restrict (fun _ hz => hz))
  have hgp := (memLp_two_iff_integrable_sq_norm hgm).mpr hip
  obtain ⟨v,hv,hvm,hve⟩ := exists_complex_energy_section (fun p => deriv f (e p)) q hgp
  have hd (θ : ℝ) (hθ : θ∈K) : DifferentiableAt ℂ f ((v:ℂ)+(θ:ℂ)*Complex.I) := by
    apply hf.differentiableAt (hS.mem_nhds ?_)
    simpa [S,K] using hθ
  have hnorm (θ : ℝ) (hθ : θ∈K) :
      ‖deriv (fun s : ℝ => f ((v:ℂ)+(s:ℂ)*Complex.I)) θ‖ = ‖deriv f (e (v,θ))‖ := by
    convert holomorphic_angular_deriv_norm (hd θ hθ) using 1
    congr 2
    apply Complex.ext <;> simp [e]
  have hae : ∀ᵐ θ ∂volume.restrict K,
      ‖deriv (fun s : ℝ => f ((v:ℂ)+(s:ℂ)*Complex.I)) θ‖ = ‖deriv f (e (v,θ))‖ :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun θ hθ => hnorm θ hθ)
  refine ⟨v,hv,?_,?_⟩
  · exact hvm.of_le (aestronglyMeasurable_deriv _ _) (hae.mono fun _ h => h.le)
  · calc
      _ = ∫ θ in K, ‖deriv f (e (v,θ))‖^2 := integral_congr_ae (hae.mono fun _ h => congrArg (·^2) h)
      _ ≤ ∫ p, ‖deriv f (e p)‖^2 ∂((volume.restrict J).prod (volume.restrict K)) := hve
      _ = ∫ z in T, ‖deriv f z‖^2 := by
        rw [Measure.prod_restrict, ← hpre]
        simpa only [Measure.volume_eq_prod] using
          hmp.setIntegral_preimage_emb e.measurableEmbedding (fun z => ‖deriv f z‖^2) T

end SLEExactGauge

end

end OAI
