import OAI.Analysis.CircleDomains.Sobolev.VerticalWeakConstant
import OAI.Analysis.CircleDomains.Sobolev.VanishingL2Pairings

namespace OAI

/-! A locally uniform limit of the constructed heights with vanishing
error energy has exactly the vertical weak derivative. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem height_zero_energy_limit
    (v : ℕ → C(ℂ, ℝ)) (G₀ G₁ : ℕ → Lp ℝ 2 (volume : Measure EuclideanPlane))
    (hw : ∀ n, DeGiorgi.HasWeakGrad (heightLimitGradient (G₀ n) (G₁ n))
      (v n ∘ complexPlaneCoordinates) univ)
    {V : ℂ → ℝ} (hv : TendstoLocallyUniformly (fun n z => v n z) V atTop)
    (hb : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ, ∀ n z, z ∈ K → |v n z| ≤ C)
    {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hE : ∀ n, (∫ p, G₀ n p^2+G₁ n p^2) ≤ e n) :
    DeGiorgi.HasWeakGrad (heightLimitGradient 0 0) (V ∘ complexPlaneCoordinates) univ := by
  let f : ℕ → EuclideanPlane → ℂ := fun n p => ⟨0, v n (complexPlaneCoordinates p)⟩
  let D (n : ℕ) : PlaneLocalWeakComplex (f n) := {
    realGradient := fun _ => 0
    imagGradient := heightLimitGradient (G₀ n) (G₁ n)
    real_weak := by intro i ψ hψ hs hsub; simp [f]
    imag_weak := hw n
    real_memLp := fun _ _ => MemLp.zero
    imag_memLp := fun R => (heightLimitWitness (G₀ n) (G₁ n)
      ((v n).continuous.comp complexPlaneCoordinates.continuous) (hw n) R).weakGrad_component_memLp }
  have hI (n : ℕ) : Integrable
      (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) := by
    have heq : (fun p => (D n).imagGradient p 0^2+((D n).imagGradient p 1-1)^2) =
        (fun p => G₀ n p^2+G₁ n p^2) := by
      funext p
      simp [D, heightLimitGradient]
    rw [heq]
    exact (Lp.memLp (G₀ n)).integrable_sq.add (Lp.memLp (G₁ n)).integrable_sq
  have h0 (n : ℕ) : (∫ p, G₀ n p^2) ≤ e n := by
    have h := hE n
    rw [integral_add (Lp.memLp (G₀ n)).integrable_sq (Lp.memLp (G₁ n)).integrable_sq] at h
    have hp : 0 ≤ (∫ p, G₁ n p^2) := integral_nonneg (fun p => sq_nonneg (G₁ n p))
    linarith
  have h1 (n : ℕ) : (∫ p, G₁ n p^2) ≤ e n := by
    have h := hE n
    rw [integral_add (Lp.memLp (G₀ n)).integrable_sq (Lp.memLp (G₁ n)).integrable_sq] at h
    have hp : 0 ≤ (∫ p, G₀ n p^2) := integral_nonneg (fun p => sq_nonneg (G₀ n p))
    linarith
  have hz (w : Lp ℝ 2 (volume : Measure EuclideanPlane)) :
      (∫ p, (0 : Lp ℝ 2 (volume : Measure EuclideanPlane)) p*w p) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure EuclideanPlane)] with p hp
    simp
  apply weak_height_identification f D
    (fun n => Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_const.prodMk ((v n).continuous.comp complexPlaneCoordinates.continuous)))
  · intro p
    exact hv.tendstoLocallyUniformlyOn.tendsto_at (mem_univ _)
  · intro K hK
    obtain ⟨C, hC⟩ := hb (complexPlaneCoordinates '' K) (hK.image complexPlaneCoordinates.continuous)
    exact ⟨C, fun n p hp => by simpa only [f, Real.norm_eq_abs] using hC n _ ⟨p, hp, rfl⟩⟩
  · exact hI
  · intro w
    simpa [D, heightLimitGradient, hz] using
      tendsto_L2_pairing_zero_of_energy (fun n => Lp.memLp (G₀ n)) he h0 (Lp.memLp w)
  · intro w
    simpa [D, heightLimitGradient, hz] using
      tendsto_L2_pairing_zero_of_energy (fun n => Lp.memLp (G₁ n)) he h1 (Lp.memLp w)

end CircleDomainRigidity

end

end OAI
