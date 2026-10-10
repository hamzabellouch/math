import OAI.Analysis.Mahler.RescaledMassMap
import OAI.Analysis.Mahler.UniformJet

namespace OAI

namespace MahlerRescaling
open Set Metric Filter
open scoped Topology
variable {n N m : ℕ} {U : Set (Mahler.ComplexEuclidean n)}
  {f : Fin N → Mahler.ComplexEuclidean n → ℂ}
  {G : Fin N → MvPolynomial (Fin n) ℂ}

/-- The rescaled functions themselves, with their actual Frechet derivatives,
converge at order epsilon to the stated homogeneous leading polynomial. -/
theorem source_rescaling_C2_bound (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) :
    ∃ C > 0, ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      DifferentiableOn ℂ (rescale (f j) m ε) (ball 0 4) ∧
      ∀ z ∈ closedBall (0 : Mahler.ComplexEuclidean n) 2,
        ‖rescale (f j) m ε z-leadingComponent G j z‖ ≤ C*ε ∧
        ‖fderiv ℂ (rescale (f j) m ε) z-fderiv ℂ (leadingComponent G j) z‖ ≤ C*ε ∧
        ‖fderiv ℂ (fderiv ℂ (rescale (f j) m ε)) z-
          fderiv ℂ (fderiv ℂ (leadingComponent G j)) z‖ ≤ C*ε := by
  obtain ⟨C,hC,δ,hδ,hb⟩ := rescaled_holomorphic_remainder_C2_bound
    (f := taylorRemainder f G j) h.open_domain h.zero_mem
    ((h.holomorphic j).sub (leadingComponent_differentiable G j).differentiableOn)
    (source_remainder_zero h j) (source_remainder_bound h j)
  refine ⟨C,hC,δ,hδ,?_⟩
  intro ε hε hεδ
  obtain ⟨hdr,hbound⟩ := hb ε hε hεδ
  have he := rescaled_source_remainder (f := f) h.homogeneous hε.ne' j
  have headd : rescale (f j) m ε =
      fun z => rescale (taylorRemainder f G j) m ε z+leadingComponent G j z := by
    funext z
    rw [he]
    exact (sub_add_cancel _ _).symm
  have hdf : DifferentiableOn ℂ (rescale (f j) m ε) (ball 0 4) := by
    rw [headd]
    exact hdr.add (leadingComponent_differentiable G j).differentiableOn
  refine ⟨hdf,?_⟩
  intro z hz
  have hz4 : z ∈ ball (0 : Mahler.ComplexEuclidean n) 4 :=
    closedBall_subset_ball (by norm_num : (2 : ℝ) < 4) hz
  have hd1 : fderiv ℂ (rescale (taylorRemainder f G j) m ε) z =
      fderiv ℂ (rescale (f j) m ε) z - fderiv ℂ (leadingComponent G j) z := by
    rw [he]
    exact fderiv_fun_sub ((hdf z hz4).differentiableAt (isOpen_ball.mem_nhds hz4))
      (leadingComponent_differentiable G j z)
  have hd2 : fderiv ℂ (fderiv ℂ (rescale (taylorRemainder f G j) m ε)) z =
      fderiv ℂ (fderiv ℂ (rescale (f j) m ε)) z-
        fderiv ℂ (fderiv ℂ (leadingComponent G j)) z := by
    rw [he]
    exact second_fderiv_sub_of_open isOpen_ball hz4 hdf
      (leadingComponent_differentiable G j).differentiableOn
  obtain ⟨h0,h1,h2⟩ := hbound z hz
  refine ⟨?_,?_,?_⟩
  · simpa only [he] using h0
  · rwa [hd1] at h1
  · rwa [hd2] at h2

/-- The exact C² convergence used at the small-sphere limit, expressed in
uniform convergence of the function and its first two complex derivatives. -/
theorem source_rescaling_uniform_C2 (h : Mahler.MassHypotheses n N m U f G) (j : Fin N) :
    TendstoUniformlyOn (fun ε : ℝ => rescale (f j) m ε) (leadingComponent G j)
      (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (rescale (f j) m ε))
      (fderiv ℂ (leadingComponent G j)) (𝓝[>] 0) (closedBall 0 2) ∧
    TendstoUniformlyOn (fun ε : ℝ => fderiv ℂ (fderiv ℂ (rescale (f j) m ε)))
      (fderiv ℂ (fderiv ℂ (leadingComponent G j))) (𝓝[>] 0) (closedBall 0 2) := by
  obtain ⟨C,hC,δ,hδ,hb⟩ := source_rescaling_C2_bound h j
  refine ⟨uniform_of_linear_error hC hδ ?_,uniform_of_linear_error hC hδ ?_,?_⟩
  · intro ε hε hεδ z hz
    exact ((hb ε hε hεδ).2 z hz).1
  · intro ε hε hεδ z hz
    exact ((hb ε hε hεδ).2 z hz).2.1
  · exact uniform_of_linear_error (F := fun ε : ℝ => fderiv ℂ (fderiv ℂ (rescale (f j) m ε)))
      (g := fderiv ℂ (fderiv ℂ (leadingComponent G j))) hC hδ
      (fun ε hε hεδ z hz => ((hb ε hε hεδ).2 z hz).2.2)

end MahlerRescaling

end OAI
