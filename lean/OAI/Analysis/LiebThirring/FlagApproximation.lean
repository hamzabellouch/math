import OAI.Analysis.LiebThirring.EnergyAlgebra

namespace OAI


noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Filter InnerProductSpace
open scoped Topology

lemma eventually_cut_prefix_negative {N : ℕ} {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (u : Fin N → C1L2) (k κ : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) (hκ : ∀ i, 0 < κ i ∧ κ i < k i)
    (horder : Antitone k) :
    ∀ᶠ n in atTop, ∀ i (v : C1L2),
      v ∈ Submodule.span ℝ ((fun j ↦ (u j).cut n) '' Iic i) →
      energy W v v+κ i^2*inner ℝ v v ≤ 0 := by
  classical
  apply eventually_all.mpr
  intro i
  let d : Iic i → ℝ := fun j ↦ κ i^2-k j^2
  have hd (j : Iic i) : d j < 0 := by
    have hj := horder j.property
    have hki := hk i
    have hkj := hk j
    have hκi := hκ i
    dsimp [d]; nlinarith
  let M := fun n (j l : Iic i) ↦ energy W ((u j).cut n) ((u l).cut n)+
    κ i^2*inner ℝ ((u j).cut n) ((u l).cut n)
  have hM (j l : Iic i) : Tendsto (fun n ↦ M n j l) atTop (𝓝 (if j=l then d j else 0)) := by
    have hh := (cut_energy_tendsto (he j) hW (u l)).add (((u j).cutoff_inner_tendsto (u l)).const_mul (κ i^2))
    convert hh using 1
    rw [orthonormal_iff_ite.mp ho]
    by_cases hjl : j=l
    · simp [hjl,d]; ring
    · have hn : (j : Fin N) ≠ l := fun h ↦ hjl (Subtype.ext h)
      simp [hjl,hn]
  filter_upwards [eventually_negative_quadratic M d hd hM] with n hn v hv
  have him : ((fun j ↦ (u j).cut n) '' Iic i) = range (fun j : Iic i ↦ (u j).cut n) := by
    ext x
    simp
  rw [him,Submodule.mem_span_range_iff_exists_fun ℝ] at hv
  obtain ⟨c,rfl⟩ := hv
  rw [energy_sum_sum hW (fun j : Iic i ↦ (u j).cut n) (fun j ↦ (u j).cut_compact n),inner_sum_sum]
  convert hn c using 1
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,M]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro l _
  ring

/-- A compact orthonormal flag with the exact strict spectral margins. -/
lemma exists_compact_negative_flag {N : ℕ} {W : ℝ → ℝ}
    (hW : LocallyIntegrable W volume) (u : Fin N → C1L2) (k κ : Fin N → ℝ)
    (ho : Orthonormal ℝ u) (he : ∀ i, (u i).IsEigen W (k i))
    (hk : ∀ i, 0 < k i) (hκ : ∀ i, 0 < κ i ∧ κ i < k i)
    (horder : Antitone k) :
    ∃ q : Fin N → C1L2, Orthonormal ℝ q ∧
      (∀ i, HasCompactSupport (q i).val) ∧
      ∀ i (v : C1L2), v ∈ Submodule.span ℝ (q '' Iic i) →
        energy W v v+κ i^2*inner ℝ v v ≤ 0 := by
  classical
  obtain ⟨n,hli,hn⟩ := ((eventually_cut_linearIndependent ho.linearIndependent).and
    (eventually_cut_prefix_negative hW u k κ ho he hk hκ horder)).exists
  let f := fun j ↦ (u j).cut n
  let q := gramSchmidtNormed ℝ f
  have hs (i : Fin N) : Submodule.span ℝ (q '' Iic i) = Submodule.span ℝ (f '' Iic i) := by
    rw [show q = gramSchmidtNormed ℝ f from rfl,span_gramSchmidtNormed,span_gramSchmidt_Iic]
  refine ⟨q,gramSchmidtNormed_orthonormal hli,?_,?_⟩
  · intro i
    apply compact_of_mem_span f (fun j ↦ (u j).cut_compact n)
    apply Submodule.span_mono (image_subset_range _ _)
    rw [← hs i]
    exact Submodule.subset_span (mem_image_of_mem q (mem_Iic.mpr le_rfl))
  · intro i v hv
    rw [hs i] at hv
    exact hn i v hv

end SharpLiebThirring.SpectralProof

end

end OAI
