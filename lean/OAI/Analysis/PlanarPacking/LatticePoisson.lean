import OAI.Analysis.PlanarPacking.ExactPair
import OAI.Analysis.PlanarPacking.LatticeIntegration

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
structure HasLatticePoisson (f : Plane→ℂ) : Prop where
  integrable : Integrable f
  summable : Summable (fun p : ℤ×ℤ => f (latticePoint p))
  fourier_summable : Summable (fun p : ℤ×ℤ => 𝓕 f (latticePoint p))
  eq : (∑' p : ℤ×ℤ, f (latticePoint p))=∑' p : ℤ×ℤ, 𝓕 f (latticePoint p)
lemma HasLatticePoisson.add {f g : Plane→ℂ} (hf : HasLatticePoisson f)
    (hg : HasLatticePoisson g) : HasLatticePoisson (fun x => f x+g x) where
  integrable := hf.integrable.add hg.integrable
  summable := hf.summable.add hg.summable
  fourier_summable := by
    simp_rw [fourier_add_integrable hf.integrable hg.integrable]
    exact hf.fourier_summable.add hg.fourier_summable
  eq := by
    simp_rw [fourier_add_integrable hf.integrable hg.integrable]
    rw [hf.summable.tsum_add hg.summable,hf.fourier_summable.tsum_add hg.fourier_summable,
      hf.eq,hg.eq]
lemma HasLatticePoisson.zero : HasLatticePoisson (fun _ : Plane => (0 : ℂ)) where
  integrable := integrable_zero _ _ _
  summable := summable_zero
  fourier_summable := by
    simp only [Real.fourier_eq',smul_zero,integral_zero]
    exact summable_zero
  eq := by simp [Real.fourier_eq']
lemma HasLatticePoisson.finset_sum {ι : Type*} (s : Finset ι) (f : ι→Plane→ℂ)
    (hf : ∀ j∈s, HasLatticePoisson (f j)) :
    HasLatticePoisson (fun x => ∑ j∈s, f j x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasLatticePoisson.zero
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
lemma gaussianSpectral_hasPoisson {μ : Measure ℝ} [SFinite μ] {f : ℝ→ℂ}
    (hf : Integrable f μ) (ht : ∀ᵐ t ∂μ, |t|≤1) : HasLatticePoisson (gaussianSpectral μ f) where
  integrable := gaussianSpectral_integrable hf
  summable := (lattice_direct_hasSum hf).summable
  fourier_summable := (lattice_transform_hasSum hf ht).summable
  eq := gaussianSpectral_hex_poisson hf ht
lemma gaussianSpectral_dirac_hasPoisson {t : ℝ} (ht : |t|≤1) (c : ℂ) :
    HasLatticePoisson (gaussianSpectral (Measure.dirac t) (fun _ => c)) := by
  apply gaussianSpectral_hasPoisson (integrable_dirac (by finiteness))
  simpa only [ae_dirac_eq,Filter.eventually_pure] using ht
lemma density_piece_hasPoisson (p : CardinalData) {j : ℕ} (hj : j<6) :
    HasLatticePoisson (gaussianSpectral
      (volume.restrict (Set.Icc ((j:ℝ)/6) (((j:ℝ)+1)/6))) (density p j)) := by
  apply gaussianSpectral_hasPoisson (density_piece_integrable p hj)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hj' : (j:ℝ)≤5 := by exact_mod_cast Nat.le_of_lt_succ hj
  have h0 : 0≤(j:ℝ) := Nat.cast_nonneg _
  have ht0 : 0≤t := by linarith [ht.1]
  rw [abs_of_nonneg ht0]
  linarith [ht.2]
lemma qComplex_hasPoisson (p : CardinalData) : HasLatticePoisson (qComplex p) := by
  apply HasLatticePoisson.add
  · apply HasLatticePoisson.add
    · apply gaussianSpectral_dirac_hasPoisson
      norm_num
    · apply HasLatticePoisson.finset_sum
      intro j hj
      apply gaussianSpectral_dirac_hasPoisson
      rw [abs_of_nonneg (by positivity)]
      have hj' : (j:ℝ)≤6 := by exact_mod_cast (Finset.mem_Icc.mp hj).2
      linarith
  · apply HasLatticePoisson.finset_sum
    intro j hj
    exact density_piece_hasPoisson p (Finset.mem_range.mp hj)
lemma qk_lattice_summable (p : CardinalData) :
    Summable (fun n : ℤ×ℤ => qSchwartz p (latticePoint n)) ∧
    Summable (fun n : ℤ×ℤ => kSchwartz p (latticePoint n)) := by
  constructor
  · simpa only [Function.comp_def,Complex.reCLM_apply,qComplex_re] using
      (qComplex_hasPoisson p).summable.mapL Complex.reCLM
  · have hh := (qComplex_hasPoisson p).fourier_summable.mapL Complex.reCLM
    simpa only [Function.comp_def,Complex.reCLM_apply,qComplex_fourier,← kSchwartz_apply] using hh
lemma qk_lattice_poisson (p : CardinalData) :
    (∑' n : ℤ×ℤ, qSchwartz p (latticePoint n))=
      ∑' n : ℤ×ℤ, kSchwartz p (latticePoint n) := by
  have hh := congrArg Complex.re (qComplex_hasPoisson p).eq
  rw [Complex.re_tsum (qComplex_hasPoisson p).summable,
    Complex.re_tsum (qComplex_hasPoisson p).fourier_summable] at hh
  simpa only [qComplex_re,qComplex_fourier,← kSchwartz_apply] using hh
lemma pair_lattice_poisson (p q : CardinalData) :
    (∑' n : ℤ×ℤ, pairLeft p q (latticePoint n))=
      ∑' n : ℤ×ℤ, pairRight p q (latticePoint n) := by
  change (∑' n : ℤ×ℤ, (qSchwartz p (latticePoint n)+kSchwartz q (latticePoint n)))=
    ∑' n : ℤ×ℤ, (qSchwartz q (latticePoint n)+kSchwartz p (latticePoint n))
  rw [(qk_lattice_summable p).1.tsum_add (qk_lattice_summable q).2,
    (qk_lattice_summable q).1.tsum_add (qk_lattice_summable p).2,
    qk_lattice_poisson p,qk_lattice_poisson q,add_comm]
end SharpPlanar

end OAI
