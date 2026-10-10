import OAI.Dynamics.EntropyCounterexample.SkewProduct
import OAI.Geometry.SingularHomology.HomologySpectrumFactor

namespace OAI

noncomputable section

namespace Problem340

open PolynomialSpectrum
open scoped OnePoint

abbrev RawBase := AddCircle (100 : ℝ) × OnePoint ℂ

def rawBaseSquare (x : RawBase) : RawBase :=
  (x.1, OnePoint.map (fun z : ℂ => z ^ 2) x.2)

def rawBaseProjection {q : ℕ} (x : RawState q) : RawBase :=
  (x.1, x.2.1)

def rawFactorInclusion {q : ℕ} (x : RawBase) : RawState q :=
  (x.1, OnePoint.map (fun z : ℂ => z ^ 2) x.2,
    fun _ => ((0 : ℂ) : OnePoint ℂ))

theorem continuous_rawBaseSquare : Continuous rawBaseSquare := by
  apply continuous_fst.prodMk
  simpa [rawQuadratic, Function.comp_def] using
    continuous_rawQuadratic.comp
      ((continuous_const : Continuous (fun _ : RawBase => (0 : ℂ))).prodMk continuous_snd)

theorem continuous_rawBaseProjection {q : ℕ} : Continuous (@rawBaseProjection q) :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)

theorem continuous_rawFactorInclusion {q : ℕ} : Continuous (@rawFactorInclusion q) := by
  exact continuous_fst.prodMk
    ((continuous_snd.comp continuous_rawBaseSquare).prodMk continuous_const)

@[simp] theorem rawNormalForm_eq_factor {q : ℕ} :
    @rawNormalForm q = rawFactorInclusion ∘ rawBaseProjection := rfl

@[simp] theorem rawProjection_factor_eq_square {q : ℕ} :
    @rawBaseProjection q ∘ rawFactorInclusion = rawBaseSquare := rfl

theorem rawUpdate_homology_pairRadii_subset {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R) (n : ℕ) :
    pairRadii (realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR)) ⊆
      insert 0 (pairRadii (realHomologyMap n rawBaseSquare continuous_rawBaseSquare)) := by
  simpa only [rawProjection_factor_eq_square] using
    homology_pairRadii_factor_subset n (rawUpdate h C R)
      rawFactorInclusion rawBaseProjection
      (continuous_rawUpdate hh hC hR) continuous_rawFactorInclusion
      continuous_rawBaseProjection (rawUpdateHomotopy hh hC hR).symm

theorem bddAbove_rawUpdate_homology_pairRadii {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R)
    (hB : BddAbove (⋃ n,
      pairRadii (realHomologyMap n rawBaseSquare continuous_rawBaseSquare))) :
    BddAbove (⋃ n,
      pairRadii (realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR))) := by
  apply bddAbove_homology_pairRadii_of_homotopy_factor
    (rawUpdate h C R) rawFactorInclusion rawBaseProjection
    (continuous_rawUpdate hh hC hR) continuous_rawFactorInclusion
    continuous_rawBaseProjection (rawUpdateHomotopy hh hC hR).symm
  simpa only [rawProjection_factor_eq_square] using hB

theorem rawUpdate_homology_pairRadii_le_two_of_cubic {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R)
    (hpoly : ∀ n, let B := realHomologyMap n rawBaseSquare continuous_rawBaseSquare
      B * (B - 1) * (B - 2) = 0)
    (n : ℕ) {r : ℝ}
    (hr : r ∈ pairRadii
      (realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR))) :
    r ≤ 2 := by
  rcases rawUpdate_homology_pairRadii_subset hh hC hR n hr with hzero | hmodel
  · rw [hzero]
    norm_num
  · exact pairRadii_le_two_of_cubic _ (hpoly n) hmodel

theorem bddAbove_rawUpdate_homology_pairRadii_of_cubic {q : ℕ}
    {h : RawState q → ℝ} {C : RawState q → ℂ} {R : RawState q → Fin q → ℂ}
    (hh : Continuous h) (hC : Continuous C) (hR : Continuous R)
    (hpoly : ∀ n, let B := realHomologyMap n rawBaseSquare continuous_rawBaseSquare
      B * (B - 1) * (B - 2) = 0) :
    BddAbove (⋃ n,
      pairRadii (realHomologyMap n (rawUpdate h C R) (continuous_rawUpdate hh hC hR))) := by
  refine ⟨2, ?_⟩
  intro r hr
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hr
  exact rawUpdate_homology_pairRadii_le_two_of_cubic hh hC hR hpoly n hn

end Problem340

end

end OAI
