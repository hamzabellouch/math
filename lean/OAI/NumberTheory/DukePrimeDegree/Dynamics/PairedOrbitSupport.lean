import OAI.NumberTheory.DukePrimeDegree.Dynamics.PairedBlockOrbit
import Mathlib.Logic.Encodable.Pi

namespace OAI

/-!
# Root-invariant finite measures supported on a block orbit

The orbit measure need not be invariant under its entire orbit group.
Only the two opposite root maps preserve it.  Polynomial recurrence is
applied to every rational stabilizer-commutant observable simultaneously;
a generic point then makes that rational commutant scalar.  This reduces
the dynamical target to finding positive mass on a block orbit, rather
than assuming a finite homogeneous invariant measure on that orbit.
-/

noncomputable section
open Matrix Set MeasureTheory Filter
open scoped Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma conjugationOrbitMap_map_invariant_element {n : ℕ} (g : G n)
    (L : Subgroup (G n)) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val)
    (μ : Measure (LatticeOrbitQuotient g L)) (h : L)
    (hinv : μ.map (fun x => latticeOrbitRightAction g L x h) = μ) :
    (μ.map (conjugationOrbitMap g L M hM)).map (slMatrixConjugation h.val) =
      μ.map (conjugationOrbitMap g L M hM) := by
  let F := conjugationOrbitMap g L M hM
  have hF : Measurable F := (continuous_conjugationOrbitMap g L M hM).measurable
  calc
    _ = μ.map (slMatrixConjugation h.val ∘ F) :=
      Measure.map_map (continuous_slMatrixConjugation h.val).measurable hF
    _ = μ.map (F ∘ fun x => latticeOrbitRightAction g L x h) := by
      congr 1
      funext x
      exact (conjugationOrbitMap_rightAction g L M hM x h).symm
    _ = (μ.map (fun x => latticeOrbitRightAction g L x h)).map F :=
      (Measure.map_map hF (continuous_latticeOrbitRightAction g L h).measurable).symm
    _ = μ.map F := by rw [hinv]

lemma ae_conjugationOrbitMap_commute_root {n : ℕ}
    (g : G n) (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ]
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L)
    (hinv : μ.map (fun x => latticeOrbitRightAction g L x
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hroot⟩) = μ)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ s : pointOrbitStabilizer g L, Commute M s.val.val) :
    ∀ᵐ x ∂μ, Commute (conjugationOrbitMap g L M hM x)
      (Matrix.transvection i j (1 : ℝ)) := by
  let F := conjugationOrbitMap g L M hM
  have hF : Measurable F := (continuous_conjugationOrbitMap g L M hM).measurable
  have hr : (μ.map F).map (rootMatrixConjugation i j 1) = μ.map F := by
    rw [← slMatrixConjugation_root i j hij]
    exact conjugationOrbitMap_map_invariant_element g L M hM μ
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hroot⟩ hinv
  exact ae_of_ae_map hF.aemeasurable
    (ae_commute_root_of_conjugation_invariance (μ.map F) i j hij hr)

lemma latticeRational_commutes_pointStabilizer {n : ℕ}
    (g : G n) (L : Subgroup (G n)) (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) :
    ∀ s : pointOrbitStabilizer g L,
      Commute (slMatrixConjugation g (rationalMatrixCast B)) s.val.val := by
  intro s
  obtain ⟨γ, hγ⟩ := pointOrbitStabilizer_eq_conjugate g L s
  rw [← hγ]
  exact ((commute_rationalMatrixCast_iff B (latticeStabilizerMatrix g L γ)).mpr
    ((mem_commutatorFamily_ker _ _).mp hB γ)).map (slMatrixConjugationHom g)

/-- Full orbit-group invariance is unnecessary: recurrence for the two
root maps and genericity almost everywhere suffice to make the actual
integral-stabilizer commutant scalar. -/
theorem realStabilizer_scalar_of_root_pair_measure {n : ℕ}
    (hn : n.Prime) (g : G n) (L : Subgroup (G n))
    (μ : Measure (LatticeOrbitQuotient g L)) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (i j : Fin n) (hij : i ≠ j)
    (hroot : Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ) ∈ L)
    (hopposite : Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ) ∈ L)
    (hinv : μ.map (fun x => latticeOrbitRightAction g L x
      ⟨Matrix.SpecialLinearGroup.transvection hij (-1 : ℝ), hroot⟩) = μ)
    (hopinv : μ.map (fun x => latticeOrbitRightAction g L x
      ⟨Matrix.SpecialLinearGroup.transvection hij.symm (-1 : ℝ), hopposite⟩) = μ)
    (hgeneric : ∀ᵐ x ∂μ, ∀ v ∈ pointLattice (latticeOrbitPoint g L x),
      v ≠ 0 → ∀ k, v k ≠ 0)
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ (commutatorFamily
      (fun γ => rationalMatrixCast (latticeStabilizerMatrix g L γ))).ker) :
    ∃ c : ℝ, M = c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  let : Encodable ℚ := Encodable.ofCountable ℚ
  let : Encodable (Matrix (Fin n) (Fin n) ℚ) :=
    inferInstanceAs (Encodable (Fin n → Fin n → ℚ))
  have hae (B : Matrix (Fin n) (Fin n) ℚ) : ∀ᵐ x ∂μ,
      ∀ hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker,
        Commute (conjugationOrbitMap g L (slMatrixConjugation g (rationalMatrixCast B))
          (latticeRational_commutes_pointStabilizer g L B hB) x)
            (Matrix.transvection i j (1 : ℝ)) ∧
        Commute (conjugationOrbitMap g L (slMatrixConjugation g (rationalMatrixCast B))
          (latticeRational_commutes_pointStabilizer g L B hB) x)
            (Matrix.transvection j i (1 : ℝ)) := by
    by_cases hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker
    · filter_upwards [ae_conjugationOrbitMap_commute_root g L μ i j hij hroot hinv
          _ (latticeRational_commutes_pointStabilizer g L B hB),
        ae_conjugationOrbitMap_commute_root g L μ j i hij.symm hopposite hopinv
          _ (latticeRational_commutes_pointStabilizer g L B hB)] with x hx hy
      intro _
      exact ⟨hx, hy⟩
    · exact Eventually.of_forall fun _ h => (hB h).elim
  have : NeBot (ae μ) := ae_neBot.mpr hμ
  obtain ⟨x, hx, hxgeneric⟩ := ((ae_all_iff.mpr hae).and hgeneric).exists
  have hscalar (B : Matrix (Fin n) (Fin n) ℚ)
      (hB : B ∈ (commutatorFamily (latticeStabilizerMatrix g L)).ker) :
      ∃ q : ℚ, B = q • (1 : Matrix (Fin n) (Fin n) ℚ) := by
    have hxB := hx B hB
    induction x using Quotient.inductionOn with
    | h b =>
      have hg : ∀ v ∈ rowLattice (g * b.val).val, v ≠ 0 → ∀ k, v k ≠ 0 := hxgeneric
      have hpair : Commute (slMatrixConjugation (g * b.val) (rationalMatrixCast B))
          (Matrix.transvection i j (1 : ℝ)) ∧
          Commute (slMatrixConjugation (g * b.val) (rationalMatrixCast B))
            (Matrix.transvection j i (1 : ℝ)) := by
        change Commute (slMatrixConjugation b.val
            (slMatrixConjugation g (rationalMatrixCast B))) _ ∧
          Commute (slMatrixConjugation b.val
            (slMatrixConjugation g (rationalMatrixCast B))) _ at hxB
        simpa only [← slMatrixConjugation_mul] using hxB
      exact rationalMatrix_scalar_of_opposite_roots hn (g * b.val) hg B i j hij
        hpair.1 hpair.2
  apply (mem_scalarMatrixSpace_iff M).mp
  rw [latticeStabilizer_commutant_rational] at hM
  apply (Submodule.span_le.mpr ?_) hM
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨q, rfl⟩ := hscalar B hB
  apply (mem_scalarMatrixSpace_iff _).mpr
  refine ⟨(q : ℝ), ?_⟩
  change (q • (1 : Matrix (Fin n) (Fin n) ℚ)).map (algebraMap ℚ ℝ) = _
  ext a b
  by_cases hab : a = b <;> simp [hab]

end DukePrimeDegree

end

end OAI
