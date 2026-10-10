import Mathlib
import OAI.Analysis.Commutator.DecomposableDenseLimit
import OAI.Analysis.Commutator.FieldNormClosure
import OAI.Analysis.Commutator.KaplanskyFull

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma fieldMember_of_bicommutant_contraction (Q : Ω → VonNeumannAlgebra H)
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hA : A∈Set.centralizer (Set.centralizer (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ))))
    (hnA : ‖A‖≤1) : FieldMember μ Q A := by
  have hcomm (s : Set Ω) (hs : MeasurableSet s) : Commute A (indicatorOperator μ s hs) := by
    exact (hA (indicatorOperator μ s hs)
      (fun B hB => (fieldMember_commutes_indicator μ Q hB s hs).eq)).symm
  obtain ⟨T,hm,hb,he⟩ := exists_field_of_commutes_indicator μ A hcomm
  let v : ℕ → H := TopologicalSpace.denseSeq H
  have hap (n : ℕ) : ∃ B : Lp H 2 μ →L[ℂ] Lp H 2 μ,
      B∈fieldAlgebra μ Q ∧ ‖B‖≤1 ∧ ∀ j : Fin n,
      ‖B (Lp.const 2 μ (v j))-A (Lp.const 2 μ (v j))‖<1/((n:ℝ)+1) :=
    Kaplansky.contraction_finite_approx (Fin n) (fieldAlgebra μ Q) (fieldAlgebra_isClosed μ Q)
      hA hnA (fun j => Lp.const 2 μ (v j)) _ (by positivity)
  choose B hB hBn hBe using hap
  choose S hS hSb hSe hSm using (fun n => fieldMember_tight μ Q (hB n) (by norm_num : (0:ℝ)≤1) (hBn n))
  have hlim (j : ℕ) : Tendsto (fun n => operator μ (S n) (hS n) (hSb n)
      (Lp.const 2 μ (TopologicalSpace.denseSeq H j))) atTop
      (𝓝 (operator μ T hm hb (Lp.const 2 μ (TopologicalSpace.denseSeq H j)))) := by
    simp only [←hSe,←he]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [eventually_ge_atTop (j+1)] with n hn
    exact (hBe n ⟨j,by omega⟩).le
  exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,
    mem_ae_of_bounded_dense_const_limit μ Q T hm hb S hS (by norm_num) hSb hSm hlim⟩

lemma fieldMember_of_bicommutant (Q : Ω → VonNeumannAlgebra H)
    (A : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hA : A∈Set.centralizer (Set.centralizer (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))) :
    FieldMember μ Q A := by
  let d : ℂ := ((‖A‖+1:ℝ):ℂ)
  have hdR : 0<‖A‖+1 := by positivity
  have hd : d≠0 := by
    dsimp only [d]
    exact_mod_cast (ne_of_gt hdR)
  have hdn : ‖d⁻¹ • A‖≤1 := by
    rw [norm_smul,norm_inv]
    have hnd : ‖d‖=‖A‖+1 := by
      dsimp only [d]
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hdR]
    rw [hnd]
    have hi : (‖A‖+1)⁻¹*‖A‖=‖A‖/(‖A‖+1) := by ring
    rw [hi]
    exact (div_le_one hdR).mpr (by linarith)
  have hdc : d⁻¹ • A∈Set.centralizer (Set.centralizer
      (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ))) := by
    intro B hB
    change B*(d⁻¹ • A)=(d⁻¹ • A)*B
    rw [mul_smul_comm,smul_mul_assoc,hA B hB]
  have hmem := fieldMember_smul μ Q d
    (fieldMember_of_bicommutant_contraction μ Q (d⁻¹ • A) hdc hdn)
  simpa only [smul_smul,mul_inv_cancel₀ hd,one_smul] using hmem

def fieldVonNeumann (Q : Ω → VonNeumannAlgebra H) : VonNeumannAlgebra (Lp H 2 μ) where
  __ := fieldAlgebra μ Q
  centralizer_centralizer' := Set.Subset.antisymm
    (fun A hA => fieldMember_of_bicommutant μ Q A hA)
    (fun A hA _ hB => (hB A hA).symm)

end Kadison.Decomposable

end

end
end

end OAI
