import Mathlib
import OAI.Probability.BinarySweep.MatrixBounds.FourierTrace
import OAI.Probability.BinarySweep.Mixing.LongRowDimension

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Young

lemma rowLen_one_le_tail (μ : YoungDiagram) : μ.rowLen 1 ≤ μ.rowLens.tail.sum := by
  by_cases hh : μ.colLen 0≤1
  · have hz : μ.rowLen 1=0 := by
      by_contra hn
      have hm : (1,0)∈μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
      have hc := YoungDiagram.mem_iff_lt_colLen.mp hm
      omega
    rw [hz]; omega
  · have hl : 1<μ.rowLens.length := by rw [YoungDiagram.length_rowLens]; omega
    have hmem : μ.rowLen 1 ∈ μ.rowLens.tail := by
      have hh := List.getElem_mem (show 0<μ.rowLens.tail.length from by simp; omega)
      simpa using hh
    exact List.single_le_sum (by simp) _ hmem

lemma rowLen_one_pos_of_tail (μ : YoungDiagram) (h : 0<μ.card-μ.rowLen 0) :
    0<μ.rowLen 1 := by
  have ht : 0<μ.rowLens.tail.sum := by rwa [rowLens_tail_sum]
  have hc : 1<μ.colLen 0 := by
    by_contra hn
    have ha : μ.colLen 0=0 ∨ μ.colLen 0=1 := by omega
    rcases ha with ha|ha <;> simp [YoungDiagram.rowLens,ha] at ht
  exact YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hc)

lemma longOriented_dimension (μ : YoungDiagram) :
    Module.finrank ℂ (SpechtSpace (longOriented μ))=Module.finrank ℂ (SpechtSpace μ) := by
  by_cases h : μ.colLen 0 ≤ μ.rowLen 0
  · exact congrArg (fun ν => Module.finrank ℂ (SpechtSpace ν)) (ite_eq_left h)
  · exact (congrArg (fun ν => Module.finrank ℂ (SpechtSpace ν)) (ite_eq_right h)).trans
      (specht_finrank_transpose μ).symm

lemma dimension_grows (μ : YoungDiagram) (hk : 0 < flatTail μ) :
    μ.card-2*flatTail μ ≤ Module.finrank ℂ (SpechtSpace μ) := by
  have ht : (longOriented μ).card-(longOriented μ).rowLen 0=flatTail μ := by
    rw [longOriented_card,longOriented_row]; rfl
  have hr := rowLen_one_pos_of_tail (longOriented μ) (by rwa [ht])
  have hh := long_row_dimension (longOriented μ) hr
  rw [longOriented_dimension] at hh
  have hle := rowLen_one_le_tail (longOriented μ)
  rw [rowLens_tail_sum,ht] at hle
  have hc := height_width_le_card μ
  have hc' : max (μ.colLen 0) (μ.rowLen 0)≤μ.card := by simpa using hc
  rw [longOriented_row] at hh
  unfold flatTail at *
  omega

lemma partition_dimension_pos {n : ℕ} (p : n.Partition) :
    0<Module.finrank ℂ (PartitionHilbert p) := by
  exact Signed.irreducible_finrank_pos (partitionHilbertRep p)

lemma partition_dimension_grows {n k : ℕ} (p : n.Partition)
    (hp : flatTail (diagram p)=k) (hk : 0<k) :
    n-2*k ≤ Module.finrank ℂ (PartitionHilbert p) := by
  rw [hilbertSpecht_finrank]
  have hh := dimension_grows (diagram p) (by rwa [hp])
  rwa [diagram_card,hp] at hh

lemma partition_log_lower {n k : ℕ} (p : n.Partition) (hp : flatTail (diagram p)=k) :
    (Real.log 2/2)*(k:ℝ)≤Real.log (Module.finrank ℂ (PartitionHilbert p)) := by
  rw [hilbertSpecht_finrank,←hp]
  simpa only [flatTail,Fintype.card_coe] using log_dimension_lower (diagram p)

lemma partition_dimension_gt_one {n : ℕ} (p : n.Partition)
    (hp : 0<flatTail (diagram p)) : 1<Module.finrank ℂ (PartitionHilbert p) := by
  have hd := partition_dimension_pos p
  have hl := partition_log_lower p rfl
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  by_contra hn
  have he : Module.finrank ℂ (PartitionHilbert p)=1 := by omega
  rw [he,Nat.cast_one,Real.log_one] at hl
  have hk : (0:ℝ)<flatTail (diagram p) := by exact_mod_cast hp
  nlinarith

open Irrep

lemma row_shape_cells (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0) (x : Cell μ) : row x=0 := by
  have ht := rowLen_one_le_tail μ
  rw [rowLens_tail_sum,hμ,Nat.sub_self] at ht
  have hm := YoungDiagram.mem_iff_lt_rowLen.mp x.property
  by_contra hn
  have ha := μ.rowLen_anti 1 (row x) (by omega)
  change col x<μ.rowLen (row x) at hm
  omega

lemma row_shape_tabloid (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0) (s t : Tabloid μ) : s=t := by
  obtain ⟨g,rfl⟩ := tabloidOfPerm_surjective μ s
  obtain ⟨h,rfl⟩ := tabloidOfPerm_surjective μ t
  apply Subtype.ext
  funext x
  exact (row_shape_cells μ hμ _).trans (row_shape_cells μ hμ _).symm

lemma hilbertSpecht_row (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0)
    (g : G μ) (v : SpechtHilbert μ) : hilbertSpecht μ g v=v := by
  apply Subtype.ext
  apply PiLp.ext
  intro t
  rw [hilbertSpecht_coeff,row_shape_tabloid μ hμ (g⁻¹ • t) t]

lemma row_average_zero {X : Type*} [Fintype X] [DecidableEq X]
    (μ : YoungDiagram) (hμ : μ.card=μ.rowLen 0) (e : Cell μ ≃ X) (p : Equiv.Perm X → ℂ)
    (hp : ∑g,p g=0) : groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) p=0 := by
  apply LinearMap.ext
  intro v
  simp only [groupAverage,LinearMap.sum_apply,LinearMap.smul_apply,MonoidHom.comp_apply]
  change (∑g,p g • hilbertSpecht μ _ v)=0
  simp only [hilbertSpecht_row μ hμ,←Finset.sum_smul,hp,zero_smul]

lemma transpose_slot_moment {X : Type*} [Fintype X] [DecidableEq X]
    (μ : YoungDiagram) (e : Cell μ ≃ X) (p : Equiv.Perm X → ℂ) (q : ℕ) :
    evenMoment q (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) p)=
    evenMoment q (groupAverage ((hilbertSpecht μ.transpose).comp
      ((transposeCells μ).symm.trans e).symm.permCongrHom.toMonoidHom)
      (fun g => p g*(realSign g:ℂ))) := by
  rw [groupAverage_comp_slots,groupAverage_comp_slots,hilbert_transpose_moment]
  congr 2
  funext g
  congr 1
  change signC μ.transpose g=(realSign (((transposeCells μ).symm.trans e).permCongr g):ℂ)
  rw [realSign_permCongr_complex]
  change ((Equiv.Perm.sign g:ℤ):ℂ)=(((Equiv.Perm.sign g:ℤ):ℝ):ℂ)
  norm_cast

theorem flat_shape_moment_zero {X : Type*} [Fintype X] [DecidableEq X]
    (μ : YoungDiagram) (e : Cell μ ≃ X) (p : Equiv.Perm X → ℂ)
    (hμ : flatTail μ=0) (hp : ∑g,p g=0) (hs : ∑g,p g*(realSign g:ℂ)=0) :
    evenMoment 1 (groupAverage ((hilbertSpecht μ).comp e.symm.permCongrHom.toMonoidHom) p)=0 := by
  have hc : max (μ.colLen 0) (μ.rowLen 0)≤μ.card := by simpa using height_width_le_card μ
  have hh : μ.card=μ.rowLen 0 ∨ μ.card=μ.colLen 0 := by
    unfold flatTail at hμ
    omega
  rcases hh with hh|hh
  · rw [row_average_zero μ hh e p hp]
    simp [evenMoment]
  · rw [transpose_slot_moment]
    have ht : μ.transpose.card=μ.transpose.rowLen 0 := by
      rw [transpose_card,YoungDiagram.rowLen_transpose,hh]
    rw [row_average_zero μ.transpose ht _ _ hs]
    simp [evenMoment]

end BinaryCoordinateSweeps.Young

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Irrep Young

lemma sign_convolution {X : Type*} [Fintype X] [DecidableEq X]
    (p q : Equiv.Perm X → ℝ) :
    (∑g,convolution p q g*realSign g)=(∑g,p g*realSign g)*(∑g,q g*realSign g) := by
  simp only [convolution,Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    _ = ∑x,∑y,p x*q y*realSign (x*y) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [Equiv.coe_mulLeft,inv_mul_cancel_left] using
        (Equiv.sum_comp (Equiv.mulLeft x) (fun g => p x*q (x⁻¹*g)*realSign g)).symm
    _ = _ := by
      simp only [map_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring

lemma sweep_sign_zero {d w : ℕ} (hd : 0<d) (hw : 0<w) :
    (∑g,sweepLaw d w g*realSign g)=0 := by
  obtain ⟨w,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : w≠0)
  rw [sweepLaw,convolutionPower,sign_convolution,binary_sign_annihilated d hd,zero_mul]

lemma sweep_centered_mass (d w : ℕ) :
    (∑g : Equiv.Perm (Slot d),((sweepLaw d w g:ℝ)-uniformLaw _ g:ℂ))=0 := by
  simp only [←Complex.ofReal_sub]
  rw [←Complex.ofReal_sum,Finset.sum_sub_distrib]
  have hp : IsProbability (sweepLaw d w) := convolutionPower_probability
    ⟨finiteLaw_nonneg _,finiteLaw_sum _⟩ w
  rw [hp.2,uniformLaw_sum,sub_self,Complex.ofReal_zero]

lemma sweep_centered_sign {d w : ℕ} (hd : 0<d) (hw : 0<w) :
    (∑g : Equiv.Perm (Slot d),((sweepLaw d w g:ℝ)-uniformLaw _ g:ℂ)*(realSign g:ℂ))=0 := by
  have : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum,sub_mul,Finset.sum_sub_distrib,
    sweep_sign_zero hd hw,uniform_sign_zero,sub_self,Complex.ofReal_zero]

lemma variation_fourier_equiv {X : Type} [Fintype X] [DecidableEq X]
    {n : ℕ} (e : X ≃ Fin n) (p q : Equiv.Perm X → ℝ) :
    totalVariation p q ^2 ≤ (1/4:ℝ)*
      ∑ℓ : n.Partition,(Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*
        evenMoment 1 (groupAverage ((partitionHilbertRep ℓ).comp e.permCongrHom.toMonoidHom)
          (fun g => (p g-q g:ℂ))) := by
  have ht := Fourier.variation_fourier_bound (p ∘ e.symm.permCongr) (q ∘ e.symm.permCongr)
  have he : totalVariation (p ∘ e.symm.permCongr) (q ∘ e.symm.permCongr)=totalVariation p q := by
    unfold totalVariation
    congr 1
    exact Equiv.sum_comp e.symm.permCongr (fun g => |p g-q g|)
  rw [he] at ht
  convert ht using 2
  apply Finset.sum_congr rfl
  intro ℓ _
  have hh := groupAverage_comp_slots e.symm (partitionHilbertRep ℓ)
    (fun g => (p g-q g:ℂ))
  simpa only [Equiv.symm_symm,Function.comp_apply] using
    congrArg (fun A => (Module.finrank ℂ (PartitionHilbert ℓ):ℝ)*evenMoment 1 A) hh

end BinaryCoordinateSweeps

end

end OAI
