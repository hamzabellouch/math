import OAI.Geometry.Relativity.CKS.CollarFieldJets

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma field_rawDQ (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) (a : I) :
    matrixScalarJets (fun y i k => D (basis a) (fun z => fieldQ b f z i k) y) x=
      rawDQ (fieldRaw b f x).1 a := by
  funext i k
  have h0 := component_three (hf.1.1) i k
  have h1 := component_three (hf.1.2.1) i k
  have he : (D (basis a) (fun z => fieldQ b f z i k)) =ᶠ[𝓝 x]
      (fun y => D (basis a) (fun z => f.metric 0 z i k) y+
        (b 0^3*(1-b 1))*D (basis a) (fun z => f.metric 1 z i k) y) := by
    filter_upwards [h0.eventually (by norm_num),h1.eventually (by norm_num)] with y hy0 hy1
    change D (basis a) (fun z => f.metric 0 z i k+(b 0^3*(1-b 1))*f.metric 1 z i k) y = _
    rw [D_add _ (hy0.differentiableAt (by norm_num))
      ((hy1.differentiableAt (by norm_num)).const_mul _),D_const_mul _ _ (hy1.differentiableAt (by norm_num))]
  have hd0 : ContDiffAt ℝ 2 (D (basis a) (fun z => f.metric 0 z i k)) x :=
    contDiffAt_D h0 (by norm_num) _
  have hd1 : ContDiffAt ℝ 2 (D (basis a) (fun z => f.metric 1 z i k)) x :=
    contDiffAt_D h1 (by norm_num) _
  change actualScalarJet _ x=_
  erw [actualScalarJet_congr he,actualScalarJet_add hd0 (contDiffAt_const.mul hd1),
    actualScalarJet_smul _ hd1]
  rfl

lemma field_rawDS (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) (a k : I) :
    actualScalarJet (D (basis a) (fun y => fieldS b f y k)) x=rawDS (fieldRaw b f x).1 a k := by
  have h := contDiffAt_pi.mp hf.2.1 k
  have he : (D (basis a) (fun y => fieldS b f y k)) =ᶠ[𝓝 x]
      (fun y => (1-b 1)*D (basis a) (fun y => f.shift y k) y) := by
    filter_upwards [h.eventually (by norm_num)] with y hy
    exact D_const_mul _ _ (hy.differentiableAt (by norm_num))
  erw [actualScalarJet_congr he,actualScalarJet_smul _ (contDiffAt_D h (by norm_num) _)]
  rfl

lemma field_rawExpansionInput (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    actualExpansionInput (fieldQ b f) (fieldQr b f) (fieldS b f) x=
      rawExpansionInput (fieldRaw b f x).1 := by
  apply Prod.ext (field_rawQ b hf)
  apply Prod.ext (funext (field_rawDQ b hf))
  apply Prod.ext (field_rawQr b hf)
  exact Prod.ext (funext (field_rawS b hf)) (funext fun a => funext (field_rawDS b hf a))

lemma fieldC_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    ContDiffAt ℝ 2 (fieldC b f) x := by
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro k
  exact ((component_diff (fieldQr_diff b hf) i k).of_le (by norm_num)).sub
    ((normalizedLie_diff (fieldQ_diff b hf) (fieldS_diff b hf) i k).const_smul (b 0))

lemma field_rawC (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x) :
    matrixScalarJets (fieldC b f) x=rawC (fieldRaw b f x).1 := by
  funext i k
  have hq := component_diff (fieldQr_diff b hf) i k
  have hl := normalizedLie_diff (fieldQ_diff b hf) (fieldS_diff b hf) i k
  change actualScalarJet (fun y => fieldQr b f y i k-b 0*normalizedLie (fieldQ b f) (fieldS b f) y i k) x = _
  erw [actualScalarJet_sub (hq.of_le (by norm_num)) (contDiffAt_const.mul hl),actualScalarJet_smul _ hl,
    actual_normalizedLieJet (Q:=fieldQr b f) (fieldQ_diff b hf) (fieldS_diff b hf),field_rawExpansionInput b hf]
  change matrixScalarJets (fieldQr b f) x i k-_=_
  rw [field_rawQr b hf]
  rfl

lemma matrixTraceField_diff {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    ContDiffAt ℝ 2 (fun y => ∑ i, ∑ k, inverse (q y) i k*t y k i) x := by
  apply ContDiffAt.sum; intro i _
  apply ContDiffAt.sum; intro k _
  have hi : ContDiffAt ℝ 2 (fun y => inverse (q y) i k) x := by
    unfold inverse
    apply ContDiffAt.div
    · fin_cases i <;> fin_cases k <;> dsimp <;>
        first | exact component_diff hq _ _ | exact (component_diff hq _ _).neg
    · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
    · exact h0
  exact hi.mul (component_diff ht k i)

lemma actual_matrixTraceJet {q t : Point → Mat} {x : Point}
    (hq : ContDiffAt ℝ 2 q x) (ht : ContDiffAt ℝ 2 t x) (h0 : determinant (q x) ≠ 0) :
    actualScalarJet (fun y => ∑ i, ∑ k, inverse (q y) i k*t y k i) x=
      matrixTraceJet (matrixScalarJets q x) (matrixScalarJets t x) := by
  have hi (i k : I) : ContDiffAt ℝ 2 (fun y => inverse (q y) i k) x := by
    unfold inverse
    apply ContDiffAt.div
    · fin_cases i <;> fin_cases k <;> dsimp <;>
        first | exact component_diff hq _ _ | exact (component_diff hq _ _).neg
    · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).contDiffAt.comp x hq
    · exact h0
  erw [actualScalarJet_sum _ (fun i _ => ContDiffAt.sum fun k _ => (hi i k).mul (component_diff ht k i))]
  apply Finset.sum_congr rfl; intro i _
  erw [actualScalarJet_sum _ (fun k _ => (hi i k).mul (component_diff ht k i))]
  apply Finset.sum_congr rfl; intro k _
  erw [actualScalarJet_mul (hi i k) (component_diff ht k i),actual_inverseMatrixJet hq h0]
  rfl

lemma fieldD_diff (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0) : ContDiffAt ℝ 2 (fieldD b f) x :=
  (matrixTraceField_diff ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0).const_smul (1/4:ℝ)

lemma field_rawD (b : Fin 5 → ℝ) {f : CollarCoefficientFields} {x : Point} (hf : f.RegularAt x)
    (h0 : determinant (fieldQ b f x) ≠ 0) :
    actualScalarJet (fieldD b f) x=rawD (fieldRaw b f x).1 := by
  unfold fieldD
  erw [actualScalarJet_smul _ (matrixTraceField_diff ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0),
    actual_matrixTraceJet ((fieldQ_diff b hf).of_le (by norm_num)) (fieldC_diff b hf) h0,
    field_rawQ b hf,field_rawC b hf]
  rfl

end
end CKSAngularGeometry

end

end OAI
