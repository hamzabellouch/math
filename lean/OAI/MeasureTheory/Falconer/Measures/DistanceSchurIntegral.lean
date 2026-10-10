import OAI.MeasureTheory.Falconer.Measures.ProductSchurIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem original_distance_schur_integral {ι : Type*} (S : Finset ι)
    (U V : ι → ℝ × UnitCircle → ℂ)
    (hU : ∀ i ∈ S, Measurable (U i)) (hV : ∀ i ∈ S, Measurable (V i))
    (C D : ι → ℝ) (hC : ∀ i ∈ S, 0 ≤ C i) (hD : ∀ i ∈ S, 0 ≤ D i)
    (hbU : ∀ i ∈ S, ∀ x, ‖U i x‖ ≤ C i) (hbV : ∀ i ∈ S, ∀ x, ‖V i x‖ ≤ D i)
    (F : ℝ × (UnitCircle × UnitCircle) → ℂ) {d : ℝ} (hd : 0 ≤ d)
    (hb : ∀ r u w, ‖F (r,(u,w))‖ ≤ d/2 * (∑ i ∈ S, (‖U i (r,u)‖^2*‖V i (r,w)‖^2 + ‖V i (r,u)‖^2*‖U i (r,w)‖^2)))
    (p v : ℝ) {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W) :
    ‖((2:ℝ)^(2*(v-p))) • (((2:ℝ)^v)⁻¹ •
      ∫ r : ℝ, ∫ u, ∫ w, Ψ (r/(2:ℝ)^v) • F (r,(u,w)) ∂sourceArcLength ∂sourceArcLength)‖ ≤
      d * ∑ i ∈ S, (sourceAngularH p v Ψ (U i) (V i)).toReal := by
  classical
  let E := S ×ˢ (Finset.univ : Finset Bool)
  let U' := fun e : ι × Bool => if e.2 then U e.1 else V e.1
  let V' := fun e : ι × Bool => if e.2 then V e.1 else U e.1
  let C' := fun e : ι × Bool => if e.2 then C e.1 else D e.1
  let D' := fun e : ι × Bool => if e.2 then D e.1 else C e.1
  have hU' : ∀ e ∈ E, Measurable (U' e) := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hU i hi | exact hV i hi
  have hV' : ∀ e ∈ E, Measurable (V' e) := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hU i hi | exact hV i hi
  have hC' : ∀ e ∈ E, 0 ≤ C' e := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hC i hi | exact hD i hi
  have hD' : ∀ e ∈ E, 0 ≤ D' e := by
    intro ⟨i,b⟩ he
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hC i hi | exact hD i hi
  have hbU' : ∀ e ∈ E, ∀ x, ‖U' e x‖ ≤ C' e := by
    intro ⟨i,b⟩ he x
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hbU i hi x | exact hbV i hi x
  have hbV' : ∀ e ∈ E, ∀ x, ‖V' e x‖ ≤ D' e := by
    intro ⟨i,b⟩ he x
    have hi := (Finset.mem_product.mp he).1
    cases b <;> first | exact hbU i hi x | exact hbV i hi x
  have hb' : ∀ r u w, ‖F (r,(u,w))‖ ≤
      d/2 * ∑ e ∈ E, ‖U' e (r,u)‖^2*‖V' e (r,w)‖^2 := by
    intro r u w
    simpa [E,U',V',Finset.sum_product,Fintype.sum_bool,add_comm] using hb r u w
  have hh := original_product_schur_integral E U' V' hU' hV' C' D' hC' hD' hbU' hbV'
    F (div_nonneg hd (by norm_num)) hb' p v hΨ hpos hs hW hw
  have hsym (i : ι) : sourceAngularH p v Ψ (V i) (U i) = sourceAngularH p v Ψ (U i) (V i) := by
    unfold sourceAngularH
    simp_rw [mul_comm (sourceAngularMoment (V i) _) (sourceAngularMoment (U i) _)]
  simp [E,U',V',Finset.sum_product,hsym,← two_mul,← Finset.mul_sum] at hh
  have hcanc (x : ℝ) : d/2*(2*x) = d*x := by ring
  rw [hcanc] at hh
  simpa using hh

end PlanarFalconer

end OAI
