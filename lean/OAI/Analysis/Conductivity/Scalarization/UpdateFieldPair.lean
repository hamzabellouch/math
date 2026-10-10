import Mathlib
import OAI.Analysis.Conductivity.Sobolev.CompactUpdateLp

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology

def CompactGlobalUpdate.fieldPair
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) :
    Lp FieldVector 2 (μ.restrict U) × Lp FieldVector 2 (μ.restrict U) :=
  (hE.toLp _ + (R.memLp_gradient_correction μ).toLp _,
    hF.toLp _ + (R.memLp_flux_correction μ).toLp _)

lemma CompactGlobalUpdate.fieldPair_eq
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U)) :
    R.fieldPair μ hE hF = (hE'.toLp _,hF'.toLp _) := by
  exact Prod.ext (R.gradient_toLp_eq μ hUm hreg hE hE').symm
    (R.flux_toLp_eq μ hF hF').symm

lemma CompactGlobalUpdate.fieldPair_ae
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) :
    ∀ᵐ x ∂μ.restrict U,
      (R.fieldPair μ hE hF).1 x = voltageGradient (fun y => u y+R.du y) x ∧
      (R.fieldPair μ hE hF).2 x = voltageFlux (fun y => u y+R.du y) R.tensor x := by
  obtain ⟨hE',hF'⟩ := R.fields_memLp μ hUm hreg hE hF
  rw [R.fieldPair_eq μ hUm hreg hE hF hE' hF']
  exact hE'.coeFn_toLp.and hF'.coeFn_toLp

lemma CompactGlobalUpdate.fieldPair_energy_bound
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A) (hreg : μ (U \ regularRegion u A U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → R.tensor x ∈ matrixFiniteLaminate a b) :
    ‖(R.fieldPair μ hE hF).1‖ ≤ (b/a)*‖hE.toLp _‖ ∧
      ‖(R.fieldPair μ hE hF).2‖ ≤ (b^2/a)*‖hE.toLp _‖ := by
  obtain ⟨hE',hF'⟩ := R.fields_memLp μ hUm hreg hE hF
  rw [R.fieldPair_eq μ hUm hreg hE hF hE' hF']
  exact R.Lp_energy_bound μ hUm hreg hE hE' hF' hint hdiv ha hab hgraph

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Matrix Set MeasureTheory
open scoped Matrix.Norms.Elementwise

lemma diagonal_conjugate_smul_sub {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    (d : DiagonalTriple) (s : ℝ) :
    Q * diagonal d * Qᵀ - s • (1 : Mat3) = Q * diagonal (d - fun _ => s) * Qᵀ := by
  change Q * diagonal d * Qᵀ - s • (1 : Mat3) = Q * diagonal (fun i => d i - s) * Qᵀ
  rw [← diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
  have he : diagonal (fun _ : Fin 3 => s) = s • (1 : Mat3) := by
    ext i j
    change (if i = j then s else 0) = s * (if i = j then 1 else 0)
    split_ifs <;> simp
  rw [he, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ.2]

lemma diagonal_conjugate_dot_bound {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    {d : DiagonalTriple} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, |d i| ≤ c) (v : Coord3) :
    ((Q * diagonal d * Qᵀ) *ᵥ v) ⬝ᵥ ((Q * diagonal d * Qᵀ) *ᵥ v) ≤
      c^2 * (v ⬝ᵥ v) := by
  rw [← mulVec_mulVec,← mulVec_mulVec,orthogonal_dotProduct hQ]
  have hv := orthogonal_dotProduct (Q := Qᵀ) ⟨by simpa using hQ.2,by simpa using hQ.1⟩ v v
  rw [← hv]
  simp only [dotProduct,mulVec_diagonal,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hs : (d i)^2 ≤ c^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hc).mpr (hd i)
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ((Qᵀ *ᵥ v) i))]

lemma diagonal_conjugate_field_bound {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    {d : DiagonalTriple} {c : ℝ} (hc : 0 ≤ c) (hd : ∀ i, |d i| ≤ c)
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖fieldVector ((Q * diagonal d * Qᵀ)*E)‖ ≤ c * ‖fieldVector E‖ := by
  have hs : ‖fieldVector ((Q * diagonal d * Qᵀ)*E)‖^2 ≤ c^2 * ‖fieldVector E‖^2 := by
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,fieldVector_inner,fieldVector_inner]
    change (∑ j, ((Q * diagonal d * Qᵀ) *ᵥ E.col j) ⬝ᵥ ((Q * diagonal d * Qᵀ) *ᵥ E.col j)) ≤
      c^2 * (∑ j, E.col j ⬝ᵥ E.col j)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => diagonal_conjugate_dot_bound hQ hc hd (E.col j)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _))).mp
  simpa only [mul_pow] using hs

lemma matrixFiniteLaminate_diagonal_bounds {a b : ℝ} (ha : 0 < a)
    {A : Symmetric3} (hA : A ∈ matrixFiniteLaminate a b) (i : Fin 3) :
    A.val i i ∈ Icc a b := by
  have h := matrixFiniteLaminate_quadratic_bounds ha hA (Pi.single i 1)
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h

lemma scalarNeighbourhood_defect_bound {a b η : ℝ} (hη : 0 ≤ η)
    {A : Symmetric3} (hA : A ∈ spectralExtension (scalarNeighbourhood a b η))
    (E : Matrix (Fin 3) (Fin 2) ℝ) :
    ‖fieldVector (A.val*E) - (A.val 0 0) • fieldVector E‖ ≤ (2*η) * ‖fieldVector E‖ := by
  obtain ⟨Q,hQ,d,⟨hd,s,hs⟩,he⟩ := hA
  have hds : ∀ i, |d i - s| ≤ η := by
    intro i
    exact (norm_le_pi_norm (d - fun _ => s) i).trans hs.le
  have hshift : A.val - s • (1 : Mat3) = Q * diagonal (d - fun _ => s) * Qᵀ := by
    rw [he]
    exact diagonal_conjugate_smul_sub hQ d s
  have hnorm : ∀ F : Matrix (Fin 3) (Fin 2) ℝ,
      ‖fieldVector (A.val*F) - s • fieldVector F‖ ≤ η * ‖fieldVector F‖ := by
    intro F
    have hb := diagonal_conjugate_field_bound (d := d - fun _ => s) hQ hη hds F
    rw [← hshift, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at hb
    exact hb
  have hssq : |A.val 0 0 - s| ≤ η := by
    have hb := diagonal_conjugate_dot_bound (d := d - fun _ => s) hQ hη hds (Pi.single 0 1)
    rw [← hshift] at hb
    have hl : (A.val 0 0 - s)^2 ≤
        ((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) ⬝ᵥ
        ((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) := by
      have he0 : ((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) 0 = A.val 0 0 - s := by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [← he0]
      simpa only [dotProduct,pow_two] using
        Finset.single_le_sum (fun i _ => mul_self_nonneg (((A.val - s • (1 : Mat3)) *ᵥ Pi.single 0 1) i))
          (Finset.mem_univ (0 : Fin 3))
    have hr : (A.val 0 0 - s)^2 ≤ η^2 := hl.trans (by simpa [dotProduct, Pi.single_apply] using hb)
    exact (sq_le_sq₀ (abs_nonneg _) hη).mp (by simpa only [sq_abs] using hr)
  have hsplit : fieldVector (A.val*E) - A.val 0 0 • fieldVector E =
      (fieldVector (A.val*E) - s • fieldVector E) + (s-A.val 0 0) • fieldVector E := by
    rw [sub_smul]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖fieldVector (A.val*E) - s • fieldVector E‖ + ‖(s-A.val 0 0) • fieldVector E‖ := norm_add_le _ _
    _ ≤ η * ‖fieldVector E‖ + η * ‖fieldVector E‖ := add_le_add (hnorm E) (by
      rw [norm_smul,Real.norm_eq_abs,abs_sub_comm]
      exact mul_le_mul_of_nonneg_right hssq (norm_nonneg _))
    _ = _ := by ring

end ScalarConductivity

end
end

end OAI
