import OAI.Geometry.Relativity.CKS.HeatRadial

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter Finset CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending
open scoped Topology ContDiff

lemma generated_uniform {p : ℕ → Poly} (hp : PolynomialRapid p) {F : ℝ → E → ℝ}
    (hF : HeatGenerated p F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 → |F t x| ≤ C := by
  obtain ⟨C,hC,h⟩ := hF.decay hp
  refine ⟨C,hC,fun t ht x hx => ?_⟩
  calc
    |F t x| ≤ C * Real.exp (-6*t) := h t ht x hx
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) hC
    _ = C := mul_one C

theorem canonical_uniform_data (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : E, ‖x‖ = 1 →
      |canonicalF f₀ m t x| ≤ |m|+K ∧
      |roundLaplacian (canonicalF f₀ m t) x| ≤ K ∧
      (∀ i : Ix, |pd i (canonicalF f₀ m t) x| ≤ K) ∧
      (∀ i j : Ix, |canonicalT f₀ t x i j| ≤ K) := by
  classical
  let p := heatPolynomials f₀
  have hp : PolynomialRapid p := smoothDatum_rapid f₀ hf₀
  have hi := inversePolynomials_rapid p hp
  have hb : HeatGenerated p (spatialHeat p (0,[])) := HeatGenerated.basic _
  obtain ⟨C₀,hC₀,b₀⟩ := generated_uniform hp hb
  obtain ⟨C₁,hC₁,b₁⟩ := generated_uniform hp (hb.time hp)
  choose C hC bC using (fun i : Ix => generated_uniform hp (hb.partial hp i))
  choose H hH bH using (fun i : Ix × Ix => generated_uniform hi (heatTensor_generated p hp i.1 i.2))
  let K := C₀+C₁+(∑ i : Ix, C i)+(∑ i : Ix × Ix, H i)
  have hsumC : 0 ≤ ∑ i : Ix, C i := sum_nonneg (fun i _ => hC i)
  have hsumH : 0 ≤ ∑ i : Ix × Ix, H i := sum_nonneg (fun i _ => hH i)
  have hc0 : C₀ ≤ K := by dsimp [K]; linarith
  have hc1 : C₁ ≤ K := by dsimp [K]; linarith
  have hc (i : Ix) : C i ≤ K := by
    have hh := single_le_sum (fun j (_ : j ∈ (univ : Finset Ix)) => hC j) (mem_univ i)
    dsimp [K]
    linarith
  have hh (i : Ix × Ix) : H i ≤ K := by
    have hh := single_le_sum (fun j (_ : j ∈ (univ : Finset (Ix × Ix))) => hH j) (mem_univ i)
    dsimp [K]
    linarith
  refine ⟨K,hC₀.trans hc0,?_⟩
  intro t ht x hx
  refine ⟨?_,?_,?_,?_⟩
  · exact (abs_add_le m _).trans (by have hb0 := (b₀ t ht x hx).trans hc0; linarith)
  · rw [← canonicalF_heat f₀ hf₀ m ht hx]
    change |deriv (fun s => m + spatialHeat p (0,[]) s x) t| ≤ K
    rw [deriv_const_add]
    exact (b₁ t ht x hx).trans hc1
  · intro i
    change |pd i (fun y => m + spatialHeat p (0,[]) t y) x| ≤ K
    rw [pd_const_add]
    exact (bC i t ht x hx).trans (hc i)
  · intro i j
    exact (bH (i,j) t ht x hx).trans (hh (i,j))

lemma thetaFrame_component (x : Point) (i : Ix) : |thetaFrame x i| ≤ 1 := by
  fin_cases i
  · exact (abs_mul _ _).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans
        (Real.abs_cos_le_one _))
  · exact (abs_mul _ _).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)).trans
        (Real.abs_sin_le_one _))
  · simpa [thetaFrame] using Real.abs_sin_le_one (x 1)
lemma phiUnit_component (x : Point) (i : Ix) : |phiUnit x i| ≤ 1 := by
  fin_cases i
  · simpa [phiUnit] using Real.abs_sin_le_one (x 2)
  · simpa [phiUnit] using Real.abs_cos_le_one (x 2)
  · simp [phiUnit]

lemma fderiv_bound {F : E → ℝ} {y v : E} {K : ℝ}
    (hK : 0 ≤ K) (hF : ∀ i : Ix, |pd i F y| ≤ K) (hv : ∀ i : Ix, |v i| ≤ 1) :
    |fderiv ℝ F y v| ≤ 3*K := by
  rw [CKSInducedSphere.fderiv_expand]
  calc
    _ ≤ ∑ i : Ix, |v i * grad F y i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Ix, K := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul]
      simpa only [grad, mul_comm] using
        (mul_le_mul (hF i) (hv i) (abs_nonneg _) hK).trans_eq (mul_one K)
    _ = 3*K := by simp

lemma pair_bound {T : CKSInducedSphere.Mat} {v w : E} {K : ℝ}
    (hK : 0 ≤ K) (hT : ∀ i j : Ix, |T i j| ≤ K)
    (hv : ∀ i : Ix, |v i| ≤ 1) (hw : ∀ i : Ix, |w i| ≤ 1) :
    |pair T v w| ≤ 9*K := by
  unfold pair
  calc
    _ ≤ ∑ i : Ix, |∑ j : Ix, v i * w j * T i j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Ix, ∑ j : Ix, |v i * w j * T i j| := sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Ix, ∑ _j : Ix, K := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      rw [abs_mul,abs_mul]
      have hh : |v i| * |w j| ≤ 1 :=
        (mul_le_of_le_one_left (abs_nonneg _) (hv i)).trans (hw j)
      simpa only [mul_comm] using
        (mul_le_mul (hT i j) hh (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hK).trans_eq
          (mul_one K)
    _ = 9*K := by simp; ring

end
end CKSSphericalChart

end

end OAI
