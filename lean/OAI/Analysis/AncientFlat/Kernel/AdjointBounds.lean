import OAI.Analysis.AncientFlat.Kernel.AdjointPairDerivative
import OAI.Analysis.AncientFlat.Regularity.ProductJets
import OAI.Analysis.AncientFlat.Kernel.KernelJetMajorant

namespace OAI
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff SchwartzMap Laplacian
namespace FlatDuality
open BiharmonicKernel InnerProductSpace ParametrixUniqueness FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma norm_adjointSchwartz_jet (c ε s : ℝ) (z : V) (h : 0<adjointTime c ε s) (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (adjointSchwartz c ε s z h : V → ℂ) x‖=
      ‖adjointAmplitude s‖*‖iteratedFDeriv ℝ n (kernel (adjointTime c ε s)) (x-z)‖ := by
  have he : (adjointSchwartz c ε s z h : V → ℂ)=
      fun y => adjointAmplitude s • kernel (adjointTime c ε s) (y-z) := by
    funext y
    rw [adjointSchwartz_apply]
    rfl
  rw [he]
  have hk : ContDiff ℝ (n : WithTop ℕ∞) (fun y : V => kernel (adjointTime c ε s) (y-z)) := by
    rw [←heatKernel_eq_kernel _ h]
    exact ((heatKernel _ h).smooth _).comp (contDiff_id.sub contDiff_const)
  rw [iteratedFDeriv_const_smul_apply' hk.contDiffAt,norm_smul,iteratedFDeriv_comp_sub]
lemma norm_adjointError_le {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) (φ : SchwartzMap V ℂ) (x : V) (C B : ℝ)
    (hC : 0≤C) (hB : 0≤B)
    (hj : ∀ n : ℕ, n≤4 → ‖iteratedFDeriv ℝ n (movingDeviation c Af t) x‖≤C*decayWeight x)
    (hBj : ‖Bf (Real.exp (t/4) • x)‖≤C*decayWeight x)
    (hφ : ∀ n : ℕ, n≤4 → ‖iteratedFDeriv ℝ n φ x‖≤B) :
    ‖adjointError c Af Bf t φ x‖≤(((Module.finrank ℝ V : ℝ)^2*16+1)*C)*decayWeight x*B := by
  have he : (deviationTest c Af t φ : V → ℂ)=fun y => movingDeviation c Af t y • φ y := by
    funext y
    rw [deviationTest_apply h ht,Complex.real_smul]
  have hd := norm_bilaplacian_smul_le (movingDeviation c Af t) (φ : V → ℂ)
    ((movingDeviation_smooth h.2.2.1 t).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (4:ℕ∞)≤⊤))) (φ.smooth 4) x
    (C*decayWeight x) B (mul_nonneg hC (decayWeight_pos x).le) hB hj hφ
  have hp : ‖potentialTest Bf t φ x‖≤C*decayWeight x*B := by
    rw [potentialTest_apply h ht,norm_mul,Complex.norm_real]
    exact mul_le_mul hBj (by simpa only [norm_iteratedFDeriv_zero] using hφ 0 (by norm_num))
      (norm_nonneg _) (mul_nonneg hC (decayWeight_pos x).le)
  calc
    _ ≤ ‖(Δ (Δ (deviationTest c Af t φ) : SchwartzMap V ℂ) : SchwartzMap V ℂ) x‖+
        ‖potentialTest Bf t φ x‖ := norm_add_le _ _
    _ ≤ (Module.finrank ℝ V : ℝ)^2*16*(C*decayWeight x)*B+C*decayWeight x*B := by
      apply add_le_add _ hp
      rw [schwartz_bilap_fun,he]
      exact hd
    _=_ := by ring
lemma adjointError_uniform_majorant {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    (ε : ℝ) (hε : 0<ε) :
    ∃ (L : ℝ) (B : V → ℝ), 0≤L ∧ Integrable (fun x => (1+‖x‖)*B x) ∧ (∀ x,0≤B x) ∧
      ∀ t (ht : t∈Icc (0:ℝ) 1) (z x : V),
        ‖adjointError c Af Bf t (adjointSchwartz c ε t z (hε.trans_le (adjointTime_bounds c ε ht).1)) x‖≤
          L*decayWeight z*((1+‖x-z‖)*B (x-z)) := by
  obtain ⟨C,hC,hCb⟩ := h.moving_four_weighted_jets
  obtain ⟨B,_,hBw,hBn,hBb⟩ := kernel_four_jet_majorant (V := V) ε (ε+c^2/16) hε
  let L := ((Module.finrank ℝ V : ℝ)^2*16+1)*C
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨L,B,hL,hBw,hBn,fun t ht z x => ?_⟩
  have hp : 0<adjointTime c ε t := hε.trans_le (adjointTime_bounds c ε ht).1
  have hj : ∀ n : ℕ, n≤4 →
      ‖iteratedFDeriv ℝ n (adjointSchwartz c ε t z hp : V → ℂ) x‖≤B (x-z) := by
    intro n hn
    rw [norm_adjointSchwartz_jet,Real.norm_of_nonneg (adjointAmplitude_bounds ht).1.le]
    exact (mul_le_mul (adjointAmplitude_bounds ht).2
      (hBb _ (adjointTime_bounds c ε ht) n hn _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have h0 := (hCb t ht 0 (by norm_num) x).2
  simp only [norm_iteratedFDeriv_zero] at h0
  have he := norm_adjointError_le h ht (adjointSchwartz c ε t z hp) x C (B (x-z)) hC (hBn _)
    (fun n hn => (hCb t ht n hn x).1) h0 hj
  calc
    _ ≤ L*decayWeight x*B (x-z) := he
    _ ≤ L*((1+‖x-z‖)*decayWeight z)*B (x-z) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (decayWeight_translate x z) hL) (hBn _)
    _=_ := by ring
end FlatDuality

end

end OAI
