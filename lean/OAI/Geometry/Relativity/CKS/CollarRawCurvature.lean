import OAI.Geometry.Relativity.CKS.CollarRawCompact

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma scalarMatrixToJet_sub (q q' : MatrixScalarJet) :
    scalarMatrixToJet q-scalarMatrixToJet q' = scalarMatrixToJet (q-q') := rfl
lemma scalarMatrixToJet_norm (q : MatrixScalarJet) : ‖scalarMatrixToJet q‖ ≤ ‖q‖ := by
  have hq (i k : I) : ‖q i k‖ ≤ ‖q‖ := Matrix.norm_entry_le_entrywise_sup_norm q
  apply norm_prod_le_iff.mpr
  constructor
  · exact (Matrix.norm_le_iff (norm_nonneg q)).mpr fun i k => (norm_fst_le (q i k)).trans (hq i k)
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro a
    apply (Matrix.norm_le_iff (norm_nonneg q)).mpr
    intro i k
    exact (norm_le_pi_norm (q i k).2.1 a).trans ((norm_fst_le (q i k).2).trans
      ((norm_snd_le (q i k)).trans (hq i k)))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro b
    apply (Matrix.norm_le_iff (norm_nonneg q)).mpr
    intro i k
    exact (Matrix.norm_entry_le_entrywise_sup_norm (q i k).2.2).trans
      ((norm_snd_le (q i k).2).trans ((norm_snd_le (q i k)).trans (hq i k)))

lemma scalarCurvatureJet_smooth {q : Jet} (hq : determinant q.1 ≠ 0) :
    ContDiffAt ℝ ∞ scalarCurvature q := by
  have h0 := operators_smooth (j:=(q,(1,0,0))) ⟨hq,by norm_num⟩
  have h1 := h0.comp q (by fun_prop : ContDiffAt ℝ ∞ (fun q : Jet => (q,((1,0,0):ScalarJet))) q)
  exact contDiffAt_fst.comp q h1

lemma rawQ_difference (p : RawCollarInput) :
    rawQ p-rawQ (rawOriginal p) = (-re p*rz p^3) • rmat p 1 := by
  simp only [rawQ,rawOriginal,rz,re,rmat,ite_true,
    ite_eq_right (show (1:Fin 5) ≠ 0 by decide),sub_zero,mul_one]
  module

theorem raw_curvature_uniform {K : Set RawCollarInput} (hK : IsCompact K)
    (hreg : K ⊆ rawDomain) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : RawCollarInput, p ∈ Metric.cthickening δ K →
      rawOriginal p ∈ Metric.cthickening δ K →
      ∀ r A : ℝ, 1 ≤ r → rz p = 1/r → 0 ≤ rwgt p → 0 ≤ A →
      |re p| ≤ A*rwgt p →
      |scalarCurvature (scalarMatrixToJet (rawQ p))-
        scalarCurvature (scalarMatrixToJet (rawQ (rawOriginal p)))| ≤ C*A*rwgt p/r^3 := by
  let : FiniteDimensional ℝ RawMetricData := inferInstance
  let : FiniteDimensional ℝ RawTensorData := inferInstance
  let : FiniteDimensional ℝ RawCollarData := inferInstance
  let : FiniteDimensional ℝ RawCollarInput := inferInstance
  let : ProperSpace RawCollarInput := FiniteDimensional.proper ℝ RawCollarInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open rawDomain_open hreg
  have hk := hK.cthickening (r:=δ)
  have hqcont : Continuous (fun p => scalarMatrixToJet (rawQ p)) := by
    unfold scalarMatrixToJet
    fun_prop
  have hqc := hk.image hqcont
  obtain ⟨L,hLip⟩ : ∃ L, LipschitzOnWith L scalarCurvature
      ((fun p => scalarMatrixToJet (rawQ p)) '' Metric.cthickening δ K) := by
    apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hqc
    rintro _ ⟨p,hp,rfl⟩
    have hdet : determinant (scalarMatrixToJet (rawQ p)).1 ≠ 0 := (hsub hp).1
    obtain ⟨L,t,ht,hL⟩ := ((scalarCurvatureJet_smooth hdet).of_le
      (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
    exact ⟨L,t,mem_nhdsWithin_of_mem_nhds ht,hL⟩
  obtain ⟨B,hbound⟩ := hk.exists_bound_of_continuousOn
    (show ContinuousOn (fun p : RawCollarInput => rmat p 1) (Metric.cthickening δ K) from (by fun_prop))
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨δ,hδ,L*M,mul_nonneg L.coe_nonneg hM,?_⟩
  intro p hp hp₀ r A hr hz hw hA he
  have hr0 : 0 < r := by linarith
  have hm : ‖rmat p 1‖ ≤ M := (hbound p hp).trans (le_max_left _ _)
  have hdiff : ‖rawQ p-rawQ (rawOriginal p)‖ ≤ M*A*rwgt p/r^3 := by
    rw [rawQ_difference,norm_smul,Real.norm_eq_abs,abs_mul,abs_neg,hz,abs_pow,
      abs_of_pos (by positivity : 0 < (1:ℝ)/r)]
    calc
      _ ≤ (A*rwgt p)*(1/r)^3*M := by gcongr
      _ = _ := by ring
  have hh := hLip.dist_le_mul _ ⟨p,hp,rfl⟩ _ ⟨rawOriginal p,hp₀,rfl⟩
  rw [dist_eq_norm,dist_eq_norm,scalarMatrixToJet_sub] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_left
    ((scalarMatrixToJet_norm _).trans hdiff) L.coe_nonneg)).trans_eq (by ring)

end
end CKSAngularGeometry

end

end OAI
