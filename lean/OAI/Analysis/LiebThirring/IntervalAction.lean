import OAI.Analysis.LiebThirring.ConnectingPath

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

def actionDensity (σ : ℝ) (k a v : Fin N → ℝ) : ℝ :=
  (∑ i, v i^2) + (∑ i, k i^2*a i^2) - (∑ i, a i^2) ^ (1+1/σ)

lemma actionDensity_continuous {σ : ℝ} (hσ : 0 < σ) (k : Fin N → ℝ) :
    Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ actionDensity σ k z.1 z.2) := by
  unfold actionDensity
  apply Continuous.sub
  · fun_prop
  · exact (by fun_prop : Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ ∑ i, z.1 i^2)).rpow_const
      (fun _ ↦ Or.inr (by positivity))

lemma penalized_action_integral {σ δ ε l r η : ℝ}
    (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hδ : 0 < δ) (hε : 0 < ε) (hlr : l ≤ r)
    (k : Fin N → ℝ) (a v : ℝ → Fin N → ℝ)
    (ha : ContinuousOn a (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (had : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ a t i) (v t i) t)
    (hal : a l = 0) (har : a r = 0) (X : ℝ → Sym N)
    (hXi : X l = symDiag k) (hXf : X r = -symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X
      (ε⁻¹ • (sourceField σ δ hσ₁ hδ k (X t) - symOuter (a t))) (Icc l r) t)
    (hp : ∀ t ∈ Icc l r, actionDefect σ k (X t,a t) - constraintDefect σ δ k (X t,a t)/ε ≤ η) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤
      (∫ t in l..r, actionDensity σ k (a t) (v t)) + (r-l)*η := by
  have hX := HasDerivWithinAt.continuousOn hXd
  have hXval := continuous_subtype_val.comp_continuousOn hX
  let G := fun t ↦ fieldPrimitive σ δ k (X t) + ∑ i, a t i * ((X t).val *ᵥ a t) i
  let G' := fun t ↦ 2*(∑ i, v t i * ((X t).val *ᵥ a t) i) - constraintDefect σ δ k (X t,a t)/ε
  have hJ : Continuous (fun A : Sym N ↦ fieldPrimitive σ δ k A) :=
    continuous_iff_continuousAt.mpr (fun A ↦ (fieldPrimitive_hasFDerivAt hσ₁ hδ k A).continuousAt)
  have hMV : ContinuousOn (fun t ↦ (X t).val *ᵥ a t) (Icc l r) :=
    (show Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × (Fin N → ℝ) ↦ z.1 *ᵥ z.2)
      by fun_prop).comp_continuousOn (hXval.prodMk ha)
  have hdot : Continuous (fun z : (Fin N → ℝ) × (Fin N → ℝ) ↦ ∑ i, z.1 i * z.2 i) := by
    fun_prop
  have hG : ContinuousOn G (Icc l r) :=
    (hJ.comp_continuousOn hX).add (hdot.comp_continuousOn (ha.prodMk hMV))
  have hG' : ContinuousOn G' (Icc l r) :=
    ((hdot.comp_continuousOn (hv.prodMk hMV)).const_mul 2).sub
      (((constraintDefect_continuous hσ₁ hδ k).comp_continuousOn (hX.prodMk ha)).div_const ε)
  have hd (t : ℝ) (ht : t ∈ Ioo l r) : HasDerivAt G (G' t) t := by
    apply action_ode_identity hσ₁ hδ hε k (had t ht)
      ((hXd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    change ε • (ε⁻¹ • (matrixField σ δ k (X t).val - vecMulVec (a t) (a t))) = _
    rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr hG hd
    (hG'.intervalIntegrable_of_Icc (μ := volume) hlr)
  have hlim : G r - G l = fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) := by
    simp only [G,har,hal,hXi,hXf,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero]
    rfl
  rw [hlim] at hi
  have hec := (actionDensity_continuous hσ₀ k).comp_continuousOn (ha.prodMk hv)
  have hbound := intervalIntegral.integral_mono_on hlr
    (hG'.intervalIntegrable_of_Icc (μ := volume) hlr)
    ((hec.add (continuousOn_const (c := η))).intervalIntegrable_of_Icc (μ := volume) hlr)
    (fun t ht ↦ (action_penalty_pointwise k (X t) (a t) (v t)).trans
      (add_le_add (le_refl (actionDensity σ k (a t) (v t))) (hp t ht)))
  change (∫ t in l..r, G' t) ≤ (∫ t in l..r, actionDensity σ k (a t) (v t) + η) at hbound
  change ContinuousOn (fun t ↦ actionDensity σ k (a t) (v t)) (Icc l r) at hec
  rw [hi,intervalIntegral.integral_add (hec.intervalIntegrable_of_Icc (μ := volume) hlr)
    (intervalIntegrable_const),intervalIntegral.integral_const,smul_eq_mul] at hbound
  exact hbound

end SharpLiebThirring.ActionProof
namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set Filter ContinuationGap
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma mulVec_hasDerivAt (C : Matrix (Fin N) (Fin N) ℝ)
    {u v : ℝ → Fin N → ℝ} {t : ℝ} (hu : ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t) (i : Fin N) :
    HasDerivAt (fun t ↦ (C *ᵥ u t) i) ((C *ᵥ v t) i) t := by
  simpa only [mulVec,dotProduct] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ (hu j).const_mul (C i j))

lemma compact_amplitudes {l r R : ℝ} {u : ℝ → Fin N → ℝ}
    (hu : ContinuousOn u (Icc l r)) :
    IsCompact ((fun z : LowerSpace N × ℝ ↦ z.1.val *ᵥ u z.2) ''
      ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r)) := by
  apply ((compact_lower_box R).prod isCompact_Icc).image_of_continuousOn
  have hu' : ContinuousOn (fun z : LowerSpace N × ℝ ↦ u z.2)
      ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r) :=
    hu.comp continuousOn_snd (fun _ hz ↦ hz.2)
  have hC : Continuous (fun z : LowerSpace N × ℝ ↦ z.1.val) := continuous_subtype_val.comp continuous_fst
  exact (show Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × (Fin N → ℝ) ↦ z.1 *ᵥ z.2)
    by fun_prop).comp_continuousOn (hC.continuousOn.prodMk hu')

/-- An arbitrary finite upper bound on all triangular actions bounds the endpoint
jump. This avoids imposing a finiteness convention on a real-valued supremum. -/
lemma regularized_action_upper_test {σ δ l r S : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hud : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t)
    (hul : u l = 0) (hur : u r = 0)
    (ho : ∀ i j, (∫ t in l..r, u t i*u t j) = if i=j then 1 else 0)
    (hS : ∀ C : LowerSpace N,
      (∫ t in l..r, actionDensity σ k (C.val *ᵥ u t) (C.val *ᵥ v t)) ≤ S) :
    fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤ S := by
  obtain ⟨R,hpath⟩ := source_connecting_path hσ₀ hσ₁ hδ hlr k hk u hu ho
  let A := (fun z : LowerSpace N × ℝ ↦ z.1.val *ᵥ u z.2) ''
    ({C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} ×ˢ Icc l r)
  let K : Set (Sym N × (Fin N → ℝ)) := Metric.closedBall 0 ‖k‖ ×ˢ A
  have hK : IsCompact K := (isCompact_closedBall (0 : Sym N) ‖k‖).prod (compact_amplitudes hu)
  have hη (η : ℝ) (hη : 0 < η) :
      fieldPrimitive σ δ k (-diagonal k) - fieldPrimitive σ δ k (diagonal k) ≤ S+(r-l)*η := by
    obtain ⟨ε₀,hε₀,hpen⟩ := matrix_compact_penalty hσ₀ hσ₁ hδ k hK hη
    let ε := min ε₀ 1
    have hε : 0 < ε := lt_min hε₀ zero_lt_one
    obtain ⟨C,X,hC,hXi,hXf,hX,hXd⟩ := hpath ε hε (min_le_right _ _)
    have ha : ContinuousOn (fun t ↦ C.val *ᵥ u t) (Icc l r) :=
      (show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hu
    have ha' : ContinuousOn (fun t ↦ C.val *ᵥ v t) (Icc l r) :=
      (show Continuous (fun a : Fin N → ℝ ↦ C.val *ᵥ a) by fun_prop).comp_continuousOn hv
    have hh := penalized_action_integral hσ₀ hσ₁ hδ hε hlr k
      (fun t ↦ C.val *ᵥ u t) (fun t ↦ C.val *ᵥ v t) ha ha'
      (fun t ht ↦ mulVec_hasDerivAt C.val (hud t ht))
      (by rw [hul,mulVec_zero]) (by rw [hur,mulVec_zero]) X hXi hXf hXd
      (fun t ht ↦ hpen ε hε (min_le_left _ _) (X t,C.val *ᵥ u t)
        ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hX t ht,
          ⟨(C,t),⟨hC,ht⟩,rfl⟩⟩)
    exact hh.trans (add_le_add (hS C) (le_refl _))
  have ht : Tendsto (fun η : ℝ ↦ S+(r-l)*η) (𝓝[>] 0) (𝓝 S) := by
    have hc : Continuous (fun η : ℝ ↦ S+(r-l)*η) := by fun_prop
    simpa only [mul_zero,add_zero] using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with η h using hη η h)

lemma finite_action_upper_test {σ l r S : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hlr : l ≤ r) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (u v : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r)) (hv : ContinuousOn v (Icc l r))
    (hud : ∀ t ∈ Ioo l r, ∀ i, HasDerivAt (fun t ↦ u t i) (v t i) t)
    (hul : u l = 0) (hur : u r = 0)
    (ho : ∀ i j, (∫ t in l..r, u t i*u t j) = if i=j then 1 else 0)
    (hS : ∀ C : LowerSpace N,
      (∫ t in l..r, actionDensity σ k (C.val *ᵥ u t) (C.val *ᵥ v t)) ≤ S) :
    (∑ i, ∫ s in -(k i)..k i, (k i^2-s^2)^σ) ≤ S := by
  apply le_of_tendsto (fieldPrimitive_endpoint_limit hσ₀ hσ₁ k (fun i ↦ (hk i).le))
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact regularized_action_upper_test hσ₀ hσ₁ hδ hlr k hk u v hu hv hud hul hur ho hS

end SharpLiebThirring.ActionProof

end

end

end

end

end

end

end

end OAI
