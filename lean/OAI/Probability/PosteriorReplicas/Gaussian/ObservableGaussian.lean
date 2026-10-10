import OAI.Probability.PosteriorReplicas.Gaussian.GramTransform

namespace OAI

open MeasureTheory ProbabilityTheory Set Matrix InnerProductSpace Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma gaussianRows_split {d ℓ : ℕ} (U : Submodule ℝ (Vec d)) :
    ((gaussianRows d ℓ).prod (gaussianRows d ℓ)).map
      (fun z j => U.starProjection (z.1 j) + Uᗮ.starProjection (z.2 j)) = gaussianRows d ℓ := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Vec d) (Vec d) (Fin ℓ)
  have hj : (gaussianRows d ℓ).map
      (fun B => ((fun j => U.starProjection (B j)), fun j => Uᗮ.starProjection (B j))) =
      ((gaussianRows d ℓ).map (fun B j => U.starProjection (B j))).prod
        ((gaussianRows d ℓ).map (fun B j => Uᗮ.starProjection (B j))) := by
    change (gaussianRows d ℓ).map (e ∘ (fun B j => (U.starProjection (B j),Uᗮ.starProjection (B j)))) = _
    rw [← Measure.map_map e.measurable (by fun_prop)]
    unfold gaussianRows
    rw [Measure.pi_map_pi (f := fun _ : Fin ℓ => fun x : Vec d =>
      (U.starProjection x,Uᗮ.starProjection x)) (fun _ => by fun_prop)]
    simp_rw [gaussian_orthogonal_pair U]
    rw [(measurePreserving_arrowProdEquivProdArrow (Vec d) (Vec d) (Fin ℓ) _ _).map_eq]
    rw [Measure.pi_map_pi (fun _ => by fun_prop), Measure.pi_map_pi (fun _ => by fun_prop)]
  have h := congrArg (Measure.map (fun z : Rows d ℓ × Rows d ℓ => fun j => z.1 j + z.2 j)) hj
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  have he : (fun B : Rows d ℓ => fun j => U.starProjection (B j) + Uᗮ.starProjection (B j)) = id := by
    funext B j
    exact Submodule.starProjection_add_starProjection_orthogonal (B j)
  simpa only [Function.comp_def, Prod.map_fst, Prod.map_snd, he, Measure.map_id] using h.symm

lemma pairingColumns_split {d ℓ m : ℕ} (v : Rows d m) (B R : Rows d ℓ) :
    pairingColumns v (fun j => (Submodule.span ℝ (range v)).starProjection (B j) +
      (Submodule.span ℝ (range v))ᗮ.starProjection (R j)) = pairingColumns v B := by
  let U := Submodule.span ℝ (range v)
  have hv (i : Fin m) : v i ∈ U := Submodule.subset_span (mem_range_self i)
  ext i j
  change ⟪v i,U.starProjection (B j)+Uᗮ.starProjection (R j)⟫ = ⟪v i,B j⟫
  rw [inner_add_right, pairing_starProjection U (hv i)]
  have hz : ⟪v i,Uᗮ.starProjection (R j)⟫ = 0 :=
    (Submodule.mem_orthogonal U _).mp (Submodule.starProjection_apply_mem _ _) _ (hv i)
  rw [hz, add_zero]

lemma rowMix_pairing {d ℓ m k : ℕ} (v : Rows d m) (B : Rows d ℓ) (C : Rows ℓ k)
    (i : Fin k) (j : Fin m) :
    ⟪v j,rowMix C B i⟫ = ⟪C i,pairingColumns v B j⟫ := by
  simp [rowMix, pairingColumns, inner_sum, inner_smul_right, PiLp.inner_apply, mul_comm]

lemma rowMix_split_cancel {d ℓ m k : ℕ} (v : Rows d m) (B R : Rows d ℓ) (C : Rows ℓ k)
    (hC : ∀ i j, ⟪C i,pairingColumns v B j⟫ = 0) :
    rowMix C (fun j => (Submodule.span ℝ (range v)).starProjection (B j) +
      (Submodule.span ℝ (range v))ᗮ.starProjection (R j)) =
      rowMix C (fun j => (Submodule.span ℝ (range v))ᗮ.starProjection (R j)) := by
  let U := Submodule.span ℝ (range v)
  have hz (i : Fin k) : U.starProjection (rowMix C B i) = 0 := by
    apply U.starProjection_apply_eq_zero_iff.mpr
    apply (Submodule.mem_orthogonal U _).mpr
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j,rfl⟩ := hx
      exact (rowMix_pairing v B C i j).trans (hC i j)
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_left,hx,hy]
    | smul a x _ hx => simp [inner_smul_left,hx]
  funext i
  change (∑ j, C i j • (U.starProjection (B j) + Uᗮ.starProjection (R j))) = _
  simp only [smul_add, Finset.sum_add_distrib]
  have hmap : (∑ j, C i j • U.starProjection (B j)) = U.starProjection (rowMix C B i) := by
    simp [rowMix, map_sum]
  rw [hmap,hz,zero_add]
  rfl

lemma observable_gaussian_lintegral {d ℓ m k : ℕ} {v : Rows d m}
    (hv : LinearIndependent ℝ v) (hkm : k+m ≤ ℓ)
    {H : Rows ℓ m × Rows d k → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ B, ∫⁻ e, H (pairingColumns v B,
      rowMix (randomComplement (pairingColumns v B) e) B) ∂gaussianRows ℓ k ∂gaussianRows d ℓ) =
    ∫⁻ B, ∫⁻ A, H (pairingColumns v B,
      fun i => (Submodule.span ℝ (range v))ᗮ.starProjection (A i)) ∂gaussianRows d k ∂gaussianRows d ℓ := by
  let U := Submodule.span ℝ (range v)
  let f : Rows d ℓ → ℝ≥0∞ := fun B => ∫⁻ e, H (pairingColumns v B,
    rowMix (randomComplement (pairingColumns v B) e) B) ∂gaussianRows ℓ k
  have hf : Measurable f := by unfold f; fun_prop
  change (∫⁻ B, f B ∂gaussianRows d ℓ) = _
  conv_lhs => rw [← gaussianRows_split U, lintegral_map hf (by fun_prop), lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_pairingColumns_independent hv (by omega : m ≤ ℓ)] with B hB
  change (∫⁻ R, ∫⁻ e, H (pairingColumns v (fun j => U.starProjection (B j)+Uᗮ.starProjection (R j)),
    rowMix (randomComplement (pairingColumns v (fun j => U.starProjection (B j)+Uᗮ.starProjection (R j))) e)
      (fun j => U.starProjection (B j)+Uᗮ.starProjection (R j))) ∂gaussianRows ℓ k ∂gaussianRows d ℓ) = _
  dsimp only [U]
  simp_rw [pairingColumns_split]
  rw [lintegral_lintegral_swap (by fun_prop)]
  calc
    _ = ∫⁻ _e, ∫⁻ A, H (pairingColumns v B, fun i => Uᗮ.starProjection (A i))
        ∂gaussianRows d k ∂gaussianRows ℓ k := by
      apply lintegral_congr_ae
      filter_upwards [ae_randomComplement_orthonormal hB hkm] with e he
      dsimp only [U]
      simp_rw [rowMix_split_cancel v B _ _ (randomComplement_orthogonal hB e)]
      have hmap := gaussianRows_mix_projected (d := d) he Uᗮ
      have h := congrArg (fun μ : Measure (Rows d k) => ∫⁻ A, H (pairingColumns v B,A) ∂μ) hmap
      rw [lintegral_map (by fun_prop) (by fun_prop), lintegral_map (by fun_prop) (by fun_prop)] at h
      exact h
    _ = _ := by simp [U]

end PosteriorReplicas
end

end OAI
