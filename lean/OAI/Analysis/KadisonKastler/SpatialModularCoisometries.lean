import OAI.Analysis.KadisonKastler.SpatialLocalScaling
import OAI.Analysis.KadisonKastler.RemoteModularCoisometries

namespace OAI

/-! # Modular coisometries after adjoining an arbitrary tensor factor

These are the concrete sequences used in the state-shifting argument.
Their scaling identity is for the modular conjugation of the full product,
so no tensor-product formula for that conjugation is assumed.
-/

namespace KadisonKastler

open Generator UnitalTomsWinter Filter
open scoped Topology

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K} {Ω : H} {ξ : K}

namespace PointedMatrixSites

variable (S : PointedMatrixSites N ξ twoRatioSiteParameter)

include S in
theorem exists_spatial_scaling_conjugations
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (d : ModularConjugationData (spatialProductAlgebra M N) (tensorVector ξ Ω))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ (s : ℕ → ℝ) (w : ℕ → Algebra (spatialProductAlgebra M N)),
      Tendsto s atTop (𝓝 r) ∧
      (∀ n, 0 < s n ∧ s n < 1 ∧ w n*star (w n)=1 ∧
        StateScales (spatialProductAlgebra M N) (tensorVector ξ Ω) (s n) (w n).val) ∧
      (∀ (a : Algebra (spatialProductAlgebra M N)) (η : SpatialHilbert H K),
        Tendsto (fun n => (a*w n-w n*a).val η) atTop (𝓝 0)) ∧
      (∀ (a : Algebra (spatialProductAlgebra M N)) (η : SpatialHilbert H K),
        Tendsto (fun n => (w n*a*star (w n)).val η) atTop (𝓝 (a.val η))) := by
  choose s v hpos hlt hclose hco hscale using
    (fun n : ℕ => S.exists_scaling_coisometry_near hr hr1
      (show 0 < (1 : ℝ)/(n+1) by positivity))
  have hs : Tendsto s atTop (𝓝 r) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hclose n).trans_le ((one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 1)).trans hk.le)
  let w (n : ℕ) := spatialRightAlgebraHom M N (S.remoteCopy n (v n))
  have hw (n : ℕ) : w n*star (w n)=1 := by
    simp only [w,← map_star,← map_mul,hco,map_one]
  refine ⟨s,w,hs,?_,?_,?_⟩
  · intro n
    exact ⟨hpos n,hlt n,hw n,(S.remoteCopy_scales n (v n) (hscale n)).spatialRight⟩
  · intro a η
    exact S.spatial_remote_commutator_tendsto M Ω hsep s v hco hscale
      (fun n => (hlt n).le) a η
  · intro a η
    have hc : 0 < r/2 := by positivity
    have hc1 : r/2 ≤ 1 := by linarith
    have hcs : ∀ᶠ n in atTop, r/2 ≤ s n :=
      (hs.eventually (eventually_gt_nhds (show r/2 < r by linarith))).mono
        (fun _ h => h.le)
    have ht := S.spatial_remote_adjoint_commutator_tendsto M Ω hsep d s v hco hscale
      hc hc1 hcs a η
    have hn (n : ℕ) : ‖(w n*a*star (w n)-a).val η‖ ≤
        ‖(a*star (w n)-star (w n)*a).val η‖ :=
      coisometry_conjugation_error_le (w n) a (hw n) η
    have hz := squeeze_zero (fun n => norm_nonneg ((w n*a*star (w n)-a).val η)) hn
      (by simpa only [norm_zero] using ht.norm)
    have hout := (tendsto_zero_iff_norm_tendsto_zero.mpr hz).add_const (a.val η)
    simpa only [AddSubgroupClass.coe_sub,sub_apply,sub_add_cancel,zero_add] using hout

theorem exists_spatial_modular_coisometries
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (J : SpatialHilbert H K ≃ₗᵢ⋆[ℂ] SpatialHilbert H K)
    (d : ModularConjugationData (spatialProductAlgebra M N) (tensorVector ξ Ω))
    (hd : d.conjugation = tomitaPolarConjugation J (tensorVector ξ Ω)
      (separating_spatialProduct_vector_of_separating M N Ω ξ hsep S.separating)
      (denseRange_spatialProduct_vector M N Ω ξ hcyc S.cyclic))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ w : ℕ → Algebra (spatialProductAlgebra M N),
      (∀ n, w n*star (w n)=1) ∧
      (∀ η : SpatialHilbert H K,
        Tendsto (fun n => (w n).val η-(t : ℂ) • d.rightAction (w n) η) atTop (𝓝 0)) ∧
      (∀ (a : Algebra (spatialProductAlgebra M N)) (η : SpatialHilbert H K),
        Tendsto (fun n => (w n*a*star (w n)).val η) atTop (𝓝 (a.val η))) := by
  obtain ⟨s,w,hs,hw,hcentral,hconj⟩ := S.exists_spatial_scaling_conjugations hsep d
    (sq_pos_of_pos ht) (show t^2 < 1 by nlinarith)
  have hsP := separating_spatialProduct_vector_of_separating M N Ω ξ hsep S.separating
  have hcP := denseRange_spatialProduct_vector M N Ω ξ hcyc S.cyclic
  have hscale := scaling_vector_limit J hsP hcP s w hs
    (fun n => (hw n).1) (fun n => (hw n).2.2.1) (fun n => (hw n).2.2.2)
  have he (n : ℕ) : d.rightAction (w n) (tensorVector ξ Ω)=
      tomitaPolarConjugation J (tensorVector ξ Ω) hsP hcP
        (star (w n).val (tensorVector ξ Ω)) := by
    change d.conjugation (star (w n).val (d.conjugation (tensorVector ξ Ω)))=_
    rw [d.fixes_vector,hd]
  have hΩ : Tendsto (fun n => (w n).val (tensorVector ξ Ω)-
      (t : ℂ) • d.rightAction (w n) (tensorVector ξ Ω)) atTop (𝓝 0) := by
    simpa only [he,Real.sqrt_sq ht.le] using hscale
  refine ⟨w,fun n => (hw n).2.2.1,?_,hconj⟩
  intro η
  apply d.scaling_defect_tendsto_of_cyclic hcP w (fun n => (hw n).2.2.1)
    (t : ℂ) ?_ hΩ η
  intro a
  have heq : (fun n => (w n*a-a*w n).val (tensorVector ξ Ω))=
      (fun n => -((a*w n-w n*a).val (tensorVector ξ Ω))) := by
    funext n
    simp only [AddSubgroupClass.coe_sub,sub_apply,neg_sub]
  rw [heq]
  simpa only [neg_zero] using (hcentral a (tensorVector ξ Ω)).neg

end PointedMatrixSites

end

end KadisonKastler

end OAI
