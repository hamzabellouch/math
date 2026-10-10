import OAI.Analysis.KadisonKastler.RemoteScalingLimit
import OAI.Analysis.KadisonKastler.IsometryGraphShift
import OAI.Analysis.KadisonKastler.ModularScalingDefect
import OAI.Analysis.KadisonKastler.ModularDefectDensity

namespace OAI

/-! # The concrete modular coisometries of the two-ratio product -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

include S in
theorem exists_modular_scaling_all_vectors (J : H ≃ₗᵢ⋆[ℂ] H)
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation = tomitaPolarConjugation J Ω S.separating S.cyclic)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ v : ℕ → Algebra M,
      (∀ n, v n*star (v n)=1) ∧
      (∀ ξ : H, Tendsto (fun n => (v n).val ξ-(t : ℂ) • d.rightAction (v n) ξ)
        atTop (𝓝 0)) ∧
      (∀ (a : Algebra M) (ξ : H),
        Tendsto (fun n => (a*v n-v n*a).val ξ) atTop (𝓝 0)) := by
  obtain ⟨s,v,hs,hv,hcentral⟩ := S.exists_remote_scaling_sequence
    (sq_pos_of_pos ht) (show t^2 < 1 by nlinarith)
  have hscale := scaling_vector_limit J S.separating S.cyclic s v hs
    (fun n => (hv n).1) (fun n => (hv n).2.2.1) (fun n => (hv n).2.2.2)
  have he (n : ℕ) : d.rightAction (v n) Ω =
      tomitaPolarConjugation J Ω S.separating S.cyclic (star (v n).val Ω) := by
    change d.conjugation (star (v n).val (d.conjugation Ω)) = _
    rw [d.fixes_vector,hd]
  have hΩ : Tendsto (fun n => (v n).val Ω-(t : ℂ) • d.rightAction (v n) Ω)
      atTop (𝓝 0) := by
    simpa only [he,Real.sqrt_sq ht.le] using hscale
  refine ⟨v,fun n => (hv n).2.2.1,?_,hcentral⟩
  intro ξ
  apply d.scaling_defect_tendsto_of_cyclic S.cyclic v (fun n => (hv n).2.2.1)
    (t : ℂ) ?_ hΩ ξ
  intro a
  have heq : (fun n => (v n*a-a*v n).val Ω) =
      (fun n => -((a*v n-v n*a).val Ω)) := by
    funext n
    simp only [AddSubgroupClass.coe_sub,sub_apply,neg_sub]
  rw [heq]
  simpa only [neg_zero] using (hcentral a Ω).neg

include S in
theorem exists_modular_coisometry_sequence (J : H ≃ₗᵢ⋆[ℂ] H)
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation = tomitaPolarConjugation J Ω S.separating S.cyclic)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ v : ℕ → Algebra M,
      (∀ n, v n*star (v n)=1) ∧
      Tendsto (fun n => (v n).val Ω-(t : ℂ) • d.rightAction (v n) Ω)
        atTop (𝓝 0) ∧
      (∀ (a : Algebra M) (η : H),
        Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η))) := by
  have hr : 0 < t^2 := sq_pos_of_pos ht
  have hr1 : t^2 < 1 := by nlinarith
  obtain ⟨s,v,hs,hv,hconv⟩ := S.exists_remote_scaling_conjugations d hr hr1
  refine ⟨v,fun n => (hv n).2.2.1,?_,hconv⟩
  have hscale := scaling_vector_limit J S.separating S.cyclic s v hs
    (fun n => (hv n).1) (fun n => (hv n).2.2.1) (fun n => (hv n).2.2.2)
  have he (n : ℕ) : d.rightAction (v n) Ω =
      tomitaPolarConjugation J Ω S.separating S.cyclic (star (v n).val Ω) := by
    change d.conjugation (star (v n).val (d.conjugation Ω)) = _
    rw [d.fixes_vector,hd]
  simpa only [he,Real.sqrt_sq ht.le] using hscale

include S in
theorem exists_modular_graph_shift (J : H ≃ₗᵢ⋆[ℂ] H)
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation = tomitaPolarConjugation J Ω S.separating S.cyclic)
    (ξ : H) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x : Algebra M) (F : Finset (Algebra M × Algebra M)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Algebra M,
      ‖y.val Ω-d.rightAction y ξ‖ < ‖(t : ℂ) • x.val Ω-d.rightAction x ξ‖+ε ∧
      ∀ p ∈ F,
        ‖inner ℂ (d.rightAction y ξ)
            ((p.1.val*d.rightAction p.2) (d.rightAction y ξ))-
          inner ℂ (d.rightAction x ξ)
            ((p.1.val*d.rightAction p.2) (d.rightAction x ξ))‖ < ε := by
  obtain ⟨v,hv,hscale,hconv⟩ := S.exists_modular_coisometry_sequence J d hd ht ht1
  exact d.exists_coisometry_graph_shift v hv hconv ξ Ω (t : ℂ) hscale x F hε

include S in
theorem exists_modular_graph_shift_adjoint (J : H ≃ₗᵢ⋆[ℂ] H)
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation = tomitaPolarConjugation J Ω S.separating S.cyclic)
    (η : H) {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (x : Algebra M) (F : Finset (Algebra M × Algebra M)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Algebra M,
      ‖y.val η-d.rightAction y Ω‖ < ‖x.val η-(t : ℂ) • d.rightAction x Ω‖+ε ∧
      ∀ p ∈ F,
        ‖inner ℂ (y.val η) ((p.1.val*d.rightAction p.2) (y.val η))-
          inner ℂ (x.val η) ((p.1.val*d.rightAction p.2) (x.val η))‖ < ε := by
  obtain ⟨v,hv,hscale,hconv⟩ := S.exists_modular_coisometry_sequence J d hd ht ht1
  exact d.exists_isometry_graph_shift v hv hconv Ω η (t : ℂ)
    (d.rightAction_adjoint_defect_tendsto v t hscale) x F hε

end PointedMatrixSites

end

end KadisonKastler

end OAI
