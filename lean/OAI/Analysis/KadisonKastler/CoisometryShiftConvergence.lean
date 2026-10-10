import OAI.Analysis.KadisonKastler.CoisometryGraphShift

namespace OAI

/-! # Finite-observable convergence in the coisometry graph shift -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularConjugationData

variable (d : ModularConjugationData M Ω)

theorem rightAction_conjugation_tendsto (v : ℕ → Algebra M)
    (hconv : ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η)))
    (b : Algebra M) (η : H) :
    Tendsto (fun n => d.rightAction (v n*b*star (v n)) η) atTop
      (𝓝 (d.rightAction b η)) := by
  have ht := d.conjugation.continuous.continuousAt.tendsto.comp
    (hconv (star b) (d.conjugation η))
  have he (n : ℕ) : star (v n*b*star (v n)).val =
      (v n*star b*star (v n)).val := by
    change star ((v n).val*b.val*star (v n).val) =
      (v n).val*star b.val*star (v n).val
    simp only [star_mul,star_star,mul_assoc]
  simpa only [rightAction,conjugationOperator_apply,he,
    StarMemClass.coe_star,Function.comp_def] using ht

theorem coisometry_coefficient_tendsto (v : ℕ → Algebra M)
    (hconv : ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η)))
    (a b : Algebra M) (ζ : H) :
    Tendsto (fun n => inner ℂ (d.rightAction (v n) ζ)
      ((a.val*d.rightAction b) (d.rightAction (v n) ζ))) atTop
      (𝓝 (inner ℂ ζ ((a.val*d.rightAction b) ζ))) := by
  have ht := (a.val.continuous.continuousAt.tendsto.comp
    (d.rightAction_conjugation_tendsto v hconv b ζ))
  have hi := (tendsto_const_nhds (x := ζ)).inner (𝕜 := ℂ) ht
  have heq : (fun n => inner ℂ (d.rightAction (v n) ζ)
      ((a.val*d.rightAction b) (d.rightAction (v n) ζ))) =
      (fun n => inner ℂ ζ ((a.val*d.rightAction (v n*b*star (v n))) ζ)) :=
    funext (fun n => d.coisometry_coefficient_identity (v n) a b ζ)
  rw [heq]
  simpa only [Function.comp_def,mul_apply_eq_comp] using hi

theorem exists_coisometry_graph_shift (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (hconv : ∀ (a : Algebra M) (η : H),
      Tendsto (fun n => (v n*a*star (v n)).val η) atTop (𝓝 (a.val η)))
    (ξ η : H) (t : ℂ)
    (hscale : Tendsto (fun n => (v n).val η-t • d.rightAction (v n) η) atTop (𝓝 0))
    (x : Algebra M) (F : Finset (Algebra M × Algebra M)) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Algebra M,
      ‖y.val η-d.rightAction y ξ‖ < ‖t • x.val η-d.rightAction x ξ‖+ε ∧
      ∀ p ∈ F,
        ‖inner ℂ (d.rightAction y ξ)
            ((p.1.val*d.rightAction p.2) (d.rightAction y ξ))-
          inner ℂ (d.rightAction x ξ)
            ((p.1.val*d.rightAction p.2) (d.rightAction x ξ))‖ < ε := by
  classical
  have herror : Tendsto (fun n => ‖x‖*‖(v n).val η-t • d.rightAction (v n) η‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hscale.norm.const_mul ‖x‖
  have hF : ∀ᶠ n in atTop, ∀ p ∈ F,
      ‖inner ℂ (d.rightAction (v n) (d.rightAction x ξ))
          ((p.1.val*d.rightAction p.2) (d.rightAction (v n) (d.rightAction x ξ)))-
        inner ℂ (d.rightAction x ξ)
          ((p.1.val*d.rightAction p.2) (d.rightAction x ξ))‖ < ε := by
    apply (eventually_all_finset F).mpr
    intro p hp
    have ht := ((d.coisometry_coefficient_tendsto v hconv p.1 p.2
      (d.rightAction x ξ)).sub_const
      (inner ℂ (d.rightAction x ξ) ((p.1.val*d.rightAction p.2) (d.rightAction x ξ)))).norm
    have ht' : Tendsto (fun n => ‖inner ℂ (d.rightAction (v n) (d.rightAction x ξ))
        ((p.1.val*d.rightAction p.2) (d.rightAction (v n) (d.rightAction x ξ)))-
      inner ℂ (d.rightAction x ξ)
        ((p.1.val*d.rightAction p.2) (d.rightAction x ξ))‖) atTop (𝓝 0) := by
      simpa only [sub_self,norm_zero] using ht
    exact ht'.eventually (gt_mem_nhds hε)
  obtain ⟨n,hn,hFn⟩ := ((herror.eventually (gt_mem_nhds hε)).and hF).exists
  refine ⟨x*v n,?_,?_⟩
  · exact (d.coisometry_graph_shift_bound x (v n) (hv n) ξ η t).trans_lt (by linarith)
  · intro p hp
    simpa only [d.rightAction_mul,mul_apply_eq_comp] using hFn p hp

end ModularConjugationData

end

end KadisonKastler

end OAI
