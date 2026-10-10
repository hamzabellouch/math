import OAI.MathematicalPhysics.AlternatingFlow.VelocityNames
import OAI.MathematicalPhysics.AlternatingFlow.MixedPrograms

namespace OAI

section ForceNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma JetBound.named_fullDt {f : A → Velocity}
    (hf : JetBound (fun a => Function.uncurry (f a)))
    (hn : Named (fun z : (A × Fin 3) × RationalPoint => f z.1.1 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2)) :
    Named (fun z : (A × Fin 3) × RationalPoint => Analytic.fullDt (f z.1.1) (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2) := by
  have h := hf.named_component_words hn |>.comp
    ((Computable.fst.pair (Computable.const [0])).pair Computable.snd)
  apply h.congr
  intro z
  rw [Bounds.fullDt_eq_full_directional _ (hf.1 z.1.1) (rationalPoint z.2)]
  simp only [wordJet, direction, Matrix.cons_val_zero, Function.comp_apply]

lemma JetBound.named_dx {f : A → Velocity}
    (hf : JetBound (fun a => Function.uncurry (f a)))
    (hn : Named (fun z : (A × Fin 3) × RationalPoint => f z.1.1 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2)) (i : Fin 3) :
    Named (fun z : (A × Fin 3) × RationalPoint => dx i (f z.1.1) (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2) := by
  have h := hf.named_component_words hn |>.comp
    ((Computable.fst.pair (Computable.const [i.succ])).pair Computable.snd)
  apply h.congr
  intro z
  rw [Bounds.dx_eq_full_directional _ (hf.1 z.1.1) i (rationalPoint z.2)]
  simp only [wordJet, direction_succ, Function.comp_apply]

lemma Named.sum3 {f : Fin 3 → A → ℝ} (hf : ∀ i, Named (f i)) :
    Named (fun z => ∑ i : Fin 3, f i z) :=
  ((hf 0).add ((hf 1).add (hf 2))).congr (fun _ => by simp [Fin.sum_univ_succ])

lemma Certified.named_advection {f : A → Velocity}
    (hf : Certified (fun a => Function.uncurry (f a)))
    (hn : Named (fun z : (A × Fin 3) × RationalPoint => f z.1.1 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2)) :
    Named (fun z : (A × Fin 3) × RationalPoint => AlternatingNS.advection (f z.1.1) (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2) := by
  have hi (i : Fin 3) := (hn.comp
    (((Computable.fst.comp Computable.fst).pair (Computable.const i)).pair Computable.snd)).mul
      (hf.jetBound.named_dx hn i)
  apply (Named.sum3 hi).congr
  intro z
  rw [Bounds.advection_eq_sum]
  simp only [Function.comp_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]

lemma Certified.named_laplacian {f : A → Velocity}
    (hf : Certified (fun a => Function.uncurry (f a)))
    (hn : Named (fun z : (A × Fin 3) × RationalPoint => f z.1.1 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2)) :
    Named (fun z : (A × Fin 3) × RationalPoint => AlternatingNS.laplacian (f z.1.1) (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2) := by
  have hi (i : Fin 3) := (hf.dx i).jetBound.named_dx (hf.jetBound.named_dx hn i) i
  exact (Named.sum3 hi).congr (fun z => by simp only [AlternatingNS.laplacian, WithLp.ofLp_sum, Finset.sum_apply])

lemma Named.computableReal_const {r : ℝ} (hr : ComputableReal r) : Named (fun _ : A => r) := by
  obtain ⟨a,ha,h⟩ := hr
  have ha' : Computable a := (Arithmetic.rat_mk.to_comp.comp
    (Computable.fst.comp ha) (Computable.snd.comp ha)).of_eq (fun n => by
      simp [Rat.mkRat_eq_div, Rat.num_div_den])
  refine ⟨fun z => a z.2, ha'.comp Computable.snd, fun _ n => ?_⟩
  simpa only [tolerance_cast] using h n

lemma force_named (ν : ℝ) (hν : ComputableReal ν) :
    Named (fun z : ((Machine × List ℕ) × Fin 3) × RationalPoint =>
      fullForce ν z.1.1.1 z.1.1.2 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2) := by
  exact ((velocity_certified.jetBound.named_fullDt velocity_named).add
    (velocity_certified.named_advection velocity_named)).sub
      ((Named.computableReal_const hν).mul (velocity_certified.named_laplacian velocity_named))

end AlternatingNS.Effective

end ForceNamesDevelopment

end OAI
