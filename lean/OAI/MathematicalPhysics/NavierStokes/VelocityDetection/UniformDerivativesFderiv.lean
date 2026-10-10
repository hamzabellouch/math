import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.JointCalculus

namespace OAI

noncomputable section
namespace VelocityDetection.UniformDerivatives
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open JointCalculus
variable {I E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Bounded.fderiv {f : I → E → F} (hf : Bounded f) :
    Bounded (fun a => fderiv ℝ (f a)) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hf (n + 1)
  refine ⟨C, hC, fun a x => ?_⟩
  simpa only [norm_iteratedFDeriv_fderiv] using hc a x

theorem Bounded.dAlong {f : I → E → F} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hfb : Bounded f) (v : E) : Bounded (fun a => JointCalculus.dAlong v (f a)) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hfb.fderiv n
  refine ⟨‖v‖ * C, mul_nonneg (norm_nonneg _) hC, fun a x => ?_⟩
  apply (norm_iteratedFDeriv_clm_apply_const
    (contDiff_infty_iff_fderiv.mp (hf a)).2.contDiffAt (by exact_mod_cast le_top)).trans
  exact mul_le_mul_of_nonneg_left (hc a x) (norm_nonneg _)

theorem const (c : F) : Bounded (fun _ : I => fun _ : E => c) := by
  intro n
  refine ⟨‖c‖, norm_nonneg _, fun _ x => ?_⟩
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_succ_const]

theorem Bounded.residual (ν : ℝ) {a : ℝ × Coord 2 → Coord 2}
    (ha : ContDiff ℝ ∞ a) (hb : ∀ i, Bounded (fun _ : Unit => fun q => a q i)) (i : Fin 2) :
    Bounded (fun _ : Unit => fun q => residual ν a q i) := by
  have hs (j : Fin 2) (_ : Unit) : ContDiff ℝ ∞ (fun q => a q j) := (contDiff_apply ℝ ℝ j).comp ha
  have hdt := (hb i).dAlong (hs i) (1, 0)
  have hdx (j : Fin 2) := (hb i).dAlong (hs i) (0, Pi.single j 1)
  have hxs (j : Fin 2) (_ : Unit) := contDiff_dAlong (0, Pi.single j 1) (hs i ())
  have hdxx (j : Fin 2) := (hdx j).dAlong (hxs j) (0, Pi.single j 1)
  have htS (_ : Unit) := contDiff_dAlong (1, 0) (hs i ())
  have hnn (j : Fin 2) (_ : Unit) := contDiff_dAlong (0, Pi.single j 1) (hxs j ())
  have hadv0 := (hb 0).mul (hs 0) (hxs 0) (hdx 0)
  have hadv1 := (hb 1).mul (hs 1) (hxs 1) (hdx 1)
  have hA0 (_ : Unit) := (hs 0 ()).mul (hxs 0 ())
  have hA1 (_ : Unit) := (hs 1 ()).mul (hxs 1 ())
  have hV := hdt.add htS hA0 hadv0 |>.add
    (fun _ => (htS ()).add (hA0 ())) hA1 hadv1
  have hL := (hdxx 0).add (hnn 0) (hnn 1) (hdxx 1)
  have hD := (const (I := Unit) (E := ℝ × Coord 2) ν).mul (fun _ => contDiff_const)
    (fun _ => (hnn 0 ()).add (hnn 1 ())) hL
  exact hV.sub (fun _ => ((htS ()).add (hA0 ())).add (hA1 ()))
    (fun _ => contDiff_const.mul ((hnn 0 ()).add (hnn 1 ()))) hD

end VelocityDetection.UniformDerivatives
end

noncomputable section
namespace VelocityDetection.UniformDerivatives
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {I E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem Bounded.postcomp {f : I → E → F} (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hb : Bounded f) (L : F →L[ℝ] G) : Bounded (fun a x => L (f a x)) := by
  intro n
  obtain ⟨C, hC, hc⟩ := hb n
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, fun a x => ?_⟩
  change ‖iteratedFDeriv ℝ n (L ∘ f a) x‖ ≤ ‖L‖ * C
  rw [
    L.iteratedFDeriv_comp_left (hf a).contDiffAt (by exact_mod_cast le_top)]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (hc a x) (norm_nonneg _))

theorem Bounded.finset_sum {J : Type*} (s : Finset J) {f : J → I → E → F}
    (hf : ∀ j a, ContDiff ℝ ∞ (f j a)) (hb : ∀ j, Bounded (f j)) :
    Bounded (fun a x => ∑ j ∈ s, f j a x) := by
  intro n
  choose C hC hc using fun j => hb j n
  refine ⟨∑ j ∈ s, C j, Finset.sum_nonneg (fun j _ => hC j), fun a x => ?_⟩
  change ‖iteratedFDeriv ℝ n (fun y => ∑ j ∈ s, f j a y) x‖ ≤ ∑ j ∈ s, C j
  rw [show (fun y => ∑ j ∈ s, f j a y) = ∑ j ∈ s, f j a by
    ext y; simp only [Finset.sum_apply], iteratedFDeriv_sum_apply]
  · exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hc j a x))
  · intro j _
    exact (contDiff_infty.mp (hf j a) n).contDiffAt

theorem Bounded.pi {J : Type*} [Fintype J] {f : I → E → J → ℝ}
    (hf : ∀ a j, ContDiff ℝ ∞ (fun x => f a x j))
    (hb : ∀ j, Bounded (fun a x => f a x j)) : Bounded f := by
  classical
  have hinj (j : J) : Bounded (fun a x => (Pi.single j (f a x j) : J → ℝ)) := by
    let L : ℝ →L[ℝ] (J → ℝ) := ContinuousLinearMap.single ℝ (fun _ : J => ℝ) j
    have h := Bounded.postcomp (f := fun a x => f a x j) (fun a => hf a j) (hb j) L
    exact h
  have hs (j : J) (a : I) : ContDiff ℝ ∞ (fun x => (Pi.single j (f a x j) : J → ℝ)) :=
    (ContinuousLinearMap.single ℝ (fun _ : J => ℝ) j).contDiff.comp (hf a j)
  have h := Bounded.finset_sum Finset.univ hs hinj
  simpa only [Finset.univ_sum_single] using h

end VelocityDetection.UniformDerivatives
end

end OAI
