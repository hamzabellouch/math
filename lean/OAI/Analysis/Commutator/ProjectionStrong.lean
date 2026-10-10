import Mathlib
import OAI.Analysis.Commutator.ProjectionChains

namespace OAI

noncomputable section

section

noncomputable section

open Filter ContinuousLinearMapWOT

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.ProjectionChains

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma projection_norm_sq {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖^2=(inner ℂ (P x) x).re := by
  rw [norm_sq_eq_re_inner (𝕜:=ℂ)]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.isSelfAdjoint
  have he : inner ℂ (P (P x)) x=inner ℂ (P x) (P x) := hs (P x) x
  rw [←he]
  have hp := congrArg (fun T : H →L[ℂ] H => T x) hP.isIdempotentElem.eq
  change P (P x)=P x at hp
  rw [hp]
  rfl

lemma projection_norm_mono {P Q : H →L[ℂ] H} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hPQ : P≤Q) (x : H) : ‖P x‖≤‖Q x‖ := by
  have h := (hP.le_iff_mul_eq_left hQ).mp hPQ
  have hx : P (Q x)=P x := congrArg (fun T : H →L[ℂ] H => T x) h
  rw [←hx]
  exact (P.le_opNorm (Q x)).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hP.norm_le P) (norm_nonneg (Q x)))

theorem exists_strong_sup (M : VonNeumannAlgebra H)
    (P : ℕ → H →L[ℂ] H) (hp : ∀ n,IsStarProjection (P n))
    (hmem : ∀ n,P n∈M) (hmono : Monotone P) :
    ∃ W : H →L[ℂ] H,W∈M ∧ IsStarProjection W ∧ (∀ n,P n≤W) ∧
      (∀ x,Tendsto (fun n => P n x) atTop (𝓝 (W x))) ∧
      ∀ Q : H →L[ℂ] H,IsStarProjection Q → (∀ n,P n≤Q) → W≤Q := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  have hω : (ω : Filter ℕ)≤atTop := Ultrafilter.of_le atTop
  obtain ⟨W,hW,hPW,hlim,hle⟩ := monotone_ultralimit ω hω P hp hmono
  have hs (x y : H) : Tendsto (fun n => inner ℂ (P n x) y) (ω : Filter ℕ)
      (𝓝 (inner ℂ (W x) y)) := by
    have hh := tendsto_iff_forall_inner_apply_tendsto.mp hlim x y
    simpa only [RCLike.star_def,inner_conj_symm,ofCLM_apply] using hh.star
  refine ⟨W,WeakOperatorLimit.mem_vonNeumann hs M (Filter.Eventually.of_forall hmem),hW,hPW,?_,hle⟩
  intro x
  have hdiff (n : ℕ) : IsStarProjection (W-P n) :=
    (hp n).sub_of_mul_eq_left hW ((hp n).le_iff_mul_eq_left hW |>.mp (hPW n))
  have hnorm : Tendsto (fun n => ‖(W-P n) x‖^2) (ω : Filter ℕ) (𝓝 0) := by
    simp_rw [projection_norm_sq (hdiff _)]
    simp only [_root_.sub_apply,inner_sub_left,Complex.sub_re]
    simpa only [sub_self,Function.comp_apply] using (tendsto_const_nhds (x := (inner ℂ (W x) x).re)).sub (Complex.continuous_re.tendsto _ |>.comp (hs x x))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (hnorm.eventually_lt_const (sq_pos_of_pos hε)).exists
  refine ⟨N,?_⟩
  intro n hn
  have hle' : W-P n≤W-P N := sub_le_sub_left (hmono hn) W
  have hnm := projection_norm_mono (hdiff n) (hdiff N) hle' x
  have hlt : ‖(W-P N) x‖<ε := by nlinarith [norm_nonneg ((W-P N) x)]
  rw [dist_eq_norm,←norm_neg,neg_sub]
  exact hnm.trans_lt hlt

end Kadison.ProjectionChains

end

end
end

end OAI
