import Mathlib
import OAI.Analysis.VlasovMaxwell.Flow.HighFlow

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma smooth_compact_jets_bound {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i : ℕ, i ≤ n → ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have hb (i : Fin (n+1)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hc.iteratedFDeriv (i:ℕ))
    exact ⟨max C 0,le_max_right _ _,fun x => (hC x).trans (le_max_left _ _)⟩
  choose C hC hbound using hb
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro i hi x
  exact (hbound ⟨i,by omega⟩ x).trans (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ _))

lemma transported_derivative_tame {d : Datum} (hd : Admissible d)
    (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ (s : Solution), PicardRegular d s → TransportFor s E B →
      ∀ T : ℝ, T∈Icc (0:ℝ) 1 → SpatialJetBound n T A E B →
      ∀ H : ℝ, 0 ≤ H →
      (∀ t∈Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun y => E (t,y)) x‖ ≤ H ∧
        ‖iteratedFDeriv ℝ (n+1) (fun y => B (t,y)) x‖ ≤ H) →
      ∀ t∈Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ (n+1) (fun w => s.f (t,w)) z‖ ≤ C*(1+H) := by
  obtain ⟨D,hD,hdjet⟩ := smooth_compact_jets_bound hd.1 hd.2.1 (n+1)
  obtain ⟨L,hL,hlow⟩ := SmoothLorentzFlow.reversePath_derivatives_bound n A hA
  obtain ⟨K,hK,htop⟩ := SmoothLorentzFlow.backward_derivative_tame n hn A hA
  obtain ⟨C,hC,hcomp⟩ := tame_iteratedFDeriv_comp (E:=Phase) (F:=Phase) (G:=ℝ) n hn (1+D+L) (by linarith)
  refine ⟨C*(1+D+K),by positivity,?_⟩
  intro E B hE hB s hs hV T hT hb H hH hh t ht z
  obtain ⟨F⟩ := exists_smoothLorentzFlow hE hB
  have hback : ContDiff ℝ ∞ (fun z => F.backward (t,z)) :=
    F.smooth_backward.comp (contDiff_const.prodMk contDiff_id)
  have hrep : (fun z => s.f (t,z))=d.f₀ ∘ (fun z => F.backward (t,z)) := by
    funext z
    rw [F.transport_for_inverse hs.smooth_f hV,hs.initial_f]
    rfl
  rw [hrep]
  have hj := hcomp d.f₀ (fun z => F.backward (t,z)) hd.1 hback z
    (fun i hi hi' => (hdjet i (by omega) _).trans (by linarith)) (by
      intro i hi hi'
      have he : (fun w => F.reversePath t w t)=(fun w => F.backward (t,w)) := by
        funext w; exact F.reversePath_end t w
      have hl := hlow E B hE hB F T hT hb t ht t ⟨ht.1,le_rfl⟩ z i hi hi'
      rw [he] at hl
      exact hl.trans (by linarith))
  have hf := hdjet (n+1) le_rfl (F.backward (t,z))
  have hg := htop E B hE hB F T hT hb H hH hh t ht z
  refine hj.trans (mul_le_mul_of_nonneg_left (by gcongr) hC |>.trans ?_)
  nlinarith [mul_nonneg hC hH,mul_nonneg (mul_nonneg hC hD) hH]

lemma norm_iteratedFDeriv_phase_slice {f : Phase → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x v : Vec) :
    ‖iteratedFDeriv ℝ n (fun y => f (y,v)) x‖ ≤ ‖iteratedFDeriv ℝ n f (x,v)‖ := by
  let g : Phase → ℝ := fun z => f (z+(0,v))
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have hh := norm_iteratedFDeriv_precomp_contraction g hg (ContinuousLinearMap.inl ℝ Vec Vec)
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro w
      simp only [ContinuousLinearMap.inl_apply,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg w),one_mul]
      exact le_rfl) n x
  simpa only [g,Function.comp_def,ContinuousLinearMap.inl_apply,iteratedFDeriv_comp_add_right,
    Prod.mk_add_mk,add_zero,zero_add] using hh

end RVM
end

end OAI
