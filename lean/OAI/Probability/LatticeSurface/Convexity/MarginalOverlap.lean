import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.CompactOverlap
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Overlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

end Overlap

namespace FacetVolume

lemma norm_le_mem_cube {n : ℕ} {x : Fin n → ℝ} {R : ℝ} (hx : ‖x‖≤R) : x∈cube n (-R) R := by
  apply mem_cube.mpr
  intro i
  have h := (norm_le_pi_norm x i).trans hx
  simpa only [Real.norm_eq_abs,abs_le,mem_Icc] using h

lemma support_cube_of_norm {n : ℕ} {p : (Fin n → ℝ) → ℝ} {R : ℝ}
    (hpK : ∀ x,R<‖x‖ → p x=0) : ∀ x,x∉cube n (-R) R → p x=0 := by
  intro x hx
  exact hpK x (lt_of_not_ge (fun h => hx (norm_le_mem_cube h)))

lemma integral_fin_cons {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ} (hf : Integrable f) :
    (∫ x,f x)=∫ r : ℝ,∫ z : Fin n → ℝ,f (Fin.cons r z) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he (z : ℝ × (Fin n → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.zero_succAbove]
  have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  rw [← hpres.integral_comp e.measurableEmbedding f]
  change (∫ z : ℝ × (Fin n → ℝ),f (e z))=_
  simp_rw [he]
  rw [Measure.volume_eq_prod,integral_prod]
  have hi := (hpres.integrable_comp_emb e.measurableEmbedding).2 hf
  change Integrable (fun z : ℝ × (Fin n → ℝ) => f (e z)) volume at hi
  simp_rw [he] at hi
  simpa only [Measure.volume_eq_prod] using hi

lemma marginal_support {n : ℕ} {p : (Fin (n+1) → ℝ) → ℝ} {R : ℝ}
    (hpK : ∀ x,R<‖x‖ → p x=0) (r : ℝ) (hr : r∉Icc (-R) R) :
    (∫ z : Fin n → ℝ,p (Fin.cons r z))=0 := by
  have he : ∀ z : Fin n → ℝ,p (Fin.cons r z)=0 := by
    intro z
    apply hpK
    have hh : R < |r| := lt_of_not_ge (fun h => hr (abs_le.mp h))
    exact hh.trans_le (by simpa only [Fin.cons_zero,Real.norm_eq_abs] using norm_le_pi_norm (Fin.cons (α:=fun _ : Fin (n+1) => ℝ) r z) 0)
  simp_rw [he];simp

lemma marginal_even {n : ℕ} {p : (Fin (n+1) → ℝ) → ℝ}
    (heven : ∀ x,p (-x)=p x) (r : ℝ) :
    (∫ z : Fin n → ℝ,p (Fin.cons (-r) z))=∫ z : Fin n → ℝ,p (Fin.cons r z) := by
  have he (z : Fin n → ℝ) : Fin.cons (α:=fun _ : Fin (n+1) => ℝ) (-r) (-z)= -Fin.cons r z := by
    ext i;refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [← integral_neg_eq_self (fun z : Fin n → ℝ => p (Fin.cons (-r) z)) volume]
  simp_rw [he,heven]

lemma marginal_overlap {n : ℕ} {p : (Fin (n+1) → ℝ) → ℝ} {R : ℝ}
    (hR : 0<R) (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (hpK : ∀ x,R<‖x‖ → p x=0) (r T : ℝ) :
    Real.sqrt ((∫ z : Fin n → ℝ,p (Fin.cons (r-T) z))*(∫ z : Fin n → ℝ,p (Fin.cons (r+T) z))) ≤
    ∫ z : Fin n → ℝ,Overlap.overlap p (ContinuousLinearMap.proj 0) T R (Fin.cons r z) := by
  let A := Overlap.overlap p (ContinuousLinearMap.proj 0) T R
  have hA := Overlap.usc_overlap hp hp0 (ContinuousLinearMap.proj 0) T R
  have hsupp (p' : (Fin (n+1) → ℝ) → ℝ) (h : ∀ x,R<‖x‖ → p' x=0)
      (r : ℝ) (z : Fin n → ℝ) (hz : z∉cube n (-R) R) : p' (Fin.cons r z)=0 := by
    exact support_cube_of_norm h _ (fun hh => hz (fin_cons_mem_cube.mp hh).2)
  have hPL := global_usc_prekopa_leindler n
    (hp.comp (continuous_const.finCons continuous_id))
    (hp.comp (continuous_const.finCons continuous_id))
    (hA.comp (continuous_const.finCons continuous_id))
    (a:= -R) (b:=R) (s:=1/2) (t:=1/2) (by linarith) (by norm_num) (by norm_num) (by norm_num)
    (fun z => hp0 _) (fun z => hp0 _) (fun z => Overlap.overlap_nonneg _ _ _ _ _)
    (hsupp p hpK (r-T)) (hsupp p hpK (r+T))
    (hsupp A (fun x hx => Overlap.overlap_support hpK hx) r) ?_
  · simpa only [Function.comp_def,id_eq,← Real.sqrt_eq_rpow,← Real.sqrt_mul
      (integral_nonneg fun z => hp0 (Fin.cons (r-T) z))] using hPL
  · intro z w
    let x : Fin (n+1) → ℝ := Fin.cons r ((1/2:ℝ) • z+(1/2:ℝ) • w)
    let χ : Fin (n+1) → ℝ := Fin.cons T ((1/2:ℝ) • w-(1/2:ℝ) • z)
    have hplus : x+χ=Fin.cons (r+T) w := by
      ext i;refine Fin.cases ?_ (fun j => ?_) i <;> simp [x,χ]
      ring
    have hminus : x-χ=Fin.cons (r-T) z := by
      ext i;refine Fin.cases ?_ (fun j => ?_) i <;> simp [x,χ]
      ring
    have hh := Overlap.kernel_le_overlap_all hp hp0 hpK x χ (show (ContinuousLinearMap.proj 0) χ=T by simp [χ])
    simpa only [Overlap.kernel,hplus,hminus,Function.comp_def,id_eq,← Real.sqrt_eq_rpow,
      ← Real.sqrt_mul (hp0 (Fin.cons (r-T) z)),mul_comm] using hh

end FacetVolume

end
end
end

end OAI
