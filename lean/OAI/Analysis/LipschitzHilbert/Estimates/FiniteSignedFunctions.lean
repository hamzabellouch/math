import OAI.Analysis.LipschitzHilbert.Estimates.FiniteSignedEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram

namespace OAI

/-! Finite randomization for actual measurable functions. Membership in
L2 is recovered from signed sums and is not assumed in advance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}

def signedFunction (f : Fin n → X → ℂ) (s : Fin n → Bool) : X → ℂ :=
  fun x => finiteSignedSum (fun i => f i x) s

omit [MeasurableSpace X] in
theorem signedFunction_isolate (f : Fin n → X → ℂ) (i : Fin n) :
    signedFunction f (fun _ => true)-signedFunction f (fun j => decide (j≠i))=
      (2:ℂ) • f i := by
  classical
  funext x
  simp only [signedFunction,finiteSignedSum,ite_true,Pi.sub_apply,←Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro j _ hji
    simp [hji]
  · simp

theorem memLp_of_signedFunction (f : Fin n → X → ℂ)
    (h : ∀ s, MemLp (signedFunction f s) 2 μ) (i : Fin n) : MemLp (f i) 2 μ := by
  have hh := (h (fun _ => true)).sub (h (fun j => decide (j≠i)))
  rw [signedFunction_isolate] at hh
  have hi := hh.const_smul (1/2:ℂ)
  simpa only [smul_smul,show (1/2:ℂ)*2=1 by norm_num,one_smul] using hi

theorem signedLpTerm_coe (f : Fin n → X → ℂ) (h : ∀ i, MemLp (f i) 2 μ)
    (s : Fin n → Bool) (i : Fin n) :
    ((if s i then (h i).toLp (f i) else -(h i).toLp (f i) : Lp ℂ 2 μ) : X → ℂ)=ᵐ[μ]
      (fun x => if s i then f i x else -f i x) := by
  split_ifs
  · exact (h i).coeFn_toLp
  · filter_upwards [Lp.coeFn_neg ((h i).toLp (f i)),(h i).coeFn_toLp] with x hx hfx
    rw [hx]
    change -((h i).toLp (f i) x) = _
    rw [hfx]

theorem signedFunction_toLp (f : Fin n → X → ℂ) (h : ∀ i, MemLp (f i) 2 μ)
    (s : Fin n → Bool) (hs : MemLp (signedFunction f s) 2 μ) :
    finiteSignedSum (fun i => (h i).toLp (f i)) s=hs.toLp (signedFunction f s) := by
  apply Lp.ext
  have he := ae_all_iff.mpr (signedLpTerm_coe μ f h s)
  have hadd := Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => if s i then (h i).toLp (f i) else -(h i).toLp (f i))
  filter_upwards [he,hadd,hs.coeFn_toLp] with x hx ha hb
  change (finiteSignedSum (fun i => (h i).toLp (f i)) s) x = _
  change (∑ i, if s i then (h i).toLp (f i) else -(h i).toLp (f i)) x = _
  rw [ha,hb]
  exact Finset.sum_congr rfl (fun i _ => hx i)

theorem signedFunction_square_bound (f : Fin n → X → ℂ) (A : ℝ) (hA : 0≤A)
    (h : ∀ s, MemLp (signedFunction f s) 2 μ ∧
      eLpNorm (signedFunction f s) 2 μ≤ENNReal.ofReal A) :
    ∃ hf : ∀ i, MemLp (f i) 2 μ,
      (∑ i, ‖(hf i).toLp (f i)‖^2)≤A^2 := by
  let hf := memLp_of_signedFunction μ f (fun s => (h s).1)
  refine ⟨hf,finiteSignedSum_square_le _ _ ?_⟩
  intro s
  rw [signedFunction_toLp μ f hf s (h s).1,Lp.norm_toLp]
  have he : (eLpNorm (signedFunction f s) 2 μ).toReal≤A := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (h s).2
    simpa only [ENNReal.toReal_ofReal hA] using hh
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg he 2

end LipschitzHilbert

end

end OAI
