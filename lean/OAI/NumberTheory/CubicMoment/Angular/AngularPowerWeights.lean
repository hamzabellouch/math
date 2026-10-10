import OAI.NumberTheory.CubicMoment.Angular.AngularLogarithmicLattice

namespace OAI

/-! Fixed real powers preserve the actual positive annular weight family.
The smooth extension used in the proof agrees with the power wherever
the original weight is nonzero. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

def UniformLogWeights.realPower {ι : Type*} {W : ι → ℝ → ℂ}
    (h : UniformLogWeights W) (q : ℝ) :
    UniformLogWeights (fun i x => ((x^q:ℝ):ℂ)*W i x) := by
  let a := Real.exp (-h.radius)
  let b := Real.exp h.radius
  have ha : 0 < a := Real.exp_pos _
  have hb : 0 < b := Real.exp_pos _
  let g := angularLogExtension a b
  have hg : ContDiff ℝ ∞ g := contDiff_id.add (angularLogPerturbation_smooth ha hb)
  let F : ℝ → ℝ → ℂ := fun _ x => (Real.exp (-q*g x):ℂ)
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    change ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Real.exp (-q*g p.2):ℂ))
    exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul (hg.comp contDiff_snd)))
  let hh := h.compactMultiplier ({0}:Set ℝ) isCompact_singleton F hF
  have hi := hh.reindex (fun i => (i,⟨0,by simp⟩))
  have he : (fun i (x : ℝ) => ((x^q:ℝ):ℂ)*W i x) =
      (fun i x => F 0 x*W i x) := by
    funext i x
    by_cases hw : W i x = 0
    · simp only [hw,mul_zero]
    · have hx := h.annular_support i (subset_tsupport (W i) hw)
      have hxp : 0 < x := lt_of_lt_of_le ha hx.1
      have hlog : g x = -Real.log x := angularLogExtension_eq_log ha hb hx
      dsimp only [F]
      rw [hlog,Real.rpow_def_of_pos hxp]
      rw [show Real.log x*q = -q*(-Real.log x) by ring]
  rw [he]
  exact hi

theorem LogarithmicWeightFamily.power_lattice_bound
    {ι : Type*} {Y : ι → ℝ} {W : ι → ℝ → ℂ} (h : LogarithmicWeightFamily Y W)
    {ℓ : ℤ} (hℓ : ℓ ≠ 0) (q : ℝ) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ i r, primary r → Squarefree r → ∀ U, 1 ≤ U →
      ‖squarefreeCoprimeAngularLattice r ℓ (fun x => ((x^q:ℝ):ℂ)*W i x) U‖ ≤
        K*(Y i)^s*norm r^ε*Real.sqrt U := by
  obtain ⟨K,hK,hbound⟩ := ((h.normalize hs).realPower q).squarefreeCoprimeAngularLattice_bound hℓ hε
  refine ⟨K,hK,?_⟩
  intro i r hr hsr U hU
  have hY : 0 < Y i := zero_lt_one.trans_le (h.length_one i)
  have he : (fun x => ((x^q:ℝ):ℂ)*normalizedLogWeight Y W s i x) =
      (fun x => (((Y i)^(-s):ℝ):ℂ)*(((x^q:ℝ):ℂ)*W i x)) := by
    funext x
    simp only [normalizedLogWeight,Complex.real_smul]
    ring
  have hb := hbound i r hr hsr U hU
  rw [he,squarefreeCoprimeAngularLattice_const_mul,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hY.le _)] at hb
  have hp : (Y i)^s*(Y i)^(-s) = 1 := by
    rw [←Real.rpow_add hY,add_neg_cancel,Real.rpow_zero]
  calc
    _ = (Y i)^s*((Y i)^(-s)*
        ‖squarefreeCoprimeAngularLattice r ℓ (fun x => ((x^q:ℝ):ℂ)*W i x) U‖) := by
      rw [←mul_assoc,hp,one_mul]
    _ ≤ (Y i)^s*(K*norm r^ε*Real.sqrt U) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hY.le _)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
