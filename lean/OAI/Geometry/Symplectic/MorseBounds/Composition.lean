import OAI.Geometry.Symplectic.MorseBounds.SymplecticFlow

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.HamiltonianComposition
open Filter Set
open scoped Topology Manifold ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
local notation "I" => 𝓘(ℝ,E)
abbrev TwoForm := (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ

def PreservesForm (w : TwoForm (E := E) (M := M)) (a : M → M) : Prop :=
  ∀ x u v, w (a x) (mfderiv I I a x u) (mfderiv I I a x v) = w x u v

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem hamiltonian_transport
    (w : TwoForm (E := E) (M := M)) (a ai : M → M)
    (ha : ContMDiff I I ∞ a) (hai : ContMDiff I I ∞ ai)
    (hr : Function.RightInverse ai a) (_hl : Function.LeftInverse ai a)
    (hs : PreservesForm w a) (B : M → ℝ) (hB : ContMDiff I 𝓘(ℝ) ∞ B)
    (V : (x : M) → TangentSpace I x)
    (hV : ∀ x, w x (V x) = mvfderiv I B x) (x : M) :
    w x (mfderiv I I a (ai x) (V (ai x))) = mvfderiv I (B ∘ ai) x := by
  have hcomp : (a ∘ ai) = id := funext hr
  have hD := mfderiv_comp x (ha.mdifferentiable (by simp) (ai x))
    (hai.mdifferentiable (by simp) x)
  rw [hcomp, mfderiv_id] at hD
  have hBder := mvfderiv_comp x (hB.mdifferentiable (by simp) (ai x))
    (hai.mdifferentiable (by simp) x)
  ext v
  have hsinv := hs (ai x) (V (ai x)) (mfderiv I I ai x v)
  have hdv : (show E from v) = mfderiv I I a (ai x) (mfderiv I I ai x v) :=
    congrArg (fun L : E →L[ℝ] E => L v) hD
  erw [hr, ← hdv] at hsinv
  erw [hsinv, hBder, ContinuousLinearMap.comp_apply, ← hV]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
lemma composition_ode
    (a b : ℝ × M → M)
    (ha : ContMDiff (𝓘(ℝ).prod I) I ∞ a)
    (VA VB : ℝ → (x : M) → TangentSpace I x)
    (hODEa : ∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => a (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (VA t (a (t,x)))))
    (hODEb : ∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => b (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (VB t (b (t,x)))))
    (t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ) I (fun s => a (s,b (s,x))) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (VA t (a (t,b (t,x))) +
          mfderiv I I (fun y => a (t,y)) (b (t,x)) (VB t (b (t,x))))) := by
  have hd := (ha.mdifferentiable (by simp) (t,b (t,x))).hasMFDerivAt
  have hc := hd.comp t ((hasMFDerivAt_id t).prodMk (hODEb t x))
  apply hc.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  change mfderiv (𝓘(ℝ).prod I) I a (t,b (t,x)) (r, r • VB t (b (t,x))) =
    r • (VA t (a (t,b (t,x))) +
      mfderiv I I (fun y => a (t,y)) (b (t,x)) (VB t (b (t,x))))
  have hpart := mfderiv_prod_eq_add_apply (ha.mdifferentiable (by simp) (t,b (t,x)))
    (v := (r,r • (show E from VB t (b (t,x)))) )
  change mfderiv (𝓘(ℝ).prod I) I a (t,b (t,x)) (r, r • VB t (b (t,x))) =
    mfderiv 𝓘(ℝ) I (fun s => a (s,b (t,x))) t r +
      mfderiv I I (fun y => a (t,y)) (b (t,x)) (r • VB t (b (t,x))) at hpart
  rw [hpart, (hODEa t (b (t,x))).mfderiv]
  change r • VA t (a (t,b (t,x))) +
    mfderiv I I (fun y => a (t,y)) (b (t,x)) (r • VB t (b (t,x))) =
      r • (VA t (a (t,b (t,x))) +
        mfderiv I I (fun y => a (t,y)) (b (t,x)) (VB t (b (t,x))))
  rw [map_smul, smul_add]


omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem hamiltonian_path_composition
    (w : TwoForm (E := E) (M := M)) (a ai b : ℝ × M → M)
    (ha : ContMDiff (𝓘(ℝ).prod I) I ∞ a)
    (hai : ContMDiff (𝓘(ℝ).prod I) I ∞ ai)
    (hb : ContMDiff (𝓘(ℝ).prod I) I ∞ b)
    (hr : ∀ t, Function.RightInverse (fun x => ai (t,x)) (fun x => a (t,x)))
    (hl : ∀ t, Function.LeftInverse (fun x => ai (t,x)) (fun x => a (t,x)))
    (hs : ∀ t, PreservesForm w (fun x => a (t,x)))
    (A B : ℝ × M → ℝ)
    (hA : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ A)
    (hB : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ B)
    (VA VB : ℝ → (x : M) → TangentSpace I x)
    (hVA : ∀ t x, w x (VA t x) = mvfderiv I (fun y => A (t,y)) x)
    (hVB : ∀ t x, w x (VB t x) = mvfderiv I (fun y => B (t,y)) x)
    (hODEa : ∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => a (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (VA t (a (t,x)))))
    (hODEb : ∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => b (s,x)) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (VB t (b (t,x))))) :
    let C : ℝ × M → ℝ := fun q => A q + B (q.1,ai q)
    let VC : ℝ → (x : M) → TangentSpace I x := fun t x =>
      (show E from VA t x) + (show E from mfderiv I I (fun y => a (t,y)) (ai (t,x)) (VB t (ai (t,x))))
    ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) ∞ C ∧
    ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q => a (q.1,b q)) ∧
    (∀ t x, w x (VC t x) = mvfderiv I (fun y => C (t,y)) x) ∧
    (∀ t x, HasMFDerivAt 𝓘(ℝ) I (fun s => a (s,b (s,x))) t
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (VC t (a (t,b (t,x)))))) := by
  dsimp only
  have has (t : ℝ) : ContMDiff I I ∞ (fun x => a (t,x)) :=
    ha.comp (contMDiff_const.prodMk contMDiff_id)
  have hais (t : ℝ) : ContMDiff I I ∞ (fun x => ai (t,x)) :=
    hai.comp (contMDiff_const.prodMk contMDiff_id)
  have hAs (t : ℝ) : ContMDiff I 𝓘(ℝ) ∞ (fun x => A (t,x)) :=
    hA.comp (contMDiff_const.prodMk contMDiff_id)
  have hBs (t : ℝ) : ContMDiff I 𝓘(ℝ) ∞ (fun x => B (t,x)) :=
    hB.comp (contMDiff_const.prodMk contMDiff_id)
  refine ⟨hA.add (hB.comp (contMDiff_fst.prodMk hai)),
    ha.comp (contMDiff_fst.prodMk hb), ?_, ?_⟩
  · intro t x
    erw [map_add, hVA, hamiltonian_transport w (fun y => a (t,y)) (fun y => ai (t,y))
      (has t) (hais t) (hr t) (hl t) (hs t) (fun y => B (t,y)) (hBs t) (VB t) (hVB t) x]
    have hh := mvfderiv_add ((hAs t).mdifferentiable (by simp) x)
      (((hBs t).comp (hais t)).mdifferentiable (by simp) x)
    exact hh.symm
  · intro t x
    have hh := composition_ode a b ha VA VB hODEa hODEb t x
    have he := hl t (b (t,x))
    change ai (t,a (t,b (t,x))) = b (t,x) at he
    have hm := congrArg (fun y : M => (show E from
      mfderiv I I (fun z => a (t,z)) y (VB t y))) he
    exact hh.congr_mfderiv (congrArg (fun z : E =>
      (ContinuousLinearMap.id ℝ ℝ).smulRight
        ((show E from VA t (a (t,b (t,x)))) + z)) hm.symm)

end
end MorseArnold.HamiltonianComposition

end

end OAI
