import OAI.Analysis.KadisonKastler.L2StrataSum

namespace OAI

/-! # Evaluation of the coordinates associated with a measurable partition -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (μ : Measure X)

theorem l2Restrict_extension_same (s : Set X) (hs : MeasurableSet s)
    (f : Lp H 2 (Measure.comap ((↑) : s → X) μ)) :
    l2Restrict μ s hs (l2Extension μ s hs f) = f := by
  apply Lp.ext
  have he := (measurePreserving_subtype_coe (μa := μ) hs).quasiMeasurePreserving.ae
    (ae_restrict_of_ae (l2Extend_apply_ae μ s hs f))
  filter_upwards [l2Restrict_apply_ae μ s hs (l2Extension μ s hs f), he] with x hr he
  rw [hr]
  change l2Extend μ s hs f x.val = f x
  rw [he, l2ExtensionFunction_coe]

variable [CompleteSpace H] (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
  (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (hcover : ⋃ n, s n = Set.univ)

theorem l2StrataCoordinates_apply (f : Lp H 2 μ) (n : ℕ) :
    l2StrataCoordinates μ s hs hd hcover f n = l2Restrict μ (s n) (hs n) f := by
  let e := l2StrataCoordinates (H := H) μ s hs hd hcover
  have he : (l2Restriction μ (s n) (hs n)).comp e.symm.toLinearIsometry.toContinuousLinearMap =
      lp.evalCLM ℂ (fun i => Lp H 2 (Measure.comap ((↑) : s i → X) μ)) 2 n := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro i
    apply ContinuousLinearMap.ext
    intro v
    change l2Restrict μ (s n) (hs n) (e.symm (lp.single 2 i v)) =
      lp.single (E := fun j => Lp H 2 (Measure.comap ((↑) : s j → X) μ)) 2 i v n
    rw [show e.symm (lp.single 2 i v) = l2Extension μ (s i) (hs i) v from
      (l2Strata_isHilbertSum μ s hs hd hcover).linearIsometryEquiv_symm_apply_single v]
    by_cases hi : i = n
    · subst i
      rw [l2Restrict_extension_same]
      simp [lp.single_apply]
    · rw [l2Restrict_extension_disjoint μ (s n) (s i) (hs n) (hs i) (hd (Ne.symm hi))]
      simp [lp.single_apply, hi]
  have h := congrArg (fun T => T (e f)) he
  change l2Restrict μ (s n) (hs n) (e.symm (e f)) = e f n at h
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h.symm

omit [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
include hs hcover in
theorem ae_iff_forall_partition (p : X → Prop) :
    (∀ᵐ x ∂μ, p x) ↔ ∀ n, ∀ᵐ x : s n ∂Measure.comap ((↑) : s n → X) μ, p x.val := by
  constructor
  · intro hp n
    exact (ae_restrict_iff_subtype (hs n)).mp (ae_restrict_of_ae hp)
  · intro hp
    have hn (n : ℕ) : ∀ᵐ x ∂μ, x ∈ s n → p x :=
      (ae_restrict_iff' (hs n)).mp ((ae_restrict_iff_subtype (hs n)).mpr (hp n))
    filter_upwards [eventually_countable_forall.mpr hn] with x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    exact hx n hn

end

end KadisonKastler

end OAI
