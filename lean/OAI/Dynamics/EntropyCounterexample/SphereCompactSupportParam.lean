import OAI.Dynamics.EntropyCounterexample.SphereCompactSupport

namespace OAI

noncomputable section

open Set Filter Metric
open scoped Topology RealInnerProductSpace

namespace Problem340.SphereCompactSupport

variable {P E W : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {v : E} (hv : ‖v‖ = 1)

include hv in

theorem exists_local_ambient_extension_param
    {n : WithTop ℕ∞} {F : P → (ℝ ∙ v)ᗮ → W}
    (hF : ContDiff ℝ n (Function.uncurry F))
    {K : Set ((ℝ ∙ v)ᗮ)} (hK : IsCompact K)
    (hzero : ∀ p w, w ∉ K → F p w = 0)
    (p : P) (x : sphere (0 : E) 1) :
    ∃ U : Set (P × E), IsOpen U ∧ (p, (x : E)) ∈ U ∧
      ∃ A : P × E → W, ContDiffOn ℝ n A U ∧
        ∀ q (y : sphere (0 : E) 1), (q, (y : E)) ∈ U →
          extension (F q) y = A (q, (y : E)) := by
  by_cases hx : (x : E) = v
  · let K' : Set E :=
      (fun w : (ℝ ∙ v)ᗮ => (stereoInvFun hv w : E)) '' K
    have hK' : IsCompact K' := hK.image
      (continuous_subtype_val.comp (continuous_stereoInvFun hv))
    have hvK : v ∉ K' := by
      rintro ⟨w, hw, heq⟩
      exact stereoInvFun_ne_north_pole hv w (Subtype.ext heq)
    refine ⟨Set.univ ×ˢ K'ᶜ, isOpen_univ.prod hK'.isClosed.isOpen_compl,
      ?_, fun _ => 0, contDiffOn_const, ?_⟩
    · exact ⟨Set.mem_univ _, by simpa [hx] using hvK⟩
    · intro q y hy
      by_cases hyv : (y : E) = v
      · simp [extension, hyv]
      · rw [extension_of_ne (F q) hyv]
        apply hzero q
        intro hw
        apply hy.2
        exact ⟨stereoToFun v y, hw, congrArg Subtype.val (stereo_left_inv hv hyv)⟩
  · let V : Set E := {y | innerSL ℝ v y ≠ (1 : ℝ)}
    have hV : IsOpen V := isOpen_ne_fun (innerSL ℝ v).continuous continuous_const
    have hxV : (x : E) ∈ V := by
      intro h
      exact hx ((inner_eq_one_iff_of_norm_eq_one hv (norm_eq_of_mem_sphere x)).mp h).symm
    refine ⟨Set.univ ×ˢ V, isOpen_univ.prod hV, ⟨Set.mem_univ _, hxV⟩,
      (fun z => F z.1 (stereoToFun v z.2)), ?_, ?_⟩
    · change ContDiffOn ℝ n
        ((Function.uncurry F) ∘ (fun z : P × E => (z.1, stereoToFun v z.2))) (univ ×ˢ V)
      apply hF.comp_contDiffOn
      exact contDiffOn_fst.prodMk
        (contDiffOn_stereoToFun.comp contDiffOn_snd (fun z hz => hz.2))
    · intro q y hy
      apply extension_of_ne
      intro hyv
      apply hy.2
      simp [hyv, hv]

include hv in

theorem continuous_extension_param
    {n : WithTop ℕ∞} {F : P → (ℝ ∙ v)ᗮ → W}
    (hF : ContDiff ℝ n (Function.uncurry F))
    {K : Set ((ℝ ∙ v)ᗮ)} (hK : IsCompact K)
    (hzero : ∀ p w, w ∉ K → F p w = 0) :
    Continuous (fun z : P × sphere (0 : E) 1 => extension (F z.1) z.2) := by
  have hemb : Continuous (fun z : P × sphere (0 : E) 1 => (z.1, (z.2 : E))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  rw [continuous_iff_continuousAt]
  rintro ⟨p, x⟩
  obtain ⟨U, hU, hx, A, hA, hmatch⟩ :=
    exists_local_ambient_extension_param hv hF hK hzero p x
  have hAc : ContinuousAt A (p, (x : E)) :=
    (hA.contDiffAt (hU.mem_nhds hx)).continuousAt
  have hcomp : ContinuousAt
      (fun z : P × sphere (0 : E) 1 => A (z.1, (z.2 : E))) (p, x) :=
    hAc.comp (f := fun z : P × sphere (0 : E) 1 => (z.1, (z.2 : E))) hemb.continuousAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hemb.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)] with z hz
  exact hmatch z.1 z.2 hz

end Problem340.SphereCompactSupport

end

end OAI
