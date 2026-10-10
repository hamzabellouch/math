import OAI.Dynamics.EntropyCounterexample.ClockLocalExtension

namespace OAI

noncomputable section

namespace Problem340

namespace HasLocalC1Extension

theorem precomp_ambient {X Y D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {eX : X → E} {eY : Y → D} {f : X → F}
    (hf : HasLocalC1Extension eX f) (k : Y → X) (K : D → E)
    (hK : ContDiff ℝ 1 K) (hcomm : ∀ y, eX (k y) = K (eY y)) :
    HasLocalC1Extension eY (f ∘ k) := by
  intro y
  obtain ⟨U, hU, hyU, F, hF, hcommF⟩ := hf (k y)
  refine ⟨K ⁻¹' U, hU.preimage hK.continuous, ?_, F ∘ K,
    hF.comp hK.contDiffOn (fun _ hx => hx), ?_⟩
  · simpa only [Set.mem_preimage, ← hcomm y] using hyU
  · intro z hz
    change f (k z) = F (K (eY z))
    rw [← hcomm z]
    apply hcommF
    simpa only [Set.mem_preimage, ← hcomm z] using hz

end HasLocalC1Extension

theorem HasLocalC1Extension.clock_coordinate {q : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : StandardClock → F}
    (hf : HasLocalC1Extension (fun x : StandardClock => x.1) f) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => f x.1) :=
  hf.precomp_ambient Prod.fst Prod.fst contDiff_fst (fun _ => rfl)

theorem HasLocalC1Extension.sphere_coordinate {q : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : StandardSphere2 → F}
    (hf : HasLocalC1Extension (fun x : StandardSphere2 => x.1) f)
    (i : Fin (q + 1)) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => f (x.2 i)) :=
  hf.precomp_ambient (fun x : CounterexampleManifold q => x.2 i)
    (fun x : CounterexampleAmbient q => x.2 i)
    ((contDiff_apply ℝ SphereAmbient i).comp contDiff_snd) (fun _ => rfl)

theorem hasLocalC1Extension_clock_coordinate (q : ℕ) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => x.1.1) :=
  .of_contDiffOn isOpen_univ (fun _ => Set.mem_univ _) Prod.fst
    contDiff_fst.contDiffOn (fun _ => rfl)

theorem hasLocalC1Extension_clock_update {q : ℕ}
    {h : CounterexampleManifold q → ℝ}
    (hh : HasLocalC1Extension (standardEmbedding q) h) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => (clockRotate (h x) x.1).1) :=
  (hh.prodMk (hasLocalC1Extension_clock_coordinate q)).comp_contDiff
    contDiff_ambientClockRotate

theorem hasLocalC1Extension_manifold_clock_lift {q : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : StandardClock → F)
    (hf : ContDiff ℝ 1 (fun t : ℝ => f (clockHomeomorph (t : AddCircle (100 : ℝ))))) :
    HasLocalC1Extension (standardEmbedding q)
      (fun x : CounterexampleManifold q => f x.1) :=
  (hasLocalC1Extension_of_clock_lift f hf).clock_coordinate

end Problem340

end

end OAI
