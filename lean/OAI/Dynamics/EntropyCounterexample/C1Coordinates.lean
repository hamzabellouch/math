import OAI.Dynamics.EntropyCounterexample.Embedding

namespace OAI

noncomputable section

namespace Problem340

def HasLocalC1Extension {X E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : X → E) (f : X → F) : Prop :=
  ∀ x, ∃ U : Set E, IsOpen U ∧ e x ∈ U ∧
    ∃ F : E → F, ContDiffOn ℝ 1 F U ∧ ∀ y, e y ∈ U → f y = F (e y)

namespace HasLocalC1Extension

variable {X E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {e : X → E} {f : X → F} {g : X → G}

theorem prodMk (hf : HasLocalC1Extension e f) (hg : HasLocalC1Extension e g) :
    HasLocalC1Extension e (fun x => (f x, g x)) := by
  intro x
  obtain ⟨U, hU, hxU, F, hF, hcommF⟩ := hf x
  obtain ⟨V, hV, hxV, G, hG, hcommG⟩ := hg x
  refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun z => (F z, G z),
    (hF.mono Set.inter_subset_left).prodMk (hG.mono Set.inter_subset_right), ?_⟩
  intro y hy
  exact Prod.ext (hcommF y hy.1) (hcommG y hy.2)

theorem pi {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {f : X → ∀ i, F i} (hf : ∀ i, HasLocalC1Extension e (fun x => f x i)) :
    HasLocalC1Extension e f := by
  intro x
  choose U hU hxU F hF hcomm using fun i => hf i x
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hxU,
    fun z i => F i z, contDiffOn_pi.mpr (fun i => (hF i).mono (Set.iInter_subset U i)), ?_⟩
  intro y hy
  funext i
  exact hcomm i y (Set.mem_iInter.mp hy i)

theorem of_contDiffOn {U : Set E} (hU : IsOpen U)
    (he : ∀ x, e x ∈ U) (F : E → F) (hF : ContDiffOn ℝ 1 F U)
    (hcomm : ∀ x, f x = F (e x)) : HasLocalC1Extension e f :=
  fun x => ⟨U, hU, he x, F, hF, fun y _ => hcomm y⟩

theorem comp_contDiff (hf : HasLocalC1Extension e f) {g : F → G}
    (hg : ContDiff ℝ 1 g) : HasLocalC1Extension e (g ∘ f) := by
  intro x
  obtain ⟨U, hU, hxU, F, hF, hcomm⟩ := hf x
  refine ⟨U, hU, hxU, g ∘ F, hg.comp_contDiffOn hF, ?_⟩
  intro y hy
  change g (f y) = g (F (e y))
  rw [hcomm y hy]

end HasLocalC1Extension

theorem isC1SelfMap_iff_hasLocalC1Extension {q : ℕ}
    {f : CounterexampleManifold q → CounterexampleManifold q} :
    IsC1SelfMap q f ↔
      HasLocalC1Extension (standardEmbedding q) (standardEmbedding q ∘ f) := by
  constructor
  · exact fun hf => hf.2
  · intro hf
    exact ⟨continuous_of_local_contDiff_extension f hf, hf⟩

theorem isC1SelfMap_of_coordinate_extensions {q : ℕ}
    {f : CounterexampleManifold q → CounterexampleManifold q}
    (hclock : HasLocalC1Extension (standardEmbedding q) (fun x => (f x).1.1))
    (hsphere : ∀ i, HasLocalC1Extension (standardEmbedding q) (fun x => ((f x).2 i).1)) :
    IsC1SelfMap q f :=
  isC1SelfMap_iff_hasLocalC1Extension.mpr (hclock.prodMk (.pi hsphere))

theorem isC1SelfMap_of_contDiffOn {q : ℕ}
    {f : CounterexampleManifold q → CounterexampleManifold q}
    {U : Set (CounterexampleAmbient q)} (hU : IsOpen U)
    (he : ∀ x, standardEmbedding q x ∈ U)
    (F : CounterexampleAmbient q → CounterexampleAmbient q)
    (hF : ContDiffOn ℝ 1 F U)
    (hcomm : ∀ y, standardEmbedding q (f y) = F (standardEmbedding q y)) :
    IsC1SelfMap q f :=
  isC1SelfMap_iff_hasLocalC1Extension.mpr
    (.of_contDiffOn hU he F hF hcomm)

end Problem340

end

end OAI
