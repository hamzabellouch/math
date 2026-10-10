import OAI.Dynamics.EntropyCounterexample.Embedding
import OAI.Dynamics.EntropyCounterexample.SphereTranslation

namespace OAI

noncomputable section

namespace Problem340.TranslationC1

def HasLocalExtension (q : ℕ) (C : CounterexampleManifold q → ℂ) : Prop :=
  ∀ x : CounterexampleManifold q,
    ∃ U : Set (CounterexampleAmbient q),
      IsOpen U ∧ standardEmbedding q x ∈ U ∧
        ∃ F : CounterexampleAmbient q → ℂ,
          ContDiffOn ℝ 1 F U ∧
            ∀ y : CounterexampleManifold q,
              standardEmbedding q y ∈ U → C y = F (standardEmbedding q y)

def translateCoordinate {q : ℕ} (i : Fin (q + 1))
    (C : CounterexampleManifold q → ℂ)
    (f : CounterexampleManifold q → CounterexampleManifold q) :
    CounterexampleManifold q → CounterexampleManifold q :=
  fun y => ((f y).1, fun j => if j = i then
    SphereTranslation.translate (C y) ((f y).2 j) else (f y).2 j)

theorem isC1SelfMap_translateCoordinate {q : ℕ} (i : Fin (q + 1))
    {C : CounterexampleManifold q → ℂ}
    {f : CounterexampleManifold q → CounterexampleManifold q}
    (hC : HasLocalExtension q C) (hf : IsC1SelfMap q f) :
    IsC1SelfMap q (translateCoordinate i C f) := by
  have hlocal : ∀ x : CounterexampleManifold q,
      ∃ U : Set (CounterexampleAmbient q),
        IsOpen U ∧ standardEmbedding q x ∈ U ∧
          ∃ F : CounterexampleAmbient q → CounterexampleAmbient q,
            ContDiffOn ℝ 1 F U ∧
              ∀ y : CounterexampleManifold q,
                standardEmbedding q y ∈ U →
                  standardEmbedding q (translateCoordinate i C f y) = F (standardEmbedding q y) := by
    intro x
    obtain ⟨U, hU, hxU, F, hF, heF⟩ := hf.2 x
    obtain ⟨V, hV, hxV, D, hD, heD⟩ := hC x
    let W := U ∩ V
    let H : CounterexampleAmbient q → ℂ × SphereAmbient :=
      fun a => (D a, (F a).2 i)
    have hFW : ContDiffOn ℝ 1 F W := hF.mono Set.inter_subset_left
    have hDW : ContDiffOn ℝ 1 D W := hD.mono Set.inter_subset_right
    have hH : ContDiffOn ℝ 1 H W :=
      hDW.prodMk (contDiffOn_pi.mp hFW.snd i)
    let O := W ∩ H ⁻¹' SphereTranslation.domain
    have hO : IsOpen O :=
      hH.continuousOn.isOpen_inter_preimage (hU.inter hV) SphereTranslation.isOpen_domain
    have hxO : standardEmbedding q x ∈ O := by
      refine ⟨⟨hxU, hxV⟩, ?_⟩
      change SphereTranslation.denom (D (standardEmbedding q x))
        ((F (standardEmbedding q x)).2 i) ≠ 0
      rw [← heD x hxV, ← heF x hxU]
      exact ne_of_gt (SphereTranslation.denom_pos (C x) ((f x).2 i))
    let G : CounterexampleAmbient q → CounterexampleAmbient q :=
      fun a => ((F a).1, fun j => if j = i then
        SphereTranslation.ambient (D a) ((F a).2 j) else (F a).2 j)
    have hFO : ContDiffOn ℝ 1 F O := hFW.mono Set.inter_subset_left
    have hG : ContDiffOn ℝ 1 G O := by
      apply hFO.fst.prodMk
      apply contDiffOn_pi.mpr
      intro j
      by_cases hji : j = i
      · subst j
        simpa only [ite_true, H, O, Function.comp_def] using
          (SphereTranslation.contDiffOn_ambient 1).comp_inter hH
      · simp only [ite_eq_right hji]
        exact contDiffOn_pi.mp hFO.snd j
    refine ⟨O, hO, hxO, G, hG, ?_⟩
    intro y hy
    have hyU : standardEmbedding q y ∈ U := hy.1.1
    have hyV : standardEmbedding q y ∈ V := hy.1.2
    have hfy := heF y hyU
    have hcy := heD y hyV
    apply Prod.ext
    · change (standardEmbedding q (f y)).1 = (F (standardEmbedding q y)).1
      exact congrArg (fun a : CounterexampleAmbient q => a.1) hfy
    · funext j
      by_cases hji : j = i
      · simp only [standardEmbedding, translateCoordinate, G, ite_eq_left hji,
          SphereTranslation.translate]
        exact congrArg₂ SphereTranslation.ambient hcy
          (congrArg (fun a : CounterexampleAmbient q => a.2 j) hfy)
      · simp only [standardEmbedding, translateCoordinate, G, ite_eq_right hji]
        exact congrArg (fun a : CounterexampleAmbient q => a.2 j) hfy
  exact ⟨continuous_of_local_contDiff_extension _ hlocal, hlocal⟩

theorem hasLocalExtension_of_contDiff {q : ℕ}
    (D : CounterexampleAmbient q → ℂ) (hD : ContDiff ℝ 1 D) :
    HasLocalExtension q (fun y => D (standardEmbedding q y)) := by
  intro x
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, D, hD.contDiffOn,
    fun _ _ => rfl⟩

theorem isC1SelfMap_translateCoordinate_of_contDiff {q : ℕ}
    (i : Fin (q + 1)) (D : CounterexampleAmbient q → ℂ)
    (hD : ContDiff ℝ 1 D)
    {f : CounterexampleManifold q → CounterexampleManifold q}
    (hf : IsC1SelfMap q f) :
    IsC1SelfMap q (translateCoordinate i (fun y => D (standardEmbedding q y)) f) :=
  isC1SelfMap_translateCoordinate i (hasLocalExtension_of_contDiff D hD) hf

end Problem340.TranslationC1

end

end OAI
