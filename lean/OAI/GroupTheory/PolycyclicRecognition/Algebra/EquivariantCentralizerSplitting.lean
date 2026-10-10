import OAI.GroupTheory.PolycyclicRecognition.Algebra.CentralizerExtensionSplitting

namespace OAI

/-! # Equivariance of the uniquely selected centralizing lifts -/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]

theorem centralizerSplitting_mem (E : GroupExtension N G Q) (t : G)
    (ht : ∀ q : Q, Commute (E.rightHom t) q)
    (hLang : Function.Bijective (extensionLangMap E t)) (q : Q) :
    centralizerSplitting E t ht hLang q ∈ Subgroup.centralizer ({t} : Set G) := by
  let e : Subgroup.centralizer ({t} : Set G) ≃* Q :=
    MulEquiv.ofBijective (centralizerProjection E t)
      ⟨centralizerProjection_injective E t hLang.1,
        centralizerProjection_surjective E t ht hLang.2⟩
  change ((e.symm q : Subgroup.centralizer ({t} : Set G)) : G) ∈ _
  exact (e.symm q).property

theorem centralizerSplitting_fixed (E : GroupExtension N G Q) (t : G)
    (ht : ∀ q : Q, Commute (E.rightHom t) q)
    (hLang : Function.Bijective (extensionLangMap E t))
    (f : G →* G) (hft : f t = t) (hfQ : ∀ g, E.rightHom (f g) = E.rightHom g)
    (q : Q) : f (centralizerSplitting E t ht hLang q) = centralizerSplitting E t ht hLang q := by
  let s := centralizerSplitting E t ht hLang
  have hs : s q ∈ Subgroup.centralizer ({t} : Set G) := centralizerSplitting_mem E t ht hLang q
  have hfs : f (s q) ∈ Subgroup.centralizer ({t} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have hh := congrArg f (Subgroup.mem_centralizer_singleton_iff.mp hs)
    simpa only [map_mul, hft] using hh
  have he := centralizerProjection_injective E t hLang.1
    (a₁ := ⟨f (s q), hfs⟩) (a₂ := ⟨s q, hs⟩) (hfQ (s q))
  exact congrArg Subtype.val he

end PolycyclicRecognition

end

end OAI
