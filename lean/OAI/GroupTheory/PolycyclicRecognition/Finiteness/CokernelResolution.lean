import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CofiberResolution
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteCofiber

namespace OAI

/-! # A finite projective resolution for the cokernel in the cyclic extension -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2

variable {G : Type} [Group G] (S : ShortComplex (Rep ℤ G))
  (P : ProjectiveResolution S.X₁) (Q : ProjectiveResolution S.X₂)

abbrev cokernelResolutionMap := ProjectiveResolution.lift S.f P Q

def cokernelResolutionAugmentation : repCofiber (cokernelResolutionMap S P Q) ⟶
    (ChainComplex.single₀ (Rep ℤ G)).obj S.X₃ :=
  homotopyCofiber.desc (cokernelResolutionMap S P Q)
    (Q.π ≫ (ChainComplex.single₀ (Rep ℤ G)).map S.g) (Homotopy.ofEq (by
      rw [← Category.assoc, ProjectiveResolution.lift_commutes, Category.assoc,
        ← Functor.map_comp, S.zero, Functor.map_zero, comp_zero]))

theorem cokernelResolutionAugmentation_apply (x : (repCofiber
    (cokernelResolutionMap S P Q)).X 0) :
    ((cokernelResolutionAugmentation S P Q).f 0).hom x =
      S.g.hom ((Q.π.f 0).hom ((repCofiberSnd (cokernelResolutionMap S P Q) 0).hom x)) := by
  unfold cokernelResolutionAugmentation
  rw [homotopyCofiber.desc_f' _ _ _ 0 (by simp)]
  rfl

theorem cokernelResolutionAugmentation_surjective (hS : S.ShortExact) :
    Function.Surjective ((cokernelResolutionAugmentation S P Q).f 0).hom := by
  let := hS.epi_g
  intro c
  obtain ⟨b, rfl⟩ := ((Rep.epi_iff_surjective S.g).mp inferInstance) c
  obtain ⟨y, rfl⟩ := ((Rep.epi_iff_surjective (Q.π.f 0)).mp inferInstance) b
  refine ⟨(repCofiberInr (cokernelResolutionMap S P Q) 0).hom y, ?_⟩
  rw [cokernelResolutionAugmentation_apply, repCofiber_snd_inr]

theorem cokernelResolutionAugmentation_boundary (hS : S.ShortExact)
    (x : (repCofiber (cokernelResolutionMap S P Q)).X 0)
    (hx : ((cokernelResolutionAugmentation S P Q).f 0).hom x = 0) :
    ∃ y : (repCofiber (cokernelResolutionMap S P Q)).X 1,
      ((repCofiber (cokernelResolutionMap S P Q)).d 1 0).hom y = x := by
  let φ := cokernelResolutionMap S P Q
  rw [cokernelResolutionAugmentation_apply] at hx
  obtain ⟨a, ha⟩ := (rep_shortComplex_exact_iff S).mp hS.exact _ hx
  obtain ⟨a₀, ha₀⟩ := ((Rep.epi_iff_surjective (P.π.f 0)).mp inferInstance) a
  have hc := congrArg (fun f => f.hom a₀) (ProjectiveResolution.lift_commutes_zero S.f P Q)
  change (Q.π.f 0).hom ((φ.f 0).hom a₀) = S.f.hom ((P.π.f 0).hom a₀) at hc
  have hz : (Q.π.f 0).hom
      ((repCofiberSnd φ 0).hom x - (φ.f 0).hom a₀) = 0 := by
    rw [map_sub, hc, ha₀, ha, sub_self]
  obtain ⟨b, hb⟩ := (rep_shortComplex_exact_iff _).mp Q.exact₀ _ hz
  let y := (repCofiberInl φ 0).hom a₀ + (repCofiberInr φ 1).hom b
  refine ⟨y, repCofiber_ext_zero φ ?_⟩
  rw [repCofiber_snd_d]
  simp only [y, map_add, repCofiber_fst_inl, repCofiber_fst_inr,
    repCofiber_snd_inl, repCofiber_snd_inr, add_zero, zero_add]
  rw [hb]
  abel

theorem cokernelResolutionAugmentation_quasiIso (hS : S.ShortExact) :
    QuasiIso (cokernelResolutionAugmentation S P Q) where
  quasiIsoAt i := by
    cases i with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff,
          ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl) rfl rfl]
        constructor
        · exact (rep_shortComplex_exact_iff _).mpr
            (cokernelResolutionAugmentation_boundary S P Q hS)
        · rw [Rep.epi_iff_surjective]
          exact cokernelResolutionAugmentation_surjective S P Q hS
    | succ i =>
        rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
        let := hS.mono_f
        exact repCofiber_exactAt_of_mono P Q (cokernelResolutionMap S P Q) S.f
          (ProjectiveResolution.lift_commutes_zero S.f P Q) i

def cokernelProjectiveResolution (hS : S.ShortExact) : ProjectiveResolution S.X₃ where
  complex := repCofiber (cokernelResolutionMap S P Q)
  π := cokernelResolutionAugmentation S P Q
  quasiIso := cokernelResolutionAugmentation_quasiIso S P Q hS

end PolycyclicRecognition

end

end OAI
