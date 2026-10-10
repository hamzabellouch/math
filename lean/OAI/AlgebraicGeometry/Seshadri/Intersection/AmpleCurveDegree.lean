import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Intersection.CurvePowerDegree
import OAI.AlgebraicGeometry.Seshadri.Intersection.CurveDegreePositive

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MaximalSeshadri.Projective MaximalSeshadri.Frames MaximalSeshadri.SectionOpens

variable {X : Scheme.{0}}

lemma section_ne_zero_of_mem_isoOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (x : X) (hx : x ∈ isoOpen s) : s ≠ 0 := by
  obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
  have hm : (⟨x,hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ isoOpen s := hx
  rw [preimage_isoOpen s U.ι e] at hm
  intro hz
  subst s
  rw [restrictSection_zero,coefficient_zero (X := U.toScheme) e,
    Scheme.basicOpen_zero] at hm
  exact hm

lemma exists_proper_nonempty_open [IsIntegral X] (hd : topologicalKrullDim X = 1) :
    ∃ (U : X.Opens) (x : X), x ∈ U ∧ U ≠ ⊤ := by
  have ht : Nontrivial X := by
    by_contra hn
    let : Subsingleton X := not_nontrivial_iff_subsingleton.mp hn
    have hh := topologicalKrullDim_zero_of_discreteTopology X
    rw [hd] at hh
    norm_num at hh
  let := ht
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  obtain ⟨U,hU,hxyU⟩ := exists_isOpen_xor_mem hxy
  rcases hxyU with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · refine ⟨⟨U,hU⟩,x,hx,?_⟩
    intro hh
    have : y ∈ (⟨U,hU⟩ : X.Opens) := by rw [hh]; trivial
    exact hy this
  · refine ⟨⟨U,hU⟩,y,hx,?_⟩
    intro hh
    have : x ∈ (⟨U,hU⟩ : X.Opens) := by rw [hh]; trivial
    exact hy this

variable [IsIntegral X] [IsNoetherian X]
variable {σ : Type} [Fintype σ]
variable (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {A : X.Modules}
    (a : σ → (O X ⟶ A)) (ha : (⨆ i, isoOpen (a i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism (baseScalars p) a ha)]
include hd a ha

theorem ample_curve_positive_effective_power (L : LineBundle X) (hL : L.IsAmple) :
    ∃ (m : ℕ) (s : O X ⟶ (L.pow m).sheaf), 0 < m ∧ s ≠ 0 ∧
      0 < eulerCharacteristic p 1 (L.pow m).sheaf - eulerCharacteristic p 1 (O X) := by
  obtain ⟨U,x,hx,hU⟩ := exists_proper_nonempty_open hd
  obtain ⟨m,hm,s,hxs,hle,haff⟩ := hL x U hx
  have hs : s ≠ 0 := section_ne_zero_of_mem_isoOpen (L.pow m) s x hxs
  refine ⟨m,s,hm,hs,projective_section_positive_degree p hd a ha (L.pow m) s hs ?_⟩
  intro hz
  apply hU
  exact top_unique (hz ▸ hle)

theorem ample_curve_degree_positive_and_powers (L : LineBundle X) (hL : L.IsAmple) :
    0 < eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X) ∧
      ∀ n : ℕ, eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (O X) =
        (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (O X)) := by
  obtain ⟨m,s,hm,hs,hdeg⟩ := ample_curve_positive_effective_power p hd a ha L hL
  have hp := projective_power_euler_of_positive_effective_power p hd a ha L m s hs hdeg
  refine ⟨?_,hp⟩
  rw [hp] at hdeg
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  nlinarith

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
