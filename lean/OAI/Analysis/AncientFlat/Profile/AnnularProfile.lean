import OAI.Analysis.AncientFlat.Profile.CompactificationIdentity

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace ParabolicAnnular
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem profile_annular_holder (G H : ℝ → ℝ) (c κ α : ℝ)
    (hc : 0<c) (hκ : 0<κ) (hα : 0<α) (hα1 : α<1)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hH0 : H 0=c) (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    ∃ K : ℝ, 0<K ∧ HolderBound α outer (profilePrincipal (V := V) G) K ∧
      HolderBound α outer (fun p : V × ℝ => (profilePotential G p : ℂ)) K ∧
      ∀ p : V × ℝ, p∈outer → κ^2/16≤profilePrincipal G p := by
  have hHp : ∀ u∈Ici (0:ℝ), 0<H u := fun u hu =>
    compactification_pos G H c κ hc hκ hH0 hmatch hpos hu
  obtain ⟨K1,hK1,h1⟩ := compact_radial_holder (V := V) α hα hα1.le (compactPrincipal H)
    ((compactPrincipal_smooth H hH).of_le (by simp))
  obtain ⟨K2,hK2,h2⟩ := compact_radial_holder (V := V) α hα hα1.le (compactPotential H)
    (compactPotential_smooth H hH hHp)
  have he1 (p : V × ℝ) (hp : p∈outer) :
      profilePrincipal G p=compactPrincipal H (‖p.1‖,-p.2) := by
    exact (compactPrincipal_eq G H hmatch (by linarith [hp.1] : 0<‖p.1‖)
      (neg_pos.mpr hp.2.2.2)).symm
  have he2 (p : V × ℝ) (hp : p∈outer) :
      profilePotential G p=compactPotential H (‖p.1‖,-p.2) := by
    exact (compactPotential_eq G H hG hmatch (by linarith [hp.1] : 0<‖p.1‖)
      (neg_pos.mpr hp.2.2.2)).symm
  have ha : HolderBound α outer (profilePrincipal (V := V) G) K1 := by
    constructor
    · intro p hp; rw [he1 p hp]; exact h1.1 p hp
    · intro p hp q hq; rw [he1 p hp,he1 q hq]; exact h1.2 p hp q hq
  have hb : HolderBound α outer (fun p : V × ℝ => (profilePotential G p : ℂ)) K2 := by
    constructor
    · intro p hp
      dsimp only
      rw [he2 p hp,Complex.norm_real]
      exact h2.1 p hp
    · intro p hp q hq
      dsimp only
      rw [he2 p hp,he2 q hq,←Complex.ofReal_sub,Complex.norm_real]
      exact h2.2 p hp q hq
  refine ⟨K1+K2,by positivity,ha.mono (by linarith),hb.mono (by linarith),?_⟩
  intro p hp
  have hGp := hpos (‖p.1‖^2/Real.sqrt (-p.2)) (by positivity)
  dsimp [profilePrincipal]
  exact div_le_div_of_nonneg_right ((sq_le_sq₀ hκ.le (hκ.le.trans hGp)).mpr hGp) (by norm_num)
end ParabolicAnnular

end

end OAI
