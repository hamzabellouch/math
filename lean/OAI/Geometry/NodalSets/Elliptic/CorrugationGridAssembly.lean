import OAI.Geometry.NodalSets.Elliptic.CorrugationCubePartition

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

def corrugationGridSum (o : Coord) (L : ℝ) (n : ℕ) (χ : Coord → ℝ) (amp J : ℝ)
    (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → Coord ≃L[ℝ] Coord) : Coord → ℝ :=
  corrugationSum Finset.univ χ amp J (L/(n:ℝ)) s e (corrugationCubeCenter o L n)

lemma corrugationGridSum_smooth (o : Coord) (L : ℝ) (n : ℕ) (χ : Coord → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (amp J : ℝ)
    (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → Coord ≃L[ℝ] Coord) :
    ContDiff ℝ ∞ (corrugationGridSum o L n χ amp J s e) :=
  corrugationSum_smooth _ χ hχ _ _ _ _ _ _

lemma corrugationGridSum_support (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (χ : Coord → ℝ) (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (amp J : ℝ) (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → Coord ≃L[ℝ] Coord) :
    HasCompactSupport (corrugationGridSum o L n χ amp J s e) ∧
    tsupport (corrugationGridSum o L n χ amp J s e) ⊆ interior (Icc o (fun i ↦ o i+L)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨corrugationSum_compact _ χ hχ _ _ (div_pos hL hnR) _ _ _,?_⟩
  exact corrugationSum_support _ χ hχ _ _ (div_pos hL hnR) _ _ _ _
    (fun k _ ↦ corrugationCube_ball_inside o hL hn k)

lemma corrugationGridSum_collar (o : Coord) {L : ℝ} (hL : 0 < L)
    {n : ℕ} (hn : 0 < n) (χ : Coord → ℝ) (hχ : tsupport χ ⊆ ball (0:Coord) (1/2))
    (amp J : ℝ) (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → Coord ≃L[ℝ] Coord)
    (x : Coord) (hx : x ∉ interior (Icc o (fun i ↦ o i+L))) :
    corrugationGridSum o L n χ amp J s e =ᶠ[𝓝 x] 0 :=
  notMem_tsupport_iff_eventuallyEq.mp
    (fun h ↦ hx ((corrugationGridSum_support o hL hn χ hχ amp J s e).2 h))

theorem corrugationGridSum_uniform_bound (amp : ℝ) : ∃ B : ℝ, 0 < B ∧
    ∀ (o : Coord) (L : ℝ) (n : ℕ), 0 < L → 0 < n →
    ∀ (χ : Coord → ℝ), tsupport χ ⊆ ball (0:Coord) (1/2) → (∀ z, |χ z| ≤ 1) →
    ∀ (J M : ℝ), 0 < J → 0 ≤ M →
    ∀ (s : (Fin 4 → Fin n) → ℝ) (e : (Fin 4 → Fin n) → Coord ≃L[ℝ] Coord),
    (∀ k, 0 ≤ s k ∧ s k ≤ M) → ∀ x,
    |corrugationGridSum o L n χ amp J s e x| ≤ M/J*B := by
  obtain ⟨B,hB,hf⟩ := corrugationPeriodicWell_bounded amp
  refine ⟨B,hB,?_⟩
  intro o L n hL hn χ hχ hχb J M hJ hM s e hs x
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hR := div_pos hL hnR
  apply finite_disjoint_sum_bound Finset.univ _ (B := M/J*B) _ (by positivity) _ x
  · intro i _ j _ hij
    exact (corrugationCube_balls_disjoint o hL hn i j hij).mono
      (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _)
      (localizedCorrugation_cube χ _ hχ _ _ hR _ _ _)
  · intro i _ z
    exact (localizedCorrugation_bound χ _ hχb hf (hs i).1 hJ _ _ _ _ z).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hs i).2 hJ.le) hB.le)

end
end Yau.Geometry

end OAI
