import OAI.MeasureTheory.Falconer.Recursion.RetainedProfileBounds
import OAI.MeasureTheory.Falconer.Incidence.CriticalPencilIncidence

namespace OAI

/-! The normal-interval factor in the multiscale product, evaluated on the
actual retained endpoint configuration. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem planar_critical_normalized_ratio (N : ℕ) {s K m R : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (1/(2:ℝ)^N)^(-s) ≤
      (R*K*80^s*(1+K*planarCriticalConstant N s))*(((P.biUnion T).card:ℝ)/m) := by
  have hh := planar_critical_normalized_incidence N hs hK hm P T hP hPchart hPball hT
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le] at hh
  rw [← mul_div_assoc,Real.rpow_neg hδ.le]
  apply (le_div_iff₀ hm).2
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hδ s)).2
  convert hh using 1; ring

theorem blockClass_retained_normal_ratio {N : ℕ} (hN : 0 < N)
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    {s A KL : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    let H := max 1 (max KL
      ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(M*(2:ℝ)^(2*i+2*j))))
    ∀ m R : ℝ, 0 < m → ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ Z, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
        InBoundedLineChart (T x) ∧
        NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) s KL (T x) ∧
        ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) x l) →
      (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i))^(-s) ≤
        (R*H*80^s*(1+H*planarCriticalConstant (blockDepth N B j-blockDepth N B i) s))*
          (((Z.biUnion T).card:ℝ)/m) := by
  obtain ⟨hne,hchart,_,hball⟩ := blockClass_retained_endpoint_ball hL hL' B f g K p q
    hsub hM hmass Q hQ hji hi hp₀ hN hs hA hprofile
  dsimp only
  intro m R hm T hT
  apply planar_critical_normalized_ratio _ hs (le_max_left _ _) hm _ T hne hchart
  · exact normalizedFiniteBallBound_mono_constant (by positivity)
      ((le_max_right _ _).trans (le_max_right _ _)) hball
  · intro x hx
    obtain ⟨hlo,hhi,hch,hb,hinc⟩ := hT x hx
    exact ⟨hlo,hhi,hch,normalizedFiniteBallBound_mono_constant (by positivity)
      ((le_max_left _ _).trans (le_max_right _ _)) hb,hinc⟩

end Falconer

end OAI
