import OAI.MeasureTheory.Falconer.Recursion.ParentProfileBounds
import OAI.MeasureTheory.Falconer.Incidence.NormalProfileIncidence
import OAI.MeasureTheory.Falconer.Geometry.EndpointMidscaleCover
import OAI.MeasureTheory.Falconer.Geometry.FullChartRegularGain
import OAI.MeasureTheory.Falconer.Geometry.QuarterCoarseCover

namespace OAI

/-! Normal and good interval bounds in the fixed chart of the recursive
endpoint construction. Retention is measured inside the active parent. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

section Parent
variable {N a₀ : ℕ} (hN : 0 < N)
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha₀ : a₀ ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))

include hN hL hL' hsub hM hmass hQ hji hi ha₀ hp₀ in
theorem blockClass_parent_quarter_normal_ratio {s A KL : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    let D := blockDepth N B j-blockDepth N B i+2
    let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(M*(2:ℝ)^(2*i+2*j))
    let H := max 1 (max KL ((max 1 C)*4^s))
    ∀ m R : ℝ, 0 < m → ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ Z, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
        InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^D) s KL (T x) ∧
        ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^D) x l) →
      (1/(2:ℝ)^D)^(-s) ≤
        (R*H*80^s*(1+H*planarCriticalConstant D s))*(((Z.biUnion T).card:ℝ)/m) := by
  obtain ⟨hne,_,_,_,hball⟩ := blockClass_parent_endpoint_ball hN hL hL' B f g K p q r₀
    hsub hM hmass Q hQ hji hi ha₀ hp₀ hs hA hprofile
  have hquarter := hne.image planarQuarter
  rw [← quarterEndpointSet_eq] at hquarter
  have hchart := (quarterEndpointSet_geometry Q hQ
    (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
    ((Finset.filter_subset _ _).trans hL') (blockDepth_antitone N B hji)
    (Nat.sub_le _ _) p₀).2.1
  dsimp only
  intro m R hm T hT
  apply planar_critical_normalized_ratio _ hs (le_max_left _ _) hm _ T hquarter
  · intro x hx
    exact ⟨(hchart x hx).1.trans (by norm_num),(hchart x hx).2.trans (by norm_num)⟩
  · exact normalizedFiniteBallBound_mono_constant (by positivity)
      ((le_max_right _ _).trans (le_max_right _ _)) hball
  · intro x hx
    obtain ⟨hlo,hhi,hch,hb,hinc⟩ := hT x hx
    exact ⟨hlo,hhi,hch,normalizedFiniteBallBound_mono_constant (by positivity)
      ((le_max_left _ _).trans (le_max_right _ _)) hb,hinc⟩

include hN hL hsub hQ hji hi hp₀ in
theorem blockClass_parent_quarter_midscale_cover {n : ℕ} (hn : 3 ≤ n)
    (hlen : blockDepth N B j-blockDepth N B i = 2*n) {t A : ℝ} (ht : 0 ≤ t)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    ((Z.image (coarsePlanarRound (1/(2:ℝ)^((n+1)+3)))).card:ℝ) ≤
      (25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))))/(1/(2:ℝ)^(n+1))^t := by
  have hc := blockClass_retained_midscale_cover hN hL B f g K p q
    (hsub.trans (Finset.filter_subset _ _)) Q hQ hji hi hp₀ hn hlen ht hprofile
  dsimp only
  rw [quarterEndpointSet_eq]
  have he : 1/(2:ℝ)^((n+1)+3) = (1/(2:ℝ)^(n+3))/2 := by
    rw [show (n+1)+3 = (n+3)+1 by omega,pow_succ]; ring
  rw [he]
  calc
    _ ≤ 25*((blockEndpointSet Q _ _ _ p₀ |>.image
        (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) :=
      planarQuarter_coarse_cover (by positivity) _
    _ ≤ 25*((49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A)))/(1/(2:ℝ)^n)^t) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ ≤ _ := by
      simp only [← mul_div_assoc]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply Real.rpow_le_rpow (by positivity) _ ht
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)

end Parent

theorem blockClass_parent_quarter_good_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s t m : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 0 < m →
    ∀ N a₀ : ℕ, 0 < N → ∀ L L' : Finset (CellPath 2),
      L ⊆ cubePaths 2 N → L' ⊆ cubePaths 2 N →
    ∀ (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2),
      classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
        prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀ →
    ∀ M : ℝ, 0 ≤ M →
      ((prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
        a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ) →
    ∀ Q : DyadicCube 2, Q.side = 1 → ∀ i j : ℕ, j ≤ i → i ≤ K → a₀ ≤ blockDepth N B i →
    ∀ p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)), blockDepth N B j-blockDepth N B i = 2*n →
    ∀ A : ℝ, 0 ≤ A →
      (∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
        let v := (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))
        t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤ v ∧
          v ≤ t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) →
      let E := Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2)
      (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
        (M*(2:ℝ)^(2*i+2*j))))*4^t ≤ E →
      25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))) ≤ E →
      let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
      let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
      let δ := 1/(2:ℝ)^(2*n+2)
      ∀ V : Space 2 → Finset (Space 2),
        (∀ z ∈ Z, m ≤ ((V z).card:ℝ) ∧ ((V z).card:ℝ) ≤ E*m ∧
          InBoundedLineChart (V z) ∧ FiniteSeparatedAt δ (V z) ∧
          NormalizedFiniteBallBound δ s E (V z) ∧ ∀ l ∈ V z, TubeIncident δ z l) →
        ¬ ((Z.biUnion V).card:ℝ) ≤ m/δ^(s+η) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgain⟩ := full_chart_regular_fine_gain hκ hκ1
  refine ⟨ε,η,max N0 6,hε,hε1,hη,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro n hn s t m hs hs1 hgap ht hm N a₀ hN L L' hL hL' B f g K p q r₀ hsub
    M hM hmass Q hQ i j hji hi ha₀ p₀ hp₀ hlen A hA hprofile
  dsimp only
  intro hpointBudget hcoverBudget V hV
  have hn3 : 3 ≤ n := by have := (le_max_right N0 6).trans hn; omega
  have ht0 : 0 ≤ t := by linarith only [hκ,hs,hgap]
  obtain ⟨hne,_,_,_,hball⟩ := blockClass_parent_endpoint_ball hN hL hL' B f g K p q r₀
    hsub hM hmass Q hQ hji hi ha₀ hp₀ ht0 hA (fun k hjk hki => (hprofile k hjk hki).1)
  have hquarter := hne.image planarQuarter
  rw [← quarterEndpointSet_eq] at hquarter
  obtain ⟨_,hchart,hsep⟩ := quarterEndpointSet_geometry Q hQ
    (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
    ((Finset.filter_subset _ _).trans hL') (blockDepth_antitone N B hji) (Nat.sub_le _ _) p₀
  have hcover := blockClass_parent_quarter_midscale_cover hN hL B f g K p q r₀ hsub
    Q hQ hji hi hp₀ hn3 hlen ht0 (fun k hjk hki => (hprofile k hjk hki).2)
  rw [hlen] at hball hsep
  have he : 2*(n+1) = 2*n+2 := by omega
  have hh := hgain (n+1) (by simpa only [Nat.add_assoc] using (le_max_left N0 6).trans hn)
    s t m hs hs1 hgap ht hm _ hquarter
    (fun x hx => ⟨(hchart x hx).1.trans (by norm_num),(hchart x hx).2.trans (by norm_num)⟩)
  rw [he] at hh
  apply hh hsep
  · exact normalizedFiniteBallBound_mono_constant (by positivity) hpointBudget hball
  · exact hcover.trans (div_le_div_of_nonneg_right hcoverBudget (by positivity))
  · simpa only [Nat.add_assoc] using hV

end Falconer

end OAI
