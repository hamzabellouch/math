import OAI.MeasureTheory.Falconer.Measures.BudgetedEndpointProduct

namespace OAI

/-! The two-scale induction step uses the actual coarse and local packets,
then lifts both selected point sets back to the original reference profile. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem profileEndpointBound_split {N B K : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (f : CellPath 2 → List ℕ) (p : CellPath 2)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {s W A D : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hW : 1 ≤ W) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hleft : ProfileEndpointBound N B K L f p Q i k s
      (profileStepBudget (4*(N+2)+11:ℕ) ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) W) A)
    (hright : ProfileEndpointBound N B K L f p Q k j s
      (profileStepBudget (4*(N+2)+11:ℕ) ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) W) D) :
    ProfileEndpointBound N B K L f p Q i j s W (A*D/(43264*((4*(N+2)+11:ℕ):ℝ)^4)) := by
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K
  let W' := profileStepBudget H G W
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hG : 1 ≤ G := profile_label_cost_one_le B K
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hU : profileStepBudget H 1 W ≤ W' := by
    dsimp [W',profileStepBudget]
    gcongr
  obtain ⟨_,_,_,_,_,hcoarseCost,hfineCost⟩ := profile_step_budget_bounds hH hG hW
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  have hSN : S ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL'
  obtain ⟨R,hRD,hR,hRcount,m₀,hm₀,U,hUdata,hcells⟩ :=
    quarter_endpoint_budgeted_scale_product (blockDepth_antitone N B hki)
      (blockDepth_antitone N B hjk) Q hQ S hSN (Nat.sub_le _ _) p₀ hp₀ hs hs1 hW hm V hV
  have hcoarseBudget : (W*(2:ℝ)^(2*i))*
      (((20*H^2)*(2:ℝ)^k)*((2*B+1:ℕ):ℝ)^K) ≤ W' := by
    exact (profile_retention_cost_le hW0 (by positivity) hi (hki.trans hi) B).trans hcoarseCost
  have hleftValue : A ≤ ((R.biUnion U).card:ℝ)/m₀ :=
    profileEndpointBound_retained_subset hL hL' f g p q Q hQ hki hi r₀ hsub
      hW0 (by positivity) hm₀ hmass ha₀ p₀ hp₀ R hR hRD hRcount hcoarseBudget hU hleft U hUdata
  obtain ⟨z,hz⟩ := hR
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp (hRD hz)
  have hrR : quarterEndpointPoint Q (blockDepth N B i) p₀ r ∈ R := by rw [he]; exact hz
  obtain ⟨P',hPsub,hP,hPcount,m₁,hm₁,T,hT,hproduct⟩ := hcells r hr hrR
  have hfineBudget : (W*(2:ℝ)^(2*k))*
      (((16*W*H^3)*(2:ℝ)^j)*((2*B+1:ℕ):ℝ)^K) ≤ W' := by
    exact (profile_retention_cost_le hW0 (by positivity) (hki.trans hi)
      (hjk.trans (hki.trans hi)) B).trans hfineCost
  have hrightValue : D ≤ ((P'.biUnion T).card:ℝ)/m₁ :=
    profileEndpointBound_retained_subset hL hL' f g p q Q hQ hjk (hki.trans hi) r₀ hsub
      hW0 (by positivity) hm₁ hmass (ha₀.trans (blockDepth_antitone N B hki)) r
      (prefixChildren_mem_image hr) P' hP hPsub hPcount hfineBudget hU hright T hT
  apply (div_le_iff₀ (show 0 < 43264*H^4 by positivity)).2
  calc
    A*D ≤ (((R.biUnion U).card:ℝ)/m₀)*(((P'.biUnion T).card:ℝ)/m₁) :=
      mul_le_mul hleftValue hrightValue hD (hA.trans hleftValue)
    _ ≤ (43264*H^4)*(((Z.biUnion V).card:ℝ)/m) := hproduct
    _ = _ := mul_comm _ _

end Falconer

end OAI
