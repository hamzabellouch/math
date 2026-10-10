import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.TwoRpowNMul
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFixedSpatialTerm

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
namespace Attempt4FullFar
open MeasureTheory Set Metric Filter Real GraphSourceScale
open scoped ContDiff RealInnerProductSpace

lemma graph_source_fixed_geometry (N a p v sig : ℝ) (G c₀ : ℝ)
    (_hc₀ : 0 < c₀) :
    let R := (2:ℝ)^N
    let H := (2:ℝ)^(p-a)
    let V := (2:ℝ)^(v-p)
    let δ := min c₀ (H⁻¹*R^(10*sig))
    let τ := (2:ℝ)^(-p)*R^(30*sig)
    let D := G*(2:ℝ)^(-a)
    ((2:ℝ)^v*τ=V*R^(30*sig)) ∧
    (D/τ=G*H*R^(-30*sig)) ∧
    (δ=min c₀ ((2:ℝ)^a/(2:ℝ)^p*R^(10*sig))) := by
  dsimp only
  have ht : 0 < (2:ℝ)^N := by positivity
  constructor
  · rw [←mul_assoc,←Real.rpow_add (by norm_num)]; congr 2
  constructor
  · rw [div_eq_mul_inv,mul_inv_rev,←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),neg_neg,
      ←Real.rpow_neg ht.le]
    rw [show G*(2:ℝ)^(-a)*(((2:ℝ)^N)^(-(30*sig))*(2:ℝ)^p) =
      G*((2:ℝ)^p*(2:ℝ)^(-a))*((2:ℝ)^N)^(-30*sig) by ring_nf]
    rw [←Real.rpow_add (by norm_num)]; congr 2
  · rw [←Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),neg_sub,
      Real.rpow_sub (by norm_num)]

theorem graph_source_fixed_nonedge_decay
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {sig c₀ Ccap G : ℝ} (hsig : 0 < sig) (hc₀ : 0 < c₀)
    (hCcap : 0 ≤ Ccap) (hG : 0 ≤ G) (T : ℝ) :
    ∃ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ (a p v L : ℝ), p-a ≤ v-p+2*sig*N → L ≤ v-p+2*sig*N → 0 ≤ v-p →
    let R := (2:ℝ)^N
    let δ := min c₀ (((2:ℝ)^(p-a))⁻¹*R^(10*sig))
    let τ := (2:ℝ)^(-p)*R^(30*sig)
    let A := 1+R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))+δ⁻¹
    ∀ (Ψ : ℝ → ℂ) (w₁ w₂ d₁ d₂ e₁ e₂ : V) (K B₁ B₂ : ℝ) (b₁ b₂ : V → ℂ),
    ContDiff ℝ ∞ Ψ → tsupport Ψ ⊆ Icc (1/4:ℝ) 4 →
    (∫ u : ℝ, ‖Ψ u‖) ≤ K → (∀ u, ‖iteratedDeriv m Ψ u‖ ≤ K) →
    ‖w₁‖=1 → ‖w₂‖=1 → 0 ≤ K → 0 ≤ B₁ → 0 ≤ B₂ →
    ‖e₁‖ ≤ G*(2:ℝ)^(-a) → ‖e₂‖ ≤ G*(2:ℝ)^(-a) →
    ‖e₁-d₁‖ ≤ G*(2:ℝ)^(-p) → ‖e₂-d₂‖ ≤ G*(2:ℝ)^(-p) →
    ¬(‖d₁-inner ℝ d₁ w₁ • w₁‖ ≤ τ ∧
      ‖d₂-inner ℝ d₂ w₂ • w₂‖ ≤ τ ∧ |inner ℝ w₁ d₁+inner ℝ w₂ d₂| ≤ τ) →
    ContDiff ℝ ∞ b₁ → ContDiff ℝ ∞ b₂ →
    (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b₁ w‖ ≤ B₁*A^j) →
    (∀ j ≤ m, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j b₂ w‖ ≤ B₂*A^j) →
    (∀ w, ‖w‖=1 → b₁ w ≠ 0 → ‖w-w₁‖ ≤ Ccap*δ) →
    (∀ w, ‖w‖=1 → b₂ w ≠ 0 → ‖w-w₂‖ ≤ Ccap*δ) →
    ‖graphFixedSpatialTermND Ψ ((2:ℝ)^v) e₁ e₂ b₁ b₂‖ ≤ C*K*B₁*B₂*R^(-T) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (T/(29*sig))
  have hm' : T ≤ 29*sig*m := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 29*sig)).mp hm
    linarith
  obtain ⟨B,hB,hBb⟩ := graph_fixed_nonedge_term_uniform V m
  have hbase : 0 ≤ 5+c₀⁻¹+G := by positivity
  refine ⟨m,B*(5+c₀⁻¹+G)^m,by positivity,?_⟩
  have hpow : Tendsto (fun N : ℕ => (2:ℝ)^N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp
    (((tendsto_rpow_atTop (by positivity : 0 < 20*sig)).comp hpow).eventually
      (Filter.eventually_ge_atTop (8*Ccap*G+4*G)))
  refine ⟨N₀,?_⟩
  intro N hN a p v L hh hL hq R δ τ A Ψ w₁ w₂ d₁ d₂ e₁ e₂ K B₁ B₂ b₁ b₂
    hΨ hsΨ hK hdΨ hw₁ hw₂ hK0 hB₁ hB₂ he₁ he₂ hed₁ hed₂ hne hb₁ hb₂ hd₁ hd₂ hs₁ hs₂
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hδ : 0 < δ := lt_min hc₀ (by positivity)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hA : 1 ≤ A := by
    have : 0 ≤ R^sig*max 1 ((2:ℝ)^L*R^(-50*sig)) := by positivity
    dsimp [A]; linarith [inv_pos.mpr hδ]
  have hD : 0 ≤ G*(2:ℝ)^(-a) := by positivity
  have hη : 0 ≤ G*(2:ℝ)^(-p) := by positivity
  have hg := graph_source_fixed_geometry (N:ℝ) a p v sig G c₀ hc₀
  simp only [Real.rpow_natCast] at hg
  rcases hg with ⟨hQτ,hDτ,hδeq⟩
  have herr : 4*(Ccap*δ)*(G*(2:ℝ)^(-a))+2*(G*(2:ℝ)^(-p)) ≤ τ/2 := by
    dsimp only [δ,τ,R]
    rw [hδeq]
    simp only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),←div_eq_mul_inv]
    exact source_error_scale hR hsig.le (by positivity) (by positivity) hCcap hG (hN₀ N hN)
  have hterm := hBb Ψ w₁ w₂ d₁ d₂ e₁ e₂ ((2:ℝ)^v) τ (Ccap*δ)
    (G*(2:ℝ)^(-a)) (G*(2:ℝ)^(-p)) A K B₁ B₂ b₁ b₂
    hΨ hsΨ hK hdΨ hw₁ hw₂ (by positivity) hτ (by positivity) hD hη hA
    hK0 hB₁ hB₂ he₁ he₂ hed₁ hed₂ herr hne hb₁ hb₂ hd₁ hd₂ hs₁ hs₂
  obtain ⟨hH,hU⟩ := length_scale hh hL
  simp only [Real.rpow_natCast] at hH hU
  have hV : 1 ≤ (2:ℝ)^(v-p) := Real.one_le_rpow (by norm_num) hq
  have hratio := ratio_power_decay hc₀ hR hsig.le (by positivity : 0 < (2:ℝ)^(p-a)) hV
    hG (by positivity : 0 ≤ (2:ℝ)^L) hH hU hm'
  have heq : (A+1+G*(2:ℝ)^(-a)/τ)/((2:ℝ)^v*τ) =
      (2+R^sig*max 1 ((2:ℝ)^L*R^(-50*sig))+δ⁻¹+
        G*(2:ℝ)^(p-a)*R^(-30*sig))/((2:ℝ)^(v-p)*R^(30*sig)) := by
    rw [hQτ,hDτ]; dsimp [A]; ring
  rw [heq] at hterm
  apply hterm.trans
  calc
    _ ≤ B*K*B₁*B₂*((5+c₀⁻¹+G)^m*R^(-T)) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

end Attempt4FullFar
end
end

end OAI
