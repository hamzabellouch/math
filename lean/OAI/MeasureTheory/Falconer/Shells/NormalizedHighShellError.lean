import OAI.MeasureTheory.Falconer.Shells.NormalizedHighShellKernel
import OAI.MeasureTheory.Falconer.Shells.WeightedHighShellInverse

namespace OAI

namespace PlanarFalconer
open MeasureTheory

 theorem measurable_list_sum {α ι : Type*} [MeasurableSpace α] (L : List ι)
    (f : ι → α → ℂ) (hf : ∀ i ∈ L, Measurable (f i)) :
    Measurable (fun x => (L.map (fun i => f i x)).sum) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hf i (by simp)).add (ih (fun a ha => hf a (by simp [ha])))

namespace PositiveDistanceData

 theorem normalizedHighShellKernel_measurable (d : PositiveDistanceData) (n : ℕ)
    (v : ℝ) (ψ : UnitCircle → ℂ) (hψ : Measurable ψ) :
    Measurable (fun p : ℝ × (Plane × Plane) => d.normalizedHighShellKernel n v p.1 ψ p.2) := by
  unfold normalizedHighShellKernel
  apply Measurable.mul
  · fun_prop
  · apply Finset.measurable_sum
    intro j _
    apply Measurable.mul
    · fun_prop
    · apply measurable_list_sum
      intro b _
      apply Measurable.const_mul
      apply Measurable.mul
      · fun_prop
      · exact measurable_sourceDistanceKernel ψ _ _ hψ
          (d.inverseEndpointSymbol_measurable b.2 0) (d.inverseEndpointSymbol_measurable b.2 1)

 theorem uniform_normalized_high_shell_error {sig T : ℝ} (hsig : 0 < sig) :
    ∃ n N₀ : ℕ, ∀ d : PositiveDistanceData, N₀ ≤ d.N → d.sig = sig →
    0 < d.Q.side → d.StronglySeparated → 0 < d.q →
    d.sig*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N →
    ∀ v r : ℝ, (d.t:ℝ)-d.sig*d.N ≤ v → (2:ℝ)^(v-1) ≤ r →
    ∀ x ∈ (d.Q.descendant d.X).carrier, ∀ y ∈ (d.Q.descendant d.Y).carrier,
    ‖(d.spatialWeight (x,y):ℂ)*Complex.exp (Complex.I*((r*dist x y:ℝ):ℂ)) -
      d.normalizedHighShellKernel n v r
        (sourceConeCircle (sourceParentAxis (d.Q.descendant d.X) (d.Q.descendant d.Y))) (x,y)‖ ≤
      ((2:ℝ)^d.N)^(-T) := by
  obtain ⟨n,N₀,h₀⟩ := uniform_weighted_high_shell_inverse (T := T) hsig
  refine ⟨n,N₀,?_⟩
  intro d hN hd hQ hs hq hqs hw ht v r hv hr x hx y hy
  have he := h₀ d hN hd hQ hs hq hqs hw ht v r hv hr x hx y hy
  have hrp : 0 < r := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hr
  have hdist : 0 < dist x y := by
    have h := (d.separated_distance_ratio hQ hs (z := (x,y)) hx hy).1
    have hp : 0 < (2:ℝ)^(-(d.a:ℝ)) := by positivity
    exact (mul_pos (by norm_num : (0:ℝ) < 96) hp).trans_le ((le_div_iff₀ hp).mp h)
  rw [d.weightedInverseCircle_normalized hQ n v (r := r) hrp (z := (x,y)) hdist _
    (measurable_sourceConeCircle _) (by norm_num : (0:ℝ) ≤ 1) (sourceConeCircle_norm_le _)] at he
  exact he

end PositiveDistanceData

end PlanarFalconer

end OAI
