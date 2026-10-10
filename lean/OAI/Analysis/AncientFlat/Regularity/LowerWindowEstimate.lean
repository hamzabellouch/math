import OAI.Analysis.AncientFlat.Evolution.LowerNearConstant
import OAI.Analysis.AncientFlat.Evolution.LowerWindows
import OAI.Analysis.AncientFlat.Geometry.WindowEstimate

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLowerOrder
open ParabolicInterior ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
theorem lower_window_fourth_estimate (α κ K θ : ℝ) (hα : 0<α) (hα1 : α<1)
    (hκ : 0<κ) (hK : 0≤K) (hθ : 0<θ) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (q : ℝ), 0<q → q≤1 → K*(4*q)^α≤δ →
      ∀ (p0 : V × ℝ) (Ω : Set (V × ℝ)), p0∈Ω → MapsTo (window p0 q) (cylinder 8) Ω →
      ∀ (a : V × ℝ → ℝ) (b : V × ℝ → ℂ) (c : Coefficients V),
      HolderBound α Ω a K → HolderBound α Ω b K → (∀ j, HolderBound α Ω (c j) K) → (∀ p∈Ω, κ≤a p) →
      ∀ (u ut f : ℝ → V → ℂ) (F U H : ℝ), 0≤F → 0≤U → 0≤H →
      (∀ t, ContDiff ℝ 4 (u t)) →
      (∀ p∈Ω, HasDerivAt (fun t => u t p.1) (ut p.2 p.1) p.2) →
      (∃ M, 0≤M ∧ JetBound α Ω u ut M) →
      HolderBound α Ω (fun p => f p.2 p.1) F → (∀ p∈Ω, ‖u p.2 p.1‖≤U) →
      (∀ p∈Ω, ∀ z∈Ω,
        ‖iteratedFDeriv ℝ 4 (u p.2) p.1-iteratedFDeriv ℝ 4 (u z.2) z.1‖≤H*pdist p z^α) →
      (∀ p∈Ω, ut p.2 p.1+(a p : ℂ)*Δ (Δ (u p.2)) p.1+b p*u p.2 p.1+spatialLower c u p=f p.2 p.1) →
      let B := θ*H+(C/(q^4*q^α))*(F+U)
      (∀ p∈cylinder 1, ‖iteratedFDeriv ℝ 4 (u (window p0 q p).2) (window p0 q p).1‖≤B*q^α) ∧
      (∀ p∈cylinder 1, ∀ z∈cylinder 1,
        ‖iteratedFDeriv ℝ 4 (u (window p0 q p).2) (window p0 q p).1-
          iteratedFDeriv ℝ 4 (u (window p0 q z).2) (window p0 q z).1‖≤B*pdist (window p0 q p) (window p0 q z)^α) := by
  obtain ⟨δ,C,hδ,_,hC,Hlocal⟩ := lower_near_constant_fourth (V := V) α κ K θ hα hα1 hκ hK hθ
  refine ⟨δ,C,hδ,hC,?_⟩
  intro q hq hq1 hsmall p0 Ω hp0 hm a b c ha hb hc hella u ut f F U H hF hU hH hs hd hj hf hu hh he
  have h2 : (cylinder 2 : Set (V × ℝ))⊆cylinder 8 := cylinder_mono (by norm_num) (by norm_num)
  have Hosc (p : V × ℝ) (hp : p∈cylinder 2) : ‖a p0-a (window p0 q p)‖≤δ := by
    have hdist : pdist p0 (window p0 q p)≤4*q := by
      conv_lhs => arg 1; rw [←window_zero p0 q]
      rw [pdist_window p0 hq.le]
      have hb := cylinder_pdist_zero (by norm_num : (0:ℝ)≤2) hp
      nlinarith
    exact (ha.2 p0 hp0 _ (hm (h2 hp))).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (pdist_nonneg _ _) hdist hα.le) hK).trans hsmall)
  have Hj : ∃ M, 0≤M ∧ JetBound α (cylinder 8) (windowValue p0 q u) (windowTime p0 q ut) M := by
    obtain ⟨M,hM,hj⟩ := hj
    exact ⟨M,hM,window_jet_bound hα.le hM hq hq1 p0 u ut hs hj hm⟩
  have Hloc := Hlocal (a p0) (hella p0 hp0) ((le_abs_self _).trans (ha.1 p0 hp0))
    (fun p => a (window p0 q p)) (fun p => q^4 • b (window p0 q p)) (windowCoeff p0 q c)
    (holder_window hα.le hq hq1 p0 ha hm) (holder_window_smul hα.le hK hq hq1 p0 4 hb hm)
    (fun j => holder_window_smul hα.le hK hq hq1 p0 (3-j.val) (hc j) hm) Hosc
    (windowValue p0 q u) (windowTime p0 q ut) (windowTime p0 q f) F U (q^4*q^α*H)
    hF hU (by positivity) (windowValue_contDiff p0 q u hs)
    (fun p hp => window_hasDerivAt p0 q u ut p (hd _ (hm hp))) Hj
    (holder_window_smul hα.le hF hq hq1 p0 4 hf hm) (fun p hp => hu _ (hm hp))
    (window_top_seminorm hq p0 u hs hh hm) (fun p hp => lower_window_equation p0 q a b c u ut f hs p (he _ (hm hp)))
  have heq : θ*(q^4*q^α*H)+C*(F+U)=q^4*q^α*(θ*H+C/(q^4*q^α)*(F+U)) := by
    have hqa : q^α≠0 := (Real.rpow_pos_of_pos hq _).ne'
    field_simp
  rw [heq] at Hloc
  exact unscale_top hq p0 (cylinder 1) u hs Hloc
end ParabolicLowerOrder

end

end OAI
