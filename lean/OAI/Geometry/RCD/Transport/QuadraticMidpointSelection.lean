import OAI.Geometry.RCD.Transport.QuadraticPlanIntegrability
import OAI.Geometry.RCD.Coordinates.DiagonalMeanSelection

namespace OAI

/-! # Simultaneous midpoint laws from a countable family of distance tests -/

open Set Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

omit [MeasurableSpace X] [BorelSpace X] in
theorem quadratic_midpoint_selection
    (π : ℕ → ℕ → Measure C(Time,X)) [∀ m k, IsProbabilityMeasure (π m k)]
    (z : ℕ → ℕ → X) (r : ℕ → ℕ → ℝ) (hr : ∀ i k, 0<r i k)
    (δ : ℕ → ℝ) (hδ : ∀ m, 0<δ m ∧ δ m<1/2) (hδ0 : Tendsto δ atTop (𝓝 0))
    (a b : ℕ → Time) (ha : ∀ m, (a m:ℝ)=δ m) (hb : ∀ m, (b m:ℝ)=1-δ m)
    (hg : ∀ m k, ∀ᵐ γ ∂π m k, IsGeodesic γ)
    (hends : ∀ m i, i ≤ m → ∀ k, ∀ᵐ γ ∂π m k,
      dist (z i k) (γ 0)≤r i k ∧ dist (z i k) (γ 1)≤r i k)
    (hlim : ∀ m i, i ≤ m → Tendsto (fun k =>
      (∫ γ, |interiorQuadraticDefect (fun x => dist (z i k) x^2/2)
        (a m) (b m) quadraticMidpointTime γ| ∂π m k)/(r i k)^2) atTop (𝓝 0))
    (P : ℕ → ℕ → C(Time,X) → Prop) (hP : ∀ m k, ∀ᵐ γ ∂π m k, P m k γ) :
    ∃ (d : ℕ → ℕ) (γ : ℕ → C(Time,X)), Tendsto d atTop atTop ∧
      (∀ k, P (d k) k (γ k) ∧ IsGeodesic (γ k)) ∧
      ∀ i, Tendsto (fun k => fullMidpointDefect (z i k) (γ k)/(r i k)^2) atTop (𝓝 0) := by
  let F m k γ := ∑ i∈Finset.range (m+1),
    |interiorQuadraticDefect (fun x => dist (z i k) x^2/2) (a m) (b m) quadraticMidpointTime γ|/(r i k)^2
  have hI m i (him : i∈Finset.range (m+1)) k : Integrable
      (fun γ => |interiorQuadraticDefect (fun x => dist (z i k) x^2/2)
        (a m) (b m) quadraticMidpointTime γ|/(r i k)^2) (π m k) := by
    have hie : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp him)
    exact (quadratic_plan_interior_integrable (π m k) (hg m k) (z i k) (hr i k).le
      ((hends m i hie k).mono fun _ h => h.1) ((hends m i hie k).mono fun _ h => h.2)
      (a m) (b m) quadraticMidpointTime).abs.div_const _
  have hFI m k : Integrable (F m k) (π m k) :=
    integrable_finsetSum _ (fun i hi => hI m i hi k)
  have hF0 m k γ : 0 ≤ F m k γ := Finset.sum_nonneg fun _ _ => div_nonneg (abs_nonneg _) (sq_nonneg _)
  have hFlim m : Tendsto (fun k => ∫ γ, F m k γ ∂π m k) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.range (m+1)) (fun i hi =>
      hlim m i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    simpa only [F,integral_finsetSum _ (fun i hi => hI m i hi _),integral_div,Finset.sum_const_zero] using hh
  let Q m k γ := P m k γ ∧ IsGeodesic γ ∧ ∀ i, i ≤ m →
    dist (z i k) (γ 0)≤r i k ∧ dist (z i k) (γ 1)≤r i k
  have hQ m k : ∀ᵐ γ ∂π m k, Q m k γ := by
    have hh : ∀ᵐ γ ∂π m k, ∀ i, i ≤ m →
        dist (z i k) (γ 0)≤r i k ∧ dist (z i k) (γ 1)≤r i k := by
      apply ae_all_iff.mpr
      intro i
      by_cases hi : i ≤ m
      · exact (hends m i hi k).mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => (hi h).elim
    exact (hP m k).and ((hg m k).and hh)
  obtain ⟨d,γ,hd,hγ,hcost⟩ := diagonal_mean_selection π F Q hFI hF0 hQ hFlim
  refine ⟨d,γ,hd,fun k => ⟨(hγ k).1,(hγ k).2.1⟩,?_⟩
  intro i
  have hsmall : Tendsto (fun k => F (d k) k (γ k)+8*δ (d k)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,Function.comp_apply] using hcost.add ((hδ0.comp hd).const_mul 8)
  apply squeeze_zero_norm' _ hsmall
  filter_upwards [hd.eventually_ge_atTop i] with k hik
  have hE := fullMidpointDefect_le_interior (γ k) (hγ k).2.1 (z i k) (hr i k).le
    ((hγ k).2.2 i hik).1 ((hγ k).2.2 i hik).2 (hδ (d k)).1 (hδ (d k)).2
    (a (d k)) (b (d k)) (ha (d k)) (hb (d k))
  have hpart : |interiorQuadraticDefect (fun x => dist (z i k) x^2/2)
      (a (d k)) (b (d k)) quadraticMidpointTime (γ k)|/(r i k)^2≤F (d k) k (γ k) := by
    dsimp only [F]
    exact Finset.single_le_sum (fun j _ =>
      div_nonneg (abs_nonneg (interiorQuadraticDefect (fun x => dist (z j k) x^2/2)
        (a (d k)) (b (d k)) quadraticMidpointTime (γ k))) (sq_nonneg (r j k)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))
  rw [Real.norm_eq_abs,abs_div,abs_of_pos (sq_pos_of_pos (hr i k))]
  calc
    _ ≤ (|interiorQuadraticDefect (fun x => dist (z i k) x^2/2)
      (a (d k)) (b (d k)) quadraticMidpointTime (γ k)|+8*(r i k)^2*δ (d k))/(r i k)^2 :=
      div_le_div_of_nonneg_right hE (sq_nonneg _)
    _ = |interiorQuadraticDefect (fun x => dist (z i k) x^2/2)
      (a (d k)) (b (d k)) quadraticMidpointTime (γ k)|/(r i k)^2+8*δ (d k) := by
      field_simp [(hr i k).ne']
    _ ≤ _ := add_le_add hpart le_rfl

end RegularPointCoordinates

end

end OAI
