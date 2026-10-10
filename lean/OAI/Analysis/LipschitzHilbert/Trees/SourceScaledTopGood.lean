import OAI.Analysis.LipschitzHilbert.Trees.SourceTopGood
import OAI.Analysis.LipschitzHilbert.Estimates.TopIntervalHorizontalRescale

namespace OAI

/-! Top concentration at the actual horizontal frequency scale. Each top
is normalized separately; its exceptional area is transported back before
forming the common exceptional set. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PlanarPacketFamily

theorem source_scaled_top_good (hL : LepingleInput) {lo hi : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (J a p : ℝ) (D : ℕ)
    (hJ : 0 ≤ J) (ha : 0 ≤ a) (hp : 0 ≤ p) :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      ∀ (τ κ : Type) [Fintype τ] [Fintype κ]
        (N : τ → ℕ) (ι : ∀ i, Fin (N i) → Type) [∀ i j, Fintype (ι i j)]
        (P : ∀ i, PlanarPacketFamily (N i) κ (ι i)), (∀ i, (P i).constant ≤ L^p) →
      ∀ (cutoff : ∀ i, Fin (N i) → ℝ) (v : τ → ℝ × ℝ → ℝ), (∀ i, Measurable (v i)) →
      ∀ (g : τ → ℝ × ℝ → EuclideanSpace ℂ κ), (∀ i, Measurable (g i)) →
      (∀ i z, ‖g i z‖ ≤ 1) → (∀ i, Monotone (cutoff i)) →
      ∀ (T : τ → SlopeBox) (r : τ → ℝ) (_hr : ∀ i, 0 < r i)
        (data : ∀ i, TopRawPacketData (P i) (lo/r i) (hi/r i) (T i) (L^a) D),
      (∀ i, TopCovariantData (data i)) →
      ∃ bad : Set (ℝ × ℝ), MeasurableSet bad ∧
        (volume.prod volume) bad ≤ ENNReal.ofReal (Real.exp (-J*L)*(∑ i, (T i).area)) ∧
        ∀ i lower upper, lower ≤ upper → upper ≤ N i → ∀ z w,
          |w| ≤ (T i).width → z ∉ bad →
          let F := fun x y => planarPacketInterval ((P i).mainCoefficient (cutoff i) (v i) (g i))
            (fun j u k t s => (P i).wave j u k t s) lower upper x y
          ‖F z.1 ((z.2-(T i).slope*z.1)+w)‖ +
            (T i).width*‖covariantSignal (data i).frequency (fun k t => F z.1 t k)
              ((z.2-(T i).slope*z.1)+w)‖ ≤
                L^(2*p+3)*((T i).weight (L^a) (D:ℝ) z)^8 := by
  classical
  obtain ⟨L0,hL0,hgood⟩ := source_top_good hL hlo hhi J a p D hJ ha hp
  refine ⟨L0,hL0,?_⟩
  intro L hL τ κ _ _ N ι _ P hP cutoff v hv g hg hg1 hc T r hr data second
  let Q := fun i => (P i).horizontalRescale (r i) (hr i)
  let U := fun i => (T i).horizontalRescale (r i) (hr i)
  let v' := fun i (z : ℝ × ℝ) => v i (z.1,r i*z.2)
  let g' := fun i (z : ℝ × ℝ) => g i (z.1,r i*z.2)
  have hv' (i : τ) : Measurable (v' i) := (hv i).comp
    (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hg' (i : τ) : Measurable (g' i) := (hg i).comp
    (measurable_fst.prodMk (measurable_const.mul measurable_snd))
  have hsingle (i : τ) : ∃ B : Set (ℝ × ℝ), MeasurableSet B ∧
      (volume.prod volume) B ≤ ENNReal.ofReal (Real.exp (-J*L)*(U i).area) ∧
      ∀ lower upper, lower ≤ upper → upper ≤ N i → ∀ z w,
        |w| ≤ (U i).width → z ∉ B →
        let F := fun x y => planarPacketInterval ((Q i).mainCoefficient (cutoff i) (v' i) (g' i))
          (fun j u k t s => (Q i).wave j u k t s) lower upper x y
        ‖F z.1 ((z.2-(U i).slope*z.1)+w)‖ +
          (U i).width*‖covariantSignal (data i).frequency (fun k t => F z.1 t k)
            ((z.2-(U i).slope*z.1)+w)‖ ≤
              L^(2*p+3)*((U i).weight (L^a) (D:ℝ) z)^8 := by
    obtain ⟨B,hB,harea,hpoint⟩ := hgood L hL Unit κ (fun _ => N i) (fun _ => ι i)
      (fun _ => Q i) (fun _ => hP i) (fun _ => cutoff i) (fun _ => v' i) (fun _ => hv' i)
      (fun _ => g' i) (fun _ => hg' i) (fun _ z => hg1 i (z.1,r i*z.2)) (fun _ => hc i)
      (fun _ => U i) (fun _ => (data i).horizontalRescale (r i) (hr i))
      (fun _ => (second i).horizontalRescale (r i) (hr i))
    refine ⟨B,hB,?_,?_⟩
    · simpa using harea
    · exact hpoint ()
  choose B hB harea hpoint using hsingle
  let C := fun i => horizontalDilation ((r i)⁻¹) (inv_ne_zero (hr i).ne') ⁻¹' B i
  have hC (i : τ) : MeasurableSet (C i) := (hB i).preimage
    (horizontalDilation ((r i)⁻¹) (inv_ne_zero (hr i).ne')).measurable
  have hareaC (i : τ) : (volume.prod volume) (C i) ≤
      ENNReal.ofReal (Real.exp (-J*L)*(T i).area) := by
    change (volume.prod volume)
      (horizontalDilation ((r i)⁻¹) (inv_ne_zero (hr i).ne') ⁻¹' B i) ≤ _
    rw [measure_horizontalDilation_preimage _ _ _ (hB i),inv_inv,abs_of_pos (hr i)]
    apply (mul_le_mul_right (harea i) (ENNReal.ofReal (r i))).trans
    rw [← ENNReal.ofReal_mul (hr i).le]
    apply ENNReal.ofReal_le_ofReal
    change r i * (Real.exp (-J*L)*((T i).length/r i*(T i).width)) ≤
      Real.exp (-J*L)*((T i).length*(T i).width)
    apply le_of_eq
    field_simp [(hr i).ne']
  refine ⟨⋃ i, C i,MeasurableSet.iUnion hC,?_,?_⟩
  · calc
      _ ≤ ∑ i, (volume.prod volume) (C i) := by
        simpa only [tsum_fintype] using measure_iUnion_le C
      _ ≤ ∑ i, ENNReal.ofReal (Real.exp (-J*L)*(T i).area) :=
        Finset.sum_le_sum (fun i _ => hareaC i)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg
          (fun i _ => mul_nonneg (Real.exp_pos _).le (T i).area_pos.le),Finset.mul_sum]
  · intro i lower upper hlu hu z w hw hout
    have hout' : (z.1/r i,z.2) ∉ B i := by
      intro hz
      apply hout
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      change (horizontalDilation ((r i)⁻¹) (inv_ne_zero (hr i).ne') z) ∈ B i
      simpa only [horizontalDilation_apply,div_eq_mul_inv,mul_comm] using hz
    have hpoint' := hpoint i lower upper hlu hu (z.1/r i,z.2) w hw hout'
    have hinterval (y : ℝ) : planarPacketInterval
        ((Q i).mainCoefficient (cutoff i) (v' i) (g' i))
        (fun j u k t s => (Q i).wave j u k t s) lower upper (z.1/r i) y =
        planarPacketInterval ((P i).mainCoefficient (cutoff i) (v i) (g i))
        (fun j u k t s => (P i).wave j u k t s) lower upper z.1 y := by
      rw [horizontalRescale_interval]
      rw [mul_div_cancel₀ _ (hr i).ne']
    have hslope : (U i).slope*(z.1/r i) = (T i).slope*z.1 := by
      change (r i*(T i).slope)*(z.1/r i) = _
      field_simp [(hr i).ne']
    have hweight : (U i).weight (L^a) (D:ℝ) (z.1/r i,z.2) =
        (T i).weight (L^a) (D:ℝ) z := by
      rw [SlopeBox.horizontalRescale_weight]
      rw [mul_div_cancel₀ _ (hr i).ne']
    dsimp only at hpoint' ⊢
    simp only [hslope,hweight,hinterval] at hpoint'
    exact hpoint'

end LipschitzHilbert.PlanarPacketFamily

end

end OAI
