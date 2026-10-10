import OAI.MeasureTheory.Falconer.Radial.InitialPlateCover
import OAI.MeasureTheory.Falconer.Radial.PlateScaleChoices
import OAI.MeasureTheory.Falconer.Radial.PlatePowerBudget
import OAI.MeasureTheory.Falconer.Radial.PlatePairLoss
import OAI.MeasureTheory.Falconer.Radial.UniformAffineSlabs

namespace OAI

/-! # The total initial-block exclusion has arbitrarily small product mass -/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

theorem eventually_initial_plate_loss {d : ℕ} (μ ν ρ : Measure (Space d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsFiniteMeasure ρ]
    (E : ℕ → Set (Space d × Space d)) (hE : ∀ j, MeasurableSet (E j))
    (S : ℕ → Finset (Space d × ℝ)) {A b M s C : ℝ}
    (hA : 1 ≤ A) (hb : 0 < b) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hgap : 0 < (s-((d-2:ℕ):ℝ))/8-256*b)
    (hν : ν ≤ ρ) (hμbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hνbounded : ∀ᵐ y ∂ν, ‖y‖ ≤ M) (hρbounded : ∀ᵐ x ∂ρ, ‖x‖ ≤ M)
    (hfrost : FrostmanBallBound μ s C)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ t : ℝ, ρ {x | inner ℝ w x = t} = 0)
    (hunit : ∀ j, ∀ p ∈ S j, ‖p.1‖ = 1)
    (hcard : ∀ j, ((S j).card:ℝ) ≤ A*(plateScale j)^(-b))
    (hcover : ∀ j, E j ⊆ ⋃ p ∈ S j,
      {x | |inner ℝ p.1 x-p.2| ≤ A*(plateScale j)^(1/4:ℝ)} ×ˢ
      {y | |inner ℝ p.1 y-p.2| ≤ A*(plateScale j)^(1/4:ℝ)}) :
    ∀ᶠ j₀ : ℕ in atTop,
      (μ.prod ν) (⋃ i ∈ Finset.range (63*j₀), E (j₀+i)) ≤ ENNReal.ofReal (1/4:ℝ) := by
  let B := A^2*(C*(3:ℝ)^s*(4*M+3)^(d-2))*(10*A)^(s-((d-2:ℕ):ℝ))
  obtain ⟨r,hr,_,hslab⟩ := uniform_affine_slabs ρ hM hρbounded hzero
    (show 0 < ENNReal.ofReal (1/8:ℝ) by positivity)
  have hwidth := (plate_cluster_width_tendsto M A).eventually (eventually_lt_nhds hr)
  have ht : Tendsto (fun j => B*(plateScale j)^((s-((d-2:ℕ):ℝ))/8-256*b))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using (plateScale_power_tendsto hgap).const_mul B
  have herror := ht.eventually (eventually_lt_nhds (show (0:ℝ) < 1/8 by norm_num))
  filter_upwards [eventually_initial_plate_card hb hA,eventually_plate_geometry M A,
    hwidth,herror] with j₀ hjcard hjgeom hjwidth hjerror
  obtain ⟨T,hTunit,hTcard,hTcover⟩ := initial_plate_block_cover E S
    (show 0 ≤ A by linarith only [hA]) hb.le hunit hcard hcover j₀
  have hTc : (T.card:ℝ) ≤ A*(plateScale j₀)^(-(128*b)) := by
    simpa only [neg_mul] using hjcard T.card hTcard
  have hsmall : 10*(A*(plateScale j₀)^(1/4:ℝ))/(plateScale j₀)^(1/8:ℝ) ≤ 1 := by
    simpa only [plate_intersection_ratio (plateScale_pos j₀) A] using hjgeom.1
  have hw : 2*M*(plateScale j₀)^(1/8:ℝ)+3*(A*(plateScale j₀)^(1/4:ℝ)) ≤ r := by
    nlinarith only [hjwidth.le]
  have hinit := initial_plate_pair_mass μ ν ρ T
    (⋃ i ∈ Finset.range (63*j₀), E (j₀+i))
    (Finset.measurableSet_biUnion _ (fun i _ => hE (j₀+i)))
    hM hC (mul_pos (show 0 < A by linarith only [hA])
      (Real.rpow_pos_of_pos (plateScale_pos _) _))
    (Real.rpow_pos_of_pos (plateScale_pos _) _)
    (Real.rpow_le_one (plateScale_pos _).le (plateScale_le_one _) (by norm_num))
    hsmall hν hμbounded hνbounded hfrost hTunit
    (fun p hp => (measure_mono (fun _ hx => hx.trans hw)).trans (hslab p.1 (hTunit p hp) p.2).le)
    hTcover
  have hpower := plate_card_power_bound (plateScale_pos j₀)
    (show 0 ≤ A by linarith only [hA]) hTc
    (B := C*(3:ℝ)^s*(4*M+3)^(d-2)) (a := s-((d-2:ℕ):ℝ))
  have hpower' : (T.card:ℝ≥0∞)^2 *
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^(d-2)) *
        (10*(A*(plateScale j₀)^(1/4:ℝ))/(plateScale j₀)^(1/8:ℝ))^(s-((d-2:ℕ):ℝ))) ≤
      ENNReal.ofReal (B*(plateScale j₀)^((s-((d-2:ℕ):ℝ))/8-256*b)) := by
    simpa only [show (2:ℝ)*(128*b) = 256*b by ring] using hpower
  have he : ENNReal.ofReal (B*(plateScale j₀)^((s-((d-2:ℕ):ℝ))/8-256*b)) ≤
      ENNReal.ofReal (1/8:ℝ) := ENNReal.ofReal_le_ofReal hjerror.le
  apply hinit.trans ((add_le_add (hpower'.trans he) le_rfl).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

end Falconer

end OAI
