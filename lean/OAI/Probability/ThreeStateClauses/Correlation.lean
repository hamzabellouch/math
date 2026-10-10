import Mathlib
import OAI.Probability.ThreeStateClauses.RadialCalculus
import OAI.Probability.ThreeStateClauses.BranchMoments

namespace OAI

/-! Correlation. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set
namespace ThreeState.TreeClauses.Positive
open Radial

lemma log_cubic_lower {z : ℝ} (hz : -1 < z) :
    z+z^2/2-z^3/6 ≤ (1+z)*Real.log (1+z) := by
  let f : ℝ → ℝ := fun r ↦ r*Real.log r-(r-1)-(r-1)^2/2+(r-1)^3/6
  let g : ℝ → ℝ := fun r ↦ Real.log r-(r-1)+(r-1)^2/2
  have df (r : ℝ) (hr : 0 < r) : HasDerivAt f (g r) r := by
    have hd := ((((hasDerivAt_id r).mul (Real.hasDerivAt_log (ne_of_gt hr))).sub
      ((hasDerivAt_id r).sub_const 1)).sub
      ((((hasDerivAt_id r).sub_const 1).pow 2).div_const 2)).add
      ((((hasDerivAt_id r).sub_const 1).pow 3).div_const 6)
    apply hd.congr_deriv
    dsimp [g]
    field_simp [ne_of_gt hr]
    ring
  have dg (r : ℝ) (hr : 0 < r) : HasDerivAt g ((r-1)^2/r) r := by
    have hd := ((Real.hasDerivAt_log (ne_of_gt hr)).sub ((hasDerivAt_id r).sub_const 1)).add
      ((((hasDerivAt_id r).sub_const 1).pow 2).div_const 2)
    apply hd.congr_deriv
    dsimp only [id]
    field_simp [ne_of_gt hr]
    ring
  have gm {a b : ℝ} (ha : 0 < a) : MonotoneOn g (Icc a b) := by
    apply monotoneOn_Icc_of_hasDerivAt_nonneg (fun r hr ↦ dg r (lt_of_lt_of_le ha hr.1))
    intro r hr
    exact div_nonneg (sq_nonneg _) (lt_trans ha hr.1).le
  have hg₁ : g 1 = 0 := by simp [g]
  have hf₁ : f 1 = 0 := by simp [f]
  have hmin (r : ℝ) (hr : 0 < r) : 0 ≤ f r := by
    rcases le_total 1 r with h | h
    · have hg (t : ℝ) (ht : t ∈ Icc 1 r) : 0 ≤ g t := by
        have hh := gm (b := r) (by norm_num : (0:ℝ) < 1) ⟨le_rfl, h⟩ ht ht.1
        rwa [hg₁] at hh
      have hmono : MonotoneOn f (Icc 1 r) :=
        monotoneOn_Icc_of_hasDerivAt_nonneg (fun t ht ↦ df t (by linarith [ht.1]))
          (fun t ht ↦ hg t ⟨ht.1.le, ht.2.le⟩)
      have hh := hmono ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
      rwa [hf₁] at hh
    · have hg (t : ℝ) (ht : t ∈ Icc r 1) : g t ≤ 0 := by
        have hh := gm (b := 1) hr ht ⟨h, le_rfl⟩ ht.2
        rwa [hg₁] at hh
      have hmono : MonotoneOn (fun t ↦ -f t) (Icc r 1) :=
        monotoneOn_Icc_of_hasDerivAt_nonneg (fun t ht ↦ (df t (lt_of_lt_of_le hr ht.1)).neg)
          (fun t ht ↦ neg_nonneg.mpr (hg t ⟨ht.1.le, ht.2.le⟩))
      have hh := hmono ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
      change -f r ≤ -f 1 at hh
      rw [hf₁] at hh
      linarith
  have hh := hmin (1+z) (by linarith)
  dsimp [f] at hh
  nlinarith

def orbit (v : Vec) : Fin 6 → Vec :=
  ![ ![v 0,v 1,v 2], ![v 0,v 2,v 1], ![v 1,v 0,v 2],
     ![v 1,v 2,v 0], ![v 2,v 0,v 1], ![v 2,v 1,v 0] ]

def avgSix (f : Fin 6 → ℝ) : ℝ :=
  (f 0+f 1+f 2+f 3+f 4+f 5)/6

def dotAvg (v w : Vec) : ℝ := avg (fun i ↦ v i*w i)

lemma avgSix_dot {v w : Vec} (hv : avg v = 0) (hw : avg w = 0) :
    avgSix (fun k ↦ dotAvg v (orbit w k)) = 0 := by
  simp [avgSix, dotAvg, orbit, avg, third_eq hv, third_eq hw]
  ring

lemma avgSix_dot_sq {v w : Vec} (hv : avg v = 0) (hw : avg w = 0) :
    avgSix (fun k ↦ dotAvg v (orbit w k)^2) = 2*momentX v*momentX w := by
  simp [avgSix, dotAvg, orbit, momentX, avg, third_eq hv, third_eq hw]
  ring

lemma avgSix_dot_cube {v w : Vec} (hv : avg v = 0) (hw : avg w = 0) :
    avgSix (fun k ↦ dotAvg v (orbit w k)^3) = 2*momentY v*momentY w := by
  simp [avgSix, dotAvg, orbit, momentY, avg, third_eq hv, third_eq hw]
  ring

lemma avgSix_mono {f g : Fin 6 → ℝ} (h : ∀ k, f k ≤ g k) : avgSix f ≤ avgSix g := by
  dsimp [avgSix]
  linarith [h 0, h 1, h 2, h 3, h 4, h 5]

theorem correlation_orbit_lower {v w : Vec} (hv : avg v = 0) (hw : avg w = 0)
    (hZ : ∀ k, -1 < dotAvg v (orbit w k)) :
    3*momentX v*momentX w-momentY v*momentY w ≤
      3*avgSix (fun k ↦ (1+dotAvg v (orbit w k))*Real.log (1+dotAvg v (orbit w k))) := by
  have h := avgSix_mono (fun k ↦ log_cubic_lower (hZ k))
  have he : avgSix (fun k ↦ dotAvg v (orbit w k)+dotAvg v (orbit w k)^2/2-dotAvg v (orbit w k)^3/6) =
      avgSix (fun k ↦ dotAvg v (orbit w k))+
      avgSix (fun k ↦ dotAvg v (orbit w k)^2)/2-
      avgSix (fun k ↦ dotAvg v (orbit w k)^3)/6 := by
    dsimp [avgSix]; ring
  rw [he, avgSix_dot hv hw, avgSix_dot_sq hv hw, avgSix_dot_cube hv hw] at h
  linarith

end ThreeState.TreeClauses.Positive

end 

noncomputable section
open Set MeasureTheory
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

def pairZ (lam : ℝ) (r m : Message) : ℝ := avg (fun i ↦ r.1 i*edgeMessage lam m i)

def pairPosterior {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (r m : Message) : Message := by
  have hz : 0 < pairZ lam r m := by
    have h := avg_mono (fun i ↦ mul_le_mul_of_nonneg_left (edge_lower hl₀ m i) (coordinate_nonneg r i))
    have he : avg (fun i ↦ r.1 i*(1-lam)) = 1-lam := by
      calc
        _ = (1-lam)*avg r.1 := by simp only [avg]; ring
        _ = _ := by rw [r.2.2]; ring
    rw [he] at h
    exact lt_of_lt_of_le (sub_pos.mpr hl₁) h
  refine ⟨fun i ↦ r.1 i*edgeMessage lam m i/pairZ lam r m, ?_, ?_⟩
  · intro i
    exact div_nonneg (mul_nonneg (coordinate_nonneg r i) ((edge_positive hl₀ hl₁ m).1 i).le) hz.le
  · rw [avg_div]
    exact div_self (ne_of_gt hz)

lemma pairZ_lower {lam : ℝ} (hl₀ : 0 ≤ lam) (r m : Message) : 1-lam ≤ pairZ lam r m := by
  have h := avg_mono (fun i ↦ mul_le_mul_of_nonneg_left (edge_lower hl₀ m i) (coordinate_nonneg r i))
  have he : avg (fun i ↦ r.1 i*(1-lam)) = 1-lam := by
    calc
      _ = (1-lam)*avg r.1 := by simp only [avg]; ring
      _ = _ := by rw [r.2.2]; ring
  rwa [he] at h

lemma pairZ_positive {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) (r m : Message) :
    0 < pairZ lam r m := lt_of_lt_of_le (sub_pos.mpr hl₁) (pairZ_lower hl₀ r m)

lemma continuous_pairZ (lam : ℝ) : Continuous (fun p : Message × Message ↦ pairZ lam p.1 p.2) :=
  continuous_avg.comp (continuous_pi (fun i ↦ ((continuous_coordinate i).comp continuous_fst).mul
    (((continuous_apply i).comp (continuous_edgeMessage lam)).comp continuous_snd)))

lemma continuous_pairPosterior {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    Continuous (fun p : Message × Message ↦ pairPosterior hl₀ hl₁ p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i ↦ (((continuous_coordinate i).comp continuous_fst).mul
    (((continuous_apply i).comp (continuous_edgeMessage lam)).comp continuous_snd)).div
      (continuous_pairZ lam) (fun p ↦ ne_of_gt (pairZ_positive hl₀ hl₁ p.1 p.2)))

lemma pairZ_dot (lam : ℝ) (r m : Message) : pairZ lam r m =
    1+dotAvg (centered r.1) (centered (edgeMessage lam m)) := by
  have hr := r.2.2
  have hm := m.2.2
  dsimp only [pairZ, dotAvg, centered, edgeMessage, edge, avg] at *
  linear_combination hr + lam*hm

lemma integral_pairZ (Q : Law) (lam : ℝ) (r : Message) :
    (∫ m, pairZ lam r m ∂Q.probability.toMeasure) = 1 := by
  have hi (i : Fin 3) : Integrable (fun m ↦ r.1 i*edgeMessage lam m i) Q.probability.toMeasure :=
    (compact_integrable ((continuous_apply i).comp (continuous_edgeMessage lam))).const_mul _
  unfold pairZ
  rw [integral_avg_measure hi]
  simp_rw [integral_const_mul, Q.edge_balanced, mul_one]
  exact r.2.2

lemma integral_pair_coordinate (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (r : Message) (i : Fin 3) :
    (∫ m, pairZ lam r m*(pairPosterior hl₀ hl₁ r m).1 i ∂Q.probability.toMeasure) = r.1 i := by
  have he (m : Message) : pairZ lam r m*(pairPosterior hl₀ hl₁ r m).1 i = r.1 i*edgeMessage lam m i := by
    change pairZ lam r m*(r.1 i*edgeMessage lam m i/pairZ lam r m) = _
    field_simp [ne_of_gt (pairZ_positive hl₀ hl₁ r m)]
  simp_rw [he]
  rw [integral_const_mul, Q.edge_balanced, mul_one]

lemma continuous_pairEntropy {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    Continuous (fun p : Message × Message ↦ pairZ lam p.1 p.2*Real.log (pairZ lam p.1 p.2)) :=
  (continuous_pairZ lam).mul ((continuous_pairZ lam).log (fun p ↦ ne_of_gt (pairZ_positive hl₀ hl₁ p.1 p.2)))

def pairCorrelation (R Q : Law) (lam : ℝ) : ℝ :=
  ∫ r, (∫ m, pairZ lam r m*Real.log (pairZ lam r m) ∂Q.probability.toMeasure) ∂ R.probability.toMeasure

lemma pairCorrelation_nonneg (R Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    0 ≤ pairCorrelation R Q lam := by
  apply integral_nonneg
  intro r
  have hc : Continuous (fun m ↦ pairZ lam r m) := (continuous_pairZ lam).comp (continuous_const.prodMk continuous_id)
  have hi := compact_integrable hc (μ := Q.probability.toMeasure)
  have he : Integrable (fun m : Message ↦ pairZ lam r m*Real.log (pairZ lam r m)) Q.probability.toMeasure :=
    compact_integrable ((continuous_pairEntropy hl₀ hl₁).comp (continuous_const.prodMk continuous_id))
  have h := integral_mono (f := fun m : Message ↦ pairZ lam r m-1)
    (g := fun m ↦ pairZ lam r m*Real.log (pairZ lam r m)) (hi.sub (integrable_const _)) he
    (fun m ↦ by
      have hp := pairZ_positive hl₀ hl₁ r m
      have hh := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
      simpa [mul_sub, ne_of_gt hp] using hh)
  rw [integral_sub (f := fun m ↦ pairZ lam r m) (g := fun _ ↦ (1:ℝ)) hi (integrable_const _), integral_pairZ] at h
  simpa using h

def orbitIndex : Fin 6 → (Fin 3 → Fin 3) :=
  ![ ![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0] ]

def orbitPerm (k : Fin 6) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (orbitIndex k) (by fin_cases k <;> decide)

lemma orbitPerm_apply (v : Vec) (k : Fin 6) (i : Fin 3) :
    v (orbitPerm k i) = orbit v k i := by
  fin_cases k <;> fin_cases i <;> rfl

lemma pairZ_orbit (lam : ℝ) (r m : Message) (k : Fin 6) :
    pairZ lam r (permute (orbitPerm k) m) =
      1+dotAvg (centered r.1) (orbit (centered (edgeMessage lam m)) k) := by
  rw [pairZ_dot]
  congr 2
  funext i
  change edgeMessage lam m (orbitPerm k i)-1 = _
  exact orbitPerm_apply (centered (edgeMessage lam m)) k i

lemma integral_avgSix_measure {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    {f : X → Fin 6 → ℝ} (hf : ∀ k, Integrable (fun x ↦ f x k) ρ) :
    (∫ x, avgSix (f x) ∂ρ) = avgSix (fun k ↦ ∫ x, f x k ∂ρ) := by
  unfold avgSix
  rw [integral_div,
    integral_add (f := fun x ↦ f x 0+f x 1+f x 2+f x 3+f x 4) (g := fun x ↦ f x 5)
      (((((hf 0).add (hf 1)).add (hf 2)).add (hf 3)).add (hf 4)) (hf 5),
    integral_add (f := fun x ↦ f x 0+f x 1+f x 2+f x 3) (g := fun x ↦ f x 4)
      ((((hf 0).add (hf 1)).add (hf 2)).add (hf 3)) (hf 4),
    integral_add (f := fun x ↦ f x 0+f x 1+f x 2) (g := fun x ↦ f x 3)
      (((hf 0).add (hf 1)).add (hf 2)) (hf 3),
    integral_add (f := fun x ↦ f x 0+f x 1) (g := fun x ↦ f x 2)
      ((hf 0).add (hf 1)) (hf 2),
    integral_add (f := fun x ↦ f x 0) (g := fun x ↦ f x 1) (hf 0) (hf 1)]

lemma xMoment_edge (lam : ℝ) (m : Message) :
    momentX (centered (edgeMessage lam m)) = lam^2*xMoment m := by
  dsimp [momentX, centered, edgeMessage, edge, xMoment, avg]
  ring

lemma yMoment_edge (lam : ℝ) (m : Message) :
    momentY (centered (edgeMessage lam m)) = lam^3*yMoment m := by
  dsimp [momentY, centered, edgeMessage, edge, yMoment, avg]
  ring

lemma pairCorrelation_increment_at (Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1)
    (r : Message) :
    3*lam^2*Q.mu*xMoment r-lam^3*Q.eta*yMoment r ≤
      3*(∫ m, pairZ lam r m*Real.log (pairZ lam r m) ∂Q.probability.toMeasure) := by
  let f : Message → Fin 6 → ℝ := fun m k ↦
    pairZ lam r (permute (orbitPerm k) m)*Real.log (pairZ lam r (permute (orbitPerm k) m))
  have hi (k : Fin 6) : Integrable (fun m ↦ f m k) Q.probability.toMeasure :=
    compact_integrable ((continuous_pairEntropy hl₀ hl₁).comp
      (continuous_const.prodMk (continuous_permute (orbitPerm k))))
  have havg : Integrable (fun m ↦ avgSix (f m)) Q.probability.toMeasure :=
    (((((hi 0).add (hi 1)).add (hi 2)).add (hi 3)).add (hi 4) |>.add (hi 5)).div_const 6
  have hpoint (m : Message) : 3*lam^2*xMoment r*xMoment m-lam^3*yMoment r*yMoment m ≤
      3*avgSix (f m) := by
    have h := correlation_orbit_lower (message_centered_avg r)
      (show avg (centered (edgeMessage lam m)) = 0 from by
        change avg (fun i ↦ edgeMessage lam m i-1) = 0
        rw [avg_sub, avg_const, (edge_positive hl₀ hl₁ m).2]; ring)
      (fun k ↦ by
        have hh := pairZ_positive hl₀ hl₁ r (permute (orbitPerm k) m)
        rw [pairZ_orbit] at hh; linarith)
    simp only [xMoment_edge, yMoment_edge] at h
    have he : (fun k ↦ (1+dotAvg (centered r.1) (orbit (centered (edgeMessage lam m)) k))*
        Real.log (1+dotAvg (centered r.1) (orbit (centered (edgeMessage lam m)) k))) = f m := by
      funext k; dsimp only [f]; rw [pairZ_orbit]
    rw [he] at h
    change 3*xMoment r*(lam^2*xMoment m)-yMoment r*(lam^3*yMoment m) ≤ _ at h
    nlinarith [h]
  have h := integral_mono
    (((compact_integrable continuous_xMoment).const_mul (3*lam^2*xMoment r)).sub
      ((compact_integrable continuous_yMoment).const_mul (lam^3*yMoment r)))
    (havg.const_mul 3) hpoint
  simp only [Pi.sub_apply] at h
  rw [integral_sub (f := fun m ↦ 3*lam^2*xMoment r*xMoment m)
    (g := fun m ↦ lam^3*yMoment r*yMoment m)
      ((compact_integrable continuous_xMoment).const_mul _)
      ((compact_integrable continuous_yMoment).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_avgSix_measure hi] at h
  have hev (k : Fin 6) : (∫ m, f m k ∂Q.probability.toMeasure) =
      ∫ m, pairZ lam r m*Real.log (pairZ lam r m) ∂Q.probability.toMeasure := by
    exact (show MeasurePreserving (permuteMeasurableEquiv (orbitPerm k))
      Q.probability.toMeasure Q.probability.toMeasure from Q.symmetric _).integral_comp' (fun m ↦ pairZ lam r m*Real.log (pairZ lam r m))
  simp_rw [hev] at h
  dsimp only [avgSix] at h
  change 3*lam^2*xMoment r*Q.mu-lam^3*yMoment r*Q.eta ≤ _ at h
  linarith

theorem pairCorrelation_increment (R Q : Law) {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam < 1) :
    3*lam^2*Q.mu*R.mu-lam^3*Q.eta*R.eta ≤ 3*pairCorrelation R Q lam := by
  have hc : Integrable (fun r ↦ ∫ m, pairZ lam r m*Real.log (pairZ lam r m) ∂Q.probability.toMeasure)
      R.probability.toMeasure :=
    (compact_integrable (continuous_pairEntropy hl₀ hl₁)
      (μ := R.probability.toMeasure.prod Q.probability.toMeasure)).integral_prod_left
  have h := integral_mono
    (((compact_integrable continuous_xMoment).const_mul (3*lam^2*Q.mu)).sub
      ((compact_integrable continuous_yMoment).const_mul (lam^3*Q.eta))) (hc.const_mul 3)
      (pairCorrelation_increment_at Q hl₀ hl₁)
  simp only [Pi.sub_apply] at h
  rw [integral_sub (f := fun r ↦ 3*lam^2*Q.mu*xMoment r)
      (g := fun r ↦ lam^3*Q.eta*yMoment r)
      ((compact_integrable continuous_xMoment).const_mul _)
      ((compact_integrable continuous_yMoment).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  exact h

end ThreeState.TreeClauses.Experiment

end

end OAI
