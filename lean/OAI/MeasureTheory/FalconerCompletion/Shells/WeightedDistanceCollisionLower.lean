import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.DistanceSincSpectralIdentity
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Fourier.MinimalMask

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma weightedDistance_collision_lower [IsFiniteMeasure e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)))
    (S : Set (ℝ × ℝ)) (hS : MeasurableSet S) :
    (e.levelMass^(-2:ℤ)*(8*K)^(-(n:ℝ)/2))^2 * (e.distance.prod e.distance).real S ≤
      (e.weightedDistance.prod e.weightedDistance).real S := by
  let := e.weightedDistance_isFinite hK hX hY hs
  have hKp : 0<K := by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
  have hc : 0≤e.levelMass^(-2:ℤ)*(8*K)^(-(n:ℝ)/2) := by positivity
  have hp := Measure.prod_mono (e.weightedDistance_lower hK hX hY hs)
    (e.weightedDistance_lower hK hX hY hs)
  have h := ENNReal.toReal_mono (measure_ne_top _ S) (Measure.le_iff.mp hp S hS)
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc] at h
  simpa only [pow_two,measureReal_def] using h

end PositiveDistanceState

theorem actual_prefix_lowpass {K : ℝ} (hK : 32*(n+2:ℝ)≤K) :
    ∃ H : ℝ, 0<H ∧ ∀ (e : PositiveDistanceState (n+1)) [IsFiniteMeasure e.ρ],
      e.X.length=e.a → e.Y.length=e.a →
      farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ)) →
      e.coincidence.toReal ≤ H*(2:ℝ)^(-(e.a:ℝ))*
        ∫ r in Icc (-((2:ℝ)^e.t)) ((2:ℝ)^e.t), ‖charFun e.weightedDistance r‖^2 := by
  obtain ⟨C,hC,hfourier⟩ := finite_measure_distance_collision_fourier_wide
  have hKp : 0<K := by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith
  let c : ℝ := (8*K)^(-(n:ℝ)/2)
  have hcp : 0<c := by dsimp [c]; positivity
  refine ⟨((n+2:ℝ)*C)/c^2,by positivity,?_⟩
  intro e he hX hY hs
  let := e.weightedDistance_isFinite hK hX hY hs
  have hc := e.weightedDistance_collision_lower hK hX hY hs
    {z : ℝ × ℝ | |z.1-z.2|≤100*(↑(n+1)+1:ℝ)*e.width} (by measurability)
  have hM : 0<e.levelMass := by unfold PositiveDistanceState.levelMass; positivity
  have hn : e.normalization.toReal = ((2:ℝ)^((e.t:ℝ)-e.a)/c^2)*
      (e.levelMass^(-2:ℤ)*c)^2 := by
    rw [PositiveDistanceState.normalization,ENNReal.toReal_ofReal (by positivity)]
    simp only [zpow_neg,zpow_ofNat,mul_pow]
    field_simp
  have hw : 100*(↑(n+1)+1:ℝ)*e.width=100*(n+2:ℝ)/(2:ℝ)^e.t := by
    simp only [PositiveDistanceState.width,Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
    push_cast
    ring
  have hco : e.coincidence.toReal=e.normalization.toReal*
      (e.distance.prod e.distance).real {z : ℝ × ℝ | |z.1-z.2|≤100*(↑(n+1)+1:ℝ)*e.width} := by
    rw [PositiveDistanceState.coincidence,ENNReal.toReal_mul,measureReal_def,e.distance_collision]
  have hd : e.coincidence.toReal ≤ ((2:ℝ)^((e.t:ℝ)-e.a)/c^2)*
      (e.weightedDistance.prod e.weightedDistance).real
        {z : ℝ × ℝ | |z.1-z.2|≤100*(n+2:ℝ)/(2:ℝ)^e.t} := by
    rw [hco,hn,mul_assoc,← hw]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hf := hfourier e.weightedDistance ((2:ℝ)^e.t) (n+2) (by positivity) (by have hn : (0:ℝ)≤n := Nat.cast_nonneg n; linarith)
  have hp : (2:ℝ)^((e.t:ℝ)-e.a)=(2:ℝ)^(-(e.a:ℝ))*(2:ℝ)^e.t := by
    rw [← Real.rpow_natCast,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  calc
    _ ≤ ((2:ℝ)^(-(e.a:ℝ))/c^2)*(((2:ℝ)^e.t)*
        (e.weightedDistance.prod e.weightedDistance).real
        {z : ℝ × ℝ | |z.1-z.2|≤100*(n+2:ℝ)/(2:ℝ)^e.t}) := by
      convert hd using 1; rw [hp]; ring
    _ ≤ ((2:ℝ)^(-(e.a:ℝ))/c^2)*((n+2:ℝ)*C*
        ∫ r in Icc (-((2:ℝ)^e.t)) ((2:ℝ)^e.t), ‖charFun e.weightedDistance r‖^2) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set MeasureTheory PlanarFalconer _root_.OAI.GraphLiteralSupport.Attempt4FullFar
open scoped ENNReal
variable {n : ℕ}
namespace PositiveDistanceState
variable (e : PositiveDistanceState (n+1))

lemma weightedDistance_mass_le [IsFiniteMeasure e.ρ] {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    e.weightedDistance.real univ≤e.levelMass^(-2:ℤ)*e.cellPair.real univ := by
  have h := Measure.le_iff.mp (e.weightedPair_le hK hX hY hs) univ MeasurableSet.univ
  have ht : (ENNReal.ofReal (e.levelMass^(-2:ℤ)) • e.cellPair) univ≠⊤ := by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have h' := ENNReal.toReal_mono ht h
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0≤e.levelMass^(-2:ℤ))] at h'
  simpa only [weightedDistance,measureReal_def,Measure.map_apply
    (continuous_fst.dist continuous_snd).measurable MeasurableSet.univ,preimage_univ] using h'

lemma weightedDistance_profile_mass {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    {B : ℕ} {s lam : ℝ} (hd : RegularizedProfileData e.ρ e.N B s lam e.mass)
    (ha : e.a≤e.N) (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    e.weightedDistance.real univ≤((2:ℝ)^e.N)^(2*(n+2:ℝ)*lam) := by
  let := hd.probability
  apply (e.weightedDistance_mass_le hK hX hY hs).trans
  simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
    e.normalized_cellPair_profile_mass hd ha hX hY

lemma prefix_low_frequency_stopping {K : ℝ} (hK : 32*(n+2:ℝ)≤K)
    {B : ℕ} {s lam : ℝ} (hd : RegularizedProfileData e.ρ e.N B s lam e.mass)
    (ha : e.a≤e.N) (hX : e.X.length=e.a) (hY : e.Y.length=e.a)
    (hs : farSeparatedGridND e.a K (fun j => (pathIndex e.X j:ℤ)) (fun j => (pathIndex e.Y j:ℤ))) :
    (2:ℝ)^(-(e.a:ℝ))*(∫ r in Icc (-((2:ℝ)^e.a)) ((2:ℝ)^e.a), ‖charFun e.weightedDistance r‖^2) ≤
      2*((2:ℝ)^e.N)^(4*(n+2:ℝ)*lam) := by
  let := hd.probability
  let := e.weightedDistance_isFinite hK hX hY hs
  have hm := e.weightedDistance_profile_mass hK hd ha hX hY hs
  have hr : (((2:ℝ)^e.N)^(2*(n+2:ℝ)*lam))^2=((2:ℝ)^e.N)^(4*(n+2:ℝ)*lam) := by
    rw [← Real.rpow_mul_natCast (by positivity : 0≤(2:ℝ)^e.N)]
    congr 1
    norm_num
    ring
  have hb (r : ℝ) : ‖charFun e.weightedDistance r‖^2≤((2:ℝ)^e.N)^(4*(n+2:ℝ)*lam) := by
    rw [← hr]
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_charFun_le r).trans hm) 2
  have hi : Integrable (fun r => ‖charFun e.weightedDistance r‖^2)
      (volume.restrict (Icc (-((2:ℝ)^e.a)) ((2:ℝ)^e.a))) := by
    simpa only [one_mul] using charFun_sq_integrable_finite e.weightedDistance
      (volume.restrict (Icc (-((2:ℝ)^e.a)) ((2:ℝ)^e.a))) 1
  have h := integral_mono_ae hi (integrable_const (((2:ℝ)^e.N)^(4*(n+2:ℝ)*lam)))
    (Filter.Eventually.of_forall hb)
  apply (mul_le_mul_of_nonneg_left h (by positivity : 0≤(2:ℝ)^(-(e.a:ℝ)))).trans_eq
  have hwidth : 0≤(2:ℝ)^e.a - -((2:ℝ)^e.a) := by
    have hp : 0<(2:ℝ)^e.a := by positivity
    linarith
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
    ENNReal.toReal_ofReal hwidth,smul_eq_mul,
    Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
  field_simp
  ring

end PositiveDistanceState
end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
