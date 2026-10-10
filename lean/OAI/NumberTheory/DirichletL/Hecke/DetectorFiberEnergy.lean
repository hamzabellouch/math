import OAI.NumberTheory.DirichletL.Hecke.DetectorFiberSpikes
import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwisePlain

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckeDetectorFiberEnergy
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorRowwisePolynomial

theorem inverse_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0<D) (hwb : 0≤wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤E)
    (height : ℝ) (hh : 0≤height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) true ((logProfile^[n]) W) D s t*P u‖^2≤E) :
    ∑ u∈rows,‖polynomial (χ u label) true W D (w u).zero.re (w u).frequency*P u‖^2≤
      12*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwiseMarked.marked_rowwise rows (fun u => χ u label) true W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf
    (by simpa using hraw 0 (by omega)) (by simpa using hraw 1 (by omega))
    (by simpa using hraw 2 (by omega))
  refine hb.trans ?_
  nlinarith

theorem plain_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0<D) (hwb : 0≤wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤E)
    (height : ℝ) (hh : 0≤height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) W) D s t*
        polynomial (χ u label) false ((logProfile^[k]) W) D s t*P u‖^2≤E) :
    ∑ u∈rows,‖polynomial (χ u label) false W D (w u).zero.re (w u).frequency*
      polynomial (χ u label) false W D (w u).zero.re (w u).frequency*P u‖^2≤
      192*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwisePlain.plain_squared_rowwise rows (fun u => χ u label) W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) hE (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf hraw
  refine hb.trans ?_
  nlinarith

end SevenEighths.HeckeDetectorFiberEnergy

end

end OAI
