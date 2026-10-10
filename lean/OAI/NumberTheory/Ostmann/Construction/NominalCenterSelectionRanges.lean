import OAI.NumberTheory.Ostmann.Construction.NominalCenterSelection
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped Topology
lemma center_near_nominal_tight {h v a n : ℝ} (hh : 4000≤h) (hn : 1≤n)
    (ha : |a-(⌊v/2⌋:ℝ)/n|≤h/1000) : |a-v/(2*n)|≤h/800 := by
  have hnp : 0<n := by linarith
  have hf : |(⌊v/2⌋:ℝ)-v/2|≤1 := by
    have hlo := Int.lt_floor_add_one (v/2)
    have hhi := Int.floor_le (v/2)
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have he : a-v/(2*n) = (a-(⌊v/2⌋:ℝ)/n)+((⌊v/2⌋:ℝ)-v/2)/n := by ring
  rw [he]
  calc
    _ ≤ |a-(⌊v/2⌋:ℝ)/n|+|((⌊v/2⌋:ℝ)-v/2)/n| := abs_add_le _ _
    _ ≤ h/1000+1/n := by
      rw [abs_div,abs_of_pos hnp]
      exact add_le_add ha (div_le_div_of_nonneg_right hf hnp.le)
    _ ≤ h/800 := by
      have : 1/n≤1 := (div_le_one hnp).mpr hn
      linarith

namespace NominalCenterArray
variable {d : Decomposition} {k : ℕ} {L J tb : ℝ} {w : Fin k → ℝ}

theorem top_bounds (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L)
    (hTop : favorableBlockWidth L/4≤J-2*tb ∧ J-2*tb≤4*favorableBlockWidth L)
    (i : Fin 3) : favorableBlockWidth L/100≤(C.top i:ℝ) ∧
      (C.top i:ℝ)≤favorableBlockWidth L := by
  have h := abs_le.mp (C.top_nominal_near hh i)
  constructor <;> linarith [hTop.1,hTop.2]

theorem comp_bounds (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L) (j : Fin k)
    (hw : favorableBlockWidth L/4≤w j ∧ w j≤4*(2:ℝ)^k*favorableBlockWidth L)
    (i : Fin 2) : favorableBlockWidth L/100≤(C.comp j i:ℝ) ∧
      (C.comp j i:ℝ)≤2*(2:ℝ)^k*favorableBlockWidth L := by
  have h := abs_le.mp (C.comp_nominal_near hh j i)
  have hP : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  constructor
  · linarith [hw.1]
  · nlinarith [hw.2,mul_nonneg (sub_nonneg.mpr hP)
      (show 0≤favorableBlockWidth L by linarith)]

theorem top_relative_near (C : NominalCenterArray d k L J tb w)
    (hh : 4000≤favorableBlockWidth L) (hTop : favorableBlockWidth L/4≤J-2*tb)
    (i : Fin 3) : |(C.top i:ℝ)-(J-2*tb)/6|≤(3/100:ℝ)*((J-2*tb)/6) := by
  have h := center_near_nominal_tight hh (by norm_num : (1:ℝ)≤3) (C.top_near i)
  norm_num only at h
  nlinarith

theorem comp_relative_near (C : NominalCenterArray d k L J tb w)
    (hh : 4000≤favorableBlockWidth L) (j : Fin k) (hw : favorableBlockWidth L/4≤w j)
    (i : Fin 2) : |(C.comp j i:ℝ)-w j/4|≤(3/100:ℝ)*(w j/4) := by
  have h := center_near_nominal_tight hh (by norm_num : (1:ℝ)≤2) (C.comp_near j i)
  norm_num only at h
  nlinarith

theorem top_log_support (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L)
    (hTop : favorableBlockWidth L/4≤J-2*tb ∧ J-2*tb≤4*favorableBlockWidth L)
    (i : Fin 3) (E : Finset ℕ) (hZ : 0<logCellMass (C.top i) E)
    (p : (logCellPrimeSource (C.top i) E hZ).Sample)
    (hp : (logCellPrimeSource (C.top i) E hZ).law.mass p≠0) :
    favorableBlockWidth L/200≤Real.log (p:ℕ) ∧ Real.log (p:ℕ)≤2*favorableBlockWidth L := by
  have hc := C.top_bounds hh hTop i
  have hs := abs_lt.mp (logCellPrimeSource_log_support (C.top i) E hZ p hp)
  constructor <;> linarith

theorem comp_log_support (C : NominalCenterArray d k L J tb w)
    (hh : 1000≤favorableBlockWidth L) (j : Fin k)
    (hw : favorableBlockWidth L/4≤w j ∧ w j≤4*(2:ℝ)^k*favorableBlockWidth L)
    (i : Fin 2) (E : Finset ℕ) (hZ : 0<logCellMass (C.comp j i) E)
    (p : (logCellPrimeSource (C.comp j i) E hZ).Sample)
    (hp : (logCellPrimeSource (C.comp j i) E hZ).law.mass p≠0) :
    favorableBlockWidth L/200≤Real.log (p:ℕ) ∧
      Real.log (p:ℕ)≤3*(2:ℝ)^k*favorableBlockWidth L := by
  have hc := C.comp_bounds hh j hw i
  have hs := abs_lt.mp (logCellPrimeSource_log_support (C.comp j i) E hZ p hp)
  have hP : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
  constructor
  · linarith
  · nlinarith [mul_nonneg (sub_nonneg.mpr hP)
      (show 0≤favorableBlockWidth L by linarith)]

end NominalCenterArray

theorem exists_nominalCenterArray_with_bounds (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop, ∀ G₀ c tb td : ℝ, 0≤G₀ →
      (G₀-2≤c ∧ c≤G₀+favorableBlockWidth L+2) →
      |tb|≤favorableBlockWidth L/16 → |td|≤favorableBlockWidth L/16 →
      ∃ C : NominalCenterArray d k L (nominalJ Bs BD Bz k L G₀ c td) tb
          (fun j => nominalCompensation Bs BD Bz k L G₀ c td j),
        4000≤favorableBlockWidth L ∧
        (∀i,favorableBlockWidth L/100≤(C.top i:ℝ) ∧ (C.top i:ℝ)≤favorableBlockWidth L) ∧
        (∀j i,favorableBlockWidth L/100≤(C.comp j i:ℝ) ∧
          (C.comp j i:ℝ)≤2*(2:ℝ)^k*favorableBlockWidth L) := by
  have hh := (exp_mul_tendsto (by norm_num : (0:ℝ)<1/100)).eventually_ge_atTop 4000
  filter_upwards [exists_nominalCenterArray d Bs BD Bz hk,
    nominalTotals_eventually Bs BD Bz hk,hh] with L hC hN hh
  intro G₀ c tb td hG hc htb htd
  obtain ⟨C⟩ := hC G₀ c tb td hG hc htb htd
  obtain ⟨_,hTop,hComp⟩ := hN G₀ c tb td hG hc htb htd
  have hhsmall : 1000≤favorableBlockWidth L := by change 4000≤favorableBlockWidth L at hh; linarith
  exact ⟨C,hh,C.top_bounds hhsmall hTop,fun j i => C.comp_bounds hhsmall j (hComp j j.isLt) i⟩

end Ostmann.Construction

end

end OAI
