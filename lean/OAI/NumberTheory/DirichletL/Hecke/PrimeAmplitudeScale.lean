import OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeBins
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SevenEighths.HeckePrimeAmplitudeBins

theorem upper_allowance_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hmesh : 0<mesh) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r cap : ℝ, dmin≤d → rmin≤r →
      C*(Z^d)^(cap*r+ε)≤((Z^d)^r)^(cap+mesh) := by
  have hh := HeckeDyadic.constant_absorbed_eventually C (dmin*(rmin*mesh-ε))
    (mul_pos hd (by linarith))
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ
  intro d r cap hd' hr'
  have hZp : 0<Z := by linarith
  have hU : 0<Z^d := Real.rpow_pos_of_pos hZp _
  have hgr : rmin*mesh-ε≤r*mesh-ε := by nlinarith
  have hexp : dmin*(rmin*mesh-ε)≤d*(r*mesh-ε) :=
    mul_le_mul hd' hgr (by linarith) (hd.trans_le hd').le
  have hc : C≤(Z^d)^(r*mesh-ε) := by
    apply hC.trans
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  calc
    _ ≤ (Z^d)^(r*mesh-ε)*(Z^d)^(cap*r+ε) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU.le _)
    _ = ((Z^d)^r)^(cap+mesh) := by
      rw [←Real.rpow_add hU,←Real.rpow_mul hU.le]
      congr 1
      ring

theorem actual_bins_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0<dmin) (hr : 0<rmin) (hmesh : 0<mesh) (hgap : ε<rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤d → ∀ r cap : ℝ, rmin≤r → 0≤cap →
      ∀ Q : ℂ, ‖Q‖≤C*(Z^d)^(cap*r+ε) →
      0≤amplitude ((Z^d)^r) cap mesh Q ∧
      amplitude ((Z^d)^r) cap mesh Q≤cap ∧
      amplitude ((Z^d)^r) cap mesh Q∈labels cap mesh ∧
      ‖Q‖≤((Z^d)^r)^(amplitude ((Z^d)^r) cap mesh Q+mesh) ∧
      (0<amplitude ((Z^d)^r) cap mesh Q →
        (Z^d)^(2*r*amplitude ((Z^d)^r) cap mesh Q)≤‖Q‖^2) := by
  filter_upwards [upper_allowance_eventually C dmin rmin ε mesh hd hmesh hgap,
    eventually_gt_atTop (1 : ℝ)] with Z hallow hZ
  intro d hd' r cap hr' hcap Q hQ
  have hU : 1<Z^d := Real.one_lt_rpow hZ (hd.trans_le hd')
  have hP : 1<(Z^d)^r := Real.one_lt_rpow hU (hr.trans_le hr')
  have hb := amplitude_bounds ((Z^d)^r) cap mesh Q hcap
  exact ⟨hb.1,hb.2,amplitude_mem_labels _ cap mesh Q hmesh,
    amplitude_upper _ cap mesh Q hP hmesh (hQ.trans (hallow d r cap hd' hr')),
    squared_spike (Z^d) r cap mesh Q hU (hr.trans_le hr') hmesh⟩

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI
