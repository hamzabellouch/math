import Mathlib
import OAI.GroupTheory.SimpleAmenable.Amenability.BarrierSignals
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.OrderedSubdivision

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section BarrierCore
open Classical

theorem conjugateLineForm_site {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (z : FlagSite a m D v) (j : Fin 4) (c : CutRing)
    (hc : cutForm a j (barrierSitePoint z)=ordinary c) :
    conjugateLineForm a j (flagSiteConjugate z)=conjugate c := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  have hpoint : (ordinary (flagSiteNumerator z).1,ordinary (flagSiteNumerator z).2)=
      (D:ℝ) • barrierSitePoint z := by
    rw [show barrierSitePoint z=scaledOrdinary D (flagSiteNumerator z) from (flagSiteNumerator_spec z).symm]
    apply Prod.ext <;> simp [scaledOrdinary,mul_div_cancel₀ _ hD']
  have hlevel : integralCutForm a j (flagSiteNumerator z)=(D:CutRing)*c := by
    apply ordinary_injective
    rw [←cutForm_ordinary,hpoint,cutForm_smul,hc,map_mul,map_natCast]
  have hconj : flagSiteConjugate z=(D:ℝ)⁻¹ •
      (conjugate (flagSiteNumerator z).1,conjugate (flagSiteNumerator z).2) := by
    apply Prod.ext <;> simp [flagSiteConjugate,scaledConjugate,div_eq_mul_inv,mul_comm]
  rw [hconj,map_smul,conjugateLineForm_integral,hlevel,map_mul,map_natCast]
  simp [hD']

noncomputable def conjugateIntersectionCoefficient (a : ℕ) (i j : Fin 4) : ℝ :=
  (|conjugate (lineNormal a i).1|+|conjugate (lineNormal a i).2|+
    |conjugate (lineNormal a j).1|+|conjugate (lineNormal a j).2|)/|conjugate (lineDet a i j)|

theorem conjugateIntersectionCoefficient_nonneg (a : ℕ) (i j : Fin 4) :
    0≤conjugateIntersectionCoefficient a i j := by unfold conjugateIntersectionCoefficient; positivity

theorem conjugateLineForm_bound {a : ℕ} (ha : 0<a) (i j : Fin 4) (hij : i≠j)
    (c d : ℝ) (p : ℝ×ℝ) (hi : conjugateLineForm a i p=c)
    (hj : conjugateLineForm a j p=d) {δ : ℝ} (hδ : 0≤δ) (hc : |c|≤δ) (hd : |d|≤δ) :
    ‖p‖≤conjugateIntersectionCoefficient a i j*δ := by
  have hdet : conjugate (lineNormal a i).1*conjugate (lineNormal a j).2-
      conjugate (lineNormal a j).1*conjugate (lineNormal a i).2≠0 := by
    have hh := conjugate_injective.ne (lineDet_ne_zero ha i j hij)
    simpa only [lineDet,map_sub,map_mul,map_zero] using hh
  have hi' : conjugate (lineNormal a i).1*p.1+conjugate (lineNormal a i).2*p.2=c := by
    simpa [conjugateLineForm] using hi
  have hj' : conjugate (lineNormal a j).1*p.1+conjugate (lineNormal a j).2*p.2=d := by
    simpa [conjugateLineForm] using hj
  have hh := real_two_lines_distance_bound _ _ _ _ c d hdet p 0 hi' hj' δ hδ
    (by simpa using hc) (by simpa using hd)
  simpa [dist_zero_right,conjugateIntersectionCoefficient,lineDet] using hh

theorem exists_barrierIntersection_core {a : ℕ} (ha : 0<a) (Q B : ℝ) :
    ∃R : ℝ,0<R ∧ ∀N : ℝ,1≤N → ∀i j : Fin 4,i≠j → ∀c d : CutRing,
      |conjugate c|≤4*N+Q → |conjugate d|≤B → ∀p : ℝ×ℝ,
      conjugateLineForm a i p=conjugate c → conjugateLineForm a j p=conjugate d →
      ‖p‖≤R*N := by
  let C := ∑i : Fin 4,∑j : Fin 4,conjugateIntersectionCoefficient a i j
  have hC : 0≤C := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun j _ => conjugateIntersectionCoefficient_nonneg a i j))
  have hCij (i j : Fin 4) : conjugateIntersectionCoefficient a i j≤C := by
    apply (Finset.single_le_sum (fun k _ => conjugateIntersectionCoefficient_nonneg a i k)
      (Finset.mem_univ j)).trans
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg
      (fun l _ => conjugateIntersectionCoefficient_nonneg a k l)) (Finset.mem_univ i)
  let A := 4+|Q|+|B|
  have hA : 0<A := by dsimp [A]; positivity
  refine ⟨1+C*A,by positivity,?_⟩
  intro N hN i j hij c d hc hd p hi hj
  have hN₀ : 0<N := lt_of_lt_of_le zero_lt_one hN
  have hc' : |conjugate c|≤A*N := by
    have hQ : |Q|≤|Q| *N := le_mul_of_one_le_right (abs_nonneg _) hN
    have hBN : 0≤|B| *N := mul_nonneg (abs_nonneg _) hN₀.le
    dsimp [A]; nlinarith [le_abs_self Q]
  have hd' : |conjugate d|≤A*N := by
    have hB : |B|≤|B| *N := le_mul_of_one_le_right (abs_nonneg _) hN
    have hQN : 0≤|Q| *N := mul_nonneg (abs_nonneg _) hN₀.le
    dsimp [A]; nlinarith [le_abs_self B]
  have hh := conjugateLineForm_bound ha i j hij (conjugate c) (conjugate d) p hi hj
    (mul_nonneg hA.le hN₀.le) hc' hd'
  calc
    ‖p‖≤conjugateIntersectionCoefficient a i j*(A*N) := hh
    _ ≤ C*(A*N) := mul_le_mul_of_nonneg_right (hCij i j) (by positivity)
    _ ≤ (1+C*A)*N := by nlinarith

theorem exists_barrierIncoming_core {a : ℕ} (ha : 0<a) :
    ∃R : ℝ,0<R ∧ ∀m : ℕ,∀i : Fin m,∀N : ℝ,1≤N → ∀j : Fin 4,∀c : CutRing,
      ∀hc : c∈barrierCandidate a j N,
      ‖flagSiteConjugate (barrierIncomingSite ha i hc)‖≤R*N := by
  obtain ⟨R,hR,hcore⟩ := exists_barrierIntersection_core ha 0 0
  refine ⟨R,hR,?_⟩
  intro m i N hN j c hc
  obtain ⟨k,hkj,hk⟩ := barrierIncoming_edge hc
  apply hcore N hN j k hkj.symm c 0 (by simpa using hc.1) (by simp)
  · apply conjugateLineForm_site (commonVertexDenominator_pos ha)
    exact cutForm_barrierLinePoint a j c _
  · apply conjugateLineForm_site (commonVertexDenominator_pos ha)
    exact hk

end BarrierCore

section BarrierSignalGeometry
open Classical Set

theorem scaledSiteConjugate_eq_smul {a m D : ℕ} {v : ℝ×ℝ} (N : ℝ)
    (z : FlagSite a m D v) : scaledSiteConjugate N z=N⁻¹ • flagSiteConjugate z := by
  apply Prod.ext <;> simp [scaledSiteConjugate,div_eq_mul_inv,mul_comm]

theorem norm_scaledSiteConjugate {a m D : ℕ} {v : ℝ×ℝ} {N : ℝ} (hN : 0<N)
    (z : FlagSite a m D v) : ‖scaledSiteConjugate N z‖=‖flagSiteConjugate z‖/N := by
  rw [scaledSiteConjugate_eq_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hN]
  ring

theorem conjugateLineForm_scaledSite {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (z : FlagSite a m D v) (j : Fin 4) (c : CutRing) (N : ℝ)
    (hc : cutForm a j (barrierSitePoint z)=ordinary c) :
    conjugateLineForm a j (scaledSiteConjugate N z)=conjugate c/N := by
  rw [scaledSiteConjugate_eq_smul,map_smul,conjugateLineForm_site hD z j c hc]
  simp [div_eq_mul_inv,mul_comm]

theorem firstSignal_true_norm {a m D : ℕ} {v : ℝ×ℝ} {N R : ℝ}
    (θ : (ℝ×ℝ) → ℝ) (b : FlagSite a m D v → Bool)
    (hθ : ∀x,R≤‖x‖ → θ x=-3) (hs : signalSuccess (flagMeanSignal θ N) b)
    (z : FlagSite a m D v) (hz : b z=true) : ‖scaledSiteConjugate N z‖<R := by
  by_contra h
  have hh := (hs z).2 (show flagMeanSignal θ N z≤-2 by
    rw [flagMeanSignal,hθ _ (le_of_not_gt h)]; norm_num)
  rw [hz] at hh
  cases hh

theorem firstSignal_true_in_box {a m D : ℕ} {v : ℝ×ℝ} {N R : ℝ} (hN : 0<N)
    (θ : (ℝ×ℝ) → ℝ) (b : FlagSite a m D v → Bool)
    (hθ : ∀x,R≤‖x‖ → θ x=-3) (hs : signalSuccess (flagMeanSignal θ N) b)
    (z : FlagSite a m D v) (hz : b z=true) : z∈flagSiteBox (N*R) := by
  have hh := firstSignal_true_norm θ b hθ hs z hz
  rw [norm_scaledSiteConjugate hN,div_lt_iff₀ hN] at hh
  change |(flagSiteConjugate z).1|≤N*R ∧ |(flagSiteConjugate z).2|≤N*R
  rw [Prod.norm_def,max_lt_iff,Real.norm_eq_abs,Real.norm_eq_abs] at hh
  constructor <;> linarith [hh.1,hh.2]

noncomputable def finiteFirstMarks {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {N R : ℝ} (hN : 0<N) (hR : 0<R) (b : FlagSite a m D v → Bool) :
    Finset (FlagSite a m D v) := (flagBoxFinset hD (mul_pos hN hR)).filter (fun z => b z=true)

theorem mem_finiteFirstMarks_iff {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {N R : ℝ} (hN : 0<N) (hR : 0<R) (θ : (ℝ×ℝ) → ℝ) (b : FlagSite a m D v → Bool)
    (hθ : ∀x,R≤‖x‖ → θ x=-3) (hs : signalSuccess (flagMeanSignal θ N) b)
    (z : FlagSite a m D v) : z∈finiteFirstMarks hD hN hR b ↔ b z=true := by
  simp only [finiteFirstMarks,Finset.mem_filter,mem_flagBoxFinset]
  exact ⟨And.right,fun hz => ⟨firstSignal_true_in_box hN θ b hθ hs z hz,hz⟩⟩

theorem firstSignal_true_finite {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {N R : ℝ} (hN : 0<N) (hR : 0<R) (θ : (ℝ×ℝ) → ℝ) (b : FlagSite a m D v → Bool)
    (hθ : ∀x,R≤‖x‖ → θ x=-3) (hs : signalSuccess (flagMeanSignal θ N) b) :
    {z | b z=true}.Finite := by
  apply (finiteFirstMarks hD hN hR b).finite_toSet.subset
  intro z hz
  exact (mem_finiteFirstMarks_iff hD hN hR θ b hθ hs z).mpr hz

theorem secondSignal_negative_empty {a m : ℕ} (ha : 0<a) (i : Fin m)
    {j : Fin 4} {N : ℝ} (hN : 0<N) {c : CutRing} (hc : c∈barrierCandidate a j N)
    (M : Finset (FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j)))
    (θ : (ℝ×ℝ) → ℝ)
    (b : FlagSite a m (commonVertexDenominator a) (barrierFlagDirection ha j) → Bool)
    (hθ : ∀x,3 ≤ |conjugateLineForm a j x| → θ x=-3)
    (hs : signalSuccess (flagMeanSignal θ N) b) (hcneg : 3*N ≤ |conjugate c|) :
    barrierActiveIntervals ha i j c M b=∅ := by
  apply barrierActiveIntervals_empty ha i hc M b
  intro z _ hz
  apply (hs z).2
  rw [flagMeanSignal,hθ]
  · norm_num
  · rw [conjugateLineForm_scaledSite (commonVertexDenominator_pos ha) z j c N hz,
      abs_div,abs_of_pos hN]
    exact (le_div_iff₀ hN).mpr hcneg

theorem cutoff_mismatch_negative {N Q c q : ℝ} (hN : Q<N) (hq : |q| ≤ Q)
    (hcut : 4*N < |c+q|) : 3*N < |c| := by
  have hh := abs_add_le c q
  linarith

end BarrierSignalGeometry

end SimpleAmenable
end
end

end OAI
