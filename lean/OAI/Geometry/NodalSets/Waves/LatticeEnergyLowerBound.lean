import OAI.Geometry.NodalSets.Elliptic.FiniteJetEnergy
import OAI.Geometry.NodalSets.Waves.LatticeDirectionalCenters
import OAI.Geometry.NodalSets.Waves.LocalCovarianceGeometry

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric Filter
open scoped ContDiff Topology
noncomputable section

lemma compact_inner_ball {Q U : Set Coord} (hQ : IsCompact Q) (hU : IsOpen U) (hQU : Q ⊆ U) :
    ∃ r > 0, ∀ x ∈ Q, closedBall x r ⊆ U := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  obtain ⟨r,hr,hri⟩ := compact_family_common_radius isCompact_univ
    (fun z : Q × Coord ↦ (z.1:Coord)+z.2)
    ((continuous_subtype_val.comp continuous_fst).add continuous_snd)
    hU (fun t _ ↦ by simpa only [add_zero] using hQU t.property)
  refine ⟨r/2,by positivity,?_⟩
  intro x hx z hz
  have hn : ‖z-x‖ ≤ r/2 := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have h := hri ⟨x,hx⟩ (mem_univ _) (z-x) (by linarith)
  simpa using h

variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {D U : Set Coord} {m J K k0 : ℕ}
namespace LocalCompactWaveData
variable (a : LocalCompactWaveData g w S D m J K k0)

def latticeEnergy (hUD : U ⊆ D) (n : ℕ) (hfin : Fintype (SourceGrid U n))
    (x : Coord) (b : ℝ) (v : Coord) : ℝ :=
  letI := hfin
  ∑ i : SourceGrid U n × Fin 3,
    ‖dualWaveCoefficient n (latticeWave a.cover a.beams hUD n i.1 i.2) (S x) x b v‖^2

theorem lattice_energy_lower_bound (hUD : U ⊆ D) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Q : Set Coord} (hQ : IsCompact Q) (hQU : Q ⊆ U) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid U n), ∀ x ∈ Q, ∀ b v,
      c/(n:ℝ)*(b^2+‖v‖^2) ≤ a.latticeEnergy hUD n hfin x b v := by
  obtain ⟨mu,hmu,B,hB,hgeom⟩ := a.original_covariance_geometry
  obtain ⟨e,he,E,hE,heta⟩ := a.lattice_eta_bounds hUD
  let R : ℝ := (2*B+2)/mu
  have hR : 0 < R := by dsimp [R]; positivity
  let L := R+2
  have hL : 0 < L := by dsimp [L]; linarith
  have hlarge : 2*B+1 ≤ R*mu := by dsimp [R]; rw [div_mul_cancel₀ _ hmu.ne']; linarith
  obtain ⟨Ca,hCa,Cr,hCr,Ci,hCi,s,hs,C,hC,hjets⟩ := a.lattice_logarithmic_jet_estimates hUD L hL
  let F := B+E*B*L+Cr
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let kappa := e^2/(2*(e+F+1)^2)
  have hkappa : 0 < kappa := by dsimp [kappa]; positivity
  obtain ⟨r,hr,hinner⟩ := compact_inner_ball hQ hU hQU
  refine ⟨s^2*kappa/2,by positivity,?_⟩
  filter_upwards [hjets,eventually_nat_frequency (half_scale_eventually L 1 r hr),
    eventually_nat_frequency (half_scale_eventually (2*Cr) 1 e he)] with n hj hn hsmall
  have hn1 : 1 ≤ n := by exact_mod_cast hn.1
  have hnpos : 0 < n := by omega
  have hN : 0 < (n:ℝ) := by exact_mod_cast hnpos
  let h := (n:ℝ)^(-1/2:ℝ)
  have hh : 0 < h := lattice_scale_pos hnpos
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn.1 (by norm_num)
  let : Finite (SourceGrid U n) := finite_source_grid hUb hnpos
  let hfin : Fintype (SourceGrid U n) := Fintype.ofFinite _
  refine ⟨hfin,?_⟩
  intro x hx b v
  have hxD := hUD (hQU hx)
  have hball : closedBall x (L*h) ⊆ U := (closedBall_subset_closedBall hn.2.1).trans (hinner x hx)
  let z (v : Coord) : SourceGrid U n := ⟨directionalLatticeIndex n x R v,
    directional_center_mem hnpos x R hR.le v hball⟩
  let V (v : Coord) := latticeWave a.cover a.beams hUD n (z v) 0
  let yy (v : Coord) := scaledLatticePoint n (z v)
  have hdist (v : Coord) : ‖x-yy v‖ ≤ L*h := by
    rw [norm_sub_rev]
    exact directional_center_distance hnpos x R hR.le v
  have hjet (v : Coord) := hj (z v) 0 x (hdist v)
  let Rp := b+(normalizedLogJet n (V v) x v).re
  let Rm := b+(normalizedLogJet n (V (-v)) x v).re
  let pp := g (yy v) (x-yy v) v
  let pm := g (yy (-v)) (x-yy (-v)) v
  let ep := a.latticeEta hUD n (z v) 0
  let em := a.latticeEta hUD n (z (-v)) 0
  have hgp := hgeom (yy v) (hUD (z v).property)
  have hgm := hgeom (yy (-v)) (hUD (z (-v)).property)
  have hpp : pp ≤ -h*‖v‖ := rounded_positive_pairing (g (yy v)) mu B R h hmu hB.le hR.le hh.le
    hgp.1 hgp.2.2 hlarge x (yy v) v (directional_rounding_error hnpos x R v)
  have hpm : h*‖v‖ ≤ pm := by
    have hh' := rounded_positive_pairing (g (yy (-v))) mu B R h hmu hB.le hR.le hh.le
      hgm.1 hgm.2.2 hlarge x (yy (-v)) (-v) (directional_rounding_error hnpos x R (-v))
    simp only [map_neg,norm_neg] at hh'
    dsimp [pm]
    linarith
  have herr (u : Coord) : |(b+(normalizedLogJet n (V u) x v).re)-
      ((b+fderiv ℝ S x v)-a.latticeEta hUD n (z u) 0*g (yy u) (x-yy u) v)| ≤ Cr*h^2*‖v‖ := by
    have hh' := ((hjet u).2.2.2.2.2 v).1
    have heq : Cr/(n:ℝ)*‖v‖ = Cr*h^2*‖v‖ := by dsimp [h]; rw [half_scale_square hN]; ring
    rw [heq] at hh'
    convert hh' using 1
    congr 1
    ring
  have hdiff : e*h*‖v‖ ≤ Rp-Rm := opposite_real_products (b+fderiv ℝ S x v)
    Rp Rm ep em pp pm h ‖v‖ e Cr hh.le (norm_nonneg _) he.le
    (heta n (z v) 0).1 (heta n (z (-v)) 0).1 hpp hpm (herr v) (herr (-v)) hsmall.2.1
  have hprod : |ep*pp| ≤ E*B*L*‖v‖ := by
    have hpabs := (bilinear_pairing_bound (g (yy v)) (x-yy v) v).trans
      (show ‖g (yy v)‖*‖x-yy v‖*‖v‖ ≤ B*(L*h)*‖v‖ by
        gcongr
        · exact hgp.1
        · exact hdist v)
    have hepos : 0 ≤ ep := he.le.trans (heta n (z v) 0).1
    rw [abs_mul,abs_of_nonneg hepos]
    calc
      ep*|pp| ≤ E*(B*(L*h)*‖v‖) := mul_le_mul (heta n (z v) 0).2 hpabs (abs_nonneg _) hE.le
      _ ≤ E*(B*L*‖v‖) := by
        gcongr
        simpa using mul_le_mul_of_nonneg_left hh1 hL.le
      _ = _ := by ring
  have hSv : |fderiv ℝ S x v| ≤ B*‖v‖ :=
    ((fderiv ℝ S x).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hgeom x hxD).2.1 (norm_nonneg v))
  have hErr : Cr*h^2*‖v‖ ≤ Cr*‖v‖ := by
    have hh2 := pow_le_pow_left₀ hh.le hh1 2
    nlinarith [mul_nonneg hCr.le (norm_nonneg v)]
  have hlog : |(normalizedLogJet n (V v) x v).re| ≤ F*‖v‖ := by
    have hpR := abs_le.mp ((herr v).trans hErr)
    have hpP := abs_le.mp hprod
    have hpS := abs_le.mp hSv
    dsimp [F,Rp,ep,pp] at *
    apply abs_le.mpr
    constructor <;> nlinarith
  have hb : |b| ≤ |Rp|+F*‖v‖ := by
    have ht := norm_sub_le (b+(normalizedLogJet n (V v) x v).re) (normalizedLogJet n (V v) x v).re
    have ht' : |b| ≤ |Rp|+|(normalizedLogJet n (V v) x v).re| := by simpa only [add_sub_cancel_right,Real.norm_eq_abs] using ht
    exact ht'.trans (add_le_add le_rfl hlog)
  have hpair := paired_products_control b ‖v‖ Rp Rm h e F (norm_nonneg _) hh hh1 he hF hdiff hb
  let f (i : SourceGrid U n × Fin 3) := dualWaveCoefficient n
    (latticeWave a.cover a.beams hUD n i.1 i.2) (S x) x b v
  have hcoef (u : Coord) : s*|b+(normalizedLogJet n (V u) x v).re| ≤ ‖f (z u,0)‖ :=
    (mul_le_mul_of_nonneg_right (hjet u).2.2.2.2.1.1 (abs_nonneg _)).trans
      (real_log_product_le_coefficient n (V u) (S x) x b v (hjet u).2.2.2.1)
  have henergy := two_coefficient_energy f (z v,0) (z (-v),0) s Rp Rm hs.le (hcoef v) (hcoef (-v))
  have hpair' := mul_le_mul_of_nonneg_left hpair (sq_nonneg s)
  have hhbound := hpair'.trans henergy
  change s^2*(kappa*h^2*(b^2+‖v‖^2)) ≤ 2*a.latticeEnergy hUD n hfin x b v at hhbound
  calc
    _ = (s^2*(kappa*h^2*(b^2+‖v‖^2)))/2 := by dsimp [h]; rw [half_scale_square hN]; ring
    _ ≤ _ := (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr (by linarith)

end LocalCompactWaveData

end
end Yau.Geometry

end OAI
