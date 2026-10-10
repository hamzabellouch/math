import OAI.MeasureTheory.Falconer.Angular.SelectedAngularBins
import OAI.MeasureTheory.Falconer.Angular.StationaryArcLength

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

noncomputable def circleAngularBin (n j : ℕ) (dir : UnitCircle) : ℝ :=
  periodicAngularBin n j (sourceAngle dir)

 theorem circleAngularBin_comp (n j : ℕ) (θ : ℝ) :
    circleAngularBin n j (sourceUnitDirection θ) = periodicAngularBin n j θ :=
  periodic_sourceAngle (periodicAngularBin_periodic n j) θ

 theorem circleAngularBin_continuous (n j : ℕ) : Continuous (circleAngularBin n j) := by
  let A := Icc (-Real.pi) Real.pi
  let : CompactSpace A := isCompact_iff_compactSpace.mp (show IsCompact A from isCompact_Icc)
  let f : A → UnitCircle := fun θ => sourceUnitDirection θ
  have hf : Continuous f := continuous_sourceUnitDirection.comp continuous_subtype_val
  have hs : Function.Surjective f := by
    intro dir
    refine ⟨⟨sourceAngle dir, (Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩,
      sourceUnitDirection_sourceAngle dir⟩
  apply (hf.isClosedMap.isQuotientMap hf hs).continuous_iff.mpr
  have he : circleAngularBin n j ∘ f = fun θ : A => periodicAngularBin n j θ := by
    funext θ
    exact circleAngularBin_comp n j θ
  rw [he]
  exact (periodicAngularBin_contDiff n j).continuous.comp continuous_subtype_val

 theorem circleAngularBin_partition {n : ℕ} (hn : 0 < n) (dir : UnitCircle) :
    ∑ j ∈ Finset.range n, circleAngularBin n j dir = 1 :=
  periodicAngularBin_partition hn (sourceAngle dir)

 theorem circleAngularBin_bounds (n j : ℕ) (dir : UnitCircle) :
    0 ≤ circleAngularBin n j dir ∧ circleAngularBin n j dir ≤ 1 :=
  periodicAngularBin_bounds n j (sourceAngle dir)

 theorem angularBinSelection_witness (p : ℤ → Prop) (t : ℝ)
    (h : angularBinSelection p t ≠ 0) : ∃ k : ℤ, p k ∧ |t-k| ≤ 1 := by
  classical
  have he : ∃ k : ℤ, (if p k then angularBinKernel (t-k) else 0) ≠ 0 := by
    by_contra hh
    push Not at hh
    exact h (by unfold angularBinSelection; simp only [hh, tsum_zero])
  obtain ⟨k,hk⟩ := he
  by_cases hp : p k
  · simp only [hp, ↓reduceIte] at hk
    have hs := angularBinKernel_tsupport (subset_closure hk)
    exact ⟨k,hp,abs_le.mpr hs⟩
  · simp [hp] at hk

 theorem angularBin_center_residue {n : ℕ} (hn : 0 < n) (j : ℕ) (k : ℤ)
    (hk : (k % (n : ℤ)).toNat = j) :
    sourceUnitDirection (2*Real.pi/(n : ℝ)*(k : ℝ)) =
      sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ)) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  have hr : k % (n : ℤ) = (j : ℤ) := by
    rw [← hk, Int.toNat_of_nonneg (Int.emod_nonneg k hn'.ne')]
  have he : (k : ℝ) = (j : ℝ)+(n : ℝ)*(k/(n : ℤ) : ℤ) := by
    exact_mod_cast (show k = (j : ℤ)+(n : ℤ)*(k/(n : ℤ)) by
      rw [← hr]; exact (Int.emod_add_mul_ediv k (n : ℤ)).symm)
  rw [he, show 2*Real.pi/(n : ℝ)*((j : ℝ)+(n : ℝ)*(k/(n : ℤ) : ℤ)) =
      2*Real.pi/(n : ℝ)*(j : ℝ)+(k/(n : ℤ) : ℤ)*(2*Real.pi) by field_simp]
  exact sourceUnitDirection_periodic.int_mul (k/(n : ℤ)) _

 theorem circleAngularBin_support_radius {n : ℕ} (hn : 0 < n) (j : ℕ) :
    Function.support (circleAngularBin n j) ⊆
      closedBall (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) (4*Real.pi/(n : ℝ)) := by
  intro dir hdir
  let θ := sourceAngle dir
  let t := (n : ℝ)/(2*Real.pi)*θ
  obtain ⟨k,hk,hnear⟩ := angularBinSelection_witness _ t hdir
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ : (0 : ℝ) < 2*Real.pi := by positivity
  have hid : θ-2*Real.pi/(n : ℝ)*(k : ℝ) = (2*Real.pi/(n : ℝ))*(t-k) := by
    dsimp [t]
    field_simp
  have hdist : dist θ (2*Real.pi/(n : ℝ)*(k : ℝ)) ≤ 2*Real.pi/(n : ℝ) := by
    rw [Real.dist_eq, hid, abs_mul, abs_of_pos (by positivity)]
    simpa using mul_le_mul_of_nonneg_left hnear (by positivity : 0 ≤ 2*Real.pi/(n : ℝ))
  change dist dir _ ≤ _
  rw [← angularBin_center_residue hn j k hk, ← sourceUnitDirection_sourceAngle dir]
  change dist (sourceDirection θ) (sourceDirection _) ≤ _
  apply (sourceDirection_dist_le θ _).trans
  calc
    _ ≤ 2*(2*Real.pi/(n : ℝ)) := mul_le_mul_of_nonneg_left hdist (by norm_num)
    _ = _ := by ring

 theorem circleAngularBin_tsupport_radius {n : ℕ} (hn : 0 < n) (j : ℕ) :
    tsupport (circleAngularBin n j) ⊆
      closedBall (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) (4*Real.pi/(n : ℝ)) :=
  closure_minimal (circleAngularBin_support_radius hn j) isClosed_closedBall

 theorem circleAngularBin_diameter {n : ℕ} (hn : 0 < n) (j : ℕ)
    {dir φ : UnitCircle} (hdir : dir ∈ tsupport (circleAngularBin n j))
    (hφ : φ ∈ tsupport (circleAngularBin n j)) : dist dir φ ≤ 8*Real.pi/(n : ℝ) := by
  have h1 := circleAngularBin_tsupport_radius hn j hdir
  have h2 := circleAngularBin_tsupport_radius hn j hφ
  have hd := dist_triangle dir (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) φ
  rw [dist_comm (sourceUnitDirection (2*Real.pi/(n : ℝ)*(j : ℝ))) φ] at hd
  exact hd.trans ((add_le_add h1 h2).trans_eq (by ring))

 theorem circleAngularBin_scale_diameter {δ : ℝ} (hδ : 0 < δ) (hcap : δ ≤ 2*Real.pi)
    (j : ℕ) {dir φ : UnitCircle}
    (hdir : dir ∈ tsupport (circleAngularBin (angularBinCount δ) j))
    (hφ : φ ∈ tsupport (circleAngularBin (angularBinCount δ) j)) : dist dir φ ≤ 4*δ := by
  have hb := (angularBinCount_bounds hδ hcap).1
  apply (circleAngularBin_diameter (angularBinCount_pos hδ) j hdir hφ).trans
  calc
    _ = 4*(2*Real.pi/(angularBinCount δ : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

end PlanarFalconer

end OAI
