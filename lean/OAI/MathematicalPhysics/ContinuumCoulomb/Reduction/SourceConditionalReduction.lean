import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceCloudComparison
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceTargetHubbard
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceContactMatrix
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceCalibrationBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceParameterSchedule
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHubbardPromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceThresholdGap
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteSourceBranch

namespace OAI

/-!
A polynomial-time source-to-unit-Coulomb reduction under explicit
analytic hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open SourcePositiveProgram SourceNuclearProgram HubbardGlobal

theorem exists_source_unit_reduction_with_planar_gap
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.ManufacturedPlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    (s : ℕ) :
    Nonempty (PolynomialManyOne binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (sourceHeisenbergPromise s) unitCoulombPromise) := by
  obtain ⟨rho,hrho,U,Fnum,Knum,qCloud,_hqCloud,hcloud⟩ :=
    source_cloud_comparison hflow hp hv hdensity
  have ha : (0:ℝ) < 8/(rho:ℝ) := div_pos (by norm_num) (by exact_mod_cast hrho)
  have hfreq := manufactured_frequency_positive hrho
  obtain ⟨Aweight,B,v,qTarget,_hAw,_hB,_hv,_hqTarget,htarget⟩ :=
    exists_source_target_parameters rho hrho s (s+14)
  obtain ⟨qLeak,_hqLeak,hleak⟩ := exists_source_leakage_threshold hfreq 6
  obtain ⟨qN,qC,_hqN,_hqC,hmat⟩ := exists_indexed_matrix_offsets rho hrho
  obtain ⟨qGap,_hqGap,hgap⟩ := exists_source_gap_offset ha
  obtain ⟨qScale,_hqScale,hscale⟩ := exists_manufactured_scale_threshold ha
  obtain ⟨kmin,hmin,hthreshold⟩ :=
    exists_source_exponent_threshold qCloud qN qGap (qTarget+qLeak) qScale 6 s v B
  let eps : ℚ := 1/100000000
  have heps : 0 < eps := by norm_num [eps]
  have hepsSmall : eps ≤ 1/1000 := by norm_num [eps]
  have htol : (eps:ℝ)/2 ≤ contactLengthTolerance := by norm_num [eps,contactLengthTolerance]
  obtain ⟨C,A,c,k,_hC,hc,_hk,hkmin,hcal⟩ :=
    PrefactorSourceContactProgram.exists_source_calibration rho hrho eps heps hepsSmall s B kmin
  have hkminN : kmin ≤ k := by exact_mod_cast hkmin
  have hkBig : 1100 ≤ k := hmin.trans hkminN
  have hconstraints := hthreshold k hkminN
  let extent := s+k/100+13
  let p := 60*B+s+14
  let pc := 12+p+9
  let h := qC+30*k+30*Aweight+extent+(12+p+7)+15
  let ap := qCloud+465*k+12+v+p+34
  let f := SourceUnitCoulomb.value rho C U Fnum Knum eps c s pc h k A B p ap
  have hcorrect (d : BinaryHeisenberg) (hd : d.Valid) (hpoly : d.PolynomialPromise s)
      (hvertices : 2 ≤ d.coordinate.length) :
      (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value → f d ∈ unitCoulombPromise.yes) ∧
      ((d.upper.value:ℝ) ≤ realSourceGroundEnergy (d.toSource hd) → f d ∈ unitCoulombPromise.no) := by
    have hMtwo := SourceBranchProgram.positive_output_vertices s d hd hvertices
    obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le hMtwo
    let m := n+1
    have hm : (output s d).vertices=m+1 := by dsimp only [m]; omega
    let N := SourceContactProgram.size d
    let u := indexedCoordinates rho C eps c s pc h k A B d hd hm
    let uu := fun i => PlanarForcingProgram.position (u i)
    let graph := indexedGraph s d hd hm
    let τ := ((N:ℝ)^(30*B))⁻¹
    let t := fun e => -coulombHoppingTarget (GaussianFrequency.frequency rho) τ (graph.weight e)
      ‖uu (graph.left e)-uu (graph.right e)‖
    let D := 25*(k:ℝ)*Real.log N
    have hN : 2 ≤ N := SourceContactProgram.size_ge_two d
    have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by norm_num) hNR
    have hN1 : (1:ℝ) ≤ N := le_trans (by norm_num) hNR
    have hhk : qCloud+9*6+72*extent+v+p ≤ k := by
      simpa only [extent,p] using hconstraints.1
    have hhP : 13 ≤ h := by dsimp [h]; omega
    have hP : 7200 ≤ N^h := ContactCalibratedGeometry.precision_ge_7200 hN hhP
    have hspacing := (hcal d hd hpoly).1
    have hsites : sites rho C eps c s pc h k A B d=List.ofFn u :=
      sites_eq_indexed rho C eps c s pc h k A B d hd hm
    have hcount : (m+1:ℕ) ≤ (N:ℝ)^6 := by
      rw [← hm]
      exact source_graph_site_count s d hd
    have hnorm (i : Fin (m+1)) : ‖uu i‖ ≤ (N:ℝ)^extent := by
      have hn := indexed_norm_bound rho C heps.le hc htol s pc h k A B d hd hpoly hkBig hP hspacing.2 hm i
      simpa only [uu,u,extent,N,Nat.add_comm s (k/100)] using hn
    have hsep (i j : Fin (m+1)) (hij : i ≠ j) : D ≤ ‖uu i-uu j‖ :=
      indexed_separation rho C heps.le hc htol s pc h k A B d hd hP hspacing.1 hm i j hij
    have hqLeak : qLeak ≤ k := by omega
    obtain ⟨hD,hleakM⟩ := hleak k hqLeak N D hNR le_rfl (m+1) hcount
    have hleakTwo : 2*localLeakageBound (GaussianFrequency.frequency rho) D ≤
        localDualMass (GaussianFrequency.frequency rho)/2 := by
      have hMtwoR : (2:ℝ) ≤ (m+1:ℕ) := by exact_mod_cast (show 2 ≤ m+1 by dsimp [m]; omega)
      exact (mul_le_mul_of_nonneg_right hMtwoR
        (localLeakageBound_nonnegative (GaussianFrequency.frequency rho) D)).trans hleakM
    have hqTarget : qTarget ≤ k := by omega
    obtain ⟨hweights,ht,hfinite⟩ := htarget d hd hpoly m k hm hqTarget D uu le_rfl hsep
    have hFweight : graph.weight=SourceContactProgram.weights s d hd := indexedGraph_weight s d hd hm
    have hKw (e : ContactMediator.GlobalEdge (SourceMetadataProgram.geometricSource s d hd)) :
        0 ≤ (SourceContactProgram.weights s d hd e:ℝ) ∧
          (SourceContactProgram.weights s d hd e:ℝ) ≤ (N:ℝ)^(30*Aweight) := by
      have hw := hweights e
      rw [hFweight] at hw
      exact ⟨(inv_nonneg.mpr (pow_nonneg hN0.le _)).trans hw.1,hw.2⟩
    have hnom (e : ContactMediator.GlobalEdge (SourceMetadataProgram.geometricSource s d hd)) :
        let r := PrefactorSourceContactProgram.nominalDistance rho (CalibrationMesh.prefactor rho)
          C eps c s pc k A B d hd e
        |(amplification rho k d:ℝ)*planarHopping r-
          coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^(30*B))⁻¹
            (SourceContactProgram.weights s d hd e) r| ≤ ((N:ℝ)^pc+1)⁻¹ := by
      have hh := ((hcal d hd hpoly).2 pc e).2.2.2
      simpa only [amplification_calibration,calibration_base_power] using hh
    have hknMatrix : qN+extent+(12+p+8) ≤ 5*k := by
      simpa only [extent,p] using hconstraints.2.1
    have hmatrix := hmat C s pc h k A B (30*Aweight) (12+p+7) eps c d hd hpoly heps.le hc htol
      hkBig hhP (by dsimp only [extent] at hknMatrix ⊢; omega) (by dsimp [h,extent]; omega)
      (by dsimp [pc]; omega) hD hspacing hleakTwo hKw hnom m hm
    have hs : 1 ≤ (amplification rho k d:ℝ) := by
      rw [amplification_real]
      exact hscale k (by omega) N hNR
    have hMN : (SourceMetadataProgram.size d:ℝ) ≤ N := by
      dsimp only [N,SourceContactProgram.size]
      rw [Nat.cast_add,Nat.cast_one]
      linarith
    have hgapScale := hgap s B k (by omega) N (SourceMetadataProgram.size d) hNR
      (Nat.cast_nonneg _) hMN
    have houtputGap := SourcePhysicalThreshold.gap_ge_one rho C eps c s pc h k A B p d hd hpoly
      (by simpa only [amplification_real,Nat.cast_pow] using hgapScale)
    obtain ⟨ho,hlo,hhi⟩ := hcloud 6 extent v p k ap C s pc h A B p eps c d hhk
      (by dsimp [ap]; omega) m n u (by dsimp [m]) (by omega)
      hsites (by simpa only [Nat.cast_add,Nat.cast_one] using hcount) hnorm D le_rfl hsep graph.left graph.right t ht
      (by simpa only [Complex.ofReal_mul] using hmatrix) houtputGap
    have hu : Function.Injective u := by
      intro i j hij
      by_contra hne
      have hdistance := hD.trans (hsep i j hne)
      simp only [uu,hij,sub_self,norm_zero] at hdistance
      norm_num at hdistance
    have hground :
        ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B p d u graph t-
          (amplification rho k d:ℝ)*((N:ℝ)^p)⁻¹:ℝ):EReal) ≤
            unitGroundEnergy ((f d).toData ho) ∧
        unitGroundEnergy ((f d).toData ho) ≤
          ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B p d u graph t+
            (amplification rho k d:ℝ)*((N:ℝ)^p)⁻¹:ℝ):EReal) := by
      simp only [SourcePhysicalThreshold.exactHubbardEnergy_eq rho C eps c s pc h k A B p d u graph t hm]
      have hnR : (n+2:ℝ)=(m+1:ℝ) := by dsimp only [m]; push_cast; ring
      simpa only [hnR] using And.intro hlo hhi
    exact SourceUnitCoulomb.promise_of_hubbard_interval rho C U Fnum Knum hrho eps c
      s pc h k A B p ap p (s+14) d hd hpoly u hu hsites graph hm
      (indexedGraph_toList s d hd hm) t ho hs (by rfl) le_rfl (by rfl)
      (by simpa only [Nat.cast_pow] using hfinite) hground
  obtain ⟨yesOutput,noOutput,hyesOutput,hnoOutput⟩ := exists_atomic_yes_no
  exact ⟨FiniteSourceBranch.reduction yesOutput noOutput hyesOutput hnoOutput s f
    (SourceUnitCoulomb.program rho C U Fnum Knum eps c s pc h k A B p ap)
    (fun d hd hp hv hy => (hcorrect d hd hp hv).1 hy)
    (fun d hd hp hv hn => (hcorrect d hd hp hv).2 hn)⟩

/-- The planar spectral hypothesis implies the estimate for the manufactured well. -/
theorem exists_source_unit_reduction_without_hydrogen
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    (s : ℕ) :
    Nonempty (PolynomialManyOne binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (sourceHeisenbergPromise s) unitCoulombPromise) :=
  exists_source_unit_reduction_with_planar_gap hflow
    (PlanarSobolev.manufacturedPlanarWell_gap hp) hv hdensity s

/-- A six-hypothesis form of the reduction, including the hydrogen spectral hypothesis. -/
theorem exists_source_unit_reduction
    (hflow : PublishedC4FlowInput)
    (hp : PlanarSobolev.PublishedNegativePlanarGroundGap)
    (hv : PublishedVerticalOscillatorGap) (hdensity : PublishedSobolevSmoothDensity)
    (_hh : PublishedHydrogenBottom) (s : ℕ) :
    Nonempty (PolynomialManyOne binaryHeisenbergCodec.encode unitCoulombCodec.encode
      (sourceHeisenbergPromise s) unitCoulombPromise) :=
  exists_source_unit_reduction_without_hydrogen hflow hp hv hdensity s

end ContinuumCoulomb

end

end OAI
