import Mathlib
import OAI.Geometry.SmoothYau.DifferentialEq.ExistsSphericalGlobalQuasimodes
import OAI.Geometry.SmoothYau.Estimates.EventualProductScalarCorrectionRate
import OAI.Geometry.SmoothYau.Smoothness.EventuallyPositiveFactorEventualJets

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [CompactSpace M]
namespace CompactMetricAtlas
variable {g : SmoothMetric E M} {k : ℕ} {hs : Module.finrank ℝ E < 2*(2*(k:ℝ))}
  (A : CompactMetricAtlas g k hs)

theorem eventually_scalar_factor_raw
    (hd : Module.finrank ℝ E=3) (tests : List (CoordinateTest E M))
    (N P B D : ℕ) (hNP : N ≤ 2*(k+1))
    (hN : Module.finrank ℝ E < 2*(2*((k+1:ℕ):ℝ)-N))
    (hD : (P+8)+((2*B+21)*(2*(k+1)+2)+10)+2 ≤ D)
    {C : ℝ} (hC : 0 < C) (U W : ℕ → M → ℝ)
    (hU : ∀ n, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (U n))
    (hW : ∀ n x, 0 < W n x)
    (hdata : ∀ᶠ n : ℕ in atTop,
      (∀ x, W n x/(n:ℝ)^B ≤ |U n x|+
        Real.sqrt (coordinateGradientPair g (U n) (U n) x)/(n:ℝ)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j (U n ∘ (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*W n ((chartAt E (A.p i)).symm y)) ∧
      (∀ i : A.t, ∀ y ∈ A.scalarChartSupport i, ∀ j ≤ 2*(k+1)+1,
        ‖iteratedFDeriv ℝ j
          ((fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x) ∘
            (chartAt E (A.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*W n ((chartAt E (A.p i)).symm y))) :
    ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
      let s := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ b ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ s ∧
      (∀ x, 0 < b x ∧ 0 < s x) ∧
      (∀ x, weightedLaplacian g b (U n) x+sphereFrequency n*s x*U n x=0) ∧
      (tsupport (fun x => b x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      (tsupport (fun x => s x-1) ⊆
        tsupport (fun x => laplaceBeltrami g (U n) x+sphereFrequency n*U n x)) ∧
      ∃ v : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x =
          sphereFrequency n*b x^3*v x^5-sphereFrequency n*s x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |s x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => s x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt E t.center).symm) y‖ ≤ L*inverseFrequency n^P) := by
  classical
  let b := fun n : ℕ => intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) (U n)
  let s := fun n : ℕ => intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) (U n)
  let Coeff : ∀ i, A.PatchCoefficients i := fun i => (A.nonempty_patchCoefficients i).some
  have hscalar := A.eventually_scalar_exactification (2*(k+1)) B (P+8) D (by omega) hD
    hC U W hU hW hdata
  have hsm : ∀ᶠ n : ℕ in atTop,
      ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (b n) ∧ ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (s n) :=
    hscalar.mono (fun n hn => ⟨hn.1,hn.2.1⟩)
  have hj : ∀ᶠ n : ℕ in atTop,
      A.ChartJetBound (2*(k+1)) (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) ∧
      A.ChartJetBound (2*(k+1)) (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^(P+8)) :=
    hscalar.mono (fun n hn => ⟨hn.2.2.2.2.1,hn.2.2.2.2.2.1⟩)
  have hfactor := A.eventually_positive_factor_of_eventual_jets hd Coeff N P hN b s hsm hj
  obtain ⟨T,hT,hraw⟩ := A.chartJetBound_controls_finite_real_raw tests N
  let L := 1+T+(Fintype.card A.t:ℝ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hTL : T ≤ L := by dsimp [L]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card A.t); linarith
  have hcardL : (Fintype.card A.t:ℝ) ≤ L := by dsimp [L]; linarith
  refine ⟨L,hL,?_⟩
  filter_upwards [hscalar,hj,hfactor,eventually_ge_atTop 1] with n hsc hj hv hn1
  obtain ⟨v,hv,hvpos,hveq,hvj⟩ := hv
  have hni : 0 ≤ inverseFrequency n := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hni1 : inverseFrequency n ≤ 1 := by
    unfold inverseFrequency
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
  have hpow : inverseFrequency n^(P+8) ≤ inverseFrequency n^P :=
    pow_le_pow_of_le_one hni hni1 (by omega)
  have hbj : A.ChartJetBound N (fun x => ((b n x-1:ℝ):ℂ)) (inverseFrequency n^P) :=
    fun i j hjN y => (hj.1 i j (hjN.trans hNP) y).trans hpow
  have hsj : A.ChartJetBound N (fun x => ((s n x-1:ℝ):ℂ)) (inverseFrequency n^P) :=
    fun i j hjN y => (hj.2 i j (hjN.trans hNP) y).trans hpow
  have hrawb := hraw (fun x => b n x-1) (hsc.1.sub contMDiff_const)
    _ (pow_nonneg hni _) hbj
  have hraws := hraw (fun x => s n x-1) (hsc.2.1.sub contMDiff_const)
    _ (pow_nonneg hni _) hsj
  have hrawv := hraw (fun x => v x-1) (hv.sub contMDiff_const)
    _ (pow_nonneg hni _) hvj
  refine ⟨hsc.1,hsc.2.1,hsc.2.2.1,hsc.2.2.2.1,
    hsc.2.2.2.2.2.2.2.1,hsc.2.2.2.2.2.2.2.2,v,hv,hvpos,hveq,?_,?_⟩
  · intro x
    have value {f : M → ℝ}
        (hf : A.ChartJetBound N (fun y => ((f y:ℝ):ℂ)) (inverseFrequency n^P)) :
        |f x| ≤ L*inverseFrequency n^P := by
      have hh := A.chartJetBound_global_value (pow_nonneg hni _) hf x
      simp only [Complex.norm_real,Real.norm_eq_abs] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hcardL (pow_nonneg hni _))
    exact ⟨value hbj,value hsj,value hvj⟩
  · intro t ht y hy j hj
    have hbound := mul_le_mul_of_nonneg_right hTL (pow_nonneg hni P)
    exact ⟨(hrawb t ht y hy j hj).trans hbound,
      (hraws t ht y hy j hj).trans hbound,(hrawv t ht y hy j hj).trans hbound⟩
end CompactMetricAtlas
end YauCounterexamples
end


namespace YauCounterexamples
open Filter

lemma eventual_choice_with_good_default {α β : Type*} {l : Filter α}
    (Q : β → Prop) (b : β) (hb : Q b) (P : α → β → Prop)
    (h : ∀ᶠ a in l, ∃ u, Q u ∧ P a u) :
    ∃ u : α → β, (∀ a, Q (u a)) ∧ ∀ᶠ a in l, P a (u a) := by
  classical
  let good (a : α) := ∃ u, Q u ∧ P a u
  let u : α → β := fun a => if ha : good a then ha.choose else b
  refine ⟨u,fun a => ?_,?_⟩
  · by_cases ha : good a
    · simpa only [u,dite_eq_left ha] using ha.choose_spec.1
    · simpa only [u,dite_eq_right ha] using hb
  · filter_upwards [h] with a ha
    change good a at ha
    simpa only [u,dite_eq_left ha] using ha.choose_spec.2
end YauCounterexamples


noncomputable section
open Set Filter Manifold Metric MeasureTheory BoxIntegral
open scoped Topology ContDiff ENNReal
namespace YauCounterexamples

theorem exists_spherical_scalar_producer
    (g₀ : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    (g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg : g ∈ sphericalProfileMetricNeighborhood)
    {t s r : ℝ} (ht : (1/5 : ℝ) ≤ t) (hts : t < s) (hsr : s < r) (hr : r < 3/10)
    {F : Set (Sphere 3)} (hF : IsClosed F)
    (hFt : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q < t)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (hmetric : ∀ y ∈ sphericalCoverage sourcePole sourceAxisOne sourceAxisTwo (3/10),
      ∀ v : Euclidean 3, selfMetricFlat (sphereChartMetric g sourcePole) y v v ≤ ‖v‖^2)
    (A : ℝ) :
    ∃ partition : TaggedPrepartition sourceSignBox, partition.IsPartition ∧ ∃ ℓ : Box (Fin 3) → ℝ,
      (∀ J ∈ partition, 0 < ℓ J) ∧ ∃ ε > 0,
    ∀ (tests : List (CoordinateTest (Euclidean 3) (Sphere 3))) (N P : ℕ),
      ∃ L > 0, ∀ᶠ n : ℕ in atTop,
      ∃ u : Euclidean 3 → ℝ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
        tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
          ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
      let U := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u
      let b := intrinsicCorrectionB g (n:ℝ) (sphereFrequency n) U
      let z := intrinsicCorrectionS g (n:ℝ) (sphereFrequency n) U
      (∀ x, U x=0 → 0 < coordinateGradientPair g U U x) ∧
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ b ∧
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ z ∧
      (∀ x, 0 < b x ∧ 0 < z x) ∧
      (∀ x, weightedLaplacian g b U x+sphereFrequency n*z x*U x=0) ∧
      tsupport (fun x => b x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
      tsupport (fun x => z x-1) ⊆ tsupport (fun x => laplaceBeltrami g U x+sphereFrequency n*U x) ∧
      ∃ v : Sphere 3 → ℝ, ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ v ∧ (∀ x, 0 < v x) ∧
        (∀ x, weightedLaplacian g b v x = sphereFrequency n*b x^3*v x^5-sphereFrequency n*z x*v x) ∧
        (∀ x, |b x-1| ≤ L*inverseFrequency n^P ∧
          |z x-1| ≤ L*inverseFrequency n^P ∧ |v x-1| ≤ L*inverseFrequency n^P) ∧
        (∀ a ∈ tests, ∀ y ∈ a.compactSet, ∀ j ≤ N,
          ‖iteratedFDeriv ℝ j ((fun x => b x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => z x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P ∧
          ‖iteratedFDeriv ℝ j ((fun x => v x-1) ∘ (chartAt (Euclidean 3) a.center).symm) y‖ ≤ L*inverseFrequency n^P) ∧
        ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
          (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
          (fun a => ε/((n:ℝ)*ℓ a.val))
          ((U ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) := by
  classical
  obtain ⟨φ,hφ,hin,hout,partition,hpart,ℓ,hℓ,ε,hε,hproduce⟩ :=
    exists_spherical_global_quasimodes g₀ hg₀ g hg ht hts hsr hr hF hFt hext hmetric A
  refine ⟨partition,hpart,ℓ,hℓ,ε,hε,?_⟩
  intro tests N P
  let k := N+2
  have hs : Module.finrank ℝ (Euclidean 3) < 2*(2*(k:ℝ)) := by
    simp only [Euclidean,finrank_euclideanSpace,Fintype.card_fin,k,Nat.cast_add,Nat.cast_ofNat]
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  let atlas := Classical.choice (nonempty_compactMetricAtlas g k hs)
  let D := (P+8)+((2*110+21)*(2*(k+1)+2)+10)+2
  obtain ⟨C,hC,hpacket⟩ := hproduce atlas.t atlas.p atlas.scalarChartSupport
    atlas.scalarChartSupport_compact (2*(k+1)+2) D
  let good (u : Euclidean 3 → ℝ) := ContDiff ℝ ∞ u ∧ HasCompactSupport u
  have hzero : good 0 := ⟨contDiff_const,by simpa using (HasCompactSupport.zero : HasCompactSupport (0 : Euclidean 3 → ℝ))⟩
  obtain ⟨u,hu,hpacket⟩ := eventual_choice_with_good_default good 0 hzero
    (fun n u => tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
      ((chartAt (Euclidean 3) sourcePole).symm y) < r} ∧
      (∀ q : Sphere 3, sphericalWeight φ n q/(n:ℝ)^110 ≤
        |(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q|+
        Real.sqrt (coordinateGradientPair g
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u)
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q)/(n:ℝ)) ∧
      (∀ i : atlas.t, ∀ y ∈ atlas.scalarChartSupport i, ∀ j ≤ 2*(k+1)+2,
        ‖iteratedFDeriv ℝ j ((roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) ∘
          (chartAt (Euclidean 3) (atlas.p i)).symm) y‖ ≤
          C*(n:ℝ)^(j+4)*sphericalWeight φ n ((chartAt (Euclidean 3) (atlas.p i)).symm y) ∧
        ‖iteratedFDeriv ℝ j ((fun q => laplaceBeltrami g
          (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q+
          sphereFrequency n*(roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q) ∘
          (chartAt (Euclidean 3) (atlas.p i)).symm) y‖ ≤
          C*(n:ℝ)^4/(n:ℝ)^D*sphericalWeight φ n ((chartAt (Euclidean 3) (atlas.p i)).symm y)) ∧
      ENNReal.ofReal (A*(n:ℝ)) < SignTests.signCertificate
        (fun a : {J : Box (Fin 3) // J ∈ partition.boxes} => Box.Ioo a.val)
        (fun a => ε/((n:ℝ)*ℓ a.val))
        (((roundPower sourceAxisOne sourceAxisTwo n ∘
          (chartAt (Euclidean 3) sourcePole).symm)+u) ∘ normalWaveEquiv))
    (hpacket.mono (by
      rintro n ⟨u,hu,hc,hs,hlow,hj,hscore,_⟩
      exact ⟨u,⟨hu,hc⟩,hs,hlow,hj,hscore⟩))
  let U (n : ℕ) := roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift (u n)
  have hU (n : ℕ) : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ (U n) :=
    (roundPower_smooth _ _ _).add (sphericalWaveLift_smooth (hu n).1 (hu n).2)
  have hNP : N ≤ 2*(k+1) := by dsimp [k]; omega
  have hN : Module.finrank ℝ (Euclidean 3) < 2*(2*((k+1:ℕ):ℝ)-N) := by
    simp only [Euclidean,finrank_euclideanSpace,Fintype.card_fin,k,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    have := Nat.cast_nonneg (α := ℝ) N
    linarith
  obtain ⟨L,hL,hfactor⟩ := atlas.eventually_scalar_factor_raw (by simp [Euclidean]) tests
    N P 110 D hNP hN (by exact le_rfl) hC U (sphericalWeight φ) hU (sphericalWeight_pos φ)
    (hpacket.mono (fun n hn => ⟨hn.2.1,
      fun i y hy j hj => (hn.2.2.1 i y hy j hj).1,
      fun i y hy j hj => (hn.2.2.1 i y hy j (by omega)).2⟩))
  refine ⟨L,hL,?_⟩
  filter_upwards [hpacket,hfactor,eventually_ge_atTop (1:ℕ)] with n hp hf hn
  obtain ⟨hb,hz,hpos,heq,hbs,hzs,v,hv,hvp,hve,hsmall,hraw⟩ := hf
  have hreg (x : Sphere 3) (hx : U n x=0) : 0 < coordinateGradientPair g (U n) (U n) x := by
    have hlow := hp.2.1 x
    change sphericalWeight φ n x/(n:ℝ)^110 ≤ |U n x|+_ at hlow
    rw [hx,abs_zero,zero_add] at hlow
    have hnpos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    have hsqrt : 0 < Real.sqrt (coordinateGradientPair g (U n) (U n) x) := by
      have hdiv := (div_pos (sphericalWeight_pos φ n x) (pow_pos hnpos 110)).trans_le hlow
      exact (div_pos_iff_of_pos_right hnpos).mp hdiv
    exact Real.sqrt_pos.mp hsqrt
  refine ⟨u n,(hu n).1,(hu n).2,hp.1,hreg,hb,hz,hpos,heq,hbs,hzs,v,hv,hvp,hve,hsmall,hraw,?_⟩
  have he : ((U n ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)=
      (((roundPower sourceAxisOne sourceAxisTwo n ∘
        (chartAt (Euclidean 3) sourcePole).symm)+u n) ∘ normalWaveEquiv) := by
    funext x
    simp only [U,Function.comp_apply,Pi.add_apply,sphericalWaveLift_apply]
  rw [he]
  exact hp.2.2.2

end YauCounterexamples
end

end OAI
