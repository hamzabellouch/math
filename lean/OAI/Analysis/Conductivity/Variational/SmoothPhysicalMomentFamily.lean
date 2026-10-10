import Mathlib
import OAI.Analysis.Conductivity.Variational.QuantitativePhysicalMoments
import OAI.Analysis.Conductivity.Variational.SmoothNormalizedEndFamily

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

lemma compact_supported_integral_smooth {f : P×Coord3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ q,tsupport (fun x => f (q,x))⊆K) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => ∫ x,f (q,x)) := by
  have he (q : P) : (∫ x in K,f (q,x))=∫ x,f (q,x) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      image_eq_zero_of_notMem_tsupport (f:=fun x => f (q,x)) (fun h => hx (hs q h)))
  simpa only [he] using contDiff_compact_integral (μ:=volume) hf hK

lemma physicalSourceMoment_family_smooth {u : P×Coord3 → Fin 2 → ℝ}
    (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) {r : Fin 2 → P×Coord3 → ℝ}
    (hr : ∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) {K : Set Coord3} (hK : IsCompact K)
    (hs : ∀ q,PairSupported (fun j x => r j (q,x)) K) :
    ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => physicalSourceMoment (fun x => u (q,x)) (fun j x => r j (q,x))) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact compact_supported_integral_smooth (hr 0) hK (fun q => hs q 0)
  · exact compact_supported_integral_smooth (hr 1) hK (fun q => hs q 1)
  · change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => ∫ x,u (q,x) 1*r 0 (q,x)-u (q,x) 0*r 1 (q,x))
    apply compact_supported_integral_smooth
      (((contDiff_apply ℝ ℝ 1).comp hu).mul (hr 0) |>.sub (((contDiff_apply ℝ ℝ 0).comp hu).mul (hr 1))) hK
    intro q
    exact (tsupport_sub _ _).trans (union_subset
      (tsupport_mul_subset_right.trans (hs q 0)) (tsupport_mul_subset_right.trans (hs q 1)))

lemma exists_physical_moments_at_regular
    {u : Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u)
    {O : Set Coord3} (hO : IsOpen O) {x : Coord3} (hx : x∈O)
    (hD : Function.Surjective (fderiv ℝ u x)) (m : Coord3) :
    ∃ r : PhysicalSourcePair,CompactSmoothPair r ∧ PairSupported r O ∧
      physicalSourceMoment u r=m := by
  obtain ⟨B,_⟩ := exists_regular_correction_box hu hO hx hD
  obtain ⟨r₀,r₁,hr₀,hr₁,hc₀,hc₁,hs₀,hs₁,hm₀,hm₁,hmt⟩ :=
    physical_overlap_moment_inverse B.chart B.smooth B.inverse_smooth B.widths B.subset_source m
  let r : PhysicalSourcePair := ![r₀,r₁]
  have hr : CompactSmoothPair r := by
    intro j; fin_cases j
    · exact ⟨hr₀,hc₀⟩
    · exact ⟨hr₁,hc₁⟩
  have hs : PairSupported r B.chart.target := by
    intro j; fin_cases j
    · exact hs₀
    · exact hs₁
  refine ⟨r,hr,hs.mono B.target_subset,?_⟩
  ext i
  fin_cases i
  · exact hm₀
  · exact hm₁
  · change (∫ x,u x 1*r₀ x-u x 0*r₁ x)=m 2
    rw [←hmt]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈B.chart.target
    · rw [B.potentials hy]; rfl
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs₀ h)),
        image_eq_zero_of_notMem_tsupport (fun h => hy (hs₁ h))]
      simp

lemma exists_smooth_matrix_inverse_extension {A : P → Mat3}
    (hA : ContDiff ℝ (↑(⊤:ℕ∞)) A) (p : P) (hp : (A p).det≠0) :
    ∃ B : P→Mat3,ContDiff ℝ (↑(⊤:ℕ∞)) B ∧ ∀ᶠ q in 𝓝 p,B q=(A q)⁻¹ := by
  let O := {q : P | (A q).det≠0}
  have hO : IsOpen O := isOpen_ne.preimage (hA.continuous.matrix_det)
  have hI : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun q => (A q)⁻¹) O :=
    fun q hq => (contDiffAt_matrix_inv hA.contDiffAt hq).contDiffWithinAt
  obtain ⟨χ,hχ,_,hχs,_,hχone⟩ := exists_smooth_core_cutoff isCompact_singleton
    (hO.inter Metric.isOpen_ball) (Metric.isBounded_ball.subset inter_subset_right)
    (show ({p}:Set P)⊆O∩Metric.ball p 1 from singleton_subset_iff.mpr ⟨hp,Metric.mem_ball_self zero_lt_one⟩)
  refine ⟨fun q => χ q • (A q)⁻¹,?_,?_⟩
  · apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact smooth_mul_of_support_in_open hO
      (by
        intro q hq
        exact ((contDiff_apply ℝ ℝ j).contDiffAt.comp_contDiffWithinAt q
          ((contDiff_apply ℝ (Fin 3 → ℝ) i).contDiffAt.comp_contDiffWithinAt q (hI q hq))))
      hχ (hχs.trans inter_subset_left)
  · filter_upwards [hχone p (mem_singleton p)] with q hq
    rw [hq,one_smul]

theorem smooth_physical_moment_family
    {u : P×Coord3 → Fin 2 → ℝ} (hu : ContDiff ℝ (↑(⊤:ℕ∞)) u) (p : P)
    {O : Set Coord3} (hO : IsOpen O) {x : Coord3} (hx : x∈O)
    (hD : Function.Surjective (fderiv ℝ (fun y => u (p,y)) x))
    {m : P → Coord3} (hm : ContDiff ℝ (↑(⊤:ℕ∞)) m) (hmz : m p=0) :
    ∃ K : Set Coord3,IsCompact K ∧ K⊆O ∧
      ∃ r : Fin 2 → P×Coord3 → ℝ,(∀ j,ContDiff ℝ (↑(⊤:ℕ∞)) (r j)) ∧
        (∀ q,PairSupported (fun j y => r j (q,y)) K) ∧ (∀ j y,r j (p,y)=0) ∧
        ∀ᶠ q in 𝓝 p,physicalSourceMoment (fun y => u (q,y)) (fun j y => r j (q,y))=m q := by
  classical
  have hup : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (p,y)) := hu.comp (contDiff_const.prodMk contDiff_id)
  choose g hg hs hgm using fun i : Fin 3 =>
    exists_physical_moments_at_regular hup hO hx hD (Pi.single i 1)
  let K := ⋃ i : Fin 3,⋃ j : Fin 2,tsupport (g i j)
  have hK : IsCompact K := isCompact_iUnion (fun i => isCompact_iUnion (fun j => (hg i j).2))
  have hKO : K⊆O := iUnion_subset (fun i => iUnion_subset (hs i))
  have hgK (i) : PairSupported (g i) K := fun j => subset_iUnion_of_subset i (subset_iUnion (fun j => tsupport (g i j)) j)
  let A : P→Mat3 := fun q i j => physicalSourceMoment (fun y => u (q,y)) (g j) i
  have hA : ContDiff ℝ (↑(⊤:ℕ∞)) A := by
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    exact (contDiff_apply ℝ ℝ i).comp (physicalSourceMoment_family_smooth hu
      (fun k => (hg j k).1.comp contDiff_snd) hK (fun _ => hgK j))
  have hAp : A p=1 := by
    ext i j
    simp [A,hgm,Pi.single_apply,Matrix.one_apply]
  obtain ⟨B,hB,hBi⟩ := exists_smooth_matrix_inverse_extension hA p (by rw [hAp]; simp)
  let c : P → Coord3 := fun q => B q*ᵥm q
  have hc : ContDiff ℝ (↑(⊤:ℕ∞)) c := by
    apply contDiff_pi.mpr; intro i
    change ContDiff ℝ (↑(⊤:ℕ∞)) (fun q => ∑ j : Fin 3,B q i j*m q j)
    exact ContDiff.sum (fun j _ => ((contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 3 → ℝ) i).comp hB)).mul ((contDiff_apply ℝ ℝ j).comp hm))
  let r : Fin 2 → P×Coord3 → ℝ := fun j z => ∑ i,c z.1 i*g i j z.2
  have hr (j) : ContDiff ℝ (↑(⊤:ℕ∞)) (r j) :=
    ContDiff.sum (fun i _ => (((contDiff_apply ℝ ℝ i).comp hc).comp contDiff_fst).mul ((hg i j).1.comp contDiff_snd))
  have hre (q) : (fun j y => r j (q,y))=∑ i,c q i • g i := by
    funext j y; simp [r,Finset.sum_apply]
  have hrs (q) : PairSupported (fun j y => r j (q,y)) K := by
    rw [hre]
    exact PairSupported.sum _ _ (fun i _ => (hgK i).smul _)
  have hrz (j) (y) : r j (p,y)=0 := by simp [r,c,hmz]
  refine ⟨K,hK,hKO,r,hr,hrs,hrz,?_⟩
  have hnear : ∀ᶠ q in 𝓝 p,(A q).det≠0 :=
    hA.continuous.matrix_det.continuousAt.eventually (isOpen_ne.mem_nhds (by change (A p).det≠0; rw [hAp]; simp))
  filter_upwards [hBi,hnear] with q hq hdet
  have huq : ContDiff ℝ (↑(⊤:ℕ∞)) (fun y => u (q,y)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  rw [hre,physicalSourceMoment_sum _ _ huq.continuous
    (fun i _ => (hg i).smul _)]
  simp_rw [physicalSourceMoment_smul]
  have hi : A q*ᵥc q=m q := by
    dsimp [c]
    rw [hq,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),Matrix.one_mulVec]
  ext i
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm,Matrix.mulVec,dotProduct,A] using congrFun hi i

end ScalarConductivity

end
end

end OAI
