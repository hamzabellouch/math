import OAI.Dynamics.ThreeTorus.Geometry
import OAI.Dynamics.ThreeTorus.RetainedPackets

namespace OAI

/-! Rounded common primitives, neutral and quantile families, exact indices, signal passages, and support tracking. -/

section

/-! The exact family of passage primitives used by the analytic estimates is
constructed from a periodic speed. The rounding is chosen before any jitter.
No smoothness or perturbation conclusion is assumed. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology
namespace ThreeTorus

lemma deriv_real_primitive {V : ℝ → ℝ} (hV : Continuous V) :
    deriv (fun x => ∫ t in 0..x, V t) = V := by
  funext x
  exact (intervalIntegral.integral_hasDerivAt_right (hV.intervalIntegrable 0 x)
    hV.aestronglyMeasurable.stronglyMeasurableAtFilter hV.continuousAt).deriv

/-- One integer-rounded primitive sequence works for every later choice of jitter.
In particular the estimates for a finite list can all use exactly this sequence. -/
theorem exists_rounded_primitive_family {V : ℝ → ℝ}
    (hp : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      ∀ J : ℝ → ℝ, ∀ hJp : Periodic J 1,
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J →
        let σ := fun (n : ℕ) (a : UnitAddCircle) => (((1+hJp.lift a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle)
        (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
          Smooth (torusPassage (H n) (σ n)).symm ∧
          MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
        (∀ n, 0 < n → ∀ x : Cover,
          torusPassage (H n) (σ n) (project x) =
            project (passageFamily V J 1 ((n:ℝ)⁻¹,Δ n) x) ∧
          (torusPassage (H n) (σ n)).symm (project x) =
            project (passageFamily V J (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
        ∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
          TendstoUniformlyOn
            (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J r ((n:ℝ)⁻¹,Δ n)) x)
            (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
            atTop K := by
  classical
  have hr : ∀ n : ℕ, ∃ d : ℝ, ∃ k : ℤ,
      (0 < n → |d| ≤ (n:ℝ)⁻¹) ∧ (n:ℝ)*((∫ t in 0..1, V t)+d) = k := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨d,k,hd,hk⟩ := passage_rounding (∫ t in 0..1, V t) hn
      exact ⟨d,k,fun _ => hd,hk⟩
    · have he : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      exact ⟨0,0,by simp⟩
  choose Δ k hΔ hk using hr
  have hsp (n : ℕ) : Periodic (fun x => (n:ℝ)*(V x+Δ n)) 1 :=
    (passage_rounded_slope hp hV.continuous n (Δ n) (hk n)).1
  have hsi (n : ℕ) : (∫ t in 0..1, (n:ℝ)*(V t+Δ n)) = k n :=
    (passage_rounded_slope hp hV.continuous n (Δ n) (hk n)).2
  have hsc (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (n:ℝ)*(V x+Δ n)) :=
    contDiff_const.mul (hV.add contDiff_const)
  let H n := circlePrimitive (hsp n) (hsc n).continuous (hsi n)
  have hHe (n : ℕ) (x : ℝ) : H n (x:UnitAddCircle) =
      ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle) := by
    rw [show H n (x:UnitAddCircle) = (((∫ t in 0..x, (n:ℝ)*(V t+Δ n)):ℝ):UnitAddCircle) from rfl]
    congr 1
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hV.continuous.intervalIntegrable 0 x) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    ring
  refine ⟨Δ,H,hΔ,(continuous_snd.tendsto (0,0)).comp (passage_parameters_tendsto hΔ),
    fun n => continuous_circlePrimitive (hsp n) (hsc n).continuous (hsi n),hHe,?_⟩
  intro J hJp hJ
  let σ := fun (n : ℕ) (a : UnitAddCircle) => (((1+hJp.lift a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle)
  have htsp (n : ℕ) : Periodic (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) 1 := by
    intro a
    dsimp only
    rw [hJp a]
  have hσ (n : ℕ) : σ n = circleSpeed (htsp n) := by
    funext a
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      change (((1+J a/(n:ℝ))/(n:ℝ):ℝ):UnitAddCircle) =
        ((((n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a):ℝ):UnitAddCircle)
      congr 1
      simp only [div_eq_mul_inv]
      ring
  refine ⟨?_,?_,?_⟩
  · intro n
    change Smooth (torusPassage (H n) (σ n)) ∧
      Smooth (torusPassage (H n) (σ n)).symm ∧
      MeasurePreserving (torusPassage (H n) (σ n)) μ μ
    rw [hσ]
    exact primitive_passage_properties (hsp n) (htsp n) (hsc n) (passage_speed_smooth hJ n) (hsi n)
  · intro n hn x
    change torusPassage (H n) (σ n) (project x) =
        project (passageFamily V J 1 ((n:ℝ)⁻¹,Δ n) x) ∧
      (torusPassage (H n) (σ n)).symm (project x) =
        project (passageFamily V J (-1) ((n:ℝ)⁻¹,Δ n) x)
    rw [hσ]
    have Hlift (u : ℝ) : H n (u:UnitAddCircle) =
        (((∫ t in 0..u, (n:ℝ)*(V t+Δ n)):ℝ):UnitAddCircle) := rfl
    have hgraphs : torusPassage (H n) (circleSpeed (htsp n)) (project x) =
          project (passageLift (fun u => ∫ t in 0..u, (n:ℝ)*(V t+Δ n))
            (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) x) ∧
        (torusPassage (H n) (circleSpeed (htsp n))).symm (project x) =
          project (passageInverseLift (fun u => ∫ t in 0..u, (n:ℝ)*(V t+Δ n))
            (fun a => (n:ℝ)⁻¹+(n:ℝ)⁻¹^2*J a) x) := by
      constructor
      · rw [torusPassage_apply]
        ext i
        fin_cases i <;> simp only [project,passageLift,circleSpeed_coe,
          ← AddCircle.coe_add,Hlift,← AddCircle.coe_sub] <;> rfl
      · rw [torusPassage_symm_apply]
        ext i
        fin_cases i <;> simp only [project,passageInverseLift,circleSpeed_coe,
          ← AddCircle.coe_add,Hlift,← AddCircle.coe_sub] <;> rfl
    rw [(passageLift_eq_family (J := J) hV.continuous hn (Δ n)).1,
      (passageLift_eq_family (J := J) hV.continuous hn (Δ n)).2] at hgraphs
    exact hgraphs
  · intro r K hK d
    exact passage_Cinfty_limit hV hJ hΔ r hK d

end ThreeTorus
end
end

section

/-! Finite simultaneous passages preserve all cross correlations exactly.
Distinct old angular indices are orthogonal in the new spare coordinate,
even when their new angular indices overlap. Equal old indices are handled
by the actual cylinder cutoffs, not by a spectral orthogonality assumption. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma continuous_twistIter {φ : UnitAddCircle → UnitAddCircle}
    (hφ : Continuous φ) (n : ℤ) : Continuous (twistIter φ n) :=
  (continuous_fst.add ((hφ.comp (continuous_fst.comp continuous_snd)).const_smul n)).prodMk
    continuous_snd

lemma two_mode_packet_correlation_zero {C D : UnitAddCircle → ℂ}
    (hC : Continuous C) (hD : Continuous D)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    {j k m l : ℤ}
    (hzero : j = k → m = l → ∀ a, starRingEnd ℂ (C a)*D a = 0) (n : ℤ) :
    (∫ x : TripleTorus,
      starRingEnd ℂ (packet j (fun p => C p.1*fourier m p.2) x)*
        packet k (fun p => D p.1*fourier l p.2) (twistIter φ n x) ∂tripleVolume) = 0 := by
  let D' := fun a => fourier n (k • φ a)*D a
  have hD' : Continuous D' := ((fourier n).continuous.comp (hφ.const_smul k)).mul hD
  have he (x : TripleTorus) :
      packet k (fun p => D p.1*fourier l p.2) (twistIter φ n x) =
        packet k (fun p => D' p.1*fourier l p.2) x := by
    rw [packet_twistIter]
    dsimp [packet,D']
    ring
  simp_rw [he]
  have hAC : Continuous (fun p : UnitAddCircle × UnitAddCircle => C p.1*fourier m p.2) :=
    (hC.comp continuous_fst).mul ((fourier m).continuous.comp continuous_snd)
  have hBD : Continuous (fun p : UnitAddCircle × UnitAddCircle => D' p.1*fourier l p.2) :=
    (hD'.comp continuous_fst).mul ((fourier l).continuous.comp continuous_snd)
  rw [integral_packet_pair hAC hBD j k]
  split_ifs with hjk
  · have hi : Integrable (fun p : UnitAddCircle × UnitAddCircle =>
        starRingEnd ℂ (C p.1*fourier m p.2)*(D' p.1*fourier l p.2)) slowVolume :=
      ((Complex.continuous_conj.comp ((hC.comp continuous_fst).mul
        ((fourier m).continuous.comp continuous_snd))).mul
        ((hD'.comp continuous_fst).mul ((fourier l).continuous.comp continuous_snd))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [MeasureTheory.integral_prod _ hi]
    have hint a : (∫ b : UnitAddCircle,
        starRingEnd ℂ (C a*fourier m b)*(D' a*fourier l b) ∂AddCircle.haarAddCircle) =
          (starRingEnd ℂ (C a)*D' a)*(if m = l then 1 else 0) := by
      simp only [map_mul]
      have hh (b : UnitAddCircle) : starRingEnd ℂ (C a)*starRingEnd ℂ (fourier m b)*(D' a*fourier l b) =
          (starRingEnd ℂ (C a)*D' a)*(starRingEnd ℂ (fourier m b)*fourier l b) := by ring
      simp_rw [hh]
      rw [integral_const_mul,integral_fourier_pair]
    simp_rw [hint]
    split_ifs with hml
    · apply integral_eq_zero_of_ae
      filter_upwards [] with a
      change starRingEnd ℂ (C a)*(fourier n (k • φ a)*D a)*1 = 0
      calc
        _ = fourier n (k • φ a)*(starRingEnd ℂ (C a)*D a) := by ring
        _ = 0 := by rw [hzero hjk hml,mul_zero]
    · simp
  · rfl

lemma retainedPassage_pair_zero
    {ψ : UnitAddCircle → ℝ} {χ ξ : ℝ → UnitAddCircle → ℝ}
    {m l : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {A B : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hξ : Continuous ξ.uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : Continuous A) (hB : Continuous B)
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (hd : m = l → ∀ s a, χ s a*ξ s a = 0)
    (N : ℕ) (S T : Finset ℤ) (n : ℤ) :
    (∫ x : TripleTorus,
      starRingEnd ℂ (retainedPassage m (H N) A S (fun j => χ ((j:ℝ)/N)) ψ x)*
        retainedPassage l (H N) B T (fun j => ξ ((j:ℝ)/N)) ψ (twistIter φ n x)
          ∂tripleVolume) = 0 := by
  classical
  let C (j : ℤ) (a : UnitAddCircle) : ℂ := (ψ a:ℂ)*(χ ((j:ℝ)/N) a:ℂ)*exactPassageCoeff m (H N) A j a
  let D (j : ℤ) (a : UnitAddCircle) : ℂ := (ψ a:ℂ)*(ξ ((j:ℝ)/N) a:ℂ)*exactPassageCoeff l (H N) B j a
  have hC j : Continuous (C j) :=
    ((Complex.continuous_ofReal.comp hψ).mul
      (Complex.continuous_ofReal.comp (hχ.comp (continuous_const.prodMk continuous_id)))).mul
      (continuous_exactPassageCoeff (hH N) hA j)
  have hD j : Continuous (D j) :=
    ((Complex.continuous_ofReal.comp hψ).mul
      (Complex.continuous_ofReal.comp (hξ.comp (continuous_const.prodMk continuous_id)))).mul
      (continuous_exactPassageCoeff (hH N) hB j)
  have he (j k : ℤ) : (∫ x : TripleTorus,
      starRingEnd ℂ (packet j (fun p => C j p.1*fourier m p.2) x)*
        packet k (fun p => D k p.1*fourier l p.2) (twistIter φ n x) ∂tripleVolume) = 0 := by
    apply two_mode_packet_correlation_zero (hC j) (hD k) hφ _ n
    intro hjk hml a
    subst k
    have hz : χ ((j:ℝ)/N) a = 0 ∨ ξ ((j:ℝ)/N) a = 0 := mul_eq_zero.mp (hd hml _ _)
    rcases hz with hz | hz <;> simp [C,D,hz]
  have hi (j k : ℤ) : Integrable (fun x : TripleTorus =>
      starRingEnd ℂ (packet j (fun p => C j p.1*fourier m p.2) x)*
        packet k (fun p => D k p.1*fourier l p.2) (twistIter φ n x)) tripleVolume :=
    ((Complex.continuous_conj.comp (continuous_packet ((hC j).comp continuous_fst |>.mul
      ((fourier m).continuous.comp continuous_snd)))).mul
      ((continuous_packet ((hD k).comp continuous_fst |>.mul
        ((fourier l).continuous.comp continuous_snd))).comp (continuous_twistIter hφ n))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  change (∫ x : TripleTorus,
    starRingEnd ℂ (∑ j ∈ S, packet j (fun p => C j p.1*fourier m p.2) x)*
      (∑ k ∈ T, packet k (fun p => D k p.1*fourier l p.2) (twistIter φ n x)) ∂tripleVolume) = 0
  simp_rw [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
  simp_rw [integral_finsetSum _ (fun k _ => hi _ k),he]
  simp

lemma finite_orthogonal_correlation {ι : Type*} [Fintype ι]
    (f : ι → TripleTorus → ℂ) (hf : ∀ i, Continuous (f i))
    {φ : UnitAddCircle → UnitAddCircle} (hφ : Continuous φ)
    (hd : ∀ i j, i ≠ j → ∀ n : ℤ,
      (∫ x, starRingEnd ℂ (f i x)*f j (twistIter φ n x) ∂tripleVolume) = 0)
    (b : ι → ℂ) (n : ℤ) :
    (∫ x, starRingEnd ℂ (∑ i, b i*f i x)*
      (∑ i, b i*f i (twistIter φ n x)) ∂tripleVolume) =
        ∑ i, (‖b i‖^2:ℝ)*(∫ x, starRingEnd ℂ (f i x)*f i (twistIter φ n x) ∂tripleVolume) := by
  classical
  have hi i j : Integrable (fun x => starRingEnd ℂ (f i x)*f j (twistIter φ n x)) tripleVolume :=
    ((Complex.continuous_conj.comp (hf i)).mul ((hf j).comp (continuous_twistIter hφ n))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi' i j : Integrable (fun x => starRingEnd ℂ (b i*f i x)*(b j*f j (twistIter φ n x))) tripleVolume := by
    have he : (fun x => starRingEnd ℂ (b i*f i x)*(b j*f j (twistIter φ n x))) =
        fun x => (starRingEnd ℂ (b i)*b j)*(starRingEnd ℂ (f i x)*f j (twistIter φ n x)) := by
      funext x
      simp only [map_mul]
      ring
    rw [he]
    exact (hi i j).const_mul _
  have he i j : (∫ x, starRingEnd ℂ (b i*f i x)*(b j*f j (twistIter φ n x)) ∂tripleVolume) =
      (starRingEnd ℂ (b i)*b j)*(∫ x, starRingEnd ℂ (f i x)*f j (twistIter φ n x) ∂tripleVolume) := by
    have hh x : starRingEnd ℂ (b i*f i x)*(b j*f j (twistIter φ n x)) =
        (starRingEnd ℂ (b i)*b j)*(starRingEnd ℂ (f i x)*f j (twistIter φ n x)) := by
      simp only [map_mul]
      ring
    simp_rw [hh]
    exact integral_const_mul _ _
  simp_rw [map_sum,Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi' i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi' i j),Finset.sum_eq_single i,he,normSq_complex]
  · intro j _ hji
    rw [he,hd i j hji.symm,mul_zero]
  · intro hh
    exact (hh (Finset.mem_univ i)).elim

/-- Exact spectral density for a finite color list, including constant tags.
Overlapping output angular indices do not cause interference: the old
angular index becomes the new spare Fourier index. -/
theorem retained_family_spectral_moment {ι : Type*} [Fintype ι]
    {ψ : UnitAddCircle → ℝ} {χ : ι → ℝ → UnitAddCircle → ℝ}
    {m : ι → ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    {J : UnitAddCircle → ℝ} {J₀ : ℝ → ℝ} {I : Set ℝ}
    (hψ : Continuous ψ) (hχ : ∀ i, Continuous (χ i).uncurry)
    (hH : ∀ n, Continuous (H n)) (hA : ∀ i, Continuous (A i))
    (hψs : ∀ x ∈ Ioc (0:ℝ) 1, ψ (x:UnitAddCircle) ≠ 0 → x ∈ I)
    (hj : Continuous J) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀)
    (hJe : ∀ x ∈ I, J (x:UnitAddCircle) = J₀ x)
    (hIo : IsOpen I) (hinj : InjOn J₀ I) (hd : ∀ x ∈ I, deriv J₀ x ≠ 0)
    (hcut : ∀ i j, i ≠ j → m i = m j → ∀ s a, χ i s a*χ j s a = 0)
    {N : ℕ} {S : ι → Finset ℤ} (hN : 0 < N) (hS : ∀ i j, j ∈ S i → j ≠ 0)
    (b : ι → ℂ) (k : ℤ) :
    let φ := fun a => (((1+J a/N)/N:ℝ):UnitAddCircle)
    let f := fun i => retainedPassage (m i) (H N) (A i) (S i) (fun j => χ i ((j:ℝ)/N)) ψ
    let p := fun i => exactRetainedPacketDensity I J₀ ψ (χ i) (m i) H (A i) (S i) N
    (∫ x : TripleTorus, starRingEnd ℂ (∑ i, b i*f i x)*
      (∑ i, b i*f i (twistIter φ k x)) ∂tripleVolume) =
        ∫ z, ((∑ i, ‖b i‖^2*p i z : ℝ):ℂ)*fourier k z ∂AddCircle.haarAddCircle := by
  classical
  dsimp only
  let φ := fun a => (((1+J a/N)/N:ℝ):UnitAddCircle)
  let f := fun i => retainedPassage (m i) (H N) (A i) (S i) (fun j => χ i ((j:ℝ)/N)) ψ
  let p := fun i => exactRetainedPacketDensity I J₀ ψ (χ i) (m i) H (A i) (S i) N
  have hφ : Continuous φ :=
    (AddCircle.continuous_mk' 1).comp ((continuous_const.add (hj.div_const N)).div_const N)
  have hf i : Continuous (f i) := continuous_retainedPassage hψ (hχ i) hH (hA i) N (S i)
  have hcross i j (hij : i ≠ j) (n : ℤ) :
      (∫ x : TripleTorus, starRingEnd ℂ (f i x)*f j (twistIter φ n x) ∂tripleVolume) = 0 :=
    retainedPassage_pair_zero hψ (hχ i) (hχ j) hH (hA i) (hA j) hφ
      (hcut i j hij) N (S i) (S j) n
  have hmoment i : (∫ x : TripleTorus, starRingEnd ℂ (f i x)*f i (twistIter φ k x) ∂tripleVolume) =
      ∫ z, (p i z:ℂ)*fourier k z ∂AddCircle.haarAddCircle :=
    retainedPassage_spectral_moment hψ (hχ i) hH (hA i) hψs hj hJ hJe hIo hinj hd hN (hS i) k
  have hp i : Integrable (p i) AddCircle.haarAddCircle :=
    exactRetainedPacketDensity_integrable hJ hIo hinj hd hψ (hχ i) hH (hA i) hN (hS i)
  have hi i : Integrable (fun z => (p i z:ℂ)*fourier k z) AddCircle.haarAddCircle :=
    (hp i).ofReal.mul_bdd (fourier k).continuous.aestronglyMeasurable
      (ae_of_all _ (fun z => le_of_eq (Circle.norm_coe _)))
  rw [finite_orthogonal_correlation f hf hφ hcross b k]
  simp_rw [hmoment,← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ => (hi i).const_mul ((‖b i‖^2:ℝ):ℂ))]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  change ((‖b i‖^2:ℝ):ℂ)*((p i z:ℂ)*fourier k z) =
    (((‖b i‖^2:ℝ):ℂ)*(p i z:ℂ))*fourier k z
  ring

end ThreeTorus
end
end

section

/-! Removing the identically zero retained modes does not alter either the
physical vector or its literal temporal density. This bridges the asymptotic
finite-retention producer and the exact finite index separations. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

lemma sum_eq_of_zero_off {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (f : α → M) (S T : Finset α)
    (hS : ∀ j, j ∉ S → f j = 0) (hT : ∀ j, j ∉ T → f j = 0) :
    ∑ j ∈ S, f j = ∑ j ∈ T, f j := by
  have eS : ∑ j ∈ S ∩ T, f j = ∑ j ∈ S, f j := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro j hj hn
    exact hT j (fun ht => hn (Finset.mem_inter.mpr ⟨hj,ht⟩))
  have eT : ∑ j ∈ S ∩ T, f j = ∑ j ∈ T, f j := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro j hj hn
    exact hS j (fun hs => hn (Finset.mem_inter.mpr ⟨hs,hj⟩))
  exact eS.symm.trans eT

lemma retainedPassage_eq_of_cover (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ)
    (χ : ℤ → UnitAddCircle → ℝ) (ψ : UnitAddCircle → ℝ)
    (hS : ∀ j, j ∉ S → ∀ a, χ j a = 0) (hT : ∀ j, j ∉ T → ∀ a, χ j a = 0) :
    retainedPassage m H A S χ ψ = retainedPassage m H A T χ ψ := by
  funext x
  apply sum_eq_of_zero_off
  · intro j hj
    simp [hS j hj]
  · intro j hj
    simp [hT j hj]

lemma exactRetainedPacketDensity_eq_of_cover
    (I : Set ℝ) (J₀ : ℝ → ℝ) (ψ : UnitAddCircle → ℝ)
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (S T : Finset ℤ) (n : ℕ)
    (hS : ∀ j, j ∉ S → ∀ a, χ ((j:ℝ)/n) a = 0)
    (hT : ∀ j, j ∉ T → ∀ a, χ ((j:ℝ)/n) a = 0) :
    exactRetainedPacketDensity I J₀ ψ χ m H A S n =
      exactRetainedPacketDensity I J₀ ψ χ m H A T n := by
  unfold exactRetainedPacketDensity
  congr 1
  funext t
  apply sum_eq_of_zero_off
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hS j hj]
  · intro j hj
    simp [unfoldedModeDensity,scaledBranchKernel,branchDensity,
      circleDensityLift,retainedCircleWeight,hT j hj]

lemma scalar_cutoff_stationary_one {C K : Set ℝ} {V : ℝ → ℝ} {m : ℤ}
    {A : ℝ → ℂ} {ξ : ℝ → ℝ}
    (hA : support A ⊆ K)
    (hξ : ∀ s ∈ (fun u => (m:ℝ)*V u) '' K, ξ =ᶠ[𝓝 s] 1) :
    ∀ s, stationaryWeight C (fun u => (m:ℝ)*V u) A s ≠ 0 → ξ s = 1 := by
  intro s hs
  exact (hξ s (stationaryWeight_support_subset hA hs)).self_of_nhds

/-- The actual second-passage coefficients have no spare-dependent modulus;
in particular their support is controlled by the actual first core. -/
lemma core_character_support (C : ℝ → ℂ) (m : ℤ) (b : UnitAddCircle) :
    support (fun u => C u*fourier m b) ⊆ tsupport C := by
  intro u hu
  exact subset_tsupport C (left_ne_zero_of_mul hu)

/-- The exact finite sampling set, with no identically zero extra modes. -/
theorem cylinder_cutoff_exact_indices {ι : Type*}
    (χ : ι → ℝ → UnitAddCircle → ℝ)
    (hc : ∀ i, HasCompactSupport (χ i).uncurry) (hz : ∀ i a, χ i 0 a = 0) :
    ∃ S : ℕ → ι → Finset ℤ,
      (∀ n i j, j ∈ S n i → j ≠ 0) ∧
      ∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0 := by
  classical
  have hex (n : ℕ) (i : ι) : ∃ S : Finset ℤ,
      (∀ j ∈ S, j ≠ 0) ∧
      (0 < n → ∀ j, j ∈ S ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) := by
    by_cases hn : 0 < n
    · obtain ⟨S,hS,hS'⟩ := cylinder_cutoff_finite_indices (hc i) (hz i) n hn
      refine ⟨S.filter (fun j => ∃ a, χ i ((j:ℝ)/n) a ≠ 0),?_,?_⟩
      · intro j hj hz
        subst j
        exact hS (Finset.mem_filter.mp hj).1
      · intro _ j
        constructor
        · exact fun hj => (Finset.mem_filter.mp hj).2
        · intro hj
          refine Finset.mem_filter.mpr ⟨?_,hj⟩
          by_contra hh
          obtain ⟨a,ha⟩ := hj
          exact ha (hS' j hh a)
    · exact ⟨∅,by simp,fun hh => (hn hh).elim⟩
  choose S hS hSe using hex
  exact ⟨S,hS,fun n hn i => hSe n i hn⟩

end ThreeTorus
end
end

section

/-! The simultaneous neutral passage with an actual integer-rounded common
primitive. Its complete geometry and all spectral estimates are supplied by
one and the same sequence of smooth Haar-preserving maps. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

/-- The jitter, all packet lists and all cutoffs are fixed before the final
passage integer. No primitive, convergence, or spectral data are assumed. -/
theorem exists_simultaneous_neutral_passage {ι : Type*} [Fintype ι]
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ι → UnitAddCircle → ℝ → ℂ}
    {V : ℝ → ℝ} {m : ι → ℤ} {o l u R : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hA : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x)
    (hA₀ : ∀ i a, ContDiff ℝ 2 (A₀ i a)) (hAc : ∀ i, Continuous (A₀ i).uncurry)
    (hAd : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2))
    (hAr : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ i (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ i a, support (A₀ i a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hp : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' Icc l u)
    (hAcont : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    {B : ι → ℝ} (hB : ∀ i, 0 ≤ B i) (hAb : ∀ i p, ‖A i p‖^2 ≤ B i)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ι → ℝ → UnitAddCircle → ℝ}
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, Continuous (χ i).uncurry) (hcχ : ∀ i, HasCompactSupport (χ i).uncurry)
    (hzχ : ∀ i a, χ i 0 a = 0) (hχ : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (hχW : ∀ i s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x)
      (A₀ i a) s ≠ 0 → χ i s a = 1) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      ∃ C : ι → ℝ, (∀ i, 0 ≤ C i) ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
        let ψ := neutralCircleCutoff c
        let J := neutralJitter c L β
        let J₀ := neutralJitterReal c L β
        let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
        (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
          Smooth (torusPassage (H n) (σ n)).symm ∧
          MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
        (∀ n, 0 < n → ∀ x : Cover,
          torusPassage (H n) (σ n) (project x) =
            project (passageFamily V J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
          (torusPassage (H n) (σ n)).symm (project x) =
            project (passageFamily V J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
        (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
          TendstoUniformlyOn
            (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J₀ r ((n:ℝ)⁻¹,Δ n)) x)
            (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
            atTop K) ∧
        ∃ S : ℕ → ι → Finset ℤ,
          (∀ n, 0 < n → ∀ i j, j ∈ S n i → j ≠ 0) ∧
          (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n) a = 0) ∧
          (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
            0 < n ∧ ∀ i,
            let f := retainedPassage (m i) (H n) (A i) (S n i) (fun j => χ i ((j:ℝ)/n)) ψ
            let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i) (S n i) n
            let pold := foldCircleDensity (fun s => ∫ a, stationaryWeight (Icc (l-R) (u+R))
              (fun x => (m i:ℝ)*V x) (A₀ i a) s ∂AddCircle.haarAddCircle)
            (∫ x : TripleTorus, ‖packet (m i) (A i) x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
              8*δ*B i+η ∧
            (∫ z, |p z-pold z| ∂AddCircle.haarAddCircle) < C i/L+4*δ*B i+η ∧
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
            (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
              ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
            (∀ j u a, ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,a)‖ =
              ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖) := by
  classical
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,hgeo⟩ := exists_rounded_primitive_family hp hV
  have hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in 0..x, V t) :=
    contDiff_real_primitive hV
  have hPV : deriv (fun x => ∫ t in 0..x, V t) = V := deriv_real_primitive hV.continuous
  have hv : Continuous hp.lift := by
    apply Continuous.quotient_lift
    exact hV.continuous
  have heV (x : ℝ) : hp.lift (x:UnitAddCircle) = V x := rfl
  have hneutral i := exact_neutral_passage (hm i) hHe (hA i) (hA₀ i) (hAc i) (hAd i)
    (hAr i) (hsupp i) hlo huo hlu hR hPr hV hPV hdV (h0 i) hHc (hAcont i) hΔt (hAs i)
    hv.measurable heV (hB i) (hAb i) c hδ hδ' (hχs i) (hχc i) (hcχ i) (hzχ i) (hχ i) (hχW i)
  choose C hC hrest using hneutral
  refine ⟨Δ,H,hΔ,hΔt,hHc,hHe,C,hC,?_⟩
  intro L hL β
  dsimp only
  obtain ⟨hg,hgraph,hlimit⟩ := hgeo (neutralJitterReal c L β)
    (neutralJitterReal_periodic c L β) (neutralJitterReal_smooth c L β)
  refine ⟨hg,hgraph,hlimit,?_⟩
  choose S hSN hST hgood using fun i => hrest i L hL β
  obtain ⟨T,hTN,hTE⟩ := cylinder_cutoff_exact_indices χ hcχ hzχ
  have hTZ n (hn : 0 < n) i j (hj : j ∉ T n i) a : χ i ((j:ℝ)/n) a = 0 := by
    by_contra hh
    exact hj ((hTE n hn i j).mpr ⟨a,hh⟩)
  refine ⟨T,fun n _ i => hTN n i,hTZ,hTE,?_⟩
  intro η hη
  have hgall := (Filter.eventually_all).mpr (fun i => hgood i η hη)
  filter_upwards [eventually_gt_atTop (0:ℕ),hgall] with n hn hall
  refine ⟨hn,fun i => ?_⟩
  have ef := retainedPassage_eq_of_cover (m i) (H n) (A i) (S i n) (T n i)
    (fun j => χ i ((j:ℝ)/n)) (neutralCircleCutoff c) (hST i n hn) (hTZ n hn i)
  have ep := exactRetainedPacketDensity_eq_of_cover (Ioo δ (1-δ))
    (neutralJitterReal c L β) (neutralCircleCutoff c) (χ i) (m i) H (A i)
    (S i n) (T n i) n (hST i n hn) (hTZ n hn i)
  simpa only [ef,ep] using hall i

end ThreeTorus
end
end

section

/-! Closure of the literal output coefficient class under a passage.
The next passage uses these very coefficients, rather than new placeholders. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

def retainedRealCore (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (u : ℝ) : ℂ :=
  (ψ₀ u:ℂ)*(χ s (u:UnitAddCircle):ℂ)*exactPassageCoeff m H A j (u:UnitAddCircle)

def retainedRealAmplitude (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ)
    (b : UnitAddCircle) (u : ℝ) : ℂ :=
  retainedRealCore ψ₀ χ m H A s j u*fourier m b

lemma retainedRealCore_smooth {ψ₀ : ℝ → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : UnitAddCircle → UnitAddCircle} {Hl : ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hχ : CylinderSmooth χ.uncurry)
    (hHl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Hl)
    (hH : ∀ t : ℝ, H (t:UnitAddCircle) = (Hl t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (s : ℝ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (retainedRealCore ψ₀ χ m H A s j) := by
  have hχ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => χ s (u:UnitAddCircle)) :=
    hχ.comp (contDiff_const.prodMk contDiff_id)
  exact ((Complex.ofRealCLM.contDiff.comp hψ).mul
    (Complex.ofRealCLM.contDiff.comp hχ')).mul (smooth_exactPassageCoeff hHl hH hA j)

lemma retainedRealAmplitude_support (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) (b : UnitAddCircle) :
    support (retainedRealAmplitude ψ₀ χ m H A s j b) ⊆ support ψ₀ := by
  intro u hu hz
  exact hu (by simp [retainedRealAmplitude,retainedRealCore,hz])

/-- Every analytic lift condition required by the next stationary-phase
passage follows from the smooth real core and the spare character. -/
lemma retainedRealAmplitude_regular {C : ℝ → ℂ}
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C) (m : ℤ) :
    (∀ b : UnitAddCircle, ContDiff ℝ 2 (fun u : ℝ => C u*fourier m b)) ∧
    Continuous (fun p : UnitAddCircle × ℝ => C p.2*fourier m p.1) ∧
    Continuous (fun p : UnitAddCircle × ℝ => deriv (fun u : ℝ => C u*fourier m p.1) p.2) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => C p.1*fourier m (p.2:UnitAddCircle)) := by
  refine ⟨fun _ => (hC.mul contDiff_const).of_le (by exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),
    (hC.continuous.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst),?_,
    (hC.comp contDiff_fst).mul ((smooth_fourier_lift m).comp contDiff_snd)⟩
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv C) :=
    (contDiff_infty_iff_deriv.mp hC).2
  have he (p : UnitAddCircle × ℝ) : deriv (fun u : ℝ => C u*fourier m p.1) p.2 =
      deriv C p.2*fourier m p.1 := deriv_mul_const (hC.differentiable (by simp) p.2) _
  simp_rw [he]
  exact (hD.continuous.comp continuous_snd).mul ((fourier m).continuous.comp continuous_fst)

lemma retainedRealAmplitude_matches {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (χ : ℝ → UnitAddCircle → ℝ) (m : ℤ) (H : ℕ → UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ) (j : ℤ) {o : ℝ}
    (he : ∀ u ∈ Ioc o (o+1), ψ (u:UnitAddCircle) = ψ₀ u) :
    ∀ b u, u ∈ Ioc o (o+1) →
      retainedAmplitude ψ χ m H A n j ((u:UnitAddCircle),b) =
        retainedRealAmplitude ψ₀ χ m (H n) A ((j:ℝ)/n) j b u := by
  intro b u hu
  simp only [retainedAmplitude,retainedRealAmplitude,retainedRealCore,he u hu]

lemma retainedAmplitude_smooth_lift
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {m : ℤ} {H : ℕ → UnitAddCircle → UnitAddCircle} {Hl : ℕ → ℝ → ℝ}
    {A : UnitAddCircle × UnitAddCircle → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => ψ u))
    (hχ : CylinderSmooth χ.uncurry)
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hH : ∀ n (t : ℝ), H n (t:UnitAddCircle) = (Hl n t:UnitAddCircle))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A (p.1,p.2)))
    (n : ℕ) (j : ℤ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => retainedAmplitude ψ χ m H A n j (p.1,p.2)) := by
  have hs := smooth_retained_amplitude (m := m) (j := j) ((j:ℝ)/n) (hHl n) (hH n) hA hχ hψ
  convert hs using 1
  funext p
  dsimp [retainedAmplitude]
  ring

end ThreeTorus

namespace ThreeTorus
open Set

lemma retainedRealCore_tsupport_subset (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) :
    tsupport (retainedRealCore ψ₀ χ m H A s j) ⊆ tsupport ψ₀ := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro u hu
  apply subset_tsupport ψ₀
  intro hz
  exact hu (by simp [retainedRealCore,hz])

lemma retainedRealCore_tsupport_cylinder (ψ₀ : ℝ → ℝ) (χ : ℝ → UnitAddCircle → ℝ)
    (m : ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : UnitAddCircle × UnitAddCircle → ℂ) (s : ℝ) (j : ℤ) :
    tsupport (retainedRealCore ψ₀ χ m H A s j) ⊆
      (fun u : ℝ => (s,(u:UnitAddCircle))) ⁻¹' tsupport χ.uncurry := by
  apply closure_minimal _
    ((isClosed_tsupport _).preimage (continuous_const.prodMk continuous_quot_mk))
  intro u hu
  apply subset_tsupport χ.uncurry
  intro hz
  exact hu (by simp [retainedRealCore,show χ s (u:UnitAddCircle) = 0 from hz])

lemma retainedRealCore_disjoint {ψ₀ : ℝ → ℝ} {χ ξ : ℝ → UnitAddCircle → ℝ}
    {m q : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A B : UnitAddCircle × UnitAddCircle → ℂ} (s : ℝ) (j : ℤ)
    (hd : Disjoint (tsupport χ.uncurry) (tsupport ξ.uncurry)) :
    Disjoint (tsupport (retainedRealCore ψ₀ χ m H A s j))
      (tsupport (retainedRealCore ψ₀ ξ q H B s j)) := by
  apply (hd.preimage (fun u : ℝ => (s,(u:UnitAddCircle)))).mono
    (retainedRealCore_tsupport_cylinder _ _ _ _ _ _ _)
    (retainedRealCore_tsupport_cylinder _ _ _ _ _ _ _)

/-- The buffered real integration interval can always be fixed before the
next passage integer, even when all the coefficients are zero. -/
lemma compact_inside_buffered_interval {K : Set ℝ} {a b : ℝ}
    (hK : IsCompact K) (hab : a < b) (hKI : K ⊆ Ioo a b) :
    ∃ l u R : ℝ, a < l ∧ l < u ∧ u < b ∧ 0 < R ∧
      K ⊆ Ioc l u ∧ Icc (l-2*R) (u+2*R) ⊆ Ioo a b := by
  let K' := insert ((a+b)/2) K
  have hc : IsCompact K' := hK.insert _
  have hsub : K' ⊆ Ioo a b := by
    intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · constructor <;> linarith
    · exact hKI hx
  obtain ⟨x,hx,hmin⟩ := hc.exists_isMinOn (insert_nonempty _ _) continuous_id.continuousOn
  obtain ⟨y,hy,hmax⟩ := hc.exists_isMaxOn (insert_nonempty _ _) continuous_id.continuousOn
  have hx' := hsub hx
  have hy' := hsub hy
  have hxy : x ≤ y := hmin hy
  let l := (a+x)/2
  let u := (y+b)/2
  have hal : a < l := by dsimp [l]; linarith [hx'.1]
  have hlu : l < u := by dsimp [l,u]; linarith [hx'.1,hy'.2]
  have hub : u < b := by dsimp [u]; linarith [hy'.2]
  let R := min (l-a) (b-u)/4
  have hR : 0 < R := div_pos (lt_min (sub_pos.mpr hal) (sub_pos.mpr hub)) (by norm_num)
  have hR₁ : 4*R ≤ l-a := by dsimp [R]; linarith [min_le_left (l-a) (b-u)]
  have hR₂ : 4*R ≤ b-u := by dsimp [R]; linarith [min_le_right (l-a) (b-u)]
  refine ⟨l,u,R,hal,hlu,hub,hR,?_,?_⟩
  · intro z hz
    have hz' : z ∈ K' := mem_insert_of_mem _ hz
    have hminz := hmin hz'
    have hmaxz := hmax hz'
    constructor <;> dsimp [l,u] at * <;> linarith
  · intro z hz
    constructor <;> linarith [hz.1,hz.2]

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

end ThreeTorus
end
end

section

/-! The second exact support separation, applied to the literal coefficients
of the first passage. No abstract output-support or disjoint-index oracle is
assumed. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators
namespace ThreeTorus

abbrev PassageOutputIndex {ι : Type*} (S : ι → Finset ℤ) := Σ i, {j // j ∈ S i}

def passageOutputCore {ι : Type*} (S : ι → Finset ℤ) (ψ₀ : ℝ → ℝ)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (m : ι → ℤ)
    (H : UnitAddCircle → UnitAddCircle) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (n : ℕ) (i : PassageOutputIndex S) : ℝ → ℂ :=
  retainedRealCore ψ₀ (χ i.1) (m i.1) H (A i.1) ((i.2.val:ℝ)/n) i.2.val

lemma passageOutputCore_disjoint {ι : Type*} {S : ι → Finset ℤ} {ψ₀ : ℝ → ℝ}
    {χ : ι → ℝ → UnitAddCircle → ℝ} {m : ι → ℤ}
    {H : UnitAddCircle → UnitAddCircle} {A : ι → UnitAddCircle × UnitAddCircle → ℂ}
    {n : ℕ} (hd : Pairwise (fun i j => Disjoint (tsupport (χ i).uncurry) (tsupport (χ j).uncurry)))
    (i k : PassageOutputIndex S) (hne : i ≠ k) (he : i.2.val = k.2.val) :
    Disjoint (tsupport (passageOutputCore S ψ₀ χ m H A n i))
      (tsupport (passageOutputCore S ψ₀ χ m H A n k)) := by
  have hne' : i.1 ≠ k.1 := by
    intro h
    apply hne
    cases i with
    | mk r i =>
      cases k with
      | mk t k =>
        dsimp at h he
        cases h
        exact congrArg (Sigma.mk r) (Subtype.ext he)
  dsimp [passageOutputCore]
  rw [he]
  exact retainedRealCore_disjoint _ _ (hd hne')

/-- After the first finite passage integer is fixed, a single integral
carrier and a family of smooth scalar-only cutoffs give the second passage
exactly disjoint final angular index sets. These cutoffs are one near the
stationary images of the actual first output supports. -/
theorem second_separation_of_actual_output {ι : Type*} [Fintype ι]
    (S : ι → Finset ℤ) (ψ₀ : ℝ → ℝ) (χ : ι → ℝ → UnitAddCircle → ℝ)
    (m : ι → ℤ) (H : UnitAddCircle → UnitAddCircle)
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ) (n : ℕ)
    (hS : ∀ i j, j ∈ S i → j ≠ 0)
    (hψ : HasCompactSupport ψ₀) (I : Set ℝ) (hψI : tsupport ψ₀ ⊆ I)
    (hχd : Pairwise (fun i j => Disjoint (tsupport (χ i).uncurry) (tsupport (χ j).uncurry)))
    (φ : UnitAddCircle → ℝ) (hφ : Continuous φ)
    (hi : InjOn (fun u : ℝ => φ (u:UnitAddCircle)) I) :
    ∃ c : ℕ, 0 < c ∧
      (∀ u : ℝ, (c:ℝ)+φ (u:UnitAddCircle) ≠ 0) ∧
      ∃ (ξ : PassageOutputIndex S → ℝ → ℝ) (T : ℕ → PassageOutputIndex S → Finset ℤ),
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ξ i) ∧ HasCompactSupport (ξ i) ∧
        ξ i 0 = 0 ∧ (∀ s, 0 ≤ ξ i s ∧ ξ i s ≤ 1) ∧
        ∀ s ∈ (fun u : ℝ => (i.2.val:ℝ)*((c:ℝ)+φ (u:UnitAddCircle))) ''
          tsupport (passageOutputCore S ψ₀ χ m H A n i), ξ i =ᶠ[𝓝 s] 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (ξ i)) (tsupport (ξ j))) ∧
      (∀ N i, (0:ℤ) ∉ T N i) ∧
      (∀ N, Pairwise (fun i j => Disjoint (T N i) (T N j))) ∧
      ∀ N, 0 < N → ∀ i j, j ∈ T N i ↔ ξ i ((j:ℝ)/N) ≠ 0 := by
  classical
  let q : PassageOutputIndex S → ℤ := fun i => i.2.val
  have hq (i : PassageOutputIndex S) : q i ≠ 0 := hS i.1 i.2.val i.2.property
  let q' : Option (PassageOutputIndex S) → ℤ := fun i => i.elim 1 q
  have hq' (i : Option (PassageOutputIndex S)) : q' i ≠ 0 := by
    cases i with
    | none => norm_num [q']
    | some i => exact hq i
  obtain ⟨c,hc,hc0,hsep⟩ := exists_integral_speed_separation q' φ hq' hφ
  have h0 (u : ℝ) : (c:ℝ)+φ (u:UnitAddCircle) ≠ 0 := by
    simpa [q'] using hc0 none (u:UnitAddCircle)
  let V : ℝ → ℝ := fun u => (c:ℝ)+φ (u:UnitAddCircle)
  let K (i : PassageOutputIndex S) := tsupport (passageOutputCore S ψ₀ χ m H A n i)
  have hK i : IsCompact (K i) := hψ.of_isClosed_subset (isClosed_tsupport _)
    (retainedRealCore_tsupport_subset _ _ _ _ _ _ _)
  have hKI i : K i ⊆ I := (retainedRealCore_tsupport_subset _ _ _ _ _ _ _).trans hψI
  have hVi : InjOn V I := fun x hx y hy he => hi hx hy (add_left_cancel he)
  have hV : Continuous V := continuous_const.add (hφ.comp continuous_quot_mk)
  have hd (i j : PassageOutputIndex S) (hne : i ≠ j) (he : q i = q j) :
      Disjoint (K i) (K j) := passageOutputCore_disjoint hχd i j hne he
  have hs i j x (_hx : x ∈ I) y (_hy : y ∈ I)
      (he : (q i:ℝ)*V x = (q j:ℝ)*V y) : q i = q j :=
    hsep (some i) (some j) (x:UnitAddCircle) (y:UnitAddCircle) he
  obtain ⟨ξ,T,hξ,hξd,hT0,hTd,hT⟩ := second_separation_cutoffs q V I K
    (fun _ => univ) hq hV hVi hK hKI (fun x _ => h0 x) hs hd
    (fun _ => isOpen_univ) (fun _ _ _ => mem_univ _)
  refine ⟨c,hc,h0,ξ,T,?_,hξd,hT0,hTd,hT⟩
  intro i
  have hz : ξ i 0 = 0 := by
    by_contra hh
    have hm := (hT 1 (by norm_num) i 0).mpr (by simpa using hh)
    exact hT0 1 i hm
  exact ⟨(hξ i).1,(hξ i).2.1,hz,(hξ i).2.2.2⟩

end ThreeTorus
end
end

section

/-! A concrete closed class for finite passage iteration.  The constructor
below uses the literal retained amplitudes; it does not postulate a next
packet state or any of its analytic regularity. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- All input data used by the proved simultaneous passage theorems.  No
asymptotic estimate, transport, density, or conclusion is a field. -/
structure PassagePackets (ι : Type*) where
  m : ι → ℤ
  nonzero : ∀ i, m i ≠ 0
  A : ι → UnitAddCircle × UnitAddCircle → ℂ
  A₀ : ι → UnitAddCircle → ℝ → ℂ
  o : ℝ
  l : ℝ
  u : ℝ
  R : ℝ
  lo : o ≤ l
  uo : u ≤ o+1
  lu : l ≤ u
  Rpos : 0 < R
  lift_matches : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x:UnitAddCircle),a) = A₀ i a x
  two : ∀ i a, ContDiff ℝ 2 (A₀ i a)
  continuous_lift : ∀ i, Continuous (A₀ i).uncurry
  continuous_deriv : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2)
  smooth_lift : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : ℝ × ℝ => A₀ i (p.2:UnitAddCircle) p.1)
  support_lift : ∀ i a, support (A₀ i a) ⊆ Ioc l u
  continuous_amplitude : ∀ i, Continuous (A i)
  smooth_amplitude : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun p : ℝ × ℝ => A i (p.1,p.2))
  V : ℝ → ℝ
  periodic : Periodic V 1
  smooth_speed : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V
  positive_deriv : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x

def PassagePackets.SpareIndependent {ι : Type*} (F : PassagePackets ι) : Prop :=
  (∀ i a x, ‖F.A₀ i a x‖ = ‖F.A₀ i 0 x‖) ∧
    ∀ i u a, ‖F.A i (u,a)‖ = ‖F.A i (u,0)‖

lemma smooth_new_speed {J : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => (1+J u/n)/n) :=
  (contDiff_const.add (hJ.div_const _)).div_const _

lemma positive_deriv_new_speed {J : ℝ → ℝ} {n : ℕ} {x : ℝ}
    (hn : 0 < n) (hd : 0 < deriv J x) :
    0 < deriv (fun u => (1+J u/n)/n) x := by
  simpa only [deriv_div_const,deriv_const_add] using
    div_pos (div_pos hd (show (0:ℝ)<n by exact_mod_cast hn)) (show (0:ℝ)<n by exact_mod_cast hn)

/-- A neutral or quantile passage produces a valid input family for the next
passage, with all real lifts supported in one common compact good interval.
The jitter may be arbitrarily broad. The constructor works at EVERY positive
passage integer, independently of the spectral/physical approximation bounds. -/
theorem literal_output_packets {ι : Type*} [Fintype ι]
    (m : ι → ℤ) (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (H : ℕ → UnitAddCircle → UnitAddCircle) (Hl : ℕ → ℝ → ℝ)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (S : ι → Finset ℤ)
    (hS : ∀ i j, j ∈ S i → j ≠ 0)
    (hAc : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    (hχ : ∀ i, CylinderSmooth (χ i).uncurry) (hχc : ∀ i, Continuous (χ i).uncurry)
    (hHc : ∀ n, Continuous (H n))
    (hHl : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Hl n))
    (hHe : ∀ n (x : ℝ), H n (x:UnitAddCircle) = (Hl n x:UnitAddCircle))
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {J : ℝ → ℝ} (hpJ : Periodic J 1) (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hdJ : ∀ x ∈ Ioo δ (1-δ), 0 < deriv J x) {n : ℕ} (hn : 0 < n) :
    ∃ F : PassagePackets (PassageOutputIndex S),
      (∀ i, F.m i = i.2.val) ∧
      (∀ i, F.A i = retainedAmplitude (neutralCircleCutoff c) (χ i.1) (m i.1) H (A i.1) n i.2.val) ∧
      (∀ i, F.A₀ i = retainedRealAmplitude c.ψ (χ i.1) (m i.1) (H n) (A i.1)
        ((i.2.val:ℝ)/n) i.2.val) ∧
      F.V = (fun x => (1+J x/n)/n) ∧ F.o = 0 ∧
      δ < F.l ∧ F.u < 1-δ ∧ F.SpareIndependent := by
  obtain ⟨l,u,R,hδl,hlu,huδ,hR,hKI,hbuffer⟩ := compact_inside_buffered_interval
    c.ψ_compact (by linarith : δ < 1-δ) c.ψ_support
  let ψ := neutralCircleCutoff c
  have hψs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => ψ x) := by
    simp only [ψ,neutralCircleCutoff_coe]
    exact contDiff_periodize c.ψ_smooth c.ψ_compact
  have hψe : ∀ x ∈ Ioc (0:ℝ) (0+1), ψ (x:UnitAddCircle) = c.ψ x := by
    intro x hx
    rw [show ψ (x:UnitAddCircle) = lawPsi c x from neutralCircleCutoff_coe c x]
    exact periodize_eq_on_unit ((subset_tsupport c.ψ).trans
      (c.ψ_support.trans (by intro z hz; constructor <;> linarith [hz.1,hz.2]))) ⟨hx.1.le,by simpa using hx.2⟩
  let A' (i : PassageOutputIndex S) := retainedAmplitude ψ (χ i.1) (m i.1) H (A i.1) n i.2.val
  let A₀' (i : PassageOutputIndex S) := retainedRealAmplitude c.ψ (χ i.1) (m i.1) (H n) (A i.1)
    ((i.2.val:ℝ)/n) i.2.val
  have hcore (i : PassageOutputIndex S) := retainedRealCore_smooth (m := m i.1) c.ψ_smooth (hχ i.1)
    (hHl n) (hHe n) (hAs i.1) ((i.2.val:ℝ)/n) i.2.val
  have hreg (i : PassageOutputIndex S) := retainedRealAmplitude_regular (hcore i) (m i.1)
  have hA' i : Continuous (A' i) := by
    dsimp [A',retainedAmplitude]
    exact (((Complex.continuous_ofReal.comp ((continuous_neutralCircleCutoff c).comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ((hχc i.1).comp (continuous_const.prodMk continuous_fst)))).mul
      ((continuous_exactPassageCoeff (hHc n) (hAc i.1) _).comp continuous_fst)).mul
      ((fourier (m i.1)).continuous.comp continuous_snd)
  let F : PassagePackets (PassageOutputIndex S) := {
    m := fun i => i.2.val
    nonzero := fun i => hS i.1 i.2.val i.2.property
    A := A'
    A₀ := A₀'
    o := 0
    l := l
    u := u
    R := R
    lo := hδ.le.trans hδl.le
    uo := by linarith
    lu := hlu.le
    Rpos := hR
    lift_matches := fun i => retainedRealAmplitude_matches (χ i.1) (m i.1) H (A i.1) n i.2.val hψe
    two := fun i => (hreg i).1
    continuous_lift := fun i => (hreg i).2.1
    continuous_deriv := fun i => (hreg i).2.2.1
    smooth_lift := fun i => (hreg i).2.2.2
    support_lift := fun i a => (retainedRealAmplitude_support _ _ _ _ _ _ _ a).trans
      ((subset_tsupport c.ψ).trans hKI)
    continuous_amplitude := hA'
    smooth_amplitude := fun i => retainedAmplitude_smooth_lift hψs (hχ i.1) hHl hHe (hAs i.1) n i.2.val
    V := fun x => (1+J x/n)/n
    periodic := fun x => by dsimp; rw [hpJ x]
    smooth_speed := smooth_new_speed hJ n
    positive_deriv := fun x hx => positive_deriv_new_speed hn (hdJ x (hbuffer hx)) }
  refine ⟨F,fun _ => rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,hδl,huδ,?_,?_⟩
  · intro i a x
    dsimp [F,A₀',retainedRealAmplitude]
    simp only [norm_mul, Circle.norm_coe]
  · intro i v a
    exact retainedAmplitude_modulus ψ (χ i.1) (m i.1) H (A i.1) n i.2.val v a

lemma output_index_injective {ι : Type*} {S : ι → Finset ℤ}
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    Injective (fun i : PassageOutputIndex S => i.2.val) := by
  intro i j he
  have hij : i.1 = j.1 := by
    by_contra h
    exact Finset.disjoint_left.mp (hd h) i.2.property (by simpa only [he] using j.2.property)
  cases i with
  | mk i k =>
    cases j with
    | mk j l =>
      dsimp at hij he
      subst j
      exact congrArg (Sigma.mk i) (Subtype.ext he)

end ThreeTorus
end
end

section

/-! A finite quantile passage, using one and the same rounded primitive and
literal finite retained Fourier coefficients for all physical and spectral
conclusions. The law and all finite input data precede the final integer. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

theorem exists_simultaneous_quantile_passage {ι : Type*} [Fintype ι]
    {A : ι → UnitAddCircle × UnitAddCircle → ℂ} {A₀ : ι → UnitAddCircle → ℝ → ℂ}
    {V : ℝ → ℝ} {m : ι → ℤ} {o l u R : ℝ}
    (hm : ∀ i, m i ≠ 0)
    (hA : ∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x)
    (hA₀ : ∀ i a, ContDiff ℝ 2 (A₀ i a)) (hAc : ∀ i, Continuous (A₀ i).uncurry)
    (hAd : ∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2))
    (hAr : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ i (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ i a, support (A₀ i a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hpV : Periodic V 1) (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' Icc l u)
    (hAcont : ∀ i, Continuous (A i))
    (hAs : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2)))
    (hmod : ∀ i a x, ‖A₀ i a x‖ = ‖A₀ i 0 x‖)
    (hmodA : ∀ i u a, ‖A i (u,a)‖ = ‖A i (u,0)‖)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ) (hi : Integrable ρ)
    (hp : ∀ y, 0 < ρ y) (hρm : ∫ y, ρ y = 1)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y, |ρ y| ≤ C/(1+y^2)) {D : ℝ}
    (hF : ∀ v, D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0)
    {δ : ℝ} (c : LawCutoffs δ) (hδ : 0 < δ) (hδ' : δ < 1/8)
    {χ : ι → ℝ → UnitAddCircle → ℝ}
    (hχs : ∀ i, CylinderSmooth (χ i).uncurry)
    (hχc : ∀ i, Continuous (χ i).uncurry) (hcχ : ∀ i, HasCompactSupport (χ i).uncurry)
    (hzχ : ∀ i a, χ i 0 a = 0) (hχ : ∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1)
    (hχW : ∀ i s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x)
      (A₀ i a) s ≠ 0 → χ i s a = 1)
    {g : ι → UnitAddCircle → ℝ} (hg : ∀ i, Continuous (g i)) {ε : ℝ}
    (hideal : ∀ i, ∀ s ∈ support (stationaryWeight (Icc (l-R) (u+R))
      (fun x => (m i:ℝ)*V x) (A₀ i 0)),
      ∀ y, |foldCircleDensity (scaledDensity ρ s) y-g i y| ≤ ε) :
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      let ψ := neutralCircleCutoff c
      let J := quantileCircleJitter ρ c
      let J₀ := lawJitter ρ c
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
        Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily V J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily V J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → ∀ i j, j ∈ S n i → j ≠ 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n) a = 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          0 < n ∧ ∀ i,
          let f := retainedPassage (m i) (H n) (A i) (S n i) (fun j => χ i ((j:ℝ)/n)) ψ
          let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i) (S n i) n
          let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x) (A₀ i 0)
          (∫ x : TripleTorus, ‖packet (m i) (A i) x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
            8*δ*(∫ u, ‖A i (u,0)‖^2 ∂AddCircle.haarAddCircle)+η ∧
          (∫ z, |p z-foldCircleDensity w z*g i ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
            (∫ s, w s)*(4*δ+ε)+η ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
          (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
            ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
          (∀ j u a, ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,a)‖ =
            ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖) := by
  classical
  obtain ⟨Δ,H,hΔ,hΔt,hHc,hHe,hgeo⟩ := exists_rounded_primitive_family hpV hV
  have hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in 0..x, V t) :=
    contDiff_real_primitive hV
  have hPV : deriv (fun x => ∫ t in 0..x, V t) = V := deriv_real_primitive hV.continuous
  obtain ⟨hg,hgraph,hlimit⟩ := hgeo (lawJitter ρ c) (periodize_periodic _)
    (lawJitter_smooth c hρ hi hp hρm)
  obtain ⟨T,hTN,hTE⟩ := cylinder_cutoff_exact_indices χ hcχ hzχ
  have hTZ n (hn : 0 < n) i j (hj : j ∉ T n i) a : χ i ((j:ℝ)/n) a = 0 := by
    by_contra hh
    exact hj ((hTE n hn i j).mpr ⟨a,hh⟩)
  refine ⟨Δ,H,hΔ,hΔt,hHc,hHe,hg,hgraph,hlimit,T,fun n _ i => hTN n i,hTZ,hTE,?_⟩
  intro η hη
  have hpass i := exact_quantile_passage (hm i) hHe (hA i) (hA₀ i) (hAc i) (hAd i)
    (hAr i) (hsupp i) hlo huo hlu hR hPr hV hPV hdV (h0 i) hHc (hAcont i) hΔt
    (hmod i) (hmodA i) (hAs i) hρ hi hp hρm hC hb hF c hδ hδ'
    (hχs i) (hχc i) (hcχ i) (hzχ i) (hχ i) (hχW i) (hg := ‹∀ i, Continuous (g i)› i)
    (hideal i) hη
  choose S hSN hST hgood using hpass
  have hgall := (Filter.eventually_all).mpr hgood
  filter_upwards [eventually_gt_atTop (0:ℕ),hgall] with n hn hall
  refine ⟨hn,fun i => ?_⟩
  have ef := retainedPassage_eq_of_cover (m i) (H n) (A i) (S i n) (T n i)
    (fun j => χ i ((j:ℝ)/n)) (neutralCircleCutoff c) (hST i n hn) (hTZ n hn i)
  have ep := exactRetainedPacketDensity_eq_of_cover (Ioo δ (1-δ)) (lawJitter ρ c)
    (neutralCircleCutoff c) (χ i) (m i) H (A i) (S i n) (T n i) n (hST i n hn) (hTZ n hn i)
  simpa only [ef,ep] using hall i

end ThreeTorus
end
end

section

/-! All law and finite-family uniformity hypotheses of the actual quantile
passage are discharged by the source's explicit positive signal law. Its
modulus and strength bound precede every future scale and packet family. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

universe u

theorem exists_signal_family_law
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ B : ℝ, 0 < B → ∀ m : ι → ℤ, (∀ i, b ≤ |(m i:ℝ)/B|) →
      ∀ φ : ℝ → ℝ, Continuous φ → ∀ K : Set ℝ, IsCompact K →
      ∀ A : ι → ℝ → ℂ, (∀ i, support (A i) ⊆ K) → ∀ C₀ : Set ℝ,
      ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℝ in atTop,
        0 < c ∧
        let ρ := signalJitter α γ d (signalPrimeProduct L) B c
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
        (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
        (∃ C > 0, (∀ y, |ρ y| ≤ C/(1+y^2)) ∧
          ∀ v, c*B*D < |v| → 𝓕 (fun y => (ρ y : ℂ)) v = 0) ∧
        ∀ i, ∀ s ∈ support (stationaryWeight C₀ (fun x => (m i:ℝ)*(c+φ x)) (A i)),
          ∀ y, |foldCircleDensity (scaledDensity ρ s) y-
            signalCircleModel (signalPrimeProduct L) γ B d (m i) y| ≤ ε := by
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hγ⟩ := exists_signal_positive_law hb hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hlaw,hdb,_⟩ := hγ γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst B hB m hm φ hφ K hK A hA C₀ ε hε
  obtain ⟨V₀,hV₀⟩ := (hK.image hφ).isBounded.exists_norm_le
  have hV x (hx : x ∈ K) : |φ x| ≤ V₀ := hV₀ _ (mem_image_of_mem φ hx)
  have hbound h R := (hlaw h).2.2.2 R
  have hαb' : α < b := by linarith
  have hαD : α ≤ D := (hαb'.trans hbD).le
  have hf i := signalCircleModel_uniform_on_weight hα hαb' hαD hB hb hLD γ hd hdc hdr hd0 hds
    (C := C₀) (m i) (hm i) hbound (hA i) hV ε hε
  have hall := (Filter.eventually_all).mpr hf
  filter_upwards [eventually_gt_atTop (0:ℝ),hall] with c hc hcmodel
  refine ⟨hc,?_⟩
  obtain ⟨hρ,hρi,hρp,hρm,C,hC,hCb,hCF⟩ := signalJitter_law_regular hα hB hc hαD hd hdc hdr
    hd0 hds (signalPrimeProduct L) hbound
  exact ⟨hρ,hρi,hρp,hρm,⟨C,hC,hCb,hCF⟩,hcmodel⟩

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter
open scoped Topology
namespace ThreeTorus

/-- The integral carrier can meet every additional lower bound, as required
when the signal strength and approximation tolerance are selected first. -/
theorem eventually_integral_speed_separation {ι X : Type*} [Finite ι]
    [TopologicalSpace X] [CompactSpace X] (m : ι → ℤ) (φ : X → ℝ)
    (hm : ∀ i, m i ≠ 0) (hφ : Continuous φ) :
    ∀ᶠ c : ℕ in Filter.atTop, 0 < c ∧
      (∀ i x, (m i : ℝ) * ((c:ℝ) + φ x) ≠ 0) ∧
      (∀ i j x y, (m i : ℝ) * ((c:ℝ) + φ x) =
        (m j : ℝ) * ((c:ℝ) + φ y) → m i = m j) := by
  obtain ⟨R,hR⟩ := (isCompact_range hφ).isBounded.exists_norm_le
  obtain ⟨D,hD⟩ := (Set.finite_range (fun i => (m i : ℝ))).isCompact.isBounded.exists_norm_le
  let B := max R 0
  let M := max D 0
  have hB : 0 ≤ B := le_max_right _ _
  have hM : 0 ≤ M := le_max_right _ _
  have hφB x : |φ x| ≤ B := (hR _ (mem_range_self x)).trans (le_max_left _ _)
  have hmM i : |(m i : ℝ)| ≤ M := (hD _ (mem_range_self i)).trans (le_max_left _ _)
  have hct := (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun c : ℕ => (c:ℝ))
    Filter.atTop Filter.atTop).eventually (Filter.eventually_gt_atTop (2*M*B+B+1))
  filter_upwards [hct] with c hc
  have hMB : 0 ≤ M*B := mul_nonneg hM hB
  have hcB : B < (c:ℝ) := by nlinarith
  have hcp : (0:ℝ) < c := hB.trans_lt hcB
  refine ⟨by exact_mod_cast hcp,?_,?_⟩
  · intro i x
    apply mul_ne_zero (by exact_mod_cast hm i)
    have ht := (abs_le.mp (hφB x)).1
    linarith
  · intro i j x y he
    by_contra hij
    have hd : 1 ≤ |((m i-m j : ℤ):ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hij)
    have he' : ((m i:ℝ)-(m j:ℝ))*(c:ℝ) = (m j:ℝ)*φ y-(m i:ℝ)*φ x := by
      nlinarith [he]
    have hh : |(m j:ℝ)*φ y-(m i:ℝ)*φ x| ≤ 2*M*B := calc
      _ ≤ |(m j:ℝ)*φ y|+|(m i:ℝ)*φ x| := abs_sub _ _
      _ = |(m j:ℝ)| *|φ y|+|(m i:ℝ)| *|φ x| := by rw [abs_mul,abs_mul]
      _ ≤ M*B+M*B := add_le_add
        (mul_le_mul (hmM j) (hφB y) (abs_nonneg _) hM)
        (mul_le_mul (hmM i) (hφB x) (abs_nonneg _) hM)
      _ = 2*M*B := by ring
    rw [← he',abs_mul,abs_of_pos hcp] at hh
    simp only [Int.cast_sub] at hd
    nlinarith

end ThreeTorus
end
end

section

/-! A genuine signal passage, not an abstract transmission oracle. The signal
prime modulus and strength bound precede all packet scales; one sufficiently
large integral carrier fixes the explicit positive law, and the SAME literal
retained coefficients satisfy geometry, physical and spectral conclusions. -/
noncomputable section
open MeasureTheory Set Function Filter
open scoped Topology BigOperators FourierTransform
namespace ThreeTorus

universe u

/-- The full conclusion of the actual quantile passage. This abbreviation
contains geometry, exact Fourier coefficients, all moments, and both errors;
its constructor below assumes no one of these output conclusions. -/
def ActualQuantileFamily {ι : Type*}
    (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
    (A₀ : ι → UnitAddCircle → ℝ → ℂ) (V : ℝ → ℝ) (m : ι → ℤ)
    (l u R : ℝ) (ρ : ℝ → ℝ) {δ : ℝ} (c : LawCutoffs δ)
    (χ : ι → ℝ → UnitAddCircle → ℝ) (g : ι → UnitAddCircle → ℝ) (ε : ℝ) : Prop :=
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ Integrable ρ ∧
    (∀ y, 0 < ρ y) ∧ (∫ y, ρ y = 1) ∧
    ∃ Δ : ℕ → ℝ, ∃ H : ℕ → UnitAddCircle → UnitAddCircle,
      (∀ n, 0 < n → |Δ n| ≤ (n:ℝ)⁻¹) ∧ Tendsto Δ atTop (𝓝 0) ∧
      (∀ n, Continuous (H n)) ∧
      (∀ n (x : ℝ), H n (x:UnitAddCircle) =
        ((n:ℝ)*((∫ t in 0..x, V t)+Δ n*x):UnitAddCircle)) ∧
      let ψ := neutralCircleCutoff c
      let J := quantileCircleJitter ρ c
      let J₀ := lawJitter ρ c
      let σ := fun (n : ℕ) a => (((1+J a/n)/n:ℝ):UnitAddCircle)
      (∀ n, Smooth (torusPassage (H n) (σ n)) ∧
        Smooth (torusPassage (H n) (σ n)).symm ∧
        MeasurePreserving (torusPassage (H n) (σ n)) μ μ) ∧
      (∀ n, 0 < n → ∀ x : Cover,
        torusPassage (H n) (σ n) (project x) =
          project (passageFamily V J₀ 1 ((n:ℝ)⁻¹,Δ n) x) ∧
        (torusPassage (H n) (σ n)).symm (project x) =
          project (passageFamily V J₀ (-1) ((n:ℝ)⁻¹,Δ n) x)) ∧
      (∀ r : ℝ, ∀ K : Set Cover, IsCompact K → ∀ d : ℕ,
        TendstoUniformlyOn
          (fun (n : ℕ) x => iteratedFDeriv ℝ d (passageFamily V J₀ r ((n:ℝ)⁻¹,Δ n)) x)
          (fun x => iteratedFDeriv ℝ d (fun y : Cover => ![y 0+r*V (y 1),y 1,y 2]) x)
          atTop K) ∧
      ∃ S : ℕ → ι → Finset ℤ,
        (∀ n, 0 < n → ∀ i j, j ∈ S n i → j ≠ 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∉ S n i → ∀ a, χ i ((j:ℝ)/n) a = 0) ∧
        (∀ n, 0 < n → ∀ i j, j ∈ S n i ↔ ∃ a, χ i ((j:ℝ)/n) a ≠ 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          0 < n ∧ ∀ i,
          let f := retainedPassage (m i) (H n) (A i) (S n i) (fun j => χ i ((j:ℝ)/n)) ψ
          let p := exactRetainedPacketDensity (Ioo δ (1-δ)) J₀ ψ (χ i) (m i) H (A i) (S n i) n
          let w := stationaryWeight (Icc (l-R) (u+R)) (fun x => (m i:ℝ)*V x) (A₀ i 0)
          (∫ x : TripleTorus, ‖packet (m i) (A i) x-f (passageChart (H n) x)‖^2 ∂tripleVolume) <
            8*δ*(∫ u, ‖A i (u,0)‖^2 ∂AddCircle.haarAddCircle)+η ∧
          (∫ z, |p z-foldCircleDensity w z*g i ((n:ℤ) • z)| ∂AddCircle.haarAddCircle) <
            (∫ s, w s)*(4*δ+ε)+η ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p x) ∧
          (∀ k : ℤ, (∫ x : TripleTorus, starRingEnd ℂ (f x)*f (twistIter (σ n) k x) ∂tripleVolume) =
            ∫ z, (p z:ℂ)*fourier k z ∂AddCircle.haarAddCircle) ∧
          (∀ j u a, ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,a)‖ =
            ‖retainedAmplitude ψ (χ i) (m i) H (A i) n j (u,0)‖)

theorem exists_actual_signal_family
    {b D : ℝ} (hb : 0 < b) (hbD : b < D)
    {d : ℝ → ℂ} (hd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) d)
    (hdc : HasCompactSupport d) (hdr : ∀ v, d (-v) = starRingEnd ℂ (d v))
    (hd0 : d 0 = 0) (hds : support d ⊆ Icc (-D) D) :
    ∃ α : ℝ, ∃ L : ℕ, ∃ γ₀ : ℝ,
      0 < α ∧ α < b/2 ∧ 2 ≤ L ∧ D/b < L ∧ 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      (∀ v, 2*γ*‖d v‖ ≤ 1/2) ∧
      ∀ (ι : Type u) [Fintype ι], ∀ (B : ℝ), 0 < B → ∀ (m : ι → ℤ), (∀ i, b ≤ |(m i:ℝ)/B|) →
      ∀ (A : ι → UnitAddCircle × UnitAddCircle → ℂ)
        (A₀ : ι → UnitAddCircle → ℝ → ℂ) (φ : ℝ → ℝ) (o l u R : ℝ),
      (∀ i a x, x ∈ Ioc o (o+1) → A i ((x : UnitAddCircle),a) = A₀ i a x) →
      (∀ i a, ContDiff ℝ 2 (A₀ i a)) → (∀ i, Continuous (A₀ i).uncurry) →
      (∀ i, Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ i p.1) p.2)) →
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => A₀ i (p.2 : UnitAddCircle) p.1)) →
      (∀ i a, support (A₀ i a) ⊆ Ioc l u) →
      o ≤ l → u ≤ o+1 → l ≤ u → 0 < R →
      Periodic φ 1 → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ →
      (∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv φ x) →
      (∀ i, Continuous (A i)) →
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => A i (p.1,p.2))) →
      (∀ i a x, ‖A₀ i a x‖ = ‖A₀ i 0 x‖) →
      (∀ i u a, ‖A i (u,a)‖ = ‖A i (u,0)‖) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ C : ℕ in atTop,
        0 < C ∧
        (∀ i j x y, (m i:ℝ)*((C:ℝ)+φ x) = (m j:ℝ)*((C:ℝ)+φ y) → m i = m j) ∧
        ∀ δ : ℝ, ∀ c : LawCutoffs δ, 0 < δ → δ < 1/8 →
        ∀ χ : ι → ℝ → UnitAddCircle → ℝ,
        (∀ i, CylinderSmooth (χ i).uncurry) →
        (∀ i, Continuous (χ i).uncurry) → (∀ i, HasCompactSupport (χ i).uncurry) →
        (∀ i a, χ i 0 a = 0) → (∀ i s a, 0 ≤ χ i s a ∧ χ i s a ≤ 1) →
        (∀ i s a, stationaryWeight (Icc (l-R) (u+R))
          (fun x => (m i:ℝ)*((C:ℝ)+φ x)) (A₀ i a) s ≠ 0 → χ i s a = 1) →
        ActualQuantileFamily A A₀ (fun x => (C:ℝ)+φ x) m l u R
          (signalJitter α γ d (signalPrimeProduct L) B C) c χ
          (fun i => signalCircleModel (signalPrimeProduct L) γ B d (m i)) ε := by
  obtain ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,hγ⟩ :=
    exists_signal_family_law hb hbD hd hdc hdr hd0 hds
  refine ⟨α,L,γ₀,hα,hαb,hL,hLD,hγ₀,?_⟩
  intro γ hγp hγs
  obtain ⟨hdb,hlaw⟩ := hγ γ hγp hγs
  refine ⟨hdb,?_⟩
  intro ι inst B hB m hm A A₀ φ o l u R hA hA₀ hAc hAd hAr hsupp hlo huo hlu hR
    hpφ hφ hdφ hAcont hAs hmod hmodA ε hε
  have hmn i : m i ≠ 0 := by
    intro hz
    have hh := hm i
    simp only [hz,Int.cast_zero,zero_div,abs_zero] at hh
    linarith
  have hφcircle : Continuous hpφ.lift := by
    apply Continuous.quotient_lift
    exact hφ.continuous
  have hsep := eventually_integral_speed_separation m hpφ.lift hmn hφcircle
  have hρ := (tendsto_natCast_atTop_atTop : Tendsto (fun C : ℕ => (C:ℝ)) atTop atTop).eventually
    (hlaw ι B hB m hm φ hφ.continuous (Icc l u) isCompact_Icc (fun i => A₀ i 0)
      (fun i => (hsupp i 0).trans Ioc_subset_Icc_self) (Icc (l-R) (u+R)) ε hε)
  filter_upwards [hsep,hρ] with C hsepC hρC
  obtain ⟨_hCp,hρs,hρi,hρp,hρm,⟨C₁,hC₁,hC₁b,hρF⟩,hideal⟩ := hρC
  refine ⟨hsepC.1,fun i j x y => hsepC.2.2 i j (x:UnitAddCircle) (y:UnitAddCircle),?_⟩
  intro δ c hδ hδ' χ hχs hχc hcχ hzχ hχ hχW
  have hpV : Periodic (fun x => (C:ℝ)+φ x) 1 := fun x => by
    change (C:ℝ)+φ (x+1) = (C:ℝ)+φ x
    rw [hpφ x]
  have hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (C:ℝ)+φ x) :=
    contDiff_const.add hφ
  have hdV x (hx : x ∈ Icc (l-2*R) (u+2*R)) :
      0 < deriv (fun x => (C:ℝ)+φ x) x := by
    simpa only [deriv_const_add] using hdφ x hx
  have h0 i : 0 ∉ (fun x => (m i:ℝ)*((C:ℝ)+φ x)) '' Icc l u := by
    rintro ⟨x,_hx,he⟩
    exact hsepC.2.1 i (x:UnitAddCircle) he
  refine ⟨hρs,hρi,hρp,hρm,?_⟩
  exact exists_simultaneous_quantile_passage hmn hA hA₀ hAc hAd hAr hsupp hlo huo hlu hR
    hpV hV hdV h0 hAcont hAs hmod hmodA hρs hρi hρp hρm hC₁.le hC₁b hρF
    c hδ hδ' hχs hχc hcχ hzχ hχ hχW
    (fun i => continuous_signalCircleModel (signalPrimeProduct L) γ B d (m i)) hideal

end ThreeTorus
end
end

section

/-! Exact support tracking for the literal passage cutoffs.  The cutoffs are
chosen before the passage integer.  Every retained point is linked to a point
of the old support, so temporal tracking is not inferred from weak convergence.
The integral carrier disappears on the actual temporal circle. -/
noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators
namespace ThreeTorus

/-- Scalar cutoffs with an arbitrarily small stationary-image enlargement,
exactly disjoint angular ranges, and the required identity on the true weights. -/
theorem tracked_frequency_cutoffs {ι : Type*} [Finite ι]
    (m : ι → ℤ) (V : ℝ → ℝ) (K : ι → Set ℝ)
    (hV : Continuous V) (hK : ∀ i, IsCompact (K i))
    (h0 : ∀ i, 0 ∉ (fun x => (m i:ℝ)*V x) '' K i)
    (hsep : Pairwise (fun i j => Disjoint ((fun x => (m i:ℝ)*V x) '' K i)
      ((fun x => (m j:ℝ)*V x) '' K j)))
    {η : ℝ} (hη : 0 < η) :
    ∃ χ : ι → ℝ → ℝ,
      (∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ i) ∧ HasCompactSupport (χ i) ∧
        χ i 0 = 0 ∧ (∀ s, 0 ≤ χ i s ∧ χ i s ≤ 1) ∧
        (∀ s ∈ (fun x => (m i:ℝ)*V x) '' K i, χ i =ᶠ[𝓝 s] 1) ∧
        (∀ s ∈ tsupport (χ i), ∃ x ∈ K i, |s-(m i:ℝ)*V x| < η) ∧
        ∀ (C : Set ℝ) (A : ℝ → ℂ), support A ⊆ K i →
          ∀ s, stationaryWeight C (fun x => (m i:ℝ)*V x) A s ≠ 0 → χ i s = 1) ∧
      Pairwise (fun i j => Disjoint (tsupport (χ i)) (tsupport (χ j))) := by
  let E i := (fun x => (m i:ℝ)*V x) '' K i
  let O i := Metric.thickening η (E i) ∩ ({0}:Set ℝ)ᶜ
  have hE i : IsCompact (E i) := (hK i).image (continuous_const.mul hV)
  have hO i : IsOpen (O i) := Metric.isOpen_thickening.inter isOpen_compl_singleton
  have hEO i : E i ⊆ O i := fun s hs =>
    ⟨Metric.self_subset_thickening hη _ hs,fun he => h0 i (show 0 ∈ E i from he ▸ hs)⟩
  obtain ⟨χ,hχ,hd⟩ := finite_disjoint_frequency_cutoffs E O hE hO hEO hsep
  refine ⟨χ,fun i => ⟨(hχ i).1,(hχ i).2.1,?_,(hχ i).2.2.2.1,
    (hχ i).2.2.2.2,?_,?_⟩,hd⟩
  · by_contra hz
    exact ((hχ i).2.2.1 (subset_tsupport (χ i) hz)).2 rfl
  · intro s hs
    obtain ⟨z,⟨x,hx,rfl⟩,hz⟩ := Metric.mem_thickening_iff.mp (((hχ i).2.2.1 hs).1)
    exact ⟨x,hx,by simpa only [Real.dist_eq] using hz⟩
  · intro C A hA s hs
    exact ((hχ i).2.2.2.2 s (stationaryWeight_support_subset hA hs)).self_of_nhds

lemma circle_dist_le_real (x y : ℝ) :
    dist (x:UnitAddCircle) (y:UnitAddCircle) ≤ |x-y| := by
  rw [dist_eq_norm,← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma integral_carrier_circle (m c : ℤ) (v : ℝ) :
    ((m:ℝ)*((c:ℝ)+v):UnitAddCircle) = ((m:ℝ)*v:UnitAddCircle) := by
  rw [mul_add,AddCircle.coe_add]
  have he : ((m:ℝ)*(c:ℝ):UnitAddCircle) = 0 := by
    rw [← Int.cast_mul]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨m*c,by simp⟩
  rw [he,zero_add]

/-- The temporal displacement uses the SAME old support point as the index
location.  A large jitter changes only the final lower bound on `n`. -/
lemma passage_temporal_drift {s v J η : ℝ} {m c : ℤ} {n : ℕ}
    (hn : 0 < n) (hs : |s-(m:ℝ)*((c:ℝ)+v)| ≤ η) :
    dist ((s+s*J/n:ℝ):UnitAddCircle) ((m:ℝ)*v:UnitAddCircle) ≤
      η+|s| *|J|/n := by
  rw [← integral_carrier_circle m c v]
  apply (circle_dist_le_real _ _).trans
  calc
    |s+s*J/n-(m:ℝ)*((c:ℝ)+v)| = |(s-(m:ℝ)*((c:ℝ)+v))+s*J/n| := by congr 1; ring
    _ ≤ |s-(m:ℝ)*((c:ℝ)+v)|+|s*J/n| := abs_add_le _ _
    _ ≤ η+|s| *|J|/n := by
      rw [abs_div,abs_mul,abs_of_pos (show (0:ℝ)<n by exact_mod_cast hn)]
      exact add_le_add hs le_rfl

lemma passage_index_drift {s v c B D P η : ℝ} {m : ℤ}
    (hc : 0 < c) (hB : 0 < B) (hD : |(m:ℝ)/B| ≤ D) (hP : |v| ≤ P)
    (hs : |s-(m:ℝ)*(c+v)| ≤ η) :
    |s/(c*B)-(m:ℝ)/B| ≤ D*P/c+η/(c*B) := by
  have hBn : B ≠ 0 := ne_of_gt hB
  have hcn : c ≠ 0 := ne_of_gt hc
  have he : s/(c*B)-(m:ℝ)/B = ((m:ℝ)/B)*v/c+(s-(m:ℝ)*(c+v))/(c*B) := by
    field_simp
    ring
  have hPn : 0 ≤ P := (abs_nonneg _).trans hP
  rw [he]
  calc
    _ ≤ |((m:ℝ)/B)*v/c|+|(s-(m:ℝ)*(c+v))/(c*B)| := abs_add_le _ _
    _ = |(m:ℝ)/B| *|v|/c+|s-(m:ℝ)*(c+v)|/(c*B) := by
      simp only [abs_div,abs_mul,abs_of_pos hc,abs_of_pos hB]
    _ ≤ D*P/c+η/(c*B) := add_le_add
      (div_le_div_of_nonneg_right (mul_le_mul hD hP (abs_nonneg _) ((abs_nonneg _).trans hD)) hc.le)
      (div_le_div_of_nonneg_right hs (mul_pos hc hB).le)

lemma passage_retained_size {s v c P η : ℝ} {m : ℤ}
    (hc : 0 ≤ c) (hP : |v| ≤ P) (hs : |s-(m:ℝ)*(c+v)| ≤ η) :
    |s| ≤ |(m:ℝ)| *(c+P)+η := by
  calc
    |s| = |(m:ℝ)*(c+v)+(s-(m:ℝ)*(c+v))| := by congr 1; ring
    _ ≤ |(m:ℝ)*(c+v)|+|s-(m:ℝ)*(c+v)| := abs_add_le _ _
    _ ≤ |(m:ℝ)| *(c+P)+η := by
      apply add_le_add _ hs
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_add_le c v).trans (by rw [abs_of_nonneg hc]; linarith))
        (abs_nonneg _)

end ThreeTorus
end
end

end OAI
