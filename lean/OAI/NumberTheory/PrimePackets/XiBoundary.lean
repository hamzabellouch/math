import Mathlib
import OAI.NumberTheory.PrimePackets.RootOverlaps

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
namespace PrimeDegreePackets

def completedXiBoundaryValue (K : Type*) [Field K] [NumberField K] : ℂ :=
  completionExponential (Module.finrank ℚ K) |(NumberField.discr K:ℝ)| 1 *
    Complex.Gamma (1/2) ^ Module.finrank ℚ K * NumberField.dedekindZeta_residue K

lemma completedXiBoundaryValue_eq (K : Type*) [Field K] [NumberField K] :
    completedXiBoundaryValue K =
      (Real.sqrt |(NumberField.discr K:ℝ)| * NumberField.dedekindZeta_residue K : ℝ) := by
  have hD : 0 < |(NumberField.discr K:ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  let D := |(NumberField.discr K : ℝ)|
  let n := Module.finrank ℚ K
  calc
    _ = (D:ℂ)^((1:ℂ)/2) * Complex.Gammaℝ 1 ^ n * NumberField.dedekindZeta_residue K := by
      dsimp only [completedXiBoundaryValue,D,n]
      rw [completionExponential_eq_cpow _ hD,Complex.Gammaℝ_def,mul_pow]
      ring
    _ = (D:ℂ)^((1:ℂ)/2) * NumberField.dedekindZeta_residue K := by simp
    _ = _ := by
      rw [Complex.ofReal_mul,Real.sqrt_eq_rpow,Complex.ofReal_cpow hD.le]
      push_cast
      rfl

lemma completedXiBoundaryValue_ne_zero (K : Type*) [Field K] [NumberField K] :
    completedXiBoundaryValue K ≠ 0 := by
  unfold completedXiBoundaryValue
  exact mul_ne_zero (mul_ne_zero (completionExponential_ne_zero _ _ _)
    (pow_ne_zero _ (Complex.Gamma_ne_zero (half_ne_nonpositive_integer
      (s := 1) (by norm_num)))))
    (Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero K))

lemma tendsto_completedXi_from_right (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ => totallyRealCompletedXi K (s:ℂ)) (𝓝[>] 1)
      (𝓝 (completedXiBoundaryValue K)) := by
  let n := Module.finrank ℚ K
  let D := |(NumberField.discr K : ℝ)|
  have hE : ContinuousAt (fun t : ℝ => completionExponential n D (t:ℂ)) 1 :=
    ContinuousAt.comp (f := Complex.ofReal) ((completionExponential_hasDerivAt n D (1:ℂ)).continuousAt)
      Complex.continuous_ofReal.continuousAt
  have hG : ContinuousAt (fun t : ℝ => Complex.Gamma ((t:ℂ)/2)^n) 1 :=
    (ContinuousAt.comp (f := Complex.ofReal)
      (gammaHalf_hasDerivAt (s := (1:ℂ)) (by norm_num)).continuousAt
      Complex.continuous_ofReal.continuousAt).pow n
  have hP := (Complex.continuous_ofReal.continuousAt.mul hE).mul hG
  have H := (hP.tendsto.mono_left nhdsWithin_le_nhds).mul
    (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  convert H using 1
  · funext s
    dsimp only [totallyRealCompletedXi,n,D,Pi.mul_apply]
    ring
  · simp only [completedXiBoundaryValue,Pi.mul_apply,Complex.ofReal_one,one_mul,n,D]

@[simp] lemma totallyRealCompletedXi_one (K : Type*) [Field K] [NumberField K] :
    totallyRealCompletedXi K 1 = 0 := by simp [totallyRealCompletedXi]

 

lemma totallyRealCompletedXi_not_continuousAt_one
    (K : Type*) [Field K] [NumberField K] :
    ¬ ContinuousAt (fun t : ℝ => totallyRealCompletedXi K (t:ℂ)) 1 := by
  intro h
  have H := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
  have he := tendsto_nhds_unique (tendsto_completedXi_from_right K) H
  simp only [Complex.ofReal_one,totallyRealCompletedXi_one] at he
  exact completedXiBoundaryValue_ne_zero K he

end PrimeDegreePackets

open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
namespace PrimeDegreePackets

 

theorem bounded_discriminant_zeta_scale (N : ℕ) :
    ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K],
        (K →+* ℝ) → |NumberField.discr K| ≤ N →
        ∀ b : ℝ, Q^(3/4:ℝ) ≤ b →
          realDedekindZeta K (1+1/Real.log b) / Real.log b ≤
            2*NumberField.dedekindZeta_residue K := by
  obtain ⟨C,hC,δ,hδ,Hδ⟩ := bounded_discr_residue_comparison N
  have hlog : Tendsto (fun Q : ℝ => Real.log (Q^(3/4:ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [hlog.eventually_gt_atTop (1/δ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/4)).eventually_ge_atTop 2]
    with Q hQδ hQpow
  intro K _ _ σ hD b hb
  have hb2 := hQpow.trans hb
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  have hlt : 1/Real.log b < δ := by
    apply (one_div_lt hlogb hδ).mpr
    exact hQδ.trans_le (Real.log_le_log (by linarith) hb)
  have HR := ((Hδ K σ hD).2 (1/Real.log b) (one_div_pos.mpr hlogb) hlt).2
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using HR

theorem weightedIdeal_realInterval_bounded_discriminant (n : ℕ) (hn0 : 0 < n)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A₀ : ℝ, 1 ≤ A₀ → ∀ η : ℝ, 0 < η →
      ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice n K), (K →+* ℝ) →
        Module.finrank ℚ K = n → |NumberField.discr K| ≤ N →
        (saturationIndex M : ℝ) ≤ Q →
        ∀ x y : ℝ, Q^(3/4:ℝ) ≤ x → x ≤ A₀*Q → η*x ≤ y → y ≤ x →
          weightedIdealRealInterval M x y ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
            ENNReal.ofReal (C*y*NumberField.dedekindZeta_residue K) := by
  obtain ⟨C,hC,H⟩ := weightedIdeal_realInterval_zeta_bound n hn0
  refine ⟨C*2,mul_pos hC (by norm_num),?_⟩
  intro A₀ hA₀ η hη
  filter_upwards [H A₀ hA₀ η hη,bounded_discriminant_zeta_scale N,eventually_ge_atTop (0:ℝ)] with Q hQ hscale hQ0
  intro K _ _ _ M σ hn hD hq x y hxl hxu hrel hyx
  have hceil : Q^(3/4:ℝ) ≤ (⌈x⌉₊:ℝ) := hxl.trans (Nat.le_ceil x)
  have HR := hscale K σ hD _ hceil
  have hy : 0 ≤ y := le_trans (mul_nonneg hη.le (le_trans (Real.rpow_nonneg hQ0 _) hxl)) hrel
  apply (hQ K M hn hq x y hxl hxu hrel hyx).trans
  apply mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  calc
    C*y*((NumberField.dedekindZeta K (1+1/Real.log (⌈x⌉₊:ℝ))).re /
        Real.log (⌈x⌉₊:ℝ)) ≤ C*y*(2*NumberField.dedekindZeta_residue K) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le hy)
      simpa only [realDedekindZeta,Complex.ofReal_add,Complex.ofReal_one,
        Complex.ofReal_div] using HR
    _ = _ := by ring

 
theorem packet_cube_moment_bounded_discriminant (d : ℕ) (hodd : Odd (d+1))
    (N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → |NumberField.discr K| ≤ N → packetScale M = Q →
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
          (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*(θ^(d+1)+(Real.log Q)^d/Q^(1/4:ℝ))) := by
  obtain ⟨C,hC,Hcount⟩ := weightedIdeal_realInterval_bounded_discriminant (d+1) (by omega) N
  let s : ℝ := Fintype.card (Fin (d+1) → SignTypeˣ)
  let B := s*C*(logMomentConstant d+1)
  have hs : 0 < s := by dsimp [s]; positivity
  have hL := logMomentConstant_nonneg d
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [Hcount 1 le_rfl 1 zero_lt_one,eventually_ge_atTop (1:ℝ)] with Q hcount hQ
  intro K _ _ _ M σ hn hD hMQ θ hθ hθ1
  have hQ' : 1 ≤ packetScale M := hMQ ▸ hQ
  have H := packetMeasure_cube_moment_of_count M σ hn hodd hθ hθ1 hC.le hQ' (by
    intro t ht htQ
    apply hcount K M (σ 0) hn hD (by rw [← hMQ]; exact saturationIndex_le_packetScale M) t t
    · simpa only [hMQ] using ht
    · simpa only [one_mul,hMQ] using htQ
    · simp
    · rfl)
  apply H.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hMQ]
  have he : 0 ≤ (Real.log Q)^d/Q^(1/4:ℝ) :=
    div_nonneg (pow_nonneg (Real.log_nonneg hQ) _) (Real.rpow_nonneg (by linarith) _)
  have hθn := pow_nonneg hθ.le (d+1)
  dsimp only [B,s]
  nlinarith [mul_nonneg (mul_nonneg hs.le hC.le) (mul_nonneg hL he)]

 

theorem packet_tight_bounded_discriminant (d : ℕ) (hodd : Odd (d+1))
    (N : ℕ)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hD : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop) :
    IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  obtain ⟨B,hB,Hcube⟩ := packet_cube_moment_bounded_discriminant d hodd N
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨∅,isCompact_empty,fun _ _ => by simp [hεtop]⟩
  let e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  let θ := min (1/2:ℝ) (e/(4*B))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos he (by positivity))
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθe : B*θ^(d+1) ≤ e/4 := by
    have hpow : θ^(d+1) ≤ θ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hθ.le (pow_le_one₀ hθ.le hθ1)
    have he' := (le_div_iff₀ (show 0 < 4*B by positivity)).mp (min_le_right (1/2:ℝ) (e/(4*B)))
    dsimp only [θ] at hpow ⊢
    nlinarith
  have Herror := ((cusp_log_error_vanishes d).comp hQ).eventually_lt_const
    (show (0:ℝ) < e/(4*B) by positivity)
  have Hmass : ∀ᶠ i in atTop,
      packetMeasure (M i) (σ i) (thickLattices (d+1) θ)ᶜ ≤ ε := by
    filter_upwards [hQ.eventually Hcube,Herror] with i hi herror
    apply (cusp_mass_le_cube_moment (packetMeasure (M i) (σ i)) θ).trans
    apply (hi (K i) (M i) (σ i) (hn i) (hD i) rfl θ hθ hθ1).trans
    rw [← ENNReal.ofReal_toReal hεtop]
    apply ENNReal.ofReal_le_ofReal
    have H := (lt_div_iff₀ (show 0 < 4*B by positivity)).mp herror
    dsimp only [Function.comp_apply] at H
    change B*(θ^(d+1)+(Real.log (packetScale (M i)))^d/(packetScale (M i))^(1/4:ℝ)) ≤ e
    nlinarith
  obtain ⟨i₀,Hi⟩ := eventually_atTop.mp Hmass
  let F : Set (X (d+1)) := ⋃ i : Fin i₀, packetSupport (M i) (σ i)
  have hF : IsCompact F := isCompact_iUnion fun i : Fin i₀ =>
    packetSupport_isCompact (M i) (σ i) (hn i) hodd
  refine ⟨thickLattices (d+1) θ ∪ F,(mahler_compact d θ hθ).union hF,?_⟩
  rintro μ ⟨i,rfl⟩
  by_cases hi : i₀ ≤ i
  · exact (measure_mono (Set.compl_subset_compl.mpr Set.subset_union_left)).trans (Hi i hi)
  · have hs : packetSupport (M i) (σ i) ⊆ thickLattices (d+1) θ ∪ F := by
      intro x hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,Nat.lt_of_not_ge hi⟩,hx⟩)
    apply (measure_mono (Set.compl_subset_compl.mpr hs)).trans
    rw [packetMeasure_compl_support (M i) (σ i) (hn i) hodd]
    exact bot_le

 
theorem packet_probability_subsequence_bounded_discriminant (d : ℕ) (hodd : Odd (d+1))
    (N : ℕ)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hfieldD : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop) :
    ∃ (ν : ProbabilityMeasure (X (d+1))) («φ» : ℕ → ℕ), StrictMono «φ» ∧
      Tendsto (fun i => packetProbability (M («φ» i)) (σ («φ» i)) (hn («φ» i)) hodd)
        atTop (𝓝 ν) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  have htight := packet_tight_bounded_discriminant d hodd N K M σ hn hfieldD hQ
  let p := fun i => packetProbability (M i) (σ i) (hn i) hodd
  have ht : IsTightMeasureSet {((μ : ProbabilityMeasure (X (d+1))) : Measure (X (d+1))) |
      μ ∈ Set.range p} := by
    convert htight using 1
    ext μ
    simp only [Set.mem_ofPred_eq,Set.mem_range]
    constructor
    · rintro ⟨ν,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨p i,⟨i,rfl⟩,rfl⟩
  obtain ⟨ν,_,«φ»,hφ,hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet ht).tendsto_subseq
      (fun i => subset_closure (Set.mem_range_self i))
  exact ⟨ν,«φ»,hφ,hlim⟩

 
theorem packet_box_moment_bounded_discriminant (d : ℕ) (hodd : Odd (d+1))
    (N : ℕ)
    {b c : ℝ} (hb : 0 ≤ b) (hc : 0 < c) :
    ∃ B r₀ : ℝ, 0 < B ∧ 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < r₀ → ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → |NumberField.discr K| ≤ N → packetScale M = Q →
        ∀ w : Fin (d+1) → ℝ, (∀ i, c ≤ |w i|) → (∀ i, |w i| ≤ b) →
          (∫⁻ x, siegelTransform (boxIndicator w ε) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*ε^(d+1)) := by
  obtain ⟨A,hA,Hcount⟩ := weightedIdeal_realInterval_bounded_discriminant (d+1) (by omega) N
  obtain ⟨r₀,hr₀,Hpar⟩ := box_interval_parameters (n := d+1) (by omega) hb hc
  let C : ℝ := (d+1:ℕ)*(b+1)^(d+1)
  let A₀ : ℝ := b^(d+1)+2*C+1
  let B : ℝ := (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*(4/c)^d*(A*4*C)
  have hC : 0 < C := by dsimp [C]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,r₀,hB,hr₀,?_⟩
  intro ε hε hεr
  obtain ⟨hεc,hε1,hA₀,hη,Hε⟩ := Hpar ε hε hεr
  filter_upwards [Hε,Hcount A₀ hA₀ (4*C*ε/A₀) hη] with Q hQ hcount
  intro K _ _ _ M σ hn hD hscale w hwlo hwhi
  obtain ⟨hxl,hxu,hrel,hyx⟩ := hQ.2 w hwlo hwhi
  have hq : (saturationIndex M:ℝ) ≤ Q := hscale ▸ saturationIndex_le_packetScale M
  have H := hcount K M (σ 0) hn hD hq _ _ hxl hxu hrel hyx
  rw [← hscale] at H
  have H' : weightedIdealRealInterval M
      (((∏ i, |w i|)+2*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε)*packetScale M)
      (4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M) ≤
      (saturationIndex M : ℝ≥0∞)⁻¹ *
      ENNReal.ofReal (A*(4*((d+1:ℕ):ℝ)*(b+1)^(d+1)*ε*packetScale M)*
        NumberField.dedekindZeta_residue K) := by
    simpa only [C,mul_assoc] using H
  convert packetMeasure_box_moment_of_count M σ hn hodd w hb hc hwlo hwhi hε hεc hε1 hA.le H' using 1
  dsimp only [B,C]
  congr 1
  ring

 
theorem packet_ball_bound_bounded_discriminant (d : ℕ) (hodd : Odd (d+1))
    (N : ℕ)
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type u) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → |NumberField.discr K| ≤ N → packetScale M = Q →
        ∀ x ∈ Ω, packetMeasure M σ ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
          ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨b,c,hb,hc,Hvec⟩ := compact_uniform_vector_envelope hΩ
  obtain ⟨A,ε₀,hA,hε₀,Hbox⟩ := packet_box_moment_bounded_discriminant d hodd N hb.le hc
  let E : ℝ := (d+1:ℕ)*b
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨A*E^(d+1),ε₀/E,by positivity,div_pos hε₀ hE,?_⟩
  intro r hr hrr
  have hrε : E*r < ε₀ := by nlinarith [(lt_div_iff₀ hE).mp hrr]
  filter_upwards [Hbox (E*r) (mul_pos hE hr) hrε] with Q hQ
  intro K _ _ _ M σ hn hD hMQ x hx
  obtain ⟨g,hg,z,hz⟩ := Hvec x hx
  have hzne : z ≠ 0 := by
    intro he
    have H : c < (0:ℝ) := by simpa [he,Matrix.vecMul,dotProduct] using (hz 0).1
    exact hc.not_gt H
  have hlo (i) : c ≤ |integerRowMap g.1 z i| := by
    simpa only [integerRowMap_apply] using (hz i).1.le
  have hhi (i) : |integerRowMap g.1 z i| ≤ b := by
    simpa only [integerRowMap_apply] using (hz i).2.le
  have hsum : (∑ i, |integerRowMap g.1 z i|) ≤ E := by
    calc
      _ ≤ ∑ _ : Fin (d+1), b := Finset.sum_le_sum fun i _ => hhi i
      _ = E := by simp [E]
  have H := right_ball_mass_le_box_moment (packetMeasure M σ) g z hzne hr.le
    (show r*(∑ i, |integerRowMap g.1 z i|) ≤ E*r by nlinarith)
  rw [hg] at H
  refine H.trans ((hQ K M σ hn hD hMQ (integerRowMap g.1 z) hlo hhi).trans_eq ?_)
  congr 1
  rw [mul_pow]
  ring

 
theorem packet_limit_ball_bound_bounded_discriminant (d : ℕ) (hodd : Odd (d+1))
    (N : ℕ)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hD : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν))
    {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧ ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → r < r₀ →
      (ν : Measure (X (d+1))) ((fun h => rightAction x h) '' matrixBall (d+1) r) ≤
        ENNReal.ofReal (C*r^(d+1)) := by
  obtain ⟨C,r₀,hC,hr₀,H⟩ := packet_ball_bound_bounded_discriminant d hodd N hΩ
  refine ⟨C,r₀,hC,hr₀,?_⟩
  intro x hx r hr hrr
  apply open_mass_le_of_probability_limit _ ν hlim (right_ball_isOpen x r)
  filter_upwards [hQ.eventually (H r hr hrr)] with i hi
  exact hi (K i) (M i) (σ i) (hn i) (hD i) rfl x hx

 

theorem packet_limit_positive_ergodic_components_bounded_discriminant
    (d : ℕ) (hodd : Odd (d+1))
    (N : ℕ)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (hfieldD : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hD : Tendsto (fun i => multiplierDiscriminant (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν)) :
    ∃ (m : MeasurableSpace (X (d+1))) (hm : m ≤ xMeasurableSpace (d+1)),
      let : MeasurableSpace (X (d+1)) := xMeasurableSpace (d+1)
      condExpKernel (ν : Measure (X (d+1))) m ∘ₘ (ν : Measure (X (d+1))).trim hm = ν ∧
      ∀ᵐ z ∂(ν : Measure (X (d+1))).trim hm,
        ErgodicSMul (Multiplicative (LogCoordinates d)) (X (d+1))
          (condExpKernel (ν : Measure (X (d+1))) m z) ∧
        0 < measureEntropy (condExpKernel (ν : Measure (X (d+1))) m z)
          (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
            (regularDiagonalWeights_sum d) 1)) := by
  have hQ := packetScale_tendsto_of_multiplierDiscriminant_tendsto
    (Nat.succ_pos d) K M hn hD
  apply diagonal_positive_ergodic_decomposition d ν
  · exact packet_limit_diagonal_invariant d hodd K M σ hn ν hlim
  · intro Ω hΩ
    exact packet_limit_ball_bound_bounded_discriminant d hodd N K M σ hn hfieldD hQ ν hlim hΩ

end PrimeDegreePackets


namespace PrimeDegreePackets.ThetaConstruction
variable {d : Type*} [Fintype d]

def integerVector (z : d → ℤ) : d → ℝ := fun i => z i

def torusProjection (x : d → ℝ) : UnitAddTorus d := fun i => x i

omit [Fintype d] in
lemma torusProjection_openQuotient : IsOpenQuotientMap (torusProjection (d := d)) := by
  exact IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

omit [Fintype d] in
lemma torusProjection_eq_iff (x y : d → ℝ) :
    torusProjection x = torusProjection y ↔ ∃ z : d → ℤ, y = x + integerVector z := by
  constructor
  · intro h
    have H (i : d) : ∃ z : ℤ, (z:ℝ) = -(x i) + y i := by
      have hi := QuotientAddGroup.eq.mp (congrFun h i)
      simpa only [AddSubgroup.mem_zmultiples_iff,zsmul_eq_mul,mul_one] using hi
    choose z hz using H
    exact ⟨z,funext (fun i => by dsimp [integerVector]; linarith [hz i])⟩
  · rintro ⟨z,rfl⟩
    funext i
    apply QuotientAddGroup.eq.mpr
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨z i,?_⟩
    simp [integerVector,zsmul_eq_mul]

def translate (f : C(d → ℝ,ℂ)) (z : d → ℤ) : C(d → ℝ,ℂ) :=
  f.comp (ContinuousMap.addRight (integerVector z))

def LocallyNormal (f : C(d → ℝ,ℂ)) : Prop :=
  ∀ K : TopologicalSpace.Compacts (d → ℝ),
    Summable (fun z : d → ℤ => ‖(translate f z).restrict K‖)

def periodizedReal (f : C(d → ℝ,ℂ)) : C(d → ℝ,ℂ) := ∑' z : d → ℤ, translate f z

lemma periodizedReal_apply (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedReal f x = ∑' z : d → ℤ, f (x + integerVector z) := by
  exact (ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hf) x).symm

lemma periodizedReal_per (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (x : d → ℝ) (z : d → ℤ) :
    periodizedReal f (x + integerVector z) = periodizedReal f x := by
  rw [periodizedReal_apply f hf,periodizedReal_apply f hf]
  convert (Equiv.addLeft z).tsum_eq (fun n : d → ℤ => f (x + integerVector n)) using 1
  apply tsum_congr
  intro n
  congr 1
  ext i
  simp [integerVector,add_assoc]

def torusRepresentative (y : UnitAddTorus d) : d → ℝ :=
  (UnitAddTorus.measurableEquivPiIoc (fun _ : d => 0) y).val

omit [Fintype d] in
lemma torusProjection_representative (y : UnitAddTorus d) :
    torusProjection (torusRepresentative y) = y := by
  exact (UnitAddTorus.measurableEquivPiIoc (fun _ : d => 0)).symm_apply_apply y

lemma periodizedReal_representative (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedReal f (torusRepresentative (torusProjection x)) = periodizedReal f x := by
  obtain ⟨z,hz⟩ := (torusProjection_eq_iff x (torusRepresentative (torusProjection x))).mp
    (torusProjection_representative _).symm
  rw [hz]
  exact periodizedReal_per f hf x z

def periodizedTorus (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) : C(UnitAddTorus d,ℂ) where
  toFun y := periodizedReal f (torusRepresentative y)
  continuous_toFun := by
    apply torusProjection_openQuotient.isQuotientMap.continuous_iff.mpr
    have he : (fun y => periodizedReal f (torusRepresentative y)) ∘ torusProjection =
        periodizedReal f := funext (periodizedReal_representative f hf)
    rw [he]
    exact (periodizedReal f).continuous

lemma periodizedTorus_apply (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f) (x : d → ℝ) :
    periodizedTorus f hf (torusProjection x) = ∑' z : d → ℤ, f (x + integerVector z) := by
  rw [periodizedTorus]
  change periodizedReal f (torusRepresentative (torusProjection x)) = _
  rw [periodizedReal_representative f hf,periodizedReal_apply f hf]

instance integerTranslationAction : AddAction (d → ℤ) (d → ℝ) where
  vadd z x := integerVector z + x
  zero_vadd x := by
    change integerVector 0 + x = x
    ext i
    simp [integerVector]
  add_vadd z w x := by
    change integerVector (z+w) + x = integerVector z + (integerVector w + x)
    ext i
    simp [integerVector,add_assoc]

instance integerTranslationMeasurable : MeasurableConstVAdd (d → ℤ) (d → ℝ) :=
  ⟨fun _ => measurable_const.add measurable_id⟩

instance integerTranslationPreservesVolume :
    VAddInvariantMeasure (d → ℤ) (d → ℝ) volume where
  measure_preimage_vadd z S hS := by
    exact (measurePreserving_add_left volume (integerVector z)).measure_preimage hS.nullMeasurableSet

def unitCube : Set (d → ℝ) := {x | ∀ i, x i ∈ Ioc (0:ℝ) 1}

lemma unitCube_fundamental : IsAddFundamentalDomain (d → ℤ) (unitCube (d := d)) volume := by
  apply IsAddFundamentalDomain.mk' (MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)).nullMeasurableSet
  intro x
  refine ⟨fun i => 1 - Int.ceil (x i),?_,?_⟩
  · intro i
    change 0 < ((1-Int.ceil (x i):ℤ):ℝ) + x i ∧
      ((1-Int.ceil (x i):ℤ):ℝ) + x i ≤ 1
    push_cast
    constructor <;> linarith [Int.ceil_lt_add_one (x i),Int.le_ceil (x i)]
  · intro z hz
    ext i
    have H := hz i
    change 0 < (z i:ℝ) + x i ∧ (z i:ℝ) + x i ≤ 1 at H
    have hc : Int.ceil (x i) = 1-z i := Int.ceil_eq_iff.mpr (by push_cast; constructor <;> linarith)
    omega

lemma integral_periodization (f : C(d → ℝ,ℂ)) (hf : Integrable f) :
    (∫ x in unitCube, ∑' z : d → ℤ, f (x + integerVector z)) = ∫ x, f x := by
  have hfd := unitCube_fundamental (d := d)
  have hn : (∑' z : d → ℤ, ∫⁻ x in unitCube, ‖f (z +ᵥ x)‖ₑ) ≠ ⊤ := by
    rw [←hfd.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)]
    exact hf.hasFiniteIntegral.ne
  have H := integral_tsum
    (fun z : d → ℤ => ((f.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable.restrict)) hn
  calc
    _ = ∫ x in unitCube, ∑' z : d → ℤ, f (z +ᵥ x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      apply tsum_congr
      intro z
      change f (x + integerVector z) = f (integerVector z + x)
      rw [add_comm]
    _ = _ := H.trans (hfd.integral_eq_tsum'' f hf).symm

omit [Fintype d] in
lemma torusProjection_add_integer (x : d → ℝ) (z : d → ℤ) :
    torusProjection (x + integerVector z) = torusProjection x :=
  ((torusProjection_eq_iff x (x + integerVector z)).mpr ⟨z,rfl⟩).symm

def fourierCharacter (m : d → ℤ) : C(d → ℝ,ℂ) :=
  (UnitAddTorus.mFourier (-m)).comp ⟨torusProjection,torusProjection_openQuotient.continuous⟩

lemma fourierCharacter_norm (m : d → ℤ) (x : d → ℝ) : ‖fourierCharacter m x‖ = 1 := by
  simp only [fourierCharacter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
    UnitAddTorus.mFourier,norm_prod]
  simp only [fourier_apply,Circle.norm_coe,Finset.prod_const_one]

lemma fourierCharacter_periodic (m z : d → ℤ) (x : d → ℝ) :
    fourierCharacter m (x + integerVector z) = fourierCharacter m x := by
  change UnitAddTorus.mFourier (-m) (torusProjection (x + integerVector z)) = _
  rw [torusProjection_add_integer]
  rfl

lemma integrable_character_mul (m : d → ℤ) (f : C(d → ℝ,ℂ))
    (hf : Integrable f) : Integrable (fourierCharacter m * f) := by
  apply hf.norm.mono' (fourierCharacter m * f).continuous.aestronglyMeasurable
  filter_upwards [] with x
  simp only [ContinuousMap.mul_apply,norm_mul,fourierCharacter_norm,one_mul]
  exact le_rfl

lemma fourierCoeff_periodizedTorus (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (hfInt : Integrable f) (m : d → ℤ) :
    UnitAddTorus.mFourierCoeff (periodizedTorus f hf) m = ∫ x, fourierCharacter m x * f x := by
  rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (fun _ => 0)]
  simp only [smul_eq_mul,zero_add]
  change (∫ x in unitCube, fourierCharacter m x * periodizedTorus f hf (torusProjection x)) = _
  calc
    _ = ∫ x in unitCube, ∑' z : d → ℤ, (fourierCharacter m * f) (x + integerVector z) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [periodizedTorus_apply,←tsum_mul_left]
      apply tsum_congr
      intro z
      rw [ContinuousMap.mul_apply,fourierCharacter_periodic]
    _ = _ := integral_periodization _ (integrable_character_mul m f hfInt)

 

theorem multivariate_poisson (f : C(d → ℝ,ℂ))
    (hf : LocallyNormal f)
    (hfInt : Integrable f)
    (hFourier : Summable (fun m : d → ℤ => ∫ x, fourierCharacter m x * f x))
    (x : d → ℝ) :
    (∑' z : d → ℤ, f (x + integerVector z)) =
      ∑' m : d → ℤ, (∫ y, fourierCharacter m y * f y) *
        UnitAddTorus.mFourier m (torusProjection x) := by
  have hs : Summable (UnitAddTorus.mFourierCoeff (periodizedTorus f hf)) := by
    exact hFourier.congr (fun m => (fourierCoeff_periodizedTorus f hf hfInt m).symm)
  have H := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (torusProjection x)
  simpa only [fourierCoeff_periodizedTorus f hf hfInt,smul_eq_mul,periodizedTorus_apply] using H.tsum_eq.symm

end PrimeDegreePackets.ThetaConstruction
end
end

end OAI
